use std::{collections::HashMap, sync::Mutex};

use egglog::{
    CommandOutput, Error, UserDefinedCommand,
    ast::{Command, Expr, Fact, Literal, ParseError},
    prelude::run_ruleset,
    scheduler::{Scheduler, SchedulerId},
};
use egglog_reports::RunReport;
use lazy_static::lazy_static;

pub struct RunExtendedSchedule;

pub trait SchedulerGen {
    fn new_scheduler(&self, egraph: &egglog::EGraph, args: &[Expr]) -> Box<dyn Scheduler>;
}

type SchedulerBuilder = Box<dyn Fn(&egglog::EGraph, &[Expr]) -> Box<dyn Scheduler> + Send + Sync>;

struct ScheduleState {
    schedulers: Vec<(String, SchedulerId)>,
}

lazy_static! {
    static ref scheduler_libs: Mutex<HashMap<String, SchedulerBuilder>> = {
        Mutex::new(HashMap::from_iter([
            (
                "back-off".into(),
                Box::new(schedulers::new_back_off_scheduler) as SchedulerBuilder,
            ),
            (
                "round-robin-back-off".into(),
                Box::new(schedulers::new_round_robin_back_off_scheduler) as SchedulerBuilder,
            ),
        ]))
    };
}

pub fn add_scheduler_builder(name: String, builder: SchedulerBuilder) {
    scheduler_libs.lock().unwrap().insert(name, builder);
}

impl ScheduleState {
    fn new() -> Self {
        Self { schedulers: vec![] }
    }

    // temp fix, may want to change something in egglog
    fn evaluate_until(
        &mut self,
        egraph: &mut egglog::EGraph,
        cond: &Expr,
    ) -> Result<bool, egglog::Error> {
        let check = Command::Check(cond.span(), vec![Fact::Fact(cond.clone())]);
        match egraph.run_program(vec![check]) {
            Ok(_) => Ok(true),
            Err(Error::CheckError(..)) => Ok(false),
            Err(e) => Err(e),
        }
    }

    // Current limitation: because it relies on the publicly available Rust APIs to access
    // the egraph, it has to split the same schedule into multiple runs. This means
    // - the same condition may be compiled and type checked multiple times
    // - the logging information may show that multiple schedules are run, but they
    //   are actually the same schedule.
    fn run(&mut self, egraph: &mut egglog::EGraph, arg: &Expr) -> Result<RunReport, egglog::Error> {
        let err = || {
            Err(egglog::Error::ParseError(ParseError(
                arg.span(),
                "Invalid schedule".into(),
            )))
        };

        if let Expr::Var(_, ruleset) = arg {
            let output = run_ruleset(egraph, ruleset.as_str())?;
            assert!(output.len() == 1);
            if let CommandOutput::RunSchedule(report) = &output[0] {
                return Ok(report.clone());
            }
            panic!("Expected a RunSchedule, got {:?}", output[0]);
        }

        let Expr::Call(span, head, exprs) = arg else {
            return err();
        };

        macro_rules! new_scope {
            ($f:expr) => {{
                let curr_scope = self.schedulers.len();
                let res: Result<RunReport, egglog::Error> = $f();
                self.schedulers.truncate(curr_scope);
                res
            }};
        }

        match head.as_str() {
            "let-scheduler" => match exprs.as_slice() {
                [Expr::Var(_, name), Expr::Call(_, scheduler_name, args)] => {
                    if self.schedulers.iter().any(|(n, _)| n == name) {
                        return Err(egglog::Error::ParseError(ParseError(
                            span.clone(),
                            format!("Scheduler {name} already exists"),
                        )));
                    }
                    let scheduler =
                        (scheduler_libs.lock().unwrap().get(scheduler_name).unwrap())(egraph, args);
                    let id = egraph.add_scheduler(scheduler);
                    self.schedulers.push((name.clone(), id));
                    Ok(RunReport::default())
                }
                _ => err(),
            },
            "run" | "run-with" => {
                let mut scheduler = None;
                let exprs: &[egglog::ast::Expr] = if head.as_str() == "run-with" {
                    let Expr::Var(_, ref scheduler_name) = exprs[0] else {
                        return err();
                    };
                    scheduler = Some(
                        self.schedulers
                            .iter()
                            .rfind(|(n, _)| n == scheduler_name)
                            .unwrap()
                            .1,
                    );
                    &exprs[1..]
                } else {
                    &exprs[..]
                };
                // Parsing
                let (ruleset, rest) = match exprs.first() {
                    None => ("", exprs),
                    Some(Expr::Var(_span, v)) if *v == ":until" => ("", exprs),
                    Some(Expr::Var(_span, ruleset)) => (ruleset.as_str(), &exprs[1..]),
                    _ => unreachable!(),
                };

                let until = match rest {
                    [] => None,
                    [Expr::Var(_span, ut), cond] if ut == ":until" => Some(cond.clone()),
                    _ => return err(),
                };

                if let Some(until) = until {
                    if self.evaluate_until(egraph, &until)? {
                        return Ok(RunReport::default());
                    }
                }

                if let Some(scheduler) = scheduler {
                    egraph.step_rules_with_scheduler(scheduler, ruleset)
                } else {
                    // Running the ruleset
                    egraph.step_rules(ruleset)
                }
            }
            "saturate" => {
                let mut report = RunReport::default();
                loop {
                    let iter_report = new_scope!(|| {
                        let mut iter_report = RunReport::default();
                        for expr in exprs {
                            let res = self.run(egraph, expr)?;
                            iter_report.union(res);
                        }
                        Ok(iter_report)
                    })?;
                    if !iter_report.updated {
                        break;
                    }
                    report.union(iter_report);
                }
                Ok(report)
            }
            "seq" => {
                new_scope!(|| {
                    let mut report = RunReport::default();
                    for expr in exprs {
                        // Recursively run each expression in the sequence
                        let res = self.run(egraph, expr)?;
                        report.union(res);
                    }
                    Ok(report)
                })
            }
            "repeat" => {
                match exprs.as_slice() {
                    [Expr::Lit(_span, Literal::Int(n)), rest @ ..] => {
                        let mut report = RunReport::default();
                        for _ in 0..*n {
                            let sub_report = new_scope!(|| {
                                let mut report = RunReport::default();
                                // Recursively run the rest of the expressions
                                for expr in rest {
                                    let res = self.run(egraph, expr)?;
                                    report.union(res);
                                }
                                Ok(report)
                            })?;
                            report.union(sub_report);
                        }
                        Ok(report)
                    }
                    _ => err(),
                }
            }
            _ => Err(egglog::Error::ParseError(ParseError(
                span.clone(),
                "Invalid schedule".into(),
            ))),
        }
    }
}

impl UserDefinedCommand for RunExtendedSchedule {
    fn update(
        &self,
        egraph: &mut egglog::EGraph,
        args: &[Expr],
    ) -> Result<Option<CommandOutput>, egglog::Error> {
        let mut schedule = ScheduleState::new();
        let mut report = RunReport::default();
        for arg in args {
            report.union(schedule.run(egraph, arg)?);
        }
        Ok(Some(CommandOutput::RunSchedule(report)))
    }
}

pub(crate) fn parse_tags(args: &[Expr]) -> HashMap<String, Literal> {
    let mut tags = HashMap::new();
    assert!(args.len().is_multiple_of(2));
    for arg in args.chunks(2) {
        let Expr::Var(_, ref tag_name) = arg[0] else {
            panic!("Invalid tag name: {:?}", arg[0]);
        };
        let Expr::Lit(_, lit) = &arg[1] else {
            panic!("Invalid tag value: {:?}", arg[1]);
        };
        if tags.contains_key(&tag_name.to_string()) {
            panic!("Tag name already exists: {:?}", tag_name);
        }
        tags.insert(tag_name.to_string(), lit.clone());
    }
    tags
}

mod schedulers {
    use std::collections::{HashMap, HashSet};

    use egglog::{
        ast::{Expr, Literal},
        scheduler::{Matches, Scheduler},
    };
    use log::{debug, info};

    use crate::parse_tags;

    fn usize_tag(tags: &HashMap<String, Literal>, name: &str) -> Option<usize> {
        tags.get(name).map(|lit| {
            let Literal::Int(n) = lit else {
                panic!("Invalid {}: {:?}", name, lit);
            };
            *n as usize
        })
    }

    pub(super) fn new_back_off_scheduler(
        _egraph: &egglog::EGraph,
        args: &[Expr],
    ) -> Box<dyn Scheduler> {
        let tags = parse_tags(args);
        Box::new(BackOffScheduler {
            default_match_limit: usize_tag(&tags, ":match-limit").unwrap_or(1000),
            default_ban_length: usize_tag(&tags, ":ban-length").unwrap_or(5),
            stats: HashMap::new(),
        })
    }

    #[derive(Debug, Clone)]
    pub struct BackOffScheduler {
        default_match_limit: usize,
        default_ban_length: usize,
        stats: HashMap<String, RuleStats>,
    }

    #[derive(Debug, Clone)]
    struct RuleStats {
        iteration: usize,
        times_applied: usize,
        banned_until: usize,
        times_banned: usize,
        match_limit: usize,
        ban_length: usize,
    }

    enum BackOffDecision {
        Ban,
        Admit,
    }

    impl BackOffScheduler {
        pub(super) fn is_banned(&self, rule: &str) -> bool {
            self.stats
                .get(rule)
                .is_some_and(|s| s.iteration < s.banned_until)
        }

        fn get_stats(&mut self, rule: String) -> &mut RuleStats {
            self.stats.entry(rule).or_insert_with(|| RuleStats {
                times_applied: 0,
                banned_until: 0,
                times_banned: 0,
                match_limit: self.default_match_limit,
                ban_length: self.default_ban_length,
                iteration: 0,
            })
        }

        fn decide(&mut self, rule: &str, match_size: usize) -> BackOffDecision {
            let stats = self.get_stats(rule.to_owned());
            stats.iteration += 1;

            if stats.iteration < stats.banned_until {
                debug!(
                    "Skipping {} ({}-{}), banned until {}...",
                    rule, stats.times_applied, stats.times_banned, stats.banned_until,
                );
                return BackOffDecision::Ban;
            }

            let threshold = stats
                .match_limit
                .checked_shl(stats.times_banned as u32)
                .unwrap();
            if match_size > threshold {
                let ban_length = stats.ban_length << stats.times_banned;
                stats.times_banned += 1;
                stats.banned_until = stats.iteration + ban_length;
                info!(
                    "Banning {} ({}-{}) for {} iters: {} < {}",
                    rule,
                    stats.times_applied,
                    stats.times_banned,
                    ban_length,
                    threshold,
                    match_size,
                );
                BackOffDecision::Ban
            } else {
                stats.times_applied += 1;
                BackOffDecision::Admit
            }
        }
    }

    impl Scheduler for BackOffScheduler {
        fn can_stop(&mut self, rules: &[&str], _ruleset: &str) -> bool {
            let stats = &mut self.stats;
            let n_stats = stats.len();

            let mut banned: Vec<(&str, RuleStats)> = rules
                .iter()
                .filter_map(|rule| {
                    let s = stats.remove(*rule)?;
                    if s.banned_until > s.iteration {
                        Some((*rule, s))
                    } else {
                        None
                    }
                })
                .collect();

            let result = if banned.is_empty() {
                true
            } else {
                let min_delta = banned
                    .iter()
                    .map(|(_, s)| {
                        assert!(s.banned_until >= s.iteration);
                        s.banned_until - s.iteration
                    })
                    .min()
                    .expect("banned cannot be empty here");

                let mut unbanned = vec![];
                for (name, s) in &mut banned {
                    s.banned_until -= min_delta;
                    if s.banned_until == s.iteration {
                        unbanned.push(*name);
                    }
                }

                assert!(!unbanned.is_empty());
                info!(
                    "Banned {}/{}, fast-forwarded by {} to unban {}",
                    banned.len(),
                    n_stats,
                    min_delta,
                    unbanned.join(", "),
                );

                false
            };

            // Recover the banned stats
            for (rule, s) in banned {
                stats.insert(rule.to_owned(), s);
            }

            result
        }

        fn filter_matches(&mut self, rule: &str, _ruleset: &str, matches: &mut Matches) -> bool {
            match self.decide(rule, matches.match_size()) {
                BackOffDecision::Ban => false,
                BackOffDecision::Admit => {
                    debug!("Choosing all matches for {}", rule);
                    matches.choose_all();
                    true
                }
            }
        }
    }

    pub(super) fn new_round_robin_back_off_scheduler(
        _egraph: &egglog::EGraph,
        args: &[Expr],
    ) -> Box<dyn Scheduler> {
        let tags = parse_tags(args);
        Box::new(RoundRobinBackoffScheduler {
            backoff: BackOffScheduler {
                default_match_limit: usize_tag(&tags, ":match-limit").unwrap_or(1000),
                default_ban_length: usize_tag(&tags, ":ban-length").unwrap_or(5),
                stats: HashMap::new(),
            },
            rule_order: Vec::new(),
            phase: Phase::Cache,
            seen_this_call: HashSet::new(),
            any_collected_this_cycle: false,
            started: false,
        })
    }

    // Applies one rule's matches per `step_rules_with_scheduler` call, wrapped
    // around a `BackOffScheduler`. Each cycle is `#rules + 1` calls:
    //   Cache call:      queries run; all matches stay as residuals (chosen: none).
    //   Drain(i) calls:  no re-query; rule_order[i]'s residuals are passed to the
    //                    inner BackOffScheduler, which decides ban/admit.
    // The caller's `:until` is evaluated between phases, so the egraph size is
    // sampled `#rules` times more often than under the default scheduler.
    //
    // The scheduler depends on the ruleset size/order, so a new scheduler should be created per ruleset.
    #[derive(Debug, Clone)]
    pub struct RoundRobinBackoffScheduler {
        backoff: BackOffScheduler,
        rule_order: Vec<String>,
        phase: Phase,
        seen_this_call: HashSet<String>,
        any_collected_this_cycle: bool,
        started: bool,
    }

    #[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
    enum Phase {
        #[default]
        Cache,
        Drain(usize),
    }

    impl RoundRobinBackoffScheduler {
        fn advance(&mut self) {
            let n = self.rule_order.len();
            self.phase = match self.phase {
                Phase::Cache if n > 0 => Phase::Drain(0),
                Phase::Cache => Phase::Cache,
                Phase::Drain(i) if i + 1 < n => Phase::Drain(i + 1),
                Phase::Drain(_) => {
                    self.any_collected_this_cycle = false;
                    Phase::Cache
                }
            };
        }
    }

    impl Scheduler for RoundRobinBackoffScheduler {
        fn can_stop(&mut self, rules: &[&str], ruleset: &str) -> bool {
            self.phase == Phase::Cache
                && !self.any_collected_this_cycle
                && self.backoff.can_stop(rules, ruleset)
        }

        fn filter_matches(&mut self, rule: &str, ruleset: &str, matches: &mut Matches) -> bool {
            // Re-seeing a rule means a new step_rules_with_scheduler call started.
            if self.seen_this_call.contains(rule) {
                self.advance();
                self.seen_this_call.clear();
            }
            self.seen_this_call.insert(rule.to_string());

            match self.phase {
                Phase::Cache => {
                    if !self.started {
                        self.rule_order.push(rule.to_string());
                    }
                    if matches.match_size() > 0 {
                        self.any_collected_this_cycle = true;
                    }
                    debug!(
                        "round-robin-back-off cache: {} ({} matches buffered)",
                        rule,
                        matches.match_size()
                    );
                    false
                }
                Phase::Drain(idx) => {
                    self.started = true;
                    let is_last = idx + 1 == self.rule_order.len();
                    if self.rule_order.get(idx).is_some_and(|r| r == rule) {
                        let _ = self.backoff.filter_matches(rule, ruleset, matches);
                    }
                    // Re-seek on the last drain for every rule that isn't currently banned,
                    // so the next Cache call skips queries for banned rules.
                    is_last && !self.backoff.is_banned(rule)
                }
            }
        }
    }
}
