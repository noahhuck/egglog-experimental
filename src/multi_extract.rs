//! An implementation of multi-extraction for egraphs.
//! Adds support for extracting multiple terms with a single command,
//! reducing the overhead of creating an extractor for each term.
//! The syntax for multi-extraction is `(multi-extract n t1 ... tm)`,
//! where n must be a positive i64.
//! This command will extract n lowest-cost variants of each of the m terms.
//! `(multi-extract 1 t)` is equivalent to `(extract t)`.

use egglog::{
    CommandOutput, EGraph, Error, Term, TermDag, TermId, TypeError, UserDefinedCommand,
    ast::Expr,
    extract::{Cost, CostModel, Extractor},
    util::{FreshGen, SymbolGen},
};
use log::log_enabled;
use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    marker::PhantomData,
};

const MAX_PRETTY_LINE_WIDTH: usize = 80;
const PRETTY_INDENT_STEP: usize = 2;
const MIN_SHARED_TERM_SIZE: usize = 4;

#[derive(Debug)]
pub struct MultiExtractOutput {
    termdag: TermDag,
    terms: Vec<Vec<TermId>>,
}

#[derive(Clone)]
struct RenderedTerm {
    inline: String,
    pretty: String,
}

impl RenderedTerm {
    fn from_symbol(symbol: String) -> Self {
        Self {
            inline: symbol.clone(),
            pretty: symbol,
        }
    }

    fn is_multiline(&self) -> bool {
        self.pretty.contains('\n')
    }
}

struct RenderContext {
    fresh: SymbolGen,
    ref_counts: HashMap<TermId, usize>,
    sizes: HashMap<TermId, usize>,
    bindings: HashMap<TermId, String>,
    buf: String,
}

fn collect_ref_counts(
    termdag: &TermDag,
    term_id: TermId,
    counts: &mut HashMap<TermId, usize>,
    visited: &mut HashSet<TermId>,
) {
    *counts.entry(term_id).or_insert(0) += 1;
    if !visited.insert(term_id) {
        return;
    }
    if let Term::App(_, children) = termdag.get(term_id) {
        for child in children {
            collect_ref_counts(termdag, *child, counts, visited);
        }
    }
}

fn compute_term_size(
    termdag: &TermDag,
    term_id: TermId,
    sizes: &mut HashMap<TermId, usize>,
) -> usize {
    if let Some(size) = sizes.get(&term_id) {
        return *size;
    }
    let size = match termdag.get(term_id) {
        Term::App(_, children) => {
            1 + children
                .iter()
                .map(|child| compute_term_size(termdag, *child, sizes))
                .sum::<usize>()
        }
        Term::Lit(_) | Term::Var(_) => 1,
    };
    sizes.insert(term_id, size);
    size
}

fn collect_multi_term_stats(
    termdag: &TermDag,
    all_term_ids: &[TermId],
) -> (HashMap<TermId, usize>, HashMap<TermId, usize>) {
    let mut counts = HashMap::default();
    let mut visited = HashSet::default();
    for &term_id in all_term_ids {
        collect_ref_counts(termdag, term_id, &mut counts, &mut visited);
    }
    let mut sizes = HashMap::default();
    for &term_id in all_term_ids {
        compute_term_size(termdag, term_id, &mut sizes);
    }
    (counts, sizes)
}

fn render_term(
    termdag: &TermDag,
    term_id: TermId,
    ctx: &mut RenderContext,
    allow_binding: bool,
    indent: usize,
) -> RenderedTerm {
    if let Some(existing) = ctx.bindings.get(&term_id) {
        return RenderedTerm::from_symbol(existing.clone());
    }

    let constructor_name = match termdag.get(term_id) {
        Term::App(name, _) => Some(name.clone()),
        _ => None,
    };

    let rendered = match termdag.get(term_id) {
        Term::App(name, children) => {
            let mut child_renderings = Vec::with_capacity(children.len());
            for child_id in children {
                let rendered_child =
                    render_term(termdag, *child_id, ctx, true, indent + PRETTY_INDENT_STEP);
                child_renderings.push(rendered_child);
            }

            let mut inline = format!("({name}");
            for child in &child_renderings {
                inline.push(' ');
                inline.push_str(&child.inline);
            }
            inline.push(')');

            let inline_len = inline.chars().count();
            let exceeds_width = indent + inline_len > MAX_PRETTY_LINE_WIDTH;
            let child_multiline = child_renderings.iter().any(|c| c.is_multiline());

            let pretty = if exceeds_width || child_multiline {
                if child_renderings.is_empty() {
                    format!("({name})")
                } else {
                    let mut s = format!("({name}");
                    for (idx, child) in child_renderings.iter().enumerate() {
                        s.push('\n');
                        s.push_str(&" ".repeat(indent + PRETTY_INDENT_STEP));
                        s.push_str(&child.pretty);
                        if idx + 1 == child_renderings.len() {
                            s.push(')');
                        }
                    }
                    s
                }
            } else {
                inline.clone()
            };

            RenderedTerm { inline, pretty }
        }
        Term::Lit(lit) => {
            let repr = format!("{lit}");
            RenderedTerm {
                inline: repr.clone(),
                pretty: repr,
            }
        }
        Term::Var(v) => RenderedTerm {
            inline: v.clone(),
            pretty: v.clone(),
        },
    };

    let term_size = *ctx.sizes.get(&term_id).unwrap_or(&1);
    let repeat_count = ctx.ref_counts.get(&term_id).copied().unwrap_or(1);
    let should_bind = allow_binding && repeat_count > 1 && term_size >= MIN_SHARED_TERM_SIZE;

    if should_bind {
        let hint = constructor_name.as_deref().unwrap_or("t");
        let let_name: String = ctx.fresh.fresh(hint);
        push_binding(&mut ctx.buf, &let_name, &rendered.pretty);
        ctx.bindings.insert(term_id, let_name.clone());
        RenderedTerm::from_symbol(let_name)
    } else {
        rendered
    }
}

fn push_binding(buf: &mut String, name: &str, body: &str) {
    let trimmed = body.trim_end();
    if trimmed.is_empty() {
        buf.push_str("(let ");
        buf.push_str(name);
        buf.push_str(")\n");
        return;
    }

    if trimmed.contains('\n') {
        buf.push_str("(let ");
        buf.push_str(name);
        buf.push('\n');
        let lines: Vec<&str> = trimmed.lines().collect();
        for (idx, line) in lines.iter().enumerate() {
            buf.push_str(&" ".repeat(PRETTY_INDENT_STEP));
            buf.push_str(line);
            if idx + 1 < lines.len() {
                buf.push('\n');
            } else {
                buf.push(')');
                buf.push('\n');
            }
        }
    } else {
        buf.push_str("(let ");
        buf.push_str(name);
        buf.push(' ');
        buf.push_str(trimmed);
        buf.push_str(")\n");
    }
}

impl std::fmt::Display for MultiExtractOutput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let all_term_ids: Vec<TermId> = self
            .terms
            .iter()
            .flat_map(|variants| variants.iter().copied())
            .collect();

        let (ref_counts, sizes) = collect_multi_term_stats(&self.termdag, &all_term_ids);

        let mut ctx = RenderContext {
            fresh: SymbolGen::new("__".to_string()),
            ref_counts,
            sizes,
            bindings: HashMap::default(),
            buf: String::new(),
        };

        let mut rendered_groups: Vec<Vec<String>> = Vec::new();
        for variants in &self.terms {
            let mut rendered_variants = Vec::new();
            for &expr in variants {
                let rendered = render_term(&self.termdag, expr, &mut ctx, true, 6);
                rendered_variants.push(rendered.pretty);
            }
            rendered_groups.push(rendered_variants);
        }

        if !ctx.buf.is_empty() {
            write!(f, "{}", ctx.buf)?;
        }
        writeln!(f, "(")?;
        for rendered_variants in &rendered_groups {
            writeln!(f, "   (")?;
            for expr_str in rendered_variants {
                writeln!(f, "      {expr_str}")?;
            }
            writeln!(f, "   )")?;
        }
        writeln!(f, ")")
    }
}

pub struct MultiExtract<C: Cost + Ord + Eq + Clone + Debug + Send + Sync, CM: CostModel<C> + Clone>
{
    cost_model: CM,
    _cost_t: PhantomData<C>,
}

impl<C: Cost + Ord + Eq + Clone + Debug + Send + Sync, CM: CostModel<C> + Clone>
    MultiExtract<C, CM>
{
    pub fn new(cost_model: CM) -> Self {
        MultiExtract {
            cost_model,
            _cost_t: PhantomData,
        }
    }
}

impl<
    C: Cost + Ord + Eq + Clone + Debug + Send + Sync,
    CM: CostModel<C> + Clone + Send + Sync + 'static,
> UserDefinedCommand for MultiExtract<C, CM>
{
    fn update(&self, egraph: &mut EGraph, args: &[Expr]) -> Result<Option<CommandOutput>, Error> {
        assert!(args.len() >= 2);

        let (variants_sort, variants_value) = egraph.eval_expr(&args[0])?;
        if variants_sort.name() != "i64" {
            return Err(Error::TypeError(TypeError::Mismatch {
                expr: args[0].clone(),
                expected: egraph.get_arcsort_by(|s| s.name() == "i64"),
                actual: variants_sort,
            }));
        }

        let n: i64 = egraph.value_to_base(variants_value);
        if n < 0 {
            panic!("Cannot extract negative number of variants");
        }

        let (sorts, values): (Vec<_>, Vec<_>) = args[1..]
            .iter()
            .map(|arg| egraph.eval_expr(arg))
            .collect::<Result<_, _>>()?;

        let mut termdag = TermDag::default();
        let extractor = Extractor::compute_costs_from_rootsorts(
            Some(sorts.clone()),
            egraph,
            self.cost_model.clone(),
        );

        let terms: Vec<Vec<_>> = values
            .into_iter()
            .zip(sorts)
            .map(|(value, sort)| {
                extractor
                    .extract_variants_with_sort(egraph, &mut termdag, value, n as usize, sort)
                    .into_iter()
                    .map(|e| e.1)
                    .collect()
            })
            .collect();

        if log_enabled!(log::Level::Info) {
            log::info!(
                "extracted {} variants for each of {} expressions",
                n,
                terms.len()
            );
        }

        Ok(Some(CommandOutput::UserDefined(std::sync::Arc::from(
            MultiExtractOutput { termdag, terms },
        ))))
    }
}
