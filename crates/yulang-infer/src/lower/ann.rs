use std::collections::HashMap;

use rowan::TextRange;
use yulang_parser::lex::SyntaxKind;

use super::{LowerState, SyntaxNode};
use crate::diagnostic::{ConstraintCause, ConstraintReason, TypeOrigin, TypeOriginKind};
use crate::lower::signature::{SigRow, SigType, SigVar};
use crate::scheme::{collect_neg_free_vars, collect_pos_free_vars};
use crate::symbols::{Name, Path};
use crate::types::{EffectAtom, Neg, Pos};

#[derive(Debug, Clone)]
pub struct LoweredPatAnn {
    pub eff: Option<LoweredEffAnn>,
    pub span: TextRange,
    pub non_generic_tvs: Vec<crate::ids::TypeVar>,
}

#[derive(Debug, Clone)]
pub enum LoweredEffAnn {
    Opaque,
    Row {
        lower: Pos,
        upper: Neg,
        non_generic_tvs: Vec<crate::ids::TypeVar>,
    },
}

pub(crate) fn pat_type_ann_node(pat: &SyntaxNode) -> Option<SyntaxNode> {
    if let Some(ann) = pat
        .children()
        .find(|child| child.kind() == SyntaxKind::TypeAnn)
    {
        return Some(ann);
    }
    if !matches!(pat.kind(), SyntaxKind::Pattern | SyntaxKind::PatParenGroup) {
        return None;
    }
    pat.children()
        .find(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Pattern | SyntaxKind::PatParenGroup
            )
        })
        .and_then(|child| pat_type_ann_node(&child))
}

pub fn lower_pat_ann(state: &mut LowerState, pat: &SyntaxNode) -> Option<LoweredPatAnn> {
    let ann = pat_type_ann_node(pat)?;
    let type_expr = ann
        .children()
        .find(|child| child.kind() == SyntaxKind::TypeExpr)?;
    let eff = match super::signature::parse_sig_type_expr(&type_expr) {
        Some(super::signature::SigType::EffectPrefixed { .. }) | None => {
            lower_effect_ann(state, &type_expr)
        }
        Some(_) => None,
    };
    let non_generic_tvs = eff
        .as_ref()
        .map(effect_ann_non_generic_tvs)
        .unwrap_or_default();
    Some(LoweredPatAnn {
        eff,
        span: ann.text_range(),
        non_generic_tvs,
    })
}

pub fn configure_arg_effect_from_ann(
    state: &mut LowerState,
    arg_eff_tv: crate::ids::TypeVar,
    ann: Option<&LoweredPatAnn>,
) {
    match ann.and_then(|ann| ann.eff.clone()) {
        None | Some(LoweredEffAnn::Opaque) => {}
        Some(LoweredEffAnn::Row { lower, upper, .. }) => {
            let cause = ann
                .map(|ann| ConstraintCause {
                    span: Some(ann.span),
                    reason: ConstraintReason::Annotation,
                })
                .unwrap_or_else(ConstraintCause::unknown);
            if let Some(ann) = ann {
                state.register_origin(
                    arg_eff_tv,
                    TypeOrigin {
                        span: Some(ann.span),
                        file_span: None,
                        kind: TypeOriginKind::Annotation,
                        label: Some("effect annotation".to_string()),
                    },
                );
            }
            state
                .infer
                .constrain_with_cause(lower, Neg::Var(arg_eff_tv), cause.clone());
            state
                .infer
                .constrain_with_cause(Pos::Var(arg_eff_tv), upper, cause);
        }
    }
}

pub fn fresh_arg_effect_tv(
    state: &mut LowerState,
    ann: Option<&LoweredPatAnn>,
) -> crate::ids::TypeVar {
    match ann.and_then(|ann| ann.eff.as_ref()) {
        None => state.fresh_exact_pure_eff_tv(),
        Some(LoweredEffAnn::Opaque) => state.fresh_tv(),
        Some(LoweredEffAnn::Row { .. }) => state.fresh_tv(),
    }
}

fn lower_effect_ann(state: &mut LowerState, type_expr: &SyntaxNode) -> Option<LoweredEffAnn> {
    let row = type_expr
        .children()
        .find(|child| child.kind() == SyntaxKind::TypeRow)?;
    let separator = row
        .children()
        .find(|child| child.kind() == SyntaxKind::Separator);
    let parts = row
        .children()
        .filter(|child| child.kind() == SyntaxKind::TypeExpr)
        .collect::<Vec<_>>();

    if separator.is_none() && parts.len() == 1 && is_wildcard_type_expr(&parts[0]) {
        return Some(LoweredEffAnn::Opaque);
    }

    if let Some(sig) = super::signature::parse_sig_type_expr(type_expr)
        && let Some(row) = sig_effect_row(sig)
        && sig_row_has_effect_args(&row)
    {
        return Some(lower_sig_effect_ann(state, type_expr, row));
    }

    let mut items = Vec::new();
    let mut tail = None;
    let mut seen_separator = false;

    for child in row.children() {
        match child.kind() {
            SyntaxKind::Separator => seen_separator = true,
            SyntaxKind::TypeExpr => {
                if seen_separator {
                    tail = lower_row_tail(state, &child);
                } else if let Some(atom) = lower_effect_atom(state, &child) {
                    items.push(atom);
                }
            }
            _ => {}
        }
    }

    if separator.is_none() {
        let tail_tv = annotation_tv(state, type_expr);
        state.infer.mark_through(tail_tv);
        let lower = Pos::Row(
            items
                .iter()
                .cloned()
                .map(|atom| state.infer.alloc_pos(Pos::Atom(atom)))
                .collect(),
            state.infer.alloc_pos(Pos::Var(tail_tv)),
        );
        let upper = Neg::Row(
            items
                .into_iter()
                .map(|atom| state.infer.alloc_neg(Neg::Atom(atom)))
                .collect(),
            state.infer.alloc_neg(Neg::Var(tail_tv)),
        );
        return Some(LoweredEffAnn::Row {
            lower,
            upper,
            non_generic_tvs: Vec::new(),
        });
    }

    let lower_tail = match tail {
        Some(tv) => {
            state.infer.mark_through(tv);
            Pos::Var(tv)
        }
        None => Pos::Bot,
    };
    let upper_tail = match tail {
        Some(tv) => Neg::Var(tv),
        None => Neg::Top,
    };

    Some(LoweredEffAnn::Row {
        lower: Pos::Row(
            items
                .iter()
                .cloned()
                .map(|atom| state.infer.alloc_pos(Pos::Atom(atom)))
                .collect(),
            state.infer.alloc_pos(lower_tail),
        ),
        upper: Neg::Row(
            items
                .into_iter()
                .map(|atom| state.infer.alloc_neg(Neg::Atom(atom)))
                .collect(),
            state.infer.alloc_neg(upper_tail),
        ),
        non_generic_tvs: Vec::new(),
    })
}

fn is_wildcard_type_expr(node: &SyntaxNode) -> bool {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .any(|tok| tok.kind() == SyntaxKind::Ident && tok.text() == "_")
}

fn lower_row_tail(state: &mut LowerState, node: &SyntaxNode) -> Option<crate::ids::TypeVar> {
    if is_wildcard_type_expr(node) {
        return Some(annotation_tv(state, node));
    }
    let has_ident = node
        .children_with_tokens()
        .filter_map(|it| it.into_token())
        .any(|tok| tok.kind() == SyntaxKind::Ident);
    has_ident.then(|| annotation_tv(state, node))
}

fn annotation_tv(state: &LowerState, node: &SyntaxNode) -> crate::ids::TypeVar {
    state.fresh_tv_with_origin(TypeOrigin {
        span: Some(node.text_range()),
        file_span: None,
        kind: TypeOriginKind::Annotation,
        label: Some(node.text().to_string()),
    })
}

fn sig_effect_row(sig: SigType) -> Option<SigRow> {
    match sig {
        SigType::EffectPrefixed { eff, .. } => Some(eff),
        SigType::Row { row, .. } => Some(row),
        _ => None,
    }
}

fn sig_row_has_effect_args(row: &SigRow) -> bool {
    row.items.iter().any(sig_type_is_effect_apply)
}

fn sig_type_is_effect_apply(sig: &SigType) -> bool {
    matches!(sig, SigType::Apply { .. })
}

fn effect_ann_non_generic_tvs(eff: &LoweredEffAnn) -> Vec<crate::ids::TypeVar> {
    match eff {
        LoweredEffAnn::Opaque => Vec::new(),
        LoweredEffAnn::Row {
            non_generic_tvs, ..
        } => non_generic_tvs.clone(),
    }
}

fn lower_sig_effect_ann(
    state: &mut LowerState,
    type_expr: &SyntaxNode,
    mut row: SigRow,
) -> LoweredEffAnn {
    if row.tail.is_none() && !row.items.is_empty() {
        row.tail = Some(SigVar {
            name: "_".to_string(),
            span: type_expr.text_range(),
        });
    }

    let mut vars = HashMap::new();
    let lower_id = super::signature::lower_sig_row_pos_id(state, &row, &mut vars);
    let upper_id = super::signature::lower_sig_row_neg_id(state, &row, &mut vars);
    let lower = { state.infer.arena.get_pos(lower_id).clone() };
    let upper = { state.infer.arena.get_neg(upper_id).clone() };
    let sig_var_tvs = vars
        .values()
        .copied()
        .collect::<std::collections::HashSet<_>>();
    let mut non_generic_tvs = collect_pos_free_vars(&state.infer, lower_id);
    non_generic_tvs.extend(collect_neg_free_vars(&state.infer, upper_id));
    non_generic_tvs.retain(|tv| !sig_var_tvs.contains(tv));
    non_generic_tvs.sort_by_key(|tv| tv.0);
    non_generic_tvs.dedup();
    LoweredEffAnn::Row {
        lower,
        upper,
        non_generic_tvs,
    }
}

fn lower_effect_atom(state: &LowerState, node: &SyntaxNode) -> Option<EffectAtom> {
    let mut segs = Vec::new();

    if let Some(tok) = node
        .children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|tok| tok.kind() == SyntaxKind::Ident)
    {
        segs.push(Name(tok.text().to_string()));
    }

    for path_sep in node
        .children()
        .filter(|child| child.kind() == SyntaxKind::PathSep)
    {
        if let Some(tok) = path_sep
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .find(|tok| tok.kind() == SyntaxKind::Ident)
        {
            segs.push(Name(tok.text().to_string()));
        }
    }

    if segs.is_empty() {
        None
    } else {
        Some(EffectAtom {
            path: state
                .ctx
                .canonical_current_type_path(&Path { segments: segs }),
            args: vec![],
        })
    }
}
