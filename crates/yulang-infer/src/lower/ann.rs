use std::collections::HashMap;

use rowan::TextRange;
use yulang_parser::lex::SyntaxKind;

use super::{LowerState, SyntaxNode};
use crate::diagnostic::{TypeOrigin, TypeOriginKind};
use crate::lower::signature::{SigRow, SigType};
use crate::solve::{EffectSubtractId, EffectSubtractability};
use crate::symbols::{Name, Path};
use crate::types::EffectAtom;

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
        atoms: Vec<EffectAtom>,
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
) -> Vec<EffectSubtractId> {
    if ann.as_ref().and_then(|ann| ann.eff.as_ref()).is_some()
        && !state.configured_arg_effect_tvs.insert(arg_eff_tv)
    {
        return state
            .configured_arg_effect_subtract_ids
            .get(&arg_eff_tv)
            .cloned()
            .unwrap_or_default();
    }
    let subtract_ids = record_effect_annotation_subtractability(state, arg_eff_tv, ann);
    if !subtract_ids.is_empty() {
        state
            .configured_arg_effect_subtract_ids
            .insert(arg_eff_tv, subtract_ids.clone());
    }
    match ann.and_then(|ann| ann.eff.clone()) {
        None | Some(LoweredEffAnn::Opaque) => {}
        Some(LoweredEffAnn::Row { .. }) => {
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
        }
    }
    subtract_ids
}

pub fn record_effect_annotation_subtractability(
    state: &LowerState,
    arg_eff_tv: crate::ids::TypeVar,
    ann: Option<&LoweredPatAnn>,
) -> Vec<EffectSubtractId> {
    match ann.and_then(|ann| ann.eff.as_ref()) {
        Some(LoweredEffAnn::Opaque) => {
            vec![
                state
                    .infer
                    .record_effect_subtractability(arg_eff_tv, EffectSubtractability::All),
            ]
        }
        Some(LoweredEffAnn::Row { atoms, .. }) => {
            if atoms.is_empty() {
                vec![
                    state
                        .infer
                        .record_effect_subtractability(arg_eff_tv, EffectSubtractability::Empty),
                ]
            } else {
                vec![state.infer.record_effect_subtractability(
                    arg_eff_tv,
                    EffectSubtractability::Set(atoms.clone()),
                )]
            }
        }
        None => Vec::new(),
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
    let mut seen_separator = false;

    for child in row.children() {
        match child.kind() {
            SyntaxKind::Separator => seen_separator = true,
            SyntaxKind::TypeExpr => {
                if !seen_separator && let Some(atom) = lower_effect_atom(state, &child) {
                    items.push(atom);
                }
            }
            _ => {}
        }
    }

    Some(LoweredEffAnn::Row {
        atoms: items,
        non_generic_tvs: Vec::new(),
    })
}

fn is_wildcard_type_expr(node: &SyntaxNode) -> bool {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .any(|tok| tok.kind() == SyntaxKind::Ident && tok.text() == "_")
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
    _type_expr: &SyntaxNode,
    row: SigRow,
) -> LoweredEffAnn {
    let mut vars = HashMap::new();
    let atoms = row
        .items
        .iter()
        .filter_map(|item| lower_sig_effect_atom_for_ann(state, item, &mut vars))
        .collect::<Vec<_>>();
    let sig_var_tvs = vars
        .values()
        .copied()
        .collect::<std::collections::HashSet<_>>();
    let mut non_generic_tvs = atoms
        .iter()
        .flat_map(|atom| atom.args.iter().flat_map(|(pos, neg)| [*pos, *neg]))
        .collect::<Vec<_>>();
    non_generic_tvs.retain(|tv| !sig_var_tvs.contains(tv));
    non_generic_tvs.sort_by_key(|tv| tv.0);
    non_generic_tvs.dedup();
    LoweredEffAnn::Row {
        atoms,
        non_generic_tvs,
    }
}

fn lower_sig_effect_atom_for_ann(
    state: &mut LowerState,
    sig: &SigType,
    vars: &mut HashMap<String, crate::ids::TypeVar>,
) -> Option<EffectAtom> {
    match sig {
        SigType::Prim { path, .. } => Some(EffectAtom {
            path: state
                .ctx
                .canonical_current_type_path(&state.rewrite_synthetic_path(path)),
            args: vec![],
        }),
        SigType::Apply { path, args, .. } => Some(EffectAtom {
            path: state
                .ctx
                .canonical_current_type_path(&state.rewrite_synthetic_path(path)),
            args: args
                .iter()
                .map(|arg| super::signature::lower_sig_effect_arg(state, arg, vars))
                .collect(),
        }),
        _ => None,
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
            path: state.ctx.canonical_current_type_path(
                &state.rewrite_synthetic_path(&Path { segments: segs }),
            ),
            args: vec![],
        })
    }
}
