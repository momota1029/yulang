use std::collections::HashMap;

use yulang_parser::lex::SyntaxKind;

use crate::ids::TypeVar;
use crate::lower::{LowerState, SyntaxNode};
use crate::solve::EffectSubtractability;
use crate::types::EffectAtom;
use crate::types::{Neg, Pos};

#[derive(Debug, Clone, Default)]
pub(crate) struct TypeParamEffectMetadata {
    source_args: Vec<TypeVar>,
    subtractabilities: Vec<(usize, EffectSubtractability)>,
}

pub(crate) fn lower_struct_field_type(
    state: &mut LowerState,
    field: &SyntaxNode,
    type_scope: &HashMap<String, TypeVar>,
) -> Option<(Pos, Neg)> {
    let type_expr = super::super::child_node(field, SyntaxKind::TypeExpr)?;
    let sig = crate::lower::signature::parse_sig_type_expr(&type_expr)?;
    let mut pos_vars = type_scope.clone();
    let mut neg_vars = type_scope.clone();
    Some((
        crate::lower::signature::lower_pure_sig_type(state, &sig, &mut pos_vars),
        crate::lower::signature::lower_pure_sig_neg_type(state, &sig, &mut neg_vars),
    ))
}

pub(crate) fn invariant_args(vars: &[TypeVar]) -> Vec<(Pos, Neg)> {
    vars.iter()
        .map(|tv| (Pos::Var(*tv), Neg::Var(*tv)))
        .collect()
}

pub(crate) fn collect_type_param_effect_metadata(
    state: &LowerState,
    type_arg_tvs: &[TypeVar],
) -> TypeParamEffectMetadata {
    let subtractabilities = type_arg_tvs
        .iter()
        .enumerate()
        .filter_map(|(index, tv)| {
            state
                .infer
                .effect_subtractability(*tv)
                .map(|subtractability| (index, subtractability))
        })
        .collect();
    TypeParamEffectMetadata {
        source_args: type_arg_tvs.to_vec(),
        subtractabilities,
    }
}

pub(crate) fn apply_type_param_effect_metadata(
    state: &LowerState,
    metadata: &TypeParamEffectMetadata,
    type_arg_tvs: &[TypeVar],
) {
    let subst = metadata
        .source_args
        .iter()
        .copied()
        .zip(type_arg_tvs.iter().copied())
        .collect::<Vec<_>>();
    for (index, subtractability) in &metadata.subtractabilities {
        let Some(&target) = type_arg_tvs.get(*index) else {
            continue;
        };
        state.infer.record_effect_subtractability(
            target,
            subst_effect_subtractability(subtractability.clone(), &subst),
        );
    }
}

fn subst_effect_subtractability(
    subtractability: EffectSubtractability,
    subst: &[(TypeVar, TypeVar)],
) -> EffectSubtractability {
    match subtractability {
        EffectSubtractability::Empty => EffectSubtractability::Empty,
        EffectSubtractability::All => EffectSubtractability::All,
        EffectSubtractability::AllExcept(atoms) => EffectSubtractability::all_except(
            atoms
                .into_iter()
                .map(|atom| subst_effect_atom(atom, subst))
                .collect(),
        ),
        EffectSubtractability::Set(atoms) => EffectSubtractability::set(
            atoms
                .into_iter()
                .map(|atom| subst_effect_atom(atom, subst))
                .collect(),
        ),
    }
}

fn subst_effect_atom(atom: EffectAtom, subst: &[(TypeVar, TypeVar)]) -> EffectAtom {
    EffectAtom {
        path: atom.path,
        args: atom
            .args
            .into_iter()
            .map(|(pos, neg)| (subst_lookup(subst, pos), subst_lookup(subst, neg)))
            .collect(),
    }
}

fn subst_lookup(subst: &[(TypeVar, TypeVar)], tv: TypeVar) -> TypeVar {
    subst
        .iter()
        .find_map(|(from, to)| (*from == tv).then_some(*to))
        .unwrap_or(tv)
}
