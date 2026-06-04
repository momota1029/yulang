use std::collections::HashMap;

use yulang_parser::lex::SyntaxKind;

use crate::ids::TypeVar;
use crate::lower::{LowerState, SyntaxNode};
use crate::solve::{EffectSubtractFact, EffectSubtractId, EffectSubtractability};
use crate::types::EffectAtom;
use crate::types::{Neg, Pos};

#[derive(Debug, Clone, Default)]
pub(crate) struct TypeParamEffectMetadata {
    source_args: Vec<TypeVar>,
    subtracts: Vec<(usize, EffectSubtractFact)>,
    non_subtracts: Vec<(usize, EffectSubtractId)>,
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
    let subtracts = type_arg_tvs
        .iter()
        .enumerate()
        .flat_map(|(index, tv)| {
            state
                .infer
                .effect_subtract_facts(*tv)
                .into_iter()
                .map(move |fact| (index, fact))
        })
        .collect();
    let non_subtracts = type_arg_tvs
        .iter()
        .enumerate()
        .flat_map(|(index, tv)| {
            state
                .infer
                .effect_non_subtract_ids(*tv)
                .into_iter()
                .map(move |id| (index, id))
        })
        .collect();
    TypeParamEffectMetadata {
        source_args: type_arg_tvs.to_vec(),
        subtracts,
        non_subtracts,
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
    let mut id_subst = HashMap::new();
    for (_, fact) in &metadata.subtracts {
        fresh_metadata_effect_subtract_id(state, &mut id_subst, fact.id);
    }
    for (_, id) in &metadata.non_subtracts {
        fresh_metadata_effect_subtract_id(state, &mut id_subst, *id);
    }
    for (index, fact) in &metadata.subtracts {
        let Some(&target) = type_arg_tvs.get(*index) else {
            continue;
        };
        state.infer.record_effect_subtract_fact(
            target,
            subst_effect_subtract_fact(fact.clone(), &subst, &id_subst),
        );
    }
    for (index, id) in &metadata.non_subtracts {
        let Some(&target) = type_arg_tvs.get(*index) else {
            continue;
        };
        if let Some(id) = id_subst.get(id).copied() {
            state.infer.record_effect_non_subtract(target, id);
        }
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

fn subst_effect_subtract_fact(
    fact: EffectSubtractFact,
    subst: &[(TypeVar, TypeVar)],
    id_subst: &HashMap<EffectSubtractId, EffectSubtractId>,
) -> EffectSubtractFact {
    EffectSubtractFact {
        id: id_subst.get(&fact.id).copied().unwrap_or(fact.id),
        subtractability: subst_effect_subtractability(fact.subtractability, subst),
    }
}

fn fresh_metadata_effect_subtract_id(
    state: &LowerState,
    id_subst: &mut HashMap<EffectSubtractId, EffectSubtractId>,
    id: EffectSubtractId,
) -> EffectSubtractId {
    *id_subst
        .entry(id)
        .or_insert_with(|| state.infer.fresh_effect_subtract_id())
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
