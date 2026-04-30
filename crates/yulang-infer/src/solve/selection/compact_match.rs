use std::collections::HashMap;

use crate::ids::TypeVar;
use crate::simplify::compact::{CompactBounds, CompactType};

use super::compact_repr::concrete_bounds_repr;
use super::compact_var::single_compact_var;

pub(super) fn match_compact_type_pattern(
    pattern: &CompactType,
    concrete: &CompactType,
    subst: &mut HashMap<TypeVar, CompactType>,
) -> bool {
    for tv in &pattern.vars {
        if let Some(existing) = subst.get(tv) {
            if existing != concrete {
                return false;
            }
        } else {
            subst.insert(*tv, concrete.clone());
        }
    }

    if compact_type_shape_is_empty(pattern) {
        return true;
    }

    if pattern.prims != concrete.prims {
        return false;
    }

    if pattern.cons.len() != concrete.cons.len()
        || !pattern
            .cons
            .iter()
            .zip(&concrete.cons)
            .all(|(pattern, concrete)| {
                pattern.path == concrete.path
                    && pattern.args.len() == concrete.args.len()
                    && pattern
                        .args
                        .iter()
                        .zip(&concrete.args)
                        .all(|(pattern, concrete)| {
                            match_compact_bounds_pattern(pattern, concrete, subst)
                        })
            })
    {
        return false;
    }

    if pattern.funs.len() != concrete.funs.len()
        || !pattern
            .funs
            .iter()
            .zip(&concrete.funs)
            .all(|(pattern, concrete)| {
                match_compact_type_pattern(&pattern.arg, &concrete.arg, subst)
                    && match_compact_type_pattern(&pattern.arg_eff, &concrete.arg_eff, subst)
                    && match_compact_type_pattern(&pattern.ret_eff, &concrete.ret_eff, subst)
                    && match_compact_type_pattern(&pattern.ret, &concrete.ret, subst)
            })
    {
        return false;
    }

    if pattern.records.len() != concrete.records.len()
        || !pattern
            .records
            .iter()
            .zip(&concrete.records)
            .all(|(pattern, concrete)| {
                pattern.fields.len() == concrete.fields.len()
                    && pattern
                        .fields
                        .iter()
                        .zip(&concrete.fields)
                        .all(|(pattern, concrete)| {
                            pattern.name == concrete.name
                                && match_compact_type_pattern(
                                    &pattern.value,
                                    &concrete.value,
                                    subst,
                                )
                        })
            })
    {
        return false;
    }

    if pattern.record_spreads.len() != concrete.record_spreads.len()
        || !pattern
            .record_spreads
            .iter()
            .zip(&concrete.record_spreads)
            .all(|(pattern, concrete)| {
                pattern.fields.len() == concrete.fields.len()
                    && pattern
                        .fields
                        .iter()
                        .zip(&concrete.fields)
                        .all(|(pattern, concrete)| {
                            pattern.name == concrete.name
                                && match_compact_type_pattern(
                                    &pattern.value,
                                    &concrete.value,
                                    subst,
                                )
                        })
                    && match_compact_type_pattern(&pattern.tail, &concrete.tail, subst)
            })
    {
        return false;
    }

    if pattern.variants.len() != concrete.variants.len()
        || !pattern
            .variants
            .iter()
            .zip(&concrete.variants)
            .all(|(pattern, concrete)| {
                pattern.items.len() == concrete.items.len()
                    && pattern.items.iter().zip(&concrete.items).all(
                        |((pattern_name, pattern_items), (concrete_name, concrete_items))| {
                            pattern_name == concrete_name
                                && pattern_items.len() == concrete_items.len()
                                && pattern_items.iter().zip(concrete_items).all(
                                    |(pattern, concrete)| {
                                        match_compact_type_pattern(pattern, concrete, subst)
                                    },
                                )
                        },
                    )
            })
    {
        return false;
    }

    if pattern.tuples.len() != concrete.tuples.len()
        || !pattern
            .tuples
            .iter()
            .zip(&concrete.tuples)
            .all(|(pattern, concrete)| {
                pattern.len() == concrete.len()
                    && pattern.iter().zip(concrete).all(|(pattern, concrete)| {
                        match_compact_type_pattern(pattern, concrete, subst)
                    })
            })
    {
        return false;
    }

    if pattern.rows.len() != concrete.rows.len()
        || !pattern
            .rows
            .iter()
            .zip(&concrete.rows)
            .all(|(pattern, concrete)| {
                pattern.items.len() == concrete.items.len()
                    && pattern
                        .items
                        .iter()
                        .zip(&concrete.items)
                        .all(|(pattern, concrete)| {
                            match_compact_type_pattern(pattern, concrete, subst)
                        })
                    && match_compact_type_pattern(&pattern.tail, &concrete.tail, subst)
            })
    {
        return false;
    }

    true
}

fn match_compact_bounds_pattern(
    pattern: &CompactBounds,
    concrete: &CompactBounds,
    subst: &mut HashMap<TypeVar, CompactType>,
) -> bool {
    if let Some(var) = exact_compact_bounds_var(pattern) {
        let ty = concrete_bounds_repr(concrete, true).unwrap_or_default();
        return bind_compact_type_var_pattern(var, &ty, subst);
    }
    pattern.self_var == concrete.self_var
        && match_compact_type_pattern(&pattern.lower, &concrete.lower, subst)
        && match_compact_type_pattern(&pattern.upper, &concrete.upper, subst)
}

fn exact_compact_bounds_var(bounds: &CompactBounds) -> Option<TypeVar> {
    (bounds.self_var.is_none() && bounds.lower == bounds.upper)
        .then(|| single_compact_var(&bounds.lower))
        .flatten()
}

fn bind_compact_type_var_pattern(
    var: TypeVar,
    ty: &CompactType,
    subst: &mut HashMap<TypeVar, CompactType>,
) -> bool {
    if let Some(existing) = subst.get(&var) {
        existing == ty
    } else {
        subst.insert(var, ty.clone());
        true
    }
}

fn compact_type_shape_is_empty(ty: &CompactType) -> bool {
    ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}
