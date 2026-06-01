use std::collections::HashSet;

use crate::ids::TypeVar;
use crate::simplify::compact::CompactRecordSpread;
use crate::symbols::Path;

use super::{
    AlongItem, CoOccurrences, CompactBounds, CompactCon, CompactFun, CompactRecord,
    CompactRoleConstraint, CompactRow, CompactType, CompactTypeScheme, CompactVariant, ExactKey,
    ExactKeyKind, exact_key_from_hash,
};

pub(super) fn analyze_co_occurrences_with_role_constraints(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
) -> CoOccurrences {
    let mut analysis = CoOccurrences::default();
    let mut expanded = HashSet::new();
    visit_compact_type(
        scheme,
        &scheme.cty.lower,
        true,
        &mut expanded,
        &mut analysis,
    );
    // Root upper vars are not counted as negative occurrences directly.
    // Doing so keeps otherwise-unconstrained root vars alive and renders
    // user-facing types like `α | int` or `α | (β -> β)`.
    visit_compact_type_children(
        scheme,
        &scheme.cty.upper,
        false,
        &mut expanded,
        &mut analysis,
    );
    for constraint in constraints {
        for arg in &constraint.args {
            visit_bounds(scheme, arg, &mut expanded, &mut analysis);
        }
    }
    analysis
}

fn visit_bounds(
    scheme: &CompactTypeScheme,
    bounds: &CompactBounds,
    expanded: &mut HashSet<(TypeVar, bool)>,
    analysis: &mut CoOccurrences,
) {
    visit_compact_type(scheme, &bounds.lower, true, expanded, analysis);
    visit_compact_type(scheme, &bounds.upper, false, expanded, analysis);
}

fn visit_compact_type(
    scheme: &CompactTypeScheme,
    ty: &CompactType,
    positive: bool,
    expanded: &mut HashSet<(TypeVar, bool)>,
    analysis: &mut CoOccurrences,
) {
    let group = along_group(ty);
    for &tv in &ty.vars {
        let map = if positive {
            &mut analysis.positive
        } else {
            &mut analysis.negative
        };
        match map.get_mut(&tv) {
            Some(existing) => existing.retain(|item| group.contains(item)),
            None => {
                map.insert(tv, group.clone());
            }
        }
        if expanded.insert((tv, positive)) {
            if let Some(bounds) = scheme.rec_vars.get(&tv) {
                let recur = if positive {
                    &bounds.lower
                } else {
                    &bounds.upper
                };
                visit_compact_type(scheme, recur, positive, expanded, analysis);
            }
        }
    }

    visit_compact_type_children(scheme, ty, positive, expanded, analysis);
}

pub(super) fn visit_compact_type_children(
    scheme: &CompactTypeScheme,
    ty: &CompactType,
    positive: bool,
    expanded: &mut HashSet<(TypeVar, bool)>,
    analysis: &mut CoOccurrences,
) {
    for con in &ty.cons {
        for arg in &con.args {
            visit_bounds(scheme, arg, expanded, analysis);
        }
    }
    for fun in &ty.funs {
        visit_compact_type(scheme, &fun.arg, !positive, expanded, analysis);
        visit_compact_type(scheme, &fun.arg_eff, !positive, expanded, analysis);
        visit_compact_type(scheme, &fun.ret_eff, positive, expanded, analysis);
        visit_compact_type(scheme, &fun.ret, positive, expanded, analysis);
    }
    for record in &ty.records {
        for field in &record.fields {
            visit_compact_type(scheme, &field.value, positive, expanded, analysis);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            visit_compact_type(scheme, &field.value, positive, expanded, analysis);
        }
        visit_compact_type(scheme, &spread.tail, positive, expanded, analysis);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_compact_type(scheme, payload, positive, expanded, analysis);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            visit_compact_type(scheme, item, positive, expanded, analysis);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            visit_compact_type(scheme, item, positive, expanded, analysis);
        }
        visit_compact_type(scheme, &row.tail, positive, expanded, analysis);
    }
}

fn along_group(ty: &CompactType) -> HashSet<AlongItem> {
    let mut out = HashSet::new();
    out.extend(ty.vars.iter().copied().map(AlongItem::Var));
    out.extend(exact_group(ty).into_iter().map(AlongItem::Exact));
    out
}

fn exact_group(ty: &CompactType) -> HashSet<ExactKey> {
    let mut out = HashSet::new();
    out.extend(ty.prims.iter().map(compact_prim_exact_key));
    out.extend(ty.cons.iter().map(compact_con_exact_key));
    out.extend(ty.funs.iter().map(compact_fun_exact_key));
    out.extend(ty.records.iter().map(compact_record_exact_key));
    out.extend(
        ty.record_spreads
            .iter()
            .map(compact_record_spread_exact_key),
    );
    out.extend(ty.variants.iter().map(compact_variant_exact_key));
    out.extend(ty.tuples.iter().map(|tuple| compact_tuple_exact_key(tuple)));
    out.extend(ty.rows.iter().map(compact_row_exact_key));
    out
}

fn compact_bounds_exact_key(bounds: &CompactBounds) -> ExactKey {
    exact_key_from_hash(
        ExactKeyKind::Other,
        (
            b'B',
            compact_type_exact_key(&bounds.lower),
            compact_type_exact_key(&bounds.upper),
        ),
    )
}

fn compact_type_exact_key(ty: &CompactType) -> ExactKey {
    let mut vars = ty.vars.iter().map(|tv| tv.0).collect::<Vec<_>>();
    vars.sort_unstable();
    let mut prims = ty
        .prims
        .iter()
        .map(compact_prim_exact_key)
        .collect::<Vec<_>>();
    prims.sort();
    let mut cons = ty
        .cons
        .iter()
        .map(compact_con_exact_key)
        .collect::<Vec<_>>();
    cons.sort();
    let mut funs = ty
        .funs
        .iter()
        .map(compact_fun_exact_key)
        .collect::<Vec<_>>();
    funs.sort();
    let mut records = ty
        .records
        .iter()
        .map(compact_record_exact_key)
        .collect::<Vec<_>>();
    records.sort();
    let mut record_spreads = ty
        .record_spreads
        .iter()
        .map(compact_record_spread_exact_key)
        .collect::<Vec<_>>();
    record_spreads.sort();
    let mut variants = ty
        .variants
        .iter()
        .map(compact_variant_exact_key)
        .collect::<Vec<_>>();
    variants.sort();
    let mut tuples = ty
        .tuples
        .iter()
        .map(|tuple| compact_tuple_exact_key(tuple))
        .collect::<Vec<_>>();
    tuples.sort();
    let mut rows = ty
        .rows
        .iter()
        .map(compact_row_exact_key)
        .collect::<Vec<_>>();
    rows.sort();
    exact_key_from_hash(
        ExactKeyKind::Other,
        (
            b'T',
            vars,
            prims,
            cons,
            funs,
            records,
            record_spreads,
            variants,
            tuples,
            rows,
        ),
    )
}

fn compact_prim_exact_key(path: &Path) -> ExactKey {
    exact_key_from_hash(ExactKeyKind::Other, (b'P', path_key(path)))
}

fn compact_con_exact_key(con: &CompactCon) -> ExactKey {
    let args = con
        .args
        .iter()
        .map(compact_bounds_exact_key)
        .collect::<Vec<_>>();
    exact_key_from_hash(ExactKeyKind::Other, (b'C', path_key(&con.path), args))
}

fn compact_fun_exact_key(fun: &CompactFun) -> ExactKey {
    exact_key_from_hash(
        ExactKeyKind::Fun,
        (
            b'F',
            compact_type_exact_key(&fun.arg),
            compact_type_exact_key(&fun.arg_eff),
            compact_type_exact_key(&fun.ret_eff),
            compact_type_exact_key(&fun.ret),
        ),
    )
}

fn compact_record_exact_key(record: &CompactRecord) -> ExactKey {
    let mut fields = record
        .fields
        .iter()
        .map(|field| {
            (
                format!("{}{}", field.name.0, if field.optional { "?" } else { "" }),
                compact_type_exact_key(&field.value),
            )
        })
        .collect::<Vec<_>>();
    fields.sort();
    exact_key_from_hash(ExactKeyKind::Other, (b'R', fields))
}

fn compact_record_spread_exact_key(spread: &CompactRecordSpread) -> ExactKey {
    let mut fields = spread
        .fields
        .iter()
        .map(|field| {
            (
                format!("{}{}", field.name.0, if field.optional { "?" } else { "" }),
                compact_type_exact_key(&field.value),
            )
        })
        .collect::<Vec<_>>();
    fields.sort();
    exact_key_from_hash(
        ExactKeyKind::Other,
        (
            b'S',
            spread.tail_wins,
            fields,
            compact_type_exact_key(&spread.tail),
        ),
    )
}

fn compact_variant_exact_key(variant: &CompactVariant) -> ExactKey {
    let mut items = variant
        .items
        .iter()
        .map(|(name, payloads)| {
            (
                name.0.clone(),
                payloads
                    .iter()
                    .map(compact_type_exact_key)
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();
    items.sort_by(|lhs, rhs| lhs.0.cmp(&rhs.0));
    exact_key_from_hash(ExactKeyKind::Other, (b'V', items))
}

fn compact_tuple_exact_key(tuple: &[CompactType]) -> ExactKey {
    let items = tuple.iter().map(compact_type_exact_key).collect::<Vec<_>>();
    exact_key_from_hash(ExactKeyKind::Other, (b'U', items))
}

fn compact_row_exact_key(row: &CompactRow) -> ExactKey {
    let mut items = row
        .items
        .iter()
        .map(compact_type_exact_key)
        .collect::<Vec<_>>();
    items.sort();
    exact_key_from_hash(
        if items.is_empty() {
            ExactKeyKind::EmptyRow
        } else {
            ExactKeyKind::ConcreteRow
        },
        (b'W', items, compact_type_exact_key(&row.tail)),
    )
}

fn path_key(path: &Path) -> String {
    path.segments
        .iter()
        .map(|seg| seg.0.clone())
        .collect::<Vec<_>>()
        .join("::")
}
