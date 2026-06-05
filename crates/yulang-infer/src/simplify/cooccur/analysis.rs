use std::collections::{HashMap, HashSet};

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
    analyze_co_occurrences_with_role_constraints_for_vars(scheme, constraints, None)
}

pub(super) fn analyze_co_occurrences_with_role_constraints_for_vars(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    record_vars: Option<&HashSet<TypeVar>>,
) -> CoOccurrences {
    let mut analysis = CoOccurrences::default();
    let mut expanded = HashSet::new();
    let mut exact_keys = ExactKeyCache::default();
    visit_compact_type(
        scheme,
        &scheme.cty.lower,
        true,
        &mut expanded,
        &mut analysis,
        &mut exact_keys,
        record_vars,
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
        &mut exact_keys,
        record_vars,
    );
    for constraint in constraints {
        for arg in &constraint.args {
            visit_bounds(
                scheme,
                arg,
                &mut expanded,
                &mut analysis,
                &mut exact_keys,
                record_vars,
            );
        }
    }
    analysis
}

fn visit_bounds(
    scheme: &CompactTypeScheme,
    bounds: &CompactBounds,
    expanded: &mut HashSet<(TypeVar, bool)>,
    analysis: &mut CoOccurrences,
    exact_keys: &mut ExactKeyCache,
    record_vars: Option<&HashSet<TypeVar>>,
) {
    let centers = center_vars(bounds);
    visit_compact_type_with_extra_vars(
        scheme,
        &bounds.lower,
        true,
        &centers,
        expanded,
        analysis,
        exact_keys,
        record_vars,
    );
    visit_compact_type_with_extra_vars(
        scheme,
        &bounds.upper,
        false,
        &centers,
        expanded,
        analysis,
        exact_keys,
        record_vars,
    );
}

fn visit_compact_type(
    scheme: &CompactTypeScheme,
    ty: &CompactType,
    positive: bool,
    expanded: &mut HashSet<(TypeVar, bool)>,
    analysis: &mut CoOccurrences,
    exact_keys: &mut ExactKeyCache,
    record_vars: Option<&HashSet<TypeVar>>,
) {
    let recordable = recordable_type_vars(ty.vars.iter().copied(), record_vars);
    let group = if recordable.is_empty() {
        None
    } else {
        Some(along_group(ty, exact_keys))
    };
    for &tv in &ty.vars {
        visit_var_occurrence(
            scheme,
            tv,
            positive,
            group.as_ref(),
            expanded,
            analysis,
            exact_keys,
            record_vars,
        );
    }

    visit_compact_type_children(
        scheme,
        ty,
        positive,
        expanded,
        analysis,
        exact_keys,
        record_vars,
    );
}

fn visit_compact_type_with_extra_vars(
    scheme: &CompactTypeScheme,
    ty: &CompactType,
    positive: bool,
    extra_vars: &HashSet<TypeVar>,
    expanded: &mut HashSet<(TypeVar, bool)>,
    analysis: &mut CoOccurrences,
    exact_keys: &mut ExactKeyCache,
    record_vars: Option<&HashSet<TypeVar>>,
) {
    let recordable = recordable_type_vars(ty.vars.iter().chain(extra_vars).copied(), record_vars);
    let group = if recordable.is_empty() {
        None
    } else {
        let mut group = along_group(ty, exact_keys);
        group.extend(extra_vars.iter().copied().map(AlongItem::Var));
        Some(group)
    };
    for &tv in ty.vars.iter().chain(extra_vars.iter()) {
        visit_var_occurrence(
            scheme,
            tv,
            positive,
            group.as_ref(),
            expanded,
            analysis,
            exact_keys,
            record_vars,
        );
    }

    visit_compact_type_children(
        scheme,
        ty,
        positive,
        expanded,
        analysis,
        exact_keys,
        record_vars,
    );
}

pub(super) fn visit_compact_type_children(
    scheme: &CompactTypeScheme,
    ty: &CompactType,
    positive: bool,
    expanded: &mut HashSet<(TypeVar, bool)>,
    analysis: &mut CoOccurrences,
    exact_keys: &mut ExactKeyCache,
    record_vars: Option<&HashSet<TypeVar>>,
) {
    for con in &ty.cons {
        for arg in &con.args {
            visit_bounds(scheme, arg, expanded, analysis, exact_keys, record_vars);
        }
    }
    for fun in &ty.funs {
        visit_compact_type(
            scheme,
            &fun.arg,
            !positive,
            expanded,
            analysis,
            exact_keys,
            record_vars,
        );
        visit_compact_type(
            scheme,
            &fun.arg_eff,
            !positive,
            expanded,
            analysis,
            exact_keys,
            record_vars,
        );
        visit_compact_type(
            scheme,
            &fun.ret_eff,
            positive,
            expanded,
            analysis,
            exact_keys,
            record_vars,
        );
        visit_compact_type(
            scheme,
            &fun.ret,
            positive,
            expanded,
            analysis,
            exact_keys,
            record_vars,
        );
    }
    for record in &ty.records {
        for field in &record.fields {
            visit_compact_type(
                scheme,
                &field.value,
                positive,
                expanded,
                analysis,
                exact_keys,
                record_vars,
            );
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            visit_compact_type(
                scheme,
                &field.value,
                positive,
                expanded,
                analysis,
                exact_keys,
                record_vars,
            );
        }
        visit_compact_type(
            scheme,
            &spread.tail,
            positive,
            expanded,
            analysis,
            exact_keys,
            record_vars,
        );
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_compact_type(
                    scheme,
                    payload,
                    positive,
                    expanded,
                    analysis,
                    exact_keys,
                    record_vars,
                );
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            visit_compact_type(
                scheme,
                item,
                positive,
                expanded,
                analysis,
                exact_keys,
                record_vars,
            );
        }
    }
    for row in &ty.rows {
        let group = row_tail_has_recordable_vars(&row.tail, record_vars)
            .then(|| row_along_group(row, exact_keys));
        visit_row_tail_vars(
            scheme,
            &row.tail,
            positive,
            group.as_ref(),
            expanded,
            analysis,
            exact_keys,
            record_vars,
        );
        for item in &row.items {
            visit_compact_type(
                scheme,
                item,
                positive,
                expanded,
                analysis,
                exact_keys,
                record_vars,
            );
        }
        visit_compact_type(
            scheme,
            &row.tail,
            positive,
            expanded,
            analysis,
            exact_keys,
            record_vars,
        );
    }
}

fn center_vars(bounds: &CompactBounds) -> HashSet<TypeVar> {
    let mut out = bounds
        .lower
        .vars
        .intersection(&bounds.upper.vars)
        .copied()
        .collect::<HashSet<_>>();
    if let Some(self_var) = bounds.self_var {
        out.insert(self_var);
    }
    out
}

fn record_var_occurrence(
    tv: TypeVar,
    positive: bool,
    group: &HashSet<AlongItem>,
    analysis: &mut CoOccurrences,
) {
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
}

fn visit_var_occurrence(
    scheme: &CompactTypeScheme,
    tv: TypeVar,
    positive: bool,
    group: Option<&HashSet<AlongItem>>,
    expanded: &mut HashSet<(TypeVar, bool)>,
    analysis: &mut CoOccurrences,
    exact_keys: &mut ExactKeyCache,
    record_vars: Option<&HashSet<TypeVar>>,
) {
    if record_var_is_recordable(tv, record_vars)
        && let Some(group) = group
    {
        record_var_occurrence(tv, positive, group, analysis);
    }
    if expanded.insert((tv, positive)) {
        if let Some(bounds) = scheme.rec_vars.get(&tv) {
            let recur = if positive {
                &bounds.lower
            } else {
                &bounds.upper
            };
            visit_compact_type(
                scheme,
                recur,
                positive,
                expanded,
                analysis,
                exact_keys,
                record_vars,
            );
        }
    }
}

fn visit_row_tail_vars(
    scheme: &CompactTypeScheme,
    ty: &CompactType,
    positive: bool,
    group: Option<&HashSet<AlongItem>>,
    expanded: &mut HashSet<(TypeVar, bool)>,
    analysis: &mut CoOccurrences,
    exact_keys: &mut ExactKeyCache,
    record_vars: Option<&HashSet<TypeVar>>,
) {
    for &tv in &ty.vars {
        visit_var_occurrence(
            scheme,
            tv,
            positive,
            group,
            expanded,
            analysis,
            exact_keys,
            record_vars,
        );
    }
    for row in &ty.rows {
        visit_row_tail_vars(
            scheme,
            &row.tail,
            positive,
            group,
            expanded,
            analysis,
            exact_keys,
            record_vars,
        );
    }
}

fn recordable_type_vars(
    vars: impl IntoIterator<Item = TypeVar>,
    record_vars: Option<&HashSet<TypeVar>>,
) -> Vec<TypeVar> {
    vars.into_iter()
        .filter(|tv| record_var_is_recordable(*tv, record_vars))
        .collect()
}

fn record_var_is_recordable(tv: TypeVar, record_vars: Option<&HashSet<TypeVar>>) -> bool {
    record_vars.is_none_or(|vars| vars.contains(&tv))
}

fn along_group(ty: &CompactType, exact_keys: &mut ExactKeyCache) -> HashSet<AlongItem> {
    let mut out = HashSet::new();
    out.extend(ty.vars.iter().copied().map(AlongItem::Var));
    out.extend(
        exact_group(ty, exact_keys)
            .into_iter()
            .map(AlongItem::Exact),
    );
    out
}

fn row_along_group(row: &CompactRow, exact_keys: &mut ExactKeyCache) -> HashSet<AlongItem> {
    let mut out = HashSet::new();
    collect_row_tail_vars(&row.tail, &mut out);
    for item in &row.items {
        out.extend(
            exact_group(item, exact_keys)
                .into_iter()
                .map(AlongItem::Exact),
        );
    }
    out
}

fn collect_row_tail_vars(ty: &CompactType, out: &mut HashSet<AlongItem>) {
    out.extend(ty.vars.iter().copied().map(AlongItem::Var));
    for row in &ty.rows {
        collect_row_tail_vars(&row.tail, out);
    }
}

fn row_tail_has_recordable_vars(ty: &CompactType, record_vars: Option<&HashSet<TypeVar>>) -> bool {
    ty.vars
        .iter()
        .copied()
        .any(|tv| record_var_is_recordable(tv, record_vars))
        || ty
            .rows
            .iter()
            .any(|row| row_tail_has_recordable_vars(&row.tail, record_vars))
}

#[derive(Default)]
pub(super) struct ExactKeyCache {
    types: HashMap<usize, ExactKey>,
    bounds: HashMap<usize, ExactKey>,
}

fn exact_group(ty: &CompactType, exact_keys: &mut ExactKeyCache) -> HashSet<ExactKey> {
    let mut out = HashSet::new();
    out.extend(ty.prims.iter().map(compact_prim_exact_key));
    out.extend(
        ty.cons
            .iter()
            .map(|con| compact_con_exact_key(con, exact_keys)),
    );
    out.extend(
        ty.funs
            .iter()
            .map(|fun| compact_fun_exact_key(fun, exact_keys)),
    );
    out.extend(
        ty.records
            .iter()
            .map(|record| compact_record_exact_key(record, exact_keys)),
    );
    out.extend(
        ty.record_spreads
            .iter()
            .map(|spread| compact_record_spread_exact_key(spread, exact_keys)),
    );
    out.extend(
        ty.variants
            .iter()
            .map(|variant| compact_variant_exact_key(variant, exact_keys)),
    );
    out.extend(
        ty.tuples
            .iter()
            .map(|tuple| compact_tuple_exact_key(tuple, exact_keys)),
    );
    out.extend(
        ty.rows
            .iter()
            .map(|row| compact_row_exact_key(row, exact_keys)),
    );
    out
}

fn compact_bounds_exact_key(bounds: &CompactBounds, exact_keys: &mut ExactKeyCache) -> ExactKey {
    let key = bounds as *const CompactBounds as usize;
    if let Some(exact) = exact_keys.bounds.get(&key).copied() {
        return exact;
    }
    let exact = exact_key_from_hash(
        ExactKeyKind::Other,
        (
            b'B',
            compact_type_exact_key(&bounds.lower, exact_keys),
            compact_type_exact_key(&bounds.upper, exact_keys),
        ),
    );
    exact_keys.bounds.insert(key, exact);
    exact
}

fn compact_type_exact_key(ty: &CompactType, exact_keys: &mut ExactKeyCache) -> ExactKey {
    let key = ty as *const CompactType as usize;
    if let Some(exact) = exact_keys.types.get(&key).copied() {
        return exact;
    }
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
        .map(|con| compact_con_exact_key(con, exact_keys))
        .collect::<Vec<_>>();
    cons.sort();
    let mut funs = ty
        .funs
        .iter()
        .map(|fun| compact_fun_exact_key(fun, exact_keys))
        .collect::<Vec<_>>();
    funs.sort();
    let mut records = ty
        .records
        .iter()
        .map(|record| compact_record_exact_key(record, exact_keys))
        .collect::<Vec<_>>();
    records.sort();
    let mut record_spreads = ty
        .record_spreads
        .iter()
        .map(|spread| compact_record_spread_exact_key(spread, exact_keys))
        .collect::<Vec<_>>();
    record_spreads.sort();
    let mut variants = ty
        .variants
        .iter()
        .map(|variant| compact_variant_exact_key(variant, exact_keys))
        .collect::<Vec<_>>();
    variants.sort();
    let mut tuples = ty
        .tuples
        .iter()
        .map(|tuple| compact_tuple_exact_key(tuple, exact_keys))
        .collect::<Vec<_>>();
    tuples.sort();
    let mut rows = ty
        .rows
        .iter()
        .map(|row| compact_row_exact_key(row, exact_keys))
        .collect::<Vec<_>>();
    rows.sort();
    let exact = exact_key_from_hash(
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
    );
    exact_keys.types.insert(key, exact);
    exact
}

fn compact_prim_exact_key(path: &Path) -> ExactKey {
    exact_key_from_hash(ExactKeyKind::Other, (b'P', path_key(path)))
}

fn compact_con_exact_key(con: &CompactCon, exact_keys: &mut ExactKeyCache) -> ExactKey {
    let args = con
        .args
        .iter()
        .map(|arg| compact_bounds_exact_key(arg, exact_keys))
        .collect::<Vec<_>>();
    exact_key_from_hash(ExactKeyKind::Other, (b'C', path_key(&con.path), args))
}

fn compact_fun_exact_key(fun: &CompactFun, exact_keys: &mut ExactKeyCache) -> ExactKey {
    exact_key_from_hash(
        ExactKeyKind::Fun,
        (
            b'F',
            compact_type_exact_key(&fun.arg, exact_keys),
            compact_type_exact_key(&fun.arg_eff, exact_keys),
            compact_type_exact_key(&fun.ret_eff, exact_keys),
            compact_type_exact_key(&fun.ret, exact_keys),
        ),
    )
}

fn compact_record_exact_key(record: &CompactRecord, exact_keys: &mut ExactKeyCache) -> ExactKey {
    let mut fields = record
        .fields
        .iter()
        .map(|field| {
            (
                format!("{}{}", field.name.0, if field.optional { "?" } else { "" }),
                compact_type_exact_key(&field.value, exact_keys),
            )
        })
        .collect::<Vec<_>>();
    fields.sort();
    exact_key_from_hash(ExactKeyKind::Other, (b'R', fields))
}

fn compact_record_spread_exact_key(
    spread: &CompactRecordSpread,
    exact_keys: &mut ExactKeyCache,
) -> ExactKey {
    let mut fields = spread
        .fields
        .iter()
        .map(|field| {
            (
                format!("{}{}", field.name.0, if field.optional { "?" } else { "" }),
                compact_type_exact_key(&field.value, exact_keys),
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
            compact_type_exact_key(&spread.tail, exact_keys),
        ),
    )
}

fn compact_variant_exact_key(variant: &CompactVariant, exact_keys: &mut ExactKeyCache) -> ExactKey {
    let mut items = variant
        .items
        .iter()
        .map(|(name, payloads)| {
            (
                name.0.clone(),
                payloads
                    .iter()
                    .map(|payload| compact_type_exact_key(payload, exact_keys))
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();
    items.sort_by(|lhs, rhs| lhs.0.cmp(&rhs.0));
    exact_key_from_hash(ExactKeyKind::Other, (b'V', items))
}

fn compact_tuple_exact_key(tuple: &[CompactType], exact_keys: &mut ExactKeyCache) -> ExactKey {
    let items = tuple
        .iter()
        .map(|item| compact_type_exact_key(item, exact_keys))
        .collect::<Vec<_>>();
    exact_key_from_hash(ExactKeyKind::Other, (b'U', items))
}

fn compact_row_exact_key(row: &CompactRow, exact_keys: &mut ExactKeyCache) -> ExactKey {
    let mut items = row
        .items
        .iter()
        .map(|item| compact_type_exact_key(item, exact_keys))
        .collect::<Vec<_>>();
    items.sort();
    exact_key_from_hash(
        if items.is_empty() {
            ExactKeyKind::EmptyRow
        } else {
            ExactKeyKind::ConcreteRow
        },
        (b'W', items),
    )
}

fn path_key(path: &Path) -> String {
    path.segments
        .iter()
        .map(|seg| seg.0.clone())
        .collect::<Vec<_>>()
        .join("::")
}
