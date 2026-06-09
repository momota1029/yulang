use std::mem;

use rustc_hash::{FxHashMap, FxHashSet};

use super::*;
use crate::constraints::{ConstraintMachine, TypeLevel};

pub(crate) fn eliminate_polar_variables(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
) -> Vec<CompactVarSubstitution> {
    let polarity = collect_var_polarities(root);
    rewrite_root_vars(root, |var| {
        if !is_simplification_candidate(machine, boundary, var) || polarity.is_bipolar(var) {
            Some(var)
        } else {
            None
        }
    })
}

pub(crate) fn coalesce_by_co_occurrence(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
) -> Vec<CompactVarSubstitution> {
    let co_occurrences = collect_co_occurrences(root);
    let subst = co_occurrences.substitution(machine, boundary);
    if subst.is_empty() {
        return Vec::new();
    }
    rewrite_root_vars(root, |var| Some(subst.representative(var)))
}

pub(crate) fn simplify_compact_root(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
) -> CompactSimplification {
    let mut substitutions = Vec::new();
    substitutions.extend(eliminate_polar_variables(machine, boundary, root));
    substitutions.extend(coalesce_by_co_occurrence(machine, boundary, root));
    let sandwiches = sandwich_compact_root(machine, boundary, root);
    substitutions.extend(eliminate_polar_variables(machine, boundary, root));
    CompactSimplification {
        substitutions: normalize_var_substitutions(substitutions),
        sandwiches,
    }
}

fn is_simplification_candidate(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    var: TypeVar,
) -> bool {
    machine.level_of(var) >= boundary
}

pub(crate) fn sandwich_compact_root(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
) -> Vec<CompactSandwich> {
    let mut fresh = FreshCompactVars::new(root);
    let mut sandwiches = FxHashMap::default();
    loop {
        let verdicts = compute_sandwich_verdicts(machine, boundary, root);
        if verdicts.lift.is_empty() {
            return sorted_sandwiches(sandwiches);
        }

        let mut changed = false;
        root.root = sandwich_type(
            machine,
            boundary,
            mem::take(&mut root.root),
            &verdicts,
            &mut fresh,
            &mut changed,
            &mut sandwiches,
        );
        for rec in &mut root.rec_vars {
            rec.bounds = sandwich_bounds(
                machine,
                boundary,
                mem::replace(&mut rec.bounds, empty_interval(rec.var)),
                &verdicts,
                &mut fresh,
                &mut changed,
                &mut sandwiches,
            );
        }
        if !changed {
            return sorted_sandwiches(sandwiches);
        }
    }
}

fn empty_interval(self_var: TypeVar) -> CompactBounds {
    CompactBounds::Interval {
        self_var,
        lower: CompactType::default(),
        upper: CompactType::default(),
    }
}

#[derive(Default)]
struct SandwichVerdicts {
    lift: FxHashMap<TypeVar, SandwichKind>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum SandwichVerdict {
    Single(SandwichKind),
    NoLift,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum SandwichKind {
    Con(Vec<String>, usize),
    Tuple(usize),
    Fun,
    ConcreteButNotLiftable,
}

fn compute_sandwich_verdicts(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &CompactRoot,
) -> SandwichVerdicts {
    let mut verdicts = FxHashMap::default();
    visit_type_for_sandwich_verdict(&root.root, &mut verdicts);
    for rec in &root.rec_vars {
        visit_bounds_for_sandwich_verdict(&rec.bounds, &mut verdicts);
    }

    let rec_vars = root
        .rec_vars
        .iter()
        .map(|rec| rec.var)
        .collect::<FxHashSet<_>>();
    let mut lift = FxHashMap::default();
    for (var, verdict) in verdicts {
        if rec_vars.contains(&var) || !is_simplification_candidate(machine, boundary, var) {
            continue;
        }
        match verdict {
            SandwichVerdict::Single(
                kind @ (SandwichKind::Con(..) | SandwichKind::Tuple(_) | SandwichKind::Fun),
            ) => {
                lift.insert(var, kind);
            }
            _ => {}
        }
    }
    SandwichVerdicts { lift }
}

fn visit_type_for_sandwich_verdict(
    ty: &CompactType,
    verdicts: &mut FxHashMap<TypeVar, SandwichVerdict>,
) {
    let kinds = sandwich_kinds(ty);
    for var in &ty.vars {
        record_sandwich_var_occurrence(verdicts, var.var, &kinds);
    }

    for con in &ty.cons {
        for arg in &con.args {
            visit_bounds_for_sandwich_verdict(arg, verdicts);
        }
    }
    for fun in &ty.funs {
        visit_type_for_sandwich_verdict(&fun.arg, verdicts);
        visit_type_for_sandwich_verdict(&fun.arg_eff, verdicts);
        visit_type_for_sandwich_verdict(&fun.ret_eff, verdicts);
        visit_type_for_sandwich_verdict(&fun.ret, verdicts);
    }
    for record in &ty.records {
        for field in &record.fields {
            visit_type_for_sandwich_verdict(&field.value, verdicts);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            visit_type_for_sandwich_verdict(&field.value, verdicts);
        }
        visit_type_for_sandwich_verdict(&spread.tail, verdicts);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_type_for_sandwich_verdict(payload, verdicts);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            visit_type_for_sandwich_verdict(item, verdicts);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            visit_type_for_sandwich_verdict(item, verdicts);
        }
        visit_type_for_sandwich_verdict(&row.tail, verdicts);
    }
}

fn visit_bounds_for_sandwich_verdict(
    bounds: &CompactBounds,
    verdicts: &mut FxHashMap<TypeVar, SandwichVerdict>,
) {
    match bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            visit_type_for_sandwich_verdict(lower, verdicts);
            visit_type_for_sandwich_verdict(upper, verdicts);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                visit_bounds_for_sandwich_verdict(arg, verdicts);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            visit_bounds_for_sandwich_verdict(arg, verdicts);
            visit_bounds_for_sandwich_verdict(arg_eff, verdicts);
            visit_bounds_for_sandwich_verdict(ret_eff, verdicts);
            visit_bounds_for_sandwich_verdict(ret, verdicts);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                visit_bounds_for_sandwich_verdict(&field.value, verdicts);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    visit_bounds_for_sandwich_verdict(payload, verdicts);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                visit_bounds_for_sandwich_verdict(item, verdicts);
            }
        }
    }
}

fn sandwich_kinds(ty: &CompactType) -> Vec<SandwichKind> {
    let mut kinds = Vec::new();
    for con in &ty.cons {
        kinds.push(SandwichKind::Con(con.path.clone(), con.args.len()));
    }
    for tuple in &ty.tuples {
        kinds.push(SandwichKind::Tuple(tuple.items.len()));
    }
    if !ty.funs.is_empty() {
        kinds.push(SandwichKind::Fun);
    }
    if !ty.builtins.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.poly_variants.is_empty()
        || !ty.rows.is_empty()
    {
        kinds.push(SandwichKind::ConcreteButNotLiftable);
    }
    kinds
}

fn record_sandwich_var_occurrence(
    verdicts: &mut FxHashMap<TypeVar, SandwichVerdict>,
    var: TypeVar,
    kinds: &[SandwichKind],
) {
    let occurrence = if kinds.len() == 1 {
        SandwichVerdict::Single(kinds[0].clone())
    } else {
        SandwichVerdict::NoLift
    };
    let merged = match (verdicts.get(&var), &occurrence) {
        (None, _) => occurrence,
        (Some(SandwichVerdict::NoLift), _) | (_, SandwichVerdict::NoLift) => {
            SandwichVerdict::NoLift
        }
        (Some(SandwichVerdict::Single(lhs)), SandwichVerdict::Single(rhs)) => {
            if lhs == rhs {
                SandwichVerdict::Single(lhs.clone())
            } else {
                SandwichVerdict::NoLift
            }
        }
    };
    verdicts.insert(var, merged);
}

fn sandwich_type(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    mut ty: CompactType,
    verdicts: &SandwichVerdicts,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
    sandwiches: &mut FxHashMap<TypeVar, CompactSandwichKind>,
) -> CompactType {
    ty.cons = ty
        .cons
        .into_iter()
        .map(|con| CompactCon {
            path: con.path,
            args: con
                .args
                .into_iter()
                .map(|arg| {
                    sandwich_bounds(machine, boundary, arg, verdicts, fresh, changed, sandwiches)
                })
                .collect(),
        })
        .collect();
    for fun in &mut ty.funs {
        fun.arg = sandwich_type(
            machine,
            boundary,
            mem::take(&mut fun.arg),
            verdicts,
            fresh,
            changed,
            sandwiches,
        );
        fun.arg_eff = sandwich_type(
            machine,
            boundary,
            mem::take(&mut fun.arg_eff),
            verdicts,
            fresh,
            changed,
            sandwiches,
        );
        fun.ret_eff = sandwich_type(
            machine,
            boundary,
            mem::take(&mut fun.ret_eff),
            verdicts,
            fresh,
            changed,
            sandwiches,
        );
        fun.ret = sandwich_type(
            machine,
            boundary,
            mem::take(&mut fun.ret),
            verdicts,
            fresh,
            changed,
            sandwiches,
        );
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            field.value = sandwich_type(
                machine,
                boundary,
                mem::take(&mut field.value),
                verdicts,
                fresh,
                changed,
                sandwiches,
            );
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            field.value = sandwich_type(
                machine,
                boundary,
                mem::take(&mut field.value),
                verdicts,
                fresh,
                changed,
                sandwiches,
            );
        }
        spread.tail = Box::new(sandwich_type(
            machine,
            boundary,
            *mem::take(&mut spread.tail),
            verdicts,
            fresh,
            changed,
            sandwiches,
        ));
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                *payload = sandwich_type(
                    machine,
                    boundary,
                    mem::take(payload),
                    verdicts,
                    fresh,
                    changed,
                    sandwiches,
                );
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            *item = sandwich_type(
                machine,
                boundary,
                mem::take(item),
                verdicts,
                fresh,
                changed,
                sandwiches,
            );
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            *item = sandwich_type(
                machine,
                boundary,
                mem::take(item),
                verdicts,
                fresh,
                changed,
                sandwiches,
            );
        }
        row.tail = Box::new(sandwich_type(
            machine,
            boundary,
            *mem::take(&mut row.tail),
            verdicts,
            fresh,
            changed,
            sandwiches,
        ));
    }
    ty
}

fn sandwich_bounds(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    bounds: CompactBounds,
    verdicts: &SandwichVerdicts,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
    sandwiches: &mut FxHashMap<TypeVar, CompactSandwichKind>,
) -> CompactBounds {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            if let Some((center, kind, lifted)) =
                try_lift_interval(machine, boundary, self_var, &lower, &upper, verdicts, fresh)
            {
                *changed = true;
                record_sandwich(sandwiches, center, &kind);
                sandwich_bounds(
                    machine, boundary, lifted, verdicts, fresh, changed, sandwiches,
                )
            } else {
                CompactBounds::Interval {
                    self_var,
                    lower: sandwich_type(
                        machine, boundary, lower, verdicts, fresh, changed, sandwiches,
                    ),
                    upper: sandwich_type(
                        machine, boundary, upper, verdicts, fresh, changed, sandwiches,
                    ),
                }
            }
        }
        CompactBounds::Con { path, args } => CompactBounds::Con {
            path,
            args: args
                .into_iter()
                .map(|arg| {
                    sandwich_bounds(machine, boundary, arg, verdicts, fresh, changed, sandwiches)
                })
                .collect(),
        },
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => CompactBounds::Fun {
            arg: Box::new(sandwich_bounds(
                machine, boundary, *arg, verdicts, fresh, changed, sandwiches,
            )),
            arg_eff: Box::new(sandwich_bounds(
                machine, boundary, *arg_eff, verdicts, fresh, changed, sandwiches,
            )),
            ret_eff: Box::new(sandwich_bounds(
                machine, boundary, *ret_eff, verdicts, fresh, changed, sandwiches,
            )),
            ret: Box::new(sandwich_bounds(
                machine, boundary, *ret, verdicts, fresh, changed, sandwiches,
            )),
        },
        CompactBounds::Record { fields } => CompactBounds::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: sandwich_bounds(
                        machine,
                        boundary,
                        field.value,
                        verdicts,
                        fresh,
                        changed,
                        sandwiches,
                    ),
                    optional: field.optional,
                })
                .collect(),
        },
        CompactBounds::PolyVariant { items } => CompactBounds::PolyVariant {
            items: items
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| {
                                sandwich_bounds(
                                    machine, boundary, payload, verdicts, fresh, changed,
                                    sandwiches,
                                )
                            })
                            .collect(),
                    )
                })
                .collect(),
        },
        CompactBounds::Tuple { items } => CompactBounds::Tuple {
            items: items
                .into_iter()
                .map(|item| {
                    sandwich_bounds(
                        machine, boundary, item, verdicts, fresh, changed, sandwiches,
                    )
                })
                .collect(),
        },
    }
}

fn try_lift_interval(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    self_var: TypeVar,
    lower: &CompactType,
    upper: &CompactType,
    verdicts: &SandwichVerdicts,
    fresh: &mut FreshCompactVars,
) -> Option<(TypeVar, SandwichKind, CompactBounds)> {
    if !is_simplification_candidate(machine, boundary, self_var) {
        return None;
    }
    let center = if verdicts.lift.contains_key(&self_var) {
        self_var
    } else {
        common_var_in_types(lower, upper).filter(|var| verdicts.lift.contains_key(var))?
    };
    let kind = verdicts.lift.get(&center)?.clone();
    let lifted = match kind.clone() {
        SandwichKind::Con(path, arity) => {
            let lower_args = single_con(lower, &path, arity)?;
            let upper_args = single_con(upper, &path, arity)?;
            CompactBounds::Con {
                path,
                args: lower_args
                    .iter()
                    .zip(upper_args)
                    .map(|(lower, upper)| merge_arg_bounds(lower, upper, fresh))
                    .collect(),
            }
        }
        SandwichKind::Tuple(arity) => {
            let lower_items = single_tuple(lower, arity)?;
            let upper_items = single_tuple(upper, arity)?;
            CompactBounds::Tuple {
                items: lower_items
                    .iter()
                    .zip(upper_items)
                    .map(|(lower, upper)| interval_from_types(lower.clone(), upper.clone(), fresh))
                    .collect(),
            }
        }
        SandwichKind::Fun => {
            let lower_fun = single_fun(lower)?;
            let upper_fun = single_fun(upper)?;
            CompactBounds::Fun {
                arg: Box::new(interval_from_types(
                    upper_fun.arg.clone(),
                    lower_fun.arg.clone(),
                    fresh,
                )),
                arg_eff: Box::new(interval_from_types(
                    upper_fun.arg_eff.clone(),
                    lower_fun.arg_eff.clone(),
                    fresh,
                )),
                ret_eff: Box::new(interval_from_types(
                    lower_fun.ret_eff.clone(),
                    upper_fun.ret_eff.clone(),
                    fresh,
                )),
                ret: Box::new(interval_from_types(
                    lower_fun.ret.clone(),
                    upper_fun.ret.clone(),
                    fresh,
                )),
            }
        }
        SandwichKind::ConcreteButNotLiftable => return None,
    };
    Some((center, kind, lifted))
}

fn record_sandwich(
    sandwiches: &mut FxHashMap<TypeVar, CompactSandwichKind>,
    var: TypeVar,
    kind: &SandwichKind,
) {
    let Some(kind) = compact_sandwich_kind(kind) else {
        return;
    };
    sandwiches.insert(var, kind);
}

fn compact_sandwich_kind(kind: &SandwichKind) -> Option<CompactSandwichKind> {
    match kind {
        SandwichKind::Con(path, arity) => Some(CompactSandwichKind::Con {
            path: path.clone(),
            arity: *arity,
        }),
        SandwichKind::Tuple(arity) => Some(CompactSandwichKind::Tuple { arity: *arity }),
        SandwichKind::Fun => Some(CompactSandwichKind::Fun),
        SandwichKind::ConcreteButNotLiftable => None,
    }
}

fn sorted_sandwiches(sandwiches: FxHashMap<TypeVar, CompactSandwichKind>) -> Vec<CompactSandwich> {
    let mut sandwiches = sandwiches
        .into_iter()
        .map(|(var, kind)| CompactSandwich { var, kind })
        .collect::<Vec<_>>();
    sandwiches.sort_by_key(|sandwich| sandwich.var.0);
    sandwiches
}

fn merge_arg_bounds(
    lower_arg: &CompactBounds,
    upper_arg: &CompactBounds,
    fresh: &mut FreshCompactVars,
) -> CompactBounds {
    match (lower_arg, upper_arg) {
        (
            CompactBounds::Interval {
                lower: lower_lower,
                upper: lower_upper,
                ..
            },
            CompactBounds::Interval {
                lower: upper_lower,
                upper: upper_upper,
                ..
            },
        ) => interval_from_types(
            merge_compact_types(true, lower_lower.clone(), upper_lower.clone()),
            merge_compact_types(false, lower_upper.clone(), upper_upper.clone()),
            fresh,
        ),
        _ if lower_arg == upper_arg => lower_arg.clone(),
        _ => lower_arg.clone(),
    }
}

fn interval_from_types(
    lower: CompactType,
    upper: CompactType,
    fresh: &mut FreshCompactVars,
) -> CompactBounds {
    let self_var = common_var_in_types(&lower, &upper).unwrap_or_else(|| fresh.fresh());
    CompactBounds::Interval {
        self_var,
        lower,
        upper,
    }
}

fn common_var_in_types(lower: &CompactType, upper: &CompactType) -> Option<TypeVar> {
    lower
        .vars
        .iter()
        .map(|var| var.var)
        .filter(|lower_var| {
            upper
                .vars
                .iter()
                .any(|upper_var| upper_var.var == *lower_var)
        })
        .min_by_key(|var| var.0)
}

fn single_con<'a>(
    ty: &'a CompactType,
    path: &[String],
    arity: usize,
) -> Option<&'a [CompactBounds]> {
    if ty.cons.len() == 1
        && ty.cons[0].path == path
        && ty.cons[0].args.len() == arity
        && ty.builtins.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        Some(&ty.cons[0].args)
    } else {
        None
    }
}

fn single_tuple(ty: &CompactType, arity: usize) -> Option<&[CompactType]> {
    if ty.tuples.len() == 1
        && ty.tuples[0].items.len() == arity
        && ty.cons.is_empty()
        && ty.builtins.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.rows.is_empty()
    {
        Some(&ty.tuples[0].items)
    } else {
        None
    }
}

fn single_fun(ty: &CompactType) -> Option<&CompactFun> {
    if ty.funs.len() == 1
        && ty.cons.is_empty()
        && ty.builtins.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        Some(&ty.funs[0])
    } else {
        None
    }
}

struct FreshCompactVars {
    next: u32,
}

impl FreshCompactVars {
    fn new(root: &CompactRoot) -> Self {
        Self {
            next: max_type_var_in_root(root).map_or(0, |var| var.0 + 1),
        }
    }

    fn fresh(&mut self) -> TypeVar {
        let var = TypeVar(self.next);
        self.next += 1;
        var
    }
}

fn max_type_var_in_root(root: &CompactRoot) -> Option<TypeVar> {
    let mut max = None;
    max_type_var_in_type(&root.root, &mut max);
    for rec in &root.rec_vars {
        update_max_type_var(rec.var, &mut max);
        max_type_var_in_bounds(&rec.bounds, &mut max);
    }
    max
}

fn max_type_var_in_type(ty: &CompactType, max: &mut Option<TypeVar>) {
    for var in &ty.vars {
        update_max_type_var(var.var, max);
    }
    for con in &ty.cons {
        for arg in &con.args {
            max_type_var_in_bounds(arg, max);
        }
    }
    for fun in &ty.funs {
        max_type_var_in_type(&fun.arg, max);
        max_type_var_in_type(&fun.arg_eff, max);
        max_type_var_in_type(&fun.ret_eff, max);
        max_type_var_in_type(&fun.ret, max);
    }
    for record in &ty.records {
        for field in &record.fields {
            max_type_var_in_type(&field.value, max);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            max_type_var_in_type(&field.value, max);
        }
        max_type_var_in_type(&spread.tail, max);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                max_type_var_in_type(payload, max);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            max_type_var_in_type(item, max);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            max_type_var_in_type(item, max);
        }
        max_type_var_in_type(&row.tail, max);
    }
}

fn max_type_var_in_bounds(bounds: &CompactBounds, max: &mut Option<TypeVar>) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            update_max_type_var(*self_var, max);
            max_type_var_in_type(lower, max);
            max_type_var_in_type(upper, max);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                max_type_var_in_bounds(arg, max);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            max_type_var_in_bounds(arg, max);
            max_type_var_in_bounds(arg_eff, max);
            max_type_var_in_bounds(ret_eff, max);
            max_type_var_in_bounds(ret, max);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                max_type_var_in_bounds(&field.value, max);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    max_type_var_in_bounds(payload, max);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                max_type_var_in_bounds(item, max);
            }
        }
    }
}

fn update_max_type_var(var: TypeVar, max: &mut Option<TypeVar>) {
    if max.is_none_or(|current| var.0 > current.0) {
        *max = Some(var);
    }
}

#[derive(Default)]
struct VarPolarities {
    positive: FxHashSet<TypeVar>,
    negative: FxHashSet<TypeVar>,
}

impl VarPolarities {
    fn record(&mut self, var: TypeVar, polarity: Polarity) {
        match polarity {
            Polarity::Positive => {
                self.positive.insert(var);
            }
            Polarity::Negative => {
                self.negative.insert(var);
            }
        }
    }

    fn is_bipolar(&self, var: TypeVar) -> bool {
        self.positive.contains(&var) && self.negative.contains(&var)
    }
}

fn collect_var_polarities(root: &CompactRoot) -> VarPolarities {
    let mut out = VarPolarities::default();
    visit_type_polarity(&root.root, Polarity::Positive, &mut out);
    for rec in &root.rec_vars {
        visit_bounds_polarity(&rec.bounds, Polarity::Positive, &mut out);
    }
    out
}

fn visit_type_polarity(ty: &CompactType, polarity: Polarity, out: &mut VarPolarities) {
    for var in &ty.vars {
        out.record(var.var, polarity);
    }
    for con in &ty.cons {
        for arg in &con.args {
            visit_bounds_polarity(arg, polarity, out);
        }
    }
    for fun in &ty.funs {
        visit_type_polarity(&fun.arg, polarity.flipped(), out);
        visit_type_polarity(&fun.arg_eff, polarity.flipped(), out);
        visit_type_polarity(&fun.ret_eff, polarity, out);
        visit_type_polarity(&fun.ret, polarity, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            visit_type_polarity(&field.value, polarity, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            visit_type_polarity(&field.value, polarity, out);
        }
        visit_type_polarity(&spread.tail, polarity, out);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_type_polarity(payload, polarity, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            visit_type_polarity(item, polarity, out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            visit_type_polarity(item, polarity, out);
        }
        visit_type_polarity(&row.tail, polarity, out);
    }
}

fn visit_bounds_polarity(bounds: &CompactBounds, polarity: Polarity, out: &mut VarPolarities) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            out.record(*self_var, Polarity::Positive);
            out.record(*self_var, Polarity::Negative);
            visit_type_polarity(lower, polarity, out);
            visit_type_polarity(upper, polarity.flipped(), out);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                visit_bounds_polarity(arg, polarity, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            visit_bounds_polarity(arg, polarity.flipped(), out);
            visit_bounds_polarity(arg_eff, polarity.flipped(), out);
            visit_bounds_polarity(ret_eff, polarity, out);
            visit_bounds_polarity(ret, polarity, out);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                visit_bounds_polarity(&field.value, polarity, out);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    visit_bounds_polarity(payload, polarity, out);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                visit_bounds_polarity(item, polarity, out);
            }
        }
    }
}

#[derive(Default)]
struct CoOccurrences {
    positive: FxHashMap<TypeVar, FxHashSet<usize>>,
    negative: FxHashMap<TypeVar, FxHashSet<usize>>,
    next_group: usize,
}

impl CoOccurrences {
    fn record_group(&mut self, vars: Vec<CompactVar>, polarity: Polarity) {
        let mut vars = vars.into_iter().map(|var| var.var).collect::<Vec<_>>();
        vars.sort_by_key(|var| var.0);
        vars.dedup();
        if vars.len() < 2 {
            return;
        }

        let group = self.next_group;
        self.next_group += 1;
        let table = match polarity {
            Polarity::Positive => &mut self.positive,
            Polarity::Negative => &mut self.negative,
        };
        for var in vars {
            table.entry(var).or_default().insert(group);
        }
    }

    fn substitution(&self, machine: &ConstraintMachine, boundary: TypeLevel) -> VarSubstitution {
        let mut union = VarUnion::default();
        register_co_occurrence_table(&self.positive, machine, boundary, &mut union);
        register_co_occurrence_table(&self.negative, machine, boundary, &mut union);
        union.into_substitution()
    }
}

fn register_co_occurrence_table(
    table: &FxHashMap<TypeVar, FxHashSet<usize>>,
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    union: &mut VarUnion,
) {
    let mut buckets = FxHashMap::<Vec<usize>, Vec<TypeVar>>::default();
    for (&var, groups) in table {
        if groups.is_empty() {
            continue;
        }
        let mut key = groups.iter().cloned().collect::<Vec<_>>();
        key.sort_unstable();
        buckets.entry(key).or_default().push(var);
    }
    for mut vars in buckets.into_values() {
        if vars.len() < 2 {
            continue;
        }
        vars.sort_by_key(|var| var.0);
        let candidates = vars
            .iter()
            .copied()
            .filter(|var| is_simplification_candidate(machine, boundary, *var))
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            continue;
        }

        let rep = vars
            .iter()
            .copied()
            .min_by_key(|var| (machine.level_of(*var), var.0))
            .expect("co-occurrence bucket should be non-empty");
        for var in candidates {
            union.union_to(rep, var);
        }
    }
}

fn collect_co_occurrences(root: &CompactRoot) -> CoOccurrences {
    let mut out = CoOccurrences::default();
    visit_type_co_occurrence(&root.root, Polarity::Positive, &[], &mut out);
    for rec in &root.rec_vars {
        visit_bounds_co_occurrence(&rec.bounds, Polarity::Positive, &mut out);
    }
    out
}

fn visit_type_co_occurrence(
    ty: &CompactType,
    polarity: Polarity,
    extra_vars: &[TypeVar],
    out: &mut CoOccurrences,
) {
    let vars = ty
        .vars
        .iter()
        .cloned()
        .chain(extra_vars.iter().copied().map(CompactVar::plain))
        .collect::<Vec<_>>();
    out.record_group(vars, polarity);

    for con in &ty.cons {
        for arg in &con.args {
            visit_bounds_co_occurrence(arg, polarity, out);
        }
    }
    for fun in &ty.funs {
        visit_type_co_occurrence(&fun.arg, polarity.flipped(), &[], out);
        visit_type_co_occurrence(&fun.arg_eff, polarity.flipped(), &[], out);
        visit_type_co_occurrence(&fun.ret_eff, polarity, &[], out);
        visit_type_co_occurrence(&fun.ret, polarity, &[], out);
    }
    for record in &ty.records {
        for field in &record.fields {
            visit_type_co_occurrence(&field.value, polarity, &[], out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            visit_type_co_occurrence(&field.value, polarity, &[], out);
        }
        visit_type_co_occurrence(&spread.tail, polarity, &[], out);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_type_co_occurrence(payload, polarity, &[], out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            visit_type_co_occurrence(item, polarity, &[], out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            visit_type_co_occurrence(item, polarity, &[], out);
        }
        visit_type_co_occurrence(&row.tail, polarity, &[], out);
    }
}

fn visit_bounds_co_occurrence(bounds: &CompactBounds, polarity: Polarity, out: &mut CoOccurrences) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            visit_type_co_occurrence(lower, polarity, &[*self_var], out);
            visit_type_co_occurrence(upper, polarity.flipped(), &[*self_var], out);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                visit_bounds_co_occurrence(arg, polarity, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            visit_bounds_co_occurrence(arg, polarity.flipped(), out);
            visit_bounds_co_occurrence(arg_eff, polarity.flipped(), out);
            visit_bounds_co_occurrence(ret_eff, polarity, out);
            visit_bounds_co_occurrence(ret, polarity, out);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                visit_bounds_co_occurrence(&field.value, polarity, out);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    visit_bounds_co_occurrence(payload, polarity, out);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                visit_bounds_co_occurrence(item, polarity, out);
            }
        }
    }
}

#[derive(Default)]
struct VarUnion {
    parent: FxHashMap<TypeVar, TypeVar>,
}

impl VarUnion {
    fn union_to(&mut self, representative: TypeVar, other: TypeVar) {
        let representative = self.find(representative);
        let other = self.find(other);
        if representative == other {
            return;
        }
        self.parent.insert(other, representative);
    }

    fn find(&mut self, var: TypeVar) -> TypeVar {
        let parent = *self.parent.entry(var).or_insert(var);
        if parent == var {
            return var;
        }
        let root = self.find(parent);
        self.parent.insert(var, root);
        root
    }

    fn into_substitution(mut self) -> VarSubstitution {
        let vars = self.parent.keys().copied().collect::<Vec<_>>();
        let mut map = FxHashMap::default();
        for var in vars {
            let rep = self.find(var);
            if rep != var {
                map.insert(var, rep);
            }
        }
        VarSubstitution { map }
    }
}

struct VarSubstitution {
    map: FxHashMap<TypeVar, TypeVar>,
}

impl VarSubstitution {
    fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    fn representative(&self, var: TypeVar) -> TypeVar {
        self.map.get(&var).copied().unwrap_or(var)
    }
}

fn rewrite_root_vars(
    root: &mut CompactRoot,
    mut rewrite: impl FnMut(TypeVar) -> Option<TypeVar>,
) -> Vec<CompactVarSubstitution> {
    let mut substitutions = FxHashMap::default();
    rewrite_type_vars(&mut root.root, &mut rewrite, &mut substitutions);
    for rec in &mut root.rec_vars {
        let source = rec.var;
        if let Some(rep) = rewrite(rec.var) {
            record_var_substitution(&mut substitutions, source, Some(rep));
            rec.var = rep;
        }
        rewrite_bounds_vars(&mut rec.bounds, &mut rewrite, &mut substitutions);
    }
    sorted_var_substitutions(substitutions)
}

fn rewrite_type_vars(
    ty: &mut CompactType,
    rewrite: &mut impl FnMut(TypeVar) -> Option<TypeVar>,
    substitutions: &mut FxHashMap<TypeVar, Option<TypeVar>>,
) {
    let mut vars = Vec::new();
    for mut var in mem::take(&mut ty.vars) {
        let source = var.var;
        let Some(rep) = rewrite(var.var) else {
            record_var_substitution(substitutions, source, None);
            continue;
        };
        record_var_substitution(substitutions, source, Some(rep));
        var.var = rep;
        push_compact_var_with_unioned_weight(&mut vars, var);
    }
    ty.vars = vars;

    for con in &mut ty.cons {
        for arg in &mut con.args {
            rewrite_bounds_vars(arg, rewrite, substitutions);
        }
    }
    for fun in &mut ty.funs {
        rewrite_type_vars(&mut fun.arg, rewrite, substitutions);
        rewrite_type_vars(&mut fun.arg_eff, rewrite, substitutions);
        rewrite_type_vars(&mut fun.ret_eff, rewrite, substitutions);
        rewrite_type_vars(&mut fun.ret, rewrite, substitutions);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            rewrite_type_vars(&mut field.value, rewrite, substitutions);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            rewrite_type_vars(&mut field.value, rewrite, substitutions);
        }
        rewrite_type_vars(&mut spread.tail, rewrite, substitutions);
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                rewrite_type_vars(payload, rewrite, substitutions);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            rewrite_type_vars(item, rewrite, substitutions);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            rewrite_type_vars(item, rewrite, substitutions);
        }
        rewrite_type_vars(&mut row.tail, rewrite, substitutions);
    }
}

fn push_compact_var_with_unioned_weight(vars: &mut Vec<CompactVar>, var: CompactVar) {
    if let Some(existing) = vars.iter_mut().find(|existing| existing.var == var.var) {
        existing.weight = existing.weight.union(&var.weight);
    } else {
        vars.push(var);
    }
}

fn rewrite_bounds_vars(
    bounds: &mut CompactBounds,
    rewrite: &mut impl FnMut(TypeVar) -> Option<TypeVar>,
    substitutions: &mut FxHashMap<TypeVar, Option<TypeVar>>,
) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            let source = *self_var;
            if let Some(rep) = rewrite(*self_var) {
                record_var_substitution(substitutions, source, Some(rep));
                *self_var = rep;
            }
            rewrite_type_vars(lower, rewrite, substitutions);
            rewrite_type_vars(upper, rewrite, substitutions);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                rewrite_bounds_vars(arg, rewrite, substitutions);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            rewrite_bounds_vars(arg, rewrite, substitutions);
            rewrite_bounds_vars(arg_eff, rewrite, substitutions);
            rewrite_bounds_vars(ret_eff, rewrite, substitutions);
            rewrite_bounds_vars(ret, rewrite, substitutions);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                rewrite_bounds_vars(&mut field.value, rewrite, substitutions);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    rewrite_bounds_vars(payload, rewrite, substitutions);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                rewrite_bounds_vars(item, rewrite, substitutions);
            }
        }
    }
}

fn record_var_substitution(
    substitutions: &mut FxHashMap<TypeVar, Option<TypeVar>>,
    source: TypeVar,
    target: Option<TypeVar>,
) {
    if target == Some(source) {
        return;
    }
    substitutions.insert(source, target);
}

fn sorted_var_substitutions(
    substitutions: FxHashMap<TypeVar, Option<TypeVar>>,
) -> Vec<CompactVarSubstitution> {
    let mut substitutions = substitutions
        .into_iter()
        .map(|(source, target)| CompactVarSubstitution { source, target })
        .collect::<Vec<_>>();
    substitutions.sort_by_key(|substitution| substitution.source.0);
    substitutions
}

fn normalize_var_substitutions(
    substitutions: Vec<CompactVarSubstitution>,
) -> Vec<CompactVarSubstitution> {
    let map = substitutions
        .into_iter()
        .map(|substitution| (substitution.source, substitution.target))
        .collect::<FxHashMap<_, _>>();
    let sources = map.keys().copied().collect::<Vec<_>>();
    let mut normalized = FxHashMap::default();
    for source in sources {
        let mut seen = FxHashSet::default();
        let target = resolve_substitution_target(source, &map, &mut seen);
        record_var_substitution(&mut normalized, source, target);
    }
    sorted_var_substitutions(normalized)
}

fn resolve_substitution_target(
    source: TypeVar,
    map: &FxHashMap<TypeVar, Option<TypeVar>>,
    seen: &mut FxHashSet<TypeVar>,
) -> Option<TypeVar> {
    if !seen.insert(source) {
        return Some(source);
    }
    match map.get(&source).copied() {
        None => Some(source),
        Some(None) => None,
        Some(Some(target)) => match resolve_substitution_target(target, map, seen) {
            Some(resolved) if resolved == target => Some(target),
            resolved => resolved,
        },
    }
}
