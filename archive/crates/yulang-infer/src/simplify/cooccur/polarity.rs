use std::collections::HashSet;

use crate::ids::TypeVar;
use crate::simplify::polar::PolarOccurrences;

use super::{CompactBounds, CompactFun, CompactRoleConstraint, CompactType, CompactTypeScheme};

pub(super) fn analyze_polar_occurrences_with_role_constraints(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
) -> PolarOccurrences {
    let mut occurrences = PolarOccurrences::default();
    let mut expanded = HashSet::new();
    let suppressed = HashSet::new();

    visit_type(
        scheme,
        scheme.cty.lower(),
        true,
        &suppressed,
        &mut expanded,
        &mut occurrences,
    );
    visit_root_upper_children(
        scheme,
        scheme.cty.lower(),
        scheme.cty.upper(),
        &mut expanded,
        &mut occurrences,
    );
    for constraint in constraints {
        for arg in &constraint.args {
            visit_bounds(scheme, arg, &suppressed, &mut expanded, &mut occurrences);
        }
    }

    occurrences
}

fn visit_bounds(
    scheme: &CompactTypeScheme,
    bounds: &CompactBounds,
    suppressed: &HashSet<TypeVar>,
    expanded: &mut HashSet<(TypeVar, bool)>,
    occurrences: &mut PolarOccurrences,
) {
    visit_bounds_with_polarity(scheme, bounds, true, suppressed, expanded, occurrences);
}

fn visit_bounds_with_polarity(
    scheme: &CompactTypeScheme,
    bounds: &CompactBounds,
    positive: bool,
    suppressed: &HashSet<TypeVar>,
    expanded: &mut HashSet<(TypeVar, bool)>,
    occurrences: &mut PolarOccurrences,
) {
    match bounds {
        CompactBounds::Interval { .. } => {}
        CompactBounds::Con { args, .. } => {
            for arg in args {
                visit_bounds(scheme, arg, suppressed, expanded, occurrences);
            }
            return;
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                visit_bounds(scheme, item, suppressed, expanded, occurrences);
            }
            return;
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            visit_bounds_with_polarity(scheme, arg, false, suppressed, expanded, occurrences);
            visit_bounds_with_polarity(scheme, arg_eff, false, suppressed, expanded, occurrences);
            visit_bounds_with_polarity(scheme, ret_eff, true, suppressed, expanded, occurrences);
            visit_bounds_with_polarity(scheme, ret, true, suppressed, expanded, occurrences);
            return;
        }
    }
    let centers = center_vars(bounds);
    for &center in &centers {
        if suppressed.contains(&center) {
            continue;
        }
        occurrences.insert(center, true);
        occurrences.insert(center, false);
    }
    visit_type(
        scheme,
        bounds.lower(),
        positive,
        suppressed,
        expanded,
        occurrences,
    );
    visit_type(
        scheme,
        bounds.upper(),
        !positive,
        suppressed,
        expanded,
        occurrences,
    );
}

fn visit_type(
    scheme: &CompactTypeScheme,
    ty: &CompactType,
    positive: bool,
    suppressed: &HashSet<TypeVar>,
    expanded: &mut HashSet<(TypeVar, bool)>,
    occurrences: &mut PolarOccurrences,
) {
    for &tv in &ty.vars {
        if suppressed.contains(&tv) {
            continue;
        }
        occurrences.insert(tv, positive);
        if expanded.insert((tv, positive))
            && let Some(bounds) = scheme.rec_vars.get(&tv)
        {
            let recur = if positive {
                bounds.lower()
            } else {
                bounds.upper()
            };
            visit_type(scheme, recur, positive, suppressed, expanded, occurrences);
        }
    }

    visit_type_children(scheme, ty, positive, suppressed, expanded, occurrences);
}

fn visit_type_children(
    scheme: &CompactTypeScheme,
    ty: &CompactType,
    positive: bool,
    suppressed: &HashSet<TypeVar>,
    expanded: &mut HashSet<(TypeVar, bool)>,
    occurrences: &mut PolarOccurrences,
) {
    for con in &ty.cons {
        for arg in &con.args {
            visit_bounds(scheme, arg, suppressed, expanded, occurrences);
        }
    }
    for fun in &ty.funs {
        visit_fun(scheme, fun, positive, suppressed, expanded, occurrences);
    }
    for record in &ty.records {
        for field in &record.fields {
            visit_type(
                scheme,
                &field.value,
                positive,
                suppressed,
                expanded,
                occurrences,
            );
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            visit_type(
                scheme,
                &field.value,
                positive,
                suppressed,
                expanded,
                occurrences,
            );
        }
        visit_type(
            scheme,
            &spread.tail,
            positive,
            suppressed,
            expanded,
            occurrences,
        );
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_type(scheme, payload, positive, suppressed, expanded, occurrences);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            visit_type(scheme, item, positive, suppressed, expanded, occurrences);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            visit_type(scheme, item, positive, suppressed, expanded, occurrences);
        }
        visit_type(
            scheme,
            &row.tail,
            positive,
            suppressed,
            expanded,
            occurrences,
        );
    }
}

fn visit_fun(
    scheme: &CompactTypeScheme,
    fun: &CompactFun,
    positive: bool,
    suppressed: &HashSet<TypeVar>,
    expanded: &mut HashSet<(TypeVar, bool)>,
    occurrences: &mut PolarOccurrences,
) {
    visit_type(
        scheme,
        &fun.arg,
        !positive,
        suppressed,
        expanded,
        occurrences,
    );
    visit_type(
        scheme,
        &fun.arg_eff,
        !positive,
        suppressed,
        expanded,
        occurrences,
    );
    visit_type(
        scheme,
        &fun.ret_eff,
        positive,
        suppressed,
        expanded,
        occurrences,
    );
    visit_type(
        scheme,
        &fun.ret,
        positive,
        suppressed,
        expanded,
        occurrences,
    );
}

fn visit_root_upper_children(
    scheme: &CompactTypeScheme,
    lower: &CompactType,
    upper: &CompactType,
    expanded: &mut HashSet<(TypeVar, bool)>,
    occurrences: &mut PolarOccurrences,
) {
    let empty = HashSet::new();
    let lower_fun_vars = lower_fun_field_vars(lower);

    for con in &upper.cons {
        for arg in &con.args {
            visit_bounds(scheme, arg, &empty, expanded, occurrences);
        }
    }
    for fun in &upper.funs {
        visit_type(
            scheme,
            &fun.arg,
            true,
            &lower_fun_vars.arg,
            expanded,
            occurrences,
        );
        visit_type(
            scheme,
            &fun.arg_eff,
            true,
            &lower_fun_vars.arg_eff,
            expanded,
            occurrences,
        );
        visit_type(
            scheme,
            &fun.ret_eff,
            false,
            &lower_fun_vars.ret_eff,
            expanded,
            occurrences,
        );
        visit_type(
            scheme,
            &fun.ret,
            false,
            &lower_fun_vars.ret,
            expanded,
            occurrences,
        );
    }
    for record in &upper.records {
        for field in &record.fields {
            visit_type(scheme, &field.value, false, &empty, expanded, occurrences);
        }
    }
    for spread in &upper.record_spreads {
        for field in &spread.fields {
            visit_type(scheme, &field.value, false, &empty, expanded, occurrences);
        }
        visit_type(scheme, &spread.tail, false, &empty, expanded, occurrences);
    }
    for variant in &upper.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_type(scheme, payload, false, &empty, expanded, occurrences);
            }
        }
    }
    for tuple in &upper.tuples {
        for item in tuple {
            visit_type(scheme, item, false, &empty, expanded, occurrences);
        }
    }
    for row in &upper.rows {
        for item in &row.items {
            visit_type(scheme, item, false, &empty, expanded, occurrences);
        }
        visit_type(scheme, &row.tail, false, &empty, expanded, occurrences);
    }
}

#[derive(Default)]
struct FunFieldVars {
    arg: HashSet<TypeVar>,
    arg_eff: HashSet<TypeVar>,
    ret_eff: HashSet<TypeVar>,
    ret: HashSet<TypeVar>,
}

fn lower_fun_field_vars(lower: &CompactType) -> FunFieldVars {
    let mut out = FunFieldVars::default();
    for fun in &lower.funs {
        collect_type_vars(&fun.arg, &mut out.arg);
        collect_type_vars(&fun.arg_eff, &mut out.arg_eff);
        collect_type_vars(&fun.ret_eff, &mut out.ret_eff);
        collect_type_vars(&fun.ret, &mut out.ret);
    }
    out
}

fn collect_type_vars(ty: &CompactType, out: &mut HashSet<TypeVar>) {
    out.extend(ty.vars.iter().copied());
    for con in &ty.cons {
        for arg in &con.args {
            collect_bounds_vars(arg, out);
        }
    }
    for fun in &ty.funs {
        collect_type_vars(&fun.arg, out);
        collect_type_vars(&fun.arg_eff, out);
        collect_type_vars(&fun.ret_eff, out);
        collect_type_vars(&fun.ret, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_type_vars(&field.value, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_type_vars(&field.value, out);
        }
        collect_type_vars(&spread.tail, out);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_type_vars(payload, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            collect_type_vars(item, out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_type_vars(item, out);
        }
        collect_type_vars(&row.tail, out);
    }
}

fn collect_bounds_vars(bounds: &CompactBounds, out: &mut HashSet<TypeVar>) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            if let Some(tv) = self_var {
                out.insert(*tv);
            }
            collect_type_vars(lower, out);
            collect_type_vars(upper, out);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                collect_bounds_vars(arg, out);
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                collect_bounds_vars(item, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_bounds_vars(arg, out);
            collect_bounds_vars(arg_eff, out);
            collect_bounds_vars(ret_eff, out);
            collect_bounds_vars(ret, out);
        }
    }
}

fn center_vars(bounds: &CompactBounds) -> HashSet<TypeVar> {
    let CompactBounds::Interval {
        self_var,
        lower,
        upper,
    } = bounds
    else {
        return HashSet::new();
    };
    let mut out = lower
        .vars
        .intersection(&upper.vars)
        .copied()
        .collect::<HashSet<_>>();
    if let Some(self_var) = self_var {
        out.insert(*self_var);
    }
    out
}
