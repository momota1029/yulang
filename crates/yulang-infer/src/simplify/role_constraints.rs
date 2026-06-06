use std::collections::HashSet;

use crate::ids::TypeVar;

use super::compact::{CompactBounds, CompactType, CompactTypeScheme, merge_compact_bounds};
use super::cooccur::CompactRoleConstraint;

#[cfg(test)]
pub(crate) fn rewrite_role_constraints(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    subst: &std::collections::HashMap<TypeVar, Option<TypeVar>>,
) -> Vec<CompactRoleConstraint> {
    rewrite_role_constraints_with_role_arg_inputs(scheme, constraints, subst, &|_| None)
}

pub(crate) fn rewrite_role_constraints_with_role_arg_inputs(
    _scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    subst: &std::collections::HashMap<TypeVar, Option<TypeVar>>,
    role_arg_inputs: &dyn Fn(&crate::symbols::Path) -> Option<Vec<bool>>,
) -> Vec<CompactRoleConstraint> {
    let mut out = Vec::new();
    for constraint in constraints {
        let rewritten = CompactRoleConstraint {
            role: constraint.role.clone(),
            args: constraint
                .args
                .iter()
                .map(|arg| super::cooccur::rewrite_bounds(arg, subst))
                .collect(),
        };
        if !out.contains(&rewritten) {
            out.push(rewritten);
        }
    }
    let coalesced = coalesce_role_constraints(out, role_arg_inputs);
    remove_empty_role_constraints(coalesced)
}

fn coalesce_role_constraints(
    constraints: Vec<CompactRoleConstraint>,
    role_arg_inputs: &dyn Fn(&crate::symbols::Path) -> Option<Vec<bool>>,
) -> Vec<CompactRoleConstraint> {
    let mut out = Vec::new();
    let mut visited = vec![false; constraints.len()];

    for index in 0..constraints.len() {
        if visited[index] {
            continue;
        }
        visited[index] = true;
        let mut component = vec![index];
        let mut cursor = 0;
        while cursor < component.len() {
            let current = component[cursor];
            cursor += 1;
            for other in 0..constraints.len() {
                if visited[other] {
                    continue;
                }
                if can_coalesce_role_constraints(
                    &constraints[current],
                    &constraints[other],
                    role_arg_inputs,
                ) {
                    visited[other] = true;
                    component.push(other);
                }
            }
        }
        out.push(merge_role_constraint_component(
            component
                .into_iter()
                .map(|index| constraints[index].clone()),
        ));
    }

    out
}

fn remove_empty_role_constraints(
    constraints: Vec<CompactRoleConstraint>,
) -> Vec<CompactRoleConstraint> {
    constraints
        .into_iter()
        .filter(|constraint| !role_constraint_is_empty(constraint))
        .collect()
}

fn role_constraint_is_empty(constraint: &CompactRoleConstraint) -> bool {
    constraint.args.iter().all(|arg| {
        arg.self_var().is_none()
            && arg.lower() == &CompactType::default()
            && arg.upper() == &CompactType::default()
    })
}

fn can_coalesce_role_constraints(
    lhs: &CompactRoleConstraint,
    rhs: &CompactRoleConstraint,
    role_arg_inputs: &dyn Fn(&crate::symbols::Path) -> Option<Vec<bool>>,
) -> bool {
    if lhs.role != rhs.role || lhs.args.len() != rhs.args.len() {
        return false;
    }
    if lhs == rhs {
        return true;
    }
    // 設計 §簡約2: role を等号で結ぶ（融合する）のは、対応する全ての引数が共通の
    // 通常引数を共有しているときのみ。関連型は融合後に境界を合流させる対象だが、
    // それだけで impl head を同じものとして扱う根拠にはしない。
    let input_indices = role_constraint_input_indices(lhs, role_arg_inputs);
    !input_indices.is_empty()
        && input_indices.iter().all(|index| {
            let lhs_arg = &lhs.args[*index];
            let rhs_arg = &rhs.args[*index];
            !bounds_vars(lhs_arg).is_disjoint(&bounds_vars(rhs_arg))
        })
}

fn role_constraint_input_indices(
    constraint: &CompactRoleConstraint,
    role_arg_inputs: &dyn Fn(&crate::symbols::Path) -> Option<Vec<bool>>,
) -> Vec<usize> {
    let Some(flags) = role_arg_inputs(&constraint.role) else {
        return (0..constraint.args.len()).collect();
    };
    if flags.len() != constraint.args.len() {
        return (0..constraint.args.len()).collect();
    }
    let indices = flags
        .into_iter()
        .enumerate()
        .filter_map(|(index, is_input)| is_input.then_some(index))
        .collect::<Vec<_>>();
    if indices.is_empty() {
        (0..constraint.args.len()).collect()
    } else {
        indices
    }
}

fn bounds_vars(bounds: &CompactBounds) -> HashSet<TypeVar> {
    let mut out = HashSet::new();
    collect_compact_bounds_vars(bounds, &mut out);
    out
}

fn merge_role_constraint_component(
    constraints: impl Iterator<Item = CompactRoleConstraint>,
) -> CompactRoleConstraint {
    let items = constraints.collect::<Vec<_>>();
    let mut constraints = items.into_iter();
    let mut merged = constraints.next().expect("component must not be empty");
    for constraint in constraints {
        merged.args = merged
            .args
            .into_iter()
            .zip(constraint.args.into_iter())
            .map(|(lhs, rhs)| merge_compact_bounds(true, lhs, rhs))
            .collect();
    }
    merged
}

#[cfg(test)]
fn role_constraint_vars(constraint: &CompactRoleConstraint) -> HashSet<TypeVar> {
    let mut out = HashSet::new();
    for arg in &constraint.args {
        collect_compact_bounds_vars(arg, &mut out);
    }
    out
}

fn collect_compact_bounds_vars(bounds: &CompactBounds, out: &mut HashSet<TypeVar>) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            if let Some(tv) = self_var {
                out.insert(*tv);
            }
            collect_compact_type_vars(lower, out);
            collect_compact_type_vars(upper, out);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                collect_compact_bounds_vars(arg, out);
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                collect_compact_bounds_vars(item, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_compact_bounds_vars(arg, out);
            collect_compact_bounds_vars(arg_eff, out);
            collect_compact_bounds_vars(ret_eff, out);
            collect_compact_bounds_vars(ret, out);
        }
    }
}

fn collect_compact_type_vars(ty: &CompactType, out: &mut HashSet<TypeVar>) {
    out.extend(ty.vars.iter().copied());
    for con in &ty.cons {
        for arg in &con.args {
            collect_compact_bounds_vars(arg, out);
        }
    }
    for fun in &ty.funs {
        collect_compact_type_vars(&fun.arg, out);
        collect_compact_type_vars(&fun.arg_eff, out);
        collect_compact_type_vars(&fun.ret_eff, out);
        collect_compact_type_vars(&fun.ret, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_compact_type_vars(&field.value, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_compact_type_vars(&field.value, out);
        }
        collect_compact_type_vars(&spread.tail, out);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_compact_type_vars(payload, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            collect_compact_type_vars(item, out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_compact_type_vars(item, out);
        }
        collect_compact_type_vars(&row.tail, out);
    }
}

#[cfg(test)]
mod tests {
    use super::{
        rewrite_role_constraints, rewrite_role_constraints_with_role_arg_inputs,
        role_constraint_vars,
    };
    use std::collections::{HashMap, HashSet};

    use crate::fresh_type_var;
    use crate::simplify::compact::{CompactBounds, CompactType, CompactTypeScheme};
    use crate::simplify::cooccur::CompactRoleConstraint;
    use crate::symbols::{Name, Path};

    #[test]
    fn rewrite_role_constraints_drops_empty_constraints_after_rewrite() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let c = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds::Interval {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };
        let constraints = vec![
            role_constraint("R", vec![var_bounds(b)]),
            role_constraint("S", vec![var_bounds(b), var_bounds(c)]),
        ];

        let subst = HashMap::from([(b, None), (c, None)]);
        let rewritten = rewrite_role_constraints(&scheme, &constraints, &subst);

        assert!(
            rewritten.is_empty(),
            "role constraints rewritten to empty bounds should disappear instead of rendering as `_`",
        );
    }

    #[test]
    fn rewrite_role_constraints_keeps_vars_connected_through_other_roles() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds::Interval {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };
        let constraints = vec![
            role_constraint("R", vec![var_bounds(b)]),
            role_constraint("S", vec![var_bounds(b), var_bounds(a)]),
        ];

        let rewritten = rewrite_role_constraints(&scheme, &constraints, &HashMap::new());

        let r = rewritten
            .iter()
            .find(|constraint| constraint.role.segments[0].0 == "R")
            .expect("R constraint should remain");
        assert!(
            role_constraint_vars(r).contains(&b),
            "vars connected to ordinary scheme vars through other roles must not be resolved",
        );
    }

    #[test]
    fn rewrite_role_constraints_does_not_coalesce_through_associated_args_only() {
        let input_a = fresh_type_var();
        let input_b = fresh_type_var();
        let assoc = fresh_type_var();
        let scheme = CompactTypeScheme::default();
        let role = role_path("Index");
        let constraints = vec![
            CompactRoleConstraint {
                role: role.clone(),
                args: vec![var_bounds(input_a), var_bounds(assoc)],
            },
            CompactRoleConstraint {
                role: role.clone(),
                args: vec![var_bounds(input_b), var_bounds(assoc)],
            },
        ];

        let rewritten = rewrite_role_constraints_with_role_arg_inputs(
            &scheme,
            &constraints,
            &HashMap::new(),
            &|path| (path == &role).then_some(vec![true, false]),
        );

        assert_eq!(
            rewritten.len(),
            2,
            "associated type variables do not make two role heads equal",
        );
    }

    #[test]
    fn rewrite_role_constraints_coalesces_inputs_and_merges_associated_args() {
        let input = fresh_type_var();
        let assoc_a = fresh_type_var();
        let assoc_b = fresh_type_var();
        let scheme = CompactTypeScheme::default();
        let role = role_path("Index");
        let constraints = vec![
            CompactRoleConstraint {
                role: role.clone(),
                args: vec![var_bounds(input), var_bounds(assoc_a)],
            },
            CompactRoleConstraint {
                role: role.clone(),
                args: vec![var_bounds(input), var_bounds(assoc_b)],
            },
        ];

        let rewritten = rewrite_role_constraints_with_role_arg_inputs(
            &scheme,
            &constraints,
            &HashMap::new(),
            &|path| (path == &role).then_some(vec![true, false]),
        );

        assert_eq!(rewritten.len(), 1);
        let vars = role_constraint_vars(&rewritten[0]);
        assert!(vars.contains(&input));
        assert!(vars.contains(&assoc_a));
        assert!(vars.contains(&assoc_b));
    }

    fn role_path(name: &str) -> Path {
        Path {
            segments: vec![Name(name.to_string())],
        }
    }

    fn role_constraint(name: &str, args: Vec<CompactBounds>) -> CompactRoleConstraint {
        CompactRoleConstraint {
            role: role_path(name),
            args,
        }
    }

    fn var_bounds(tv: crate::ids::TypeVar) -> CompactBounds {
        CompactBounds::Interval {
            self_var: None,
            lower: CompactType {
                vars: HashSet::from([tv]),
                ..CompactType::default()
            },
            upper: CompactType {
                vars: HashSet::from([tv]),
                ..CompactType::default()
            },
        }
    }
}
