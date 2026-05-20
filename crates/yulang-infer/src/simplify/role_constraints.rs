use std::collections::HashSet;

use crate::ids::TypeVar;

use super::compact::{CompactBounds, CompactType, CompactTypeScheme, merge_compact_bounds};
use super::cooccur::CompactRoleConstraint;

pub(crate) fn rewrite_role_constraints(
    _scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    subst: &std::collections::HashMap<TypeVar, Option<TypeVar>>,
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
    let coalesced = coalesce_role_constraints(out);
    remove_empty_role_constraints(coalesced)
}

fn coalesce_role_constraints(
    constraints: Vec<CompactRoleConstraint>,
) -> Vec<CompactRoleConstraint> {
    let mut out = Vec::new();
    let mut visited = vec![false; constraints.len()];
    let var_sets = constraints
        .iter()
        .map(role_constraint_vars)
        .collect::<Vec<_>>();

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
                    &var_sets[current],
                    &var_sets[other],
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
        arg.self_var.is_none()
            && arg.lower == CompactType::default()
            && arg.upper == CompactType::default()
    })
}

fn can_coalesce_role_constraints(
    lhs: &CompactRoleConstraint,
    rhs: &CompactRoleConstraint,
    lhs_vars: &HashSet<TypeVar>,
    rhs_vars: &HashSet<TypeVar>,
) -> bool {
    lhs.role == rhs.role
        && lhs.args.len() == rhs.args.len()
        && (lhs == rhs || !lhs_vars.is_disjoint(rhs_vars))
}

fn merge_role_constraint_component(
    mut constraints: impl Iterator<Item = CompactRoleConstraint>,
) -> CompactRoleConstraint {
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

fn role_constraint_vars(constraint: &CompactRoleConstraint) -> HashSet<TypeVar> {
    let mut out = HashSet::new();
    for arg in &constraint.args {
        collect_compact_bounds_vars(arg, &mut out);
    }
    out
}

fn collect_compact_bounds_vars(bounds: &CompactBounds, out: &mut HashSet<TypeVar>) {
    if let Some(tv) = bounds.self_var {
        out.insert(tv);
    }
    collect_compact_type_vars(&bounds.lower, out);
    collect_compact_type_vars(&bounds.upper, out);
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
    use super::{rewrite_role_constraints, role_constraint_vars};
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
            cty: CompactBounds {
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
            cty: CompactBounds {
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

    fn role_constraint(name: &str, args: Vec<CompactBounds>) -> CompactRoleConstraint {
        CompactRoleConstraint {
            role: Path {
                segments: vec![Name(name.to_string())],
            },
            args,
        }
    }

    fn var_bounds(tv: crate::ids::TypeVar) -> CompactBounds {
        CompactBounds {
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
