use super::*;

pub(crate) fn collect_pattern_defs(
    arena: &poly_expr::Arena,
    pat: poly_expr::PatId,
    out: &mut Vec<poly_expr::DefId>,
) {
    match arena.pat(pat) {
        poly_expr::Pat::Wild | poly_expr::Pat::Lit(_) | poly_expr::Pat::Ref(_) => {}
        poly_expr::Pat::Var(def) => out.push(*def),
        poly_expr::Pat::As(inner, def) => {
            collect_pattern_defs(arena, *inner, out);
            out.push(*def);
        }
        poly_expr::Pat::Tuple(items)
        | poly_expr::Pat::PolyVariant(_, items)
        | poly_expr::Pat::Con(_, items) => {
            for item in items {
                collect_pattern_defs(arena, *item, out);
            }
        }
        poly_expr::Pat::Or(left, right) => {
            collect_pattern_defs(arena, *left, out);
            collect_pattern_defs(arena, *right, out);
        }
        poly_expr::Pat::List {
            prefix,
            spread,
            suffix,
        } => {
            for item in prefix.iter().chain(suffix) {
                collect_pattern_defs(arena, *item, out);
            }
            if let Some(spread) = spread {
                collect_pattern_defs(arena, *spread, out);
            }
        }
        poly_expr::Pat::Record { fields, spread } => {
            for field in fields {
                collect_pattern_defs(arena, field.pat, out);
            }
            match spread {
                poly_expr::RecordSpread::Head(def) | poly_expr::RecordSpread::Tail(def) => {
                    out.push(*def)
                }
                poly_expr::RecordSpread::None => {}
            }
        }
    }
}

pub(crate) fn exact_role_input_types(
    predicate: &types::InstantiatedRolePredicate,
) -> Option<Vec<Type>> {
    predicate.inputs.iter().map(exact_role_input_type).collect()
}

pub(crate) fn exact_role_input_type(input: &types::InstantiatedRoleArg) -> Option<Type> {
    if equivalent_boundary_types(&input.lower, &input.upper) {
        return Some(input.lower.clone());
    }
    if matches!(input.lower, Type::Never) && !matches!(input.upper, Type::Any) {
        return Some(input.upper.clone());
    }
    if matches!(input.upper, Type::Any) && !matches!(input.lower, Type::Never) {
        return Some(input.lower.clone());
    }
    None
}
