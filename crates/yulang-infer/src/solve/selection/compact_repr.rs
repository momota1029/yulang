use crate::ids::{NegId, PosId, TypeVar};
use crate::lower::builtin_types::{
    join_primitive_type_paths, primitive_numeric_type_family, primitive_type_family,
};
use crate::simplify::compact::{CompactBounds, CompactType, compact_type_var, merge_compact_types};
use crate::symbols::Path;

use super::Infer;

pub(crate) fn concrete_tv_repr(
    infer: &Infer,
    tv: TypeVar,
    allow_boundary: bool,
) -> Option<CompactType> {
    let scheme = compact_type_var(infer, tv);
    concrete_bounds_repr(&scheme.cty, allow_boundary)
}

pub(super) fn concrete_tv_lower_repr(
    infer: &Infer,
    tv: TypeVar,
    allow_boundary: bool,
) -> Option<CompactType> {
    let scheme = compact_type_var(infer, tv);
    concrete_or_boundary_compact_type(scheme.cty.lower(), allow_boundary)
}

pub(super) fn concrete_tv_lower_join_repr(
    infer: &Infer,
    tvs: &[TypeVar],
    allow_boundary: bool,
) -> Option<CompactType> {
    let mut out = CompactType::default();
    for tv in tvs {
        let repr = concrete_tv_lower_repr(infer, *tv, allow_boundary)?;
        out = merge_compact_types(true, out, repr);
    }
    normalize_builtin_numeric_compact_type(&mut out);
    concrete_joined_lower_repr(out, allow_boundary)
}

pub(super) fn concrete_pos_repr(
    infer: &Infer,
    pos: PosId,
    allow_boundary: bool,
) -> Option<CompactType> {
    let ty = crate::simplify::compact::compact_pos_expr(infer, pos);
    concrete_or_boundary_compact_type(&ty, allow_boundary)
}

pub(super) fn concrete_neg_repr(
    infer: &Infer,
    neg: NegId,
    allow_boundary: bool,
) -> Option<CompactType> {
    let ty = crate::simplify::compact::compact_neg_expr(infer, neg);
    concrete_or_boundary_compact_type(&ty, allow_boundary)
}

pub(super) fn concrete_lower_bounds_repr(
    bounds: &CompactBounds,
    allow_boundary: bool,
) -> Option<CompactType> {
    let lower = compact_bounds_side(bounds, true);
    concrete_or_boundary_compact_type(&lower, allow_boundary)
}

pub(super) fn concrete_tv_upper_repr(
    infer: &Infer,
    tv: TypeVar,
    allow_boundary: bool,
) -> Option<CompactType> {
    let scheme = compact_type_var(infer, tv);
    concrete_or_boundary_compact_type(scheme.cty.upper(), allow_boundary)
}

pub(super) fn concrete_bounds_repr(
    bounds: &CompactBounds,
    allow_boundary: bool,
) -> Option<CompactType> {
    let CompactBounds::Interval { lower, upper, .. } = bounds else {
        let ty = compact_bounds_side(bounds, true);
        return concrete_or_boundary_compact_type(&ty, allow_boundary);
    };
    let lower_empty = lower == &CompactType::default();
    let upper_empty = upper == &CompactType::default();
    match (lower_empty, upper_empty) {
        (false, true) => concrete_or_boundary_compact_type(lower, allow_boundary),
        (true, false) => concrete_or_boundary_compact_type(upper, allow_boundary),
        (false, false) if lower == upper => {
            concrete_or_boundary_compact_type(lower, allow_boundary)
        }
        (false, false) if allow_boundary => boundary_join_concrete_bounds(lower, upper)
            .or_else(|| boundary_concrete_compact_type(lower))
            .or_else(|| boundary_concrete_compact_type(upper)),
        _ => None,
    }
}

fn compact_bounds_side(bounds: &CompactBounds, positive: bool) -> CompactType {
    match bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            if positive {
                lower.clone()
            } else {
                upper.clone()
            }
        }
        CompactBounds::Con { path, args } => CompactType {
            cons: vec![crate::simplify::compact::CompactCon {
                path: path.clone(),
                args: args.clone(),
            }],
            ..CompactType::default()
        },
        CompactBounds::Tuple { items } => CompactType {
            tuples: vec![
                items
                    .iter()
                    .map(|item| compact_bounds_side(item, positive))
                    .collect(),
            ],
            ..CompactType::default()
        },
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => CompactType {
            funs: vec![crate::simplify::compact::CompactFun {
                arg: compact_bounds_side(arg, positive),
                arg_eff: compact_bounds_side(arg_eff, positive),
                ret_eff: compact_bounds_side(ret_eff, positive),
                ret: compact_bounds_side(ret, positive),
            }],
            ..CompactType::default()
        },
    }
}

fn boundary_join_concrete_bounds(lower: &CompactType, upper: &CompactType) -> Option<CompactType> {
    let lower = boundary_concrete_compact_type(lower)?;
    let upper = boundary_concrete_compact_type(upper)?;
    if lower == upper {
        return Some(lower);
    }
    let lower_path = single_primitive_path(&lower)?;
    let upper_path = single_primitive_path(&upper)?;
    let joined_path = join_primitive_type_paths(lower_path, upper_path)?;
    let mut joined = CompactType::default();
    joined.cons.push(crate::simplify::compact::CompactCon {
        path: joined_path,
        args: Vec::new(),
    });
    Some(joined)
}

fn concrete_or_boundary_compact_type(
    ty: &CompactType,
    allow_boundary: bool,
) -> Option<CompactType> {
    if allow_boundary {
        boundary_concrete_compact_type(ty)
    } else if is_concrete_compact_type(ty, false) {
        Some(ty.clone())
    } else {
        None
    }
}

fn concrete_joined_lower_repr(ty: CompactType, allow_boundary: bool) -> Option<CompactType> {
    if ty == CompactType::default() {
        return None;
    }
    if allow_boundary {
        return boundary_concrete_compact_type(&ty);
    }
    is_concrete_compact_type(&ty, false).then_some(ty)
}

fn boundary_concrete_compact_type(ty: &CompactType) -> Option<CompactType> {
    if let Some(mut normalized) = normalize_boundary_compact_type(ty) {
        normalize_builtin_numeric_compact_type(&mut normalized);
        return Some(normalized);
    }
    let mut stripped = ty.clone();
    stripped.vars.clear();
    normalize_builtin_numeric_compact_type(&mut stripped);
    if stripped != CompactType::default() && is_concrete_compact_type(&stripped, true) {
        return Some(stripped);
    }

    let widened = normalize_boundary_compact_type(&stripped)?;
    (widened != CompactType::default() && is_concrete_compact_type(&widened, true))
        .then_some(widened)
}

fn normalize_boundary_compact_type(ty: &CompactType) -> Option<CompactType> {
    let mut normalized = ty.clone();
    normalized.vars.clear();
    for con in &mut normalized.cons {
        for arg in &mut con.args {
            *arg = boundary_lower_bounds(arg);
        }
    }
    (normalized != CompactType::default()).then_some(normalized)
}

fn boundary_lower_bounds(bounds: &CompactBounds) -> CompactBounds {
    if let Some(concrete) = concrete_lower_bounds_repr(bounds, true) {
        if concrete != CompactType::default() {
            return exact_compact_bounds(concrete);
        }
    }
    if let CompactBounds::Interval {
        self_var: None,
        lower,
        ..
    } = bounds
        && lower != &CompactType::default()
    {
        return exact_compact_bounds(lower.clone());
    }
    CompactBounds::default()
}

fn exact_compact_bounds(ty: CompactType) -> CompactBounds {
    CompactBounds::Interval {
        self_var: None,
        lower: ty.clone(),
        upper: ty,
    }
}

fn is_concrete_compact_type(ty: &CompactType, allow_boundary: bool) -> bool {
    ty.vars.is_empty()
        && ty.cons.iter().all(|con| {
            con.args.iter().all(|arg| {
                arg.self_var().is_none()
                    && (concrete_bounds_repr(arg, allow_boundary).is_some()
                        || (allow_boundary && *arg == CompactBounds::default()))
            })
        })
        && ty.funs.iter().all(|fun| {
            is_concrete_compact_type(&fun.arg, allow_boundary)
                && is_concrete_compact_type(&fun.arg_eff, allow_boundary)
                && is_concrete_compact_type(&fun.ret_eff, allow_boundary)
                && is_concrete_compact_type(&fun.ret, allow_boundary)
        })
        && ty.records.iter().all(|record| {
            record
                .fields
                .iter()
                .all(|field| is_concrete_compact_type(&field.value, allow_boundary))
        })
        && ty.record_spreads.iter().all(|record| {
            record
                .fields
                .iter()
                .all(|field| is_concrete_compact_type(&field.value, allow_boundary))
                && is_concrete_compact_type(&record.tail, allow_boundary)
        })
        && ty.variants.iter().all(|variant| {
            variant.items.iter().all(|(_, items)| {
                items
                    .iter()
                    .all(|item| is_concrete_compact_type(item, allow_boundary))
            })
        })
        && ty.tuples.iter().all(|items| {
            items
                .iter()
                .all(|item| is_concrete_compact_type(item, allow_boundary))
        })
        && ty.rows.iter().all(|row| {
            row.items
                .iter()
                .all(|item| is_concrete_compact_type(item, allow_boundary))
                && is_concrete_compact_type(&row.tail, allow_boundary)
        })
}

fn normalize_builtin_numeric_compact_type(ty: &mut CompactType) {
    normalize_named_compact_type_order(ty);
    for con in &mut ty.cons {
        for arg in &mut con.args {
            normalize_builtin_numeric_compact_type(arg.lower_mut());
            normalize_builtin_numeric_compact_type(arg.upper_mut());
        }
    }
    for fun in &mut ty.funs {
        normalize_builtin_numeric_compact_type(&mut fun.arg);
        normalize_builtin_numeric_compact_type(&mut fun.arg_eff);
        normalize_builtin_numeric_compact_type(&mut fun.ret_eff);
        normalize_builtin_numeric_compact_type(&mut fun.ret);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            normalize_builtin_numeric_compact_type(&mut field.value);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            normalize_builtin_numeric_compact_type(&mut field.value);
        }
        normalize_builtin_numeric_compact_type(&mut spread.tail);
    }
    for variant in &mut ty.variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                normalize_builtin_numeric_compact_type(payload);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in tuple {
            normalize_builtin_numeric_compact_type(item);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            normalize_builtin_numeric_compact_type(item);
        }
        normalize_builtin_numeric_compact_type(&mut row.tail);
    }
}

fn normalize_named_compact_type_order(ty: &mut CompactType) {
    let joined = ty
        .prims
        .iter()
        .cloned()
        .chain(
            ty.cons
                .iter()
                .filter(|con| con.args.is_empty())
                .map(|con| con.path.clone()),
        )
        .fold(Vec::<Path>::new(), |mut out, path| {
            if let Some(index) = out
                .iter()
                .position(|existing| join_local_named_paths(existing, &path).is_some())
            {
                let joined = join_local_named_paths(&out[index], &path).expect("checked above");
                out[index] = joined;
            } else {
                out.push(path);
            }
            out
        });

    ty.prims
        .retain(|path| joined.iter().any(|joined_path| joined_path == path));
    ty.cons.retain(|con| {
        !con.args.is_empty() || joined.iter().any(|joined_path| joined_path == &con.path)
    });
    for joined_path in joined {
        let exists_as_prim = ty.prims.iter().any(|path| path == &joined_path);
        let exists_as_con = ty
            .cons
            .iter()
            .any(|con| con.args.is_empty() && con.path == joined_path);
        if !exists_as_prim && !exists_as_con {
            ty.cons.push(crate::simplify::compact::CompactCon {
                path: joined_path,
                args: Vec::new(),
            });
        }
    }
}

fn join_local_named_paths(left: &Path, right: &Path) -> Option<Path> {
    if left == right {
        return Some(left.clone());
    }
    join_primitive_type_paths(left, right)
}

fn single_primitive_path(ty: &CompactType) -> Option<&Path> {
    if !ty.vars.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.variants.is_empty()
        || !ty.tuples.is_empty()
        || !ty.rows.is_empty()
    {
        return None;
    }
    let mut paths = ty.prims.iter().chain(
        ty.cons
            .iter()
            .filter(|con| con.args.is_empty())
            .map(|con| &con.path),
    );
    let path = paths.next()?;
    paths.next().is_none().then_some(path).filter(|path| {
        primitive_numeric_type_family(path).is_some() || primitive_type_family(path).is_some()
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simplify::compact::CompactCon;
    use crate::symbols::Name;

    #[test]
    fn joined_lower_repr_keeps_boundary_constructor_arguments() {
        let item = CompactType {
            vars: [TypeVar(1)].into_iter().collect(),
            ..CompactType::default()
        };
        let ref_lines = CompactType {
            cons: vec![CompactCon {
                path: Path {
                    segments: vec![
                        Name("std".to_string()),
                        Name("str".to_string()),
                        Name("ref_lines".to_string()),
                    ],
                },
                args: vec![exact_compact_bounds(item)],
            }],
            ..CompactType::default()
        };

        assert_eq!(
            concrete_joined_lower_repr(ref_lines.clone(), true),
            Some(ref_lines)
        );
    }
}
