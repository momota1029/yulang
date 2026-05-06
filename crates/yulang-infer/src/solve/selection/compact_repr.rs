use crate::ids::TypeVar;
use crate::simplify::compact::{CompactBounds, CompactType, compact_type_var};
use crate::symbols::{Name, Path};

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
    concrete_or_boundary_compact_type(&scheme.cty.lower, allow_boundary)
}

pub(super) fn concrete_tv_upper_repr(
    infer: &Infer,
    tv: TypeVar,
    allow_boundary: bool,
) -> Option<CompactType> {
    let scheme = compact_type_var(infer, tv);
    concrete_or_boundary_compact_type(&scheme.cty.upper, allow_boundary)
}

pub(super) fn concrete_bounds_repr(
    bounds: &CompactBounds,
    allow_boundary: bool,
) -> Option<CompactType> {
    let lower_empty = bounds.lower == CompactType::default();
    let upper_empty = bounds.upper == CompactType::default();
    match (lower_empty, upper_empty) {
        (false, true) => concrete_or_boundary_compact_type(&bounds.lower, allow_boundary),
        (true, false) => concrete_or_boundary_compact_type(&bounds.upper, allow_boundary),
        (false, false) if bounds.lower == bounds.upper => {
            concrete_or_boundary_compact_type(&bounds.lower, allow_boundary)
        }
        (false, false) if allow_boundary => boundary_concrete_compact_type(&bounds.lower)
            .or_else(|| boundary_concrete_compact_type(&bounds.upper)),
        _ => None,
    }
}

fn concrete_or_boundary_compact_type(
    ty: &CompactType,
    allow_boundary: bool,
) -> Option<CompactType> {
    if allow_boundary {
        boundary_concrete_compact_type(ty)
    } else if is_concrete_compact_type(ty) {
        Some(ty.clone())
    } else {
        None
    }
}

fn boundary_concrete_compact_type(ty: &CompactType) -> Option<CompactType> {
    if is_concrete_compact_type(ty) {
        let mut normalized = ty.clone();
        normalize_builtin_numeric_compact_type(&mut normalized);
        return Some(normalized);
    }
    let mut stripped = ty.clone();
    stripped.vars.clear();
    normalize_builtin_numeric_compact_type(&mut stripped);
    (stripped != CompactType::default() && is_concrete_compact_type(&stripped)).then_some(stripped)
}

fn is_concrete_compact_type(ty: &CompactType) -> bool {
    ty.vars.is_empty()
        && ty.cons.iter().all(|con| {
            con.args
                .iter()
                .all(|arg| arg.self_var.is_none() && concrete_bounds_repr(arg, false).is_some())
        })
        && ty.funs.iter().all(|fun| {
            is_concrete_compact_type(&fun.arg)
                && is_concrete_compact_type(&fun.arg_eff)
                && is_concrete_compact_type(&fun.ret_eff)
                && is_concrete_compact_type(&fun.ret)
        })
        && ty.records.iter().all(|record| {
            record
                .fields
                .iter()
                .all(|field| is_concrete_compact_type(&field.value))
        })
        && ty.record_spreads.iter().all(|record| {
            record
                .fields
                .iter()
                .all(|field| is_concrete_compact_type(&field.value))
                && is_concrete_compact_type(&record.tail)
        })
        && ty.variants.iter().all(|variant| {
            variant
                .items
                .iter()
                .all(|(_, items)| items.iter().all(is_concrete_compact_type))
        })
        && ty
            .tuples
            .iter()
            .all(|items| items.iter().all(is_concrete_compact_type))
        && ty.rows.iter().all(|row| {
            row.items.iter().all(is_concrete_compact_type) && is_concrete_compact_type(&row.tail)
        })
}

fn normalize_builtin_numeric_compact_type(ty: &mut CompactType) {
    normalize_named_compact_type_order(ty);
    for con in &mut ty.cons {
        for arg in &mut con.args {
            normalize_builtin_numeric_compact_type(&mut arg.lower);
            normalize_builtin_numeric_compact_type(&mut arg.upper);
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
    let left_leaf = left.segments.last()?.0.as_str();
    let right_leaf = right.segments.last()?.0.as_str();
    let joined = yulang_core_ir::join_named_leaves(left_leaf, right_leaf)?;
    if joined == left_leaf {
        return Some(left.clone());
    }
    if joined == right_leaf {
        return Some(right.clone());
    }
    Some(Path {
        segments: vec![Name(joined)],
    })
}
