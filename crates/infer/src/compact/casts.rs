use rustc_hash::FxHashSet;

use crate::casts::CastTable;

use super::{CompactBounds, CompactCon, CompactRoot, CompactType, Polarity, merge_cons};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CompactCastBatch {
    pub(crate) key: CompactCastKey,
    pub(crate) applications: Vec<CompactCastApplication>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CompactCastApplication {
    pub(crate) key: CompactCastKey,
    pub(crate) source: CompactType,
    pub(crate) target: CompactType,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactCastKey {
    pub(crate) source: Vec<String>,
    pub(crate) source_arity: usize,
    pub(crate) target: Vec<String>,
    pub(crate) target_arity: usize,
}

pub(crate) fn find_next_compact_cast(
    root: &CompactRoot,
    casts: &CastTable,
    applied: &FxHashSet<CompactCastKey>,
) -> Option<CompactCastBatch> {
    let mut pairs = Vec::new();
    collect_cast_pairs_in_type(&root.root, &mut pairs);
    for rec in &root.rec_vars {
        collect_cast_pairs_in_bounds(&rec.bounds, &mut pairs);
    }

    let key = pairs.iter().find_map(|(key, _, _)| {
        if !applied.contains(key) && !casts.candidates(&key.source, &key.target).is_empty() {
            Some(key.clone())
        } else {
            None
        }
    })?;
    let applications = pairs
        .into_iter()
        .filter_map(|(candidate, source, target)| {
            if candidate == key {
                Some(CompactCastApplication {
                    key: key.clone(),
                    source: CompactType::from_con(source),
                    target: CompactType::from_con(target),
                })
            } else {
                None
            }
        })
        .collect::<Vec<_>>();

    Some(CompactCastBatch { key, applications })
}

pub(crate) fn normalize_compact_casts(root: &mut CompactRoot, applied: &FxHashSet<CompactCastKey>) {
    if applied.is_empty() {
        return;
    }
    normalize_type(&mut root.root, Polarity::Positive, applied);
    for rec in &mut root.rec_vars {
        normalize_bounds(&mut rec.bounds, applied);
    }
}

fn collect_cast_pairs_in_type(
    ty: &CompactType,
    out: &mut Vec<(CompactCastKey, CompactCon, CompactCon)>,
) {
    for (source_index, source) in ty.cons.iter().enumerate() {
        for (target_index, target) in ty.cons.iter().enumerate() {
            if source_index == target_index {
                continue;
            }
            out.push((cast_key(source, target), source.clone(), target.clone()));
        }
    }

    for con in &ty.cons {
        for arg in &con.args {
            collect_cast_pairs_in_bounds(arg, out);
        }
    }
    for fun in &ty.funs {
        collect_cast_pairs_in_type(&fun.arg, out);
        collect_cast_pairs_in_type(&fun.arg_eff, out);
        collect_cast_pairs_in_type(&fun.ret_eff, out);
        collect_cast_pairs_in_type(&fun.ret, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_cast_pairs_in_type(&field.value, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_cast_pairs_in_type(&field.value, out);
        }
        collect_cast_pairs_in_type(&spread.tail, out);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_cast_pairs_in_type(payload, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            collect_cast_pairs_in_type(item, out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_cast_pairs_in_type(item, out);
        }
        collect_cast_pairs_in_type(&row.tail, out);
    }
}

fn collect_cast_pairs_in_bounds(
    bounds: &CompactBounds,
    out: &mut Vec<(CompactCastKey, CompactCon, CompactCon)>,
) {
    match bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            collect_cast_pairs_in_type(lower, out);
            collect_cast_pairs_in_type(upper, out);
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                collect_cast_pairs_in_bounds(arg, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_cast_pairs_in_bounds(arg, out);
            collect_cast_pairs_in_bounds(arg_eff, out);
            collect_cast_pairs_in_bounds(ret_eff, out);
            collect_cast_pairs_in_bounds(ret, out);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                collect_cast_pairs_in_bounds(&field.value, out);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_cast_pairs_in_bounds(payload, out);
                }
            }
        }
    }
}

fn normalize_type(ty: &mut CompactType, polarity: Polarity, applied: &FxHashSet<CompactCastKey>) {
    for con in &mut ty.cons {
        for arg in &mut con.args {
            normalize_bounds(arg, applied);
        }
    }
    for fun in &mut ty.funs {
        normalize_type(&mut fun.arg, polarity.flipped(), applied);
        normalize_type(&mut fun.arg_eff, polarity.flipped(), applied);
        normalize_type(&mut fun.ret_eff, polarity, applied);
        normalize_type(&mut fun.ret, polarity, applied);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            normalize_type(&mut field.value, polarity, applied);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            normalize_type(&mut field.value, polarity, applied);
        }
        normalize_type(&mut spread.tail, polarity, applied);
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                normalize_type(payload, polarity, applied);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            normalize_type(item, polarity, applied);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            normalize_type(item, polarity, applied);
        }
        normalize_type(&mut row.tail, polarity, applied);
    }
    normalize_type_cons(ty, polarity, applied);
}

fn normalize_bounds(bounds: &mut CompactBounds, applied: &FxHashSet<CompactCastKey>) {
    match bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            normalize_type(lower, Polarity::Positive, applied);
            normalize_type(upper, Polarity::Negative, applied);
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                normalize_bounds(arg, applied);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            normalize_bounds(arg, applied);
            normalize_bounds(arg_eff, applied);
            normalize_bounds(ret_eff, applied);
            normalize_bounds(ret, applied);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                normalize_bounds(&mut field.value, applied);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    normalize_bounds(payload, applied);
                }
            }
        }
    }
}

fn normalize_type_cons(
    ty: &mut CompactType,
    polarity: Polarity,
    applied: &FxHashSet<CompactCastKey>,
) {
    if ty.cons.len() < 2 {
        return;
    }

    let targets = ty.cons.clone();
    let mut normalized = Vec::with_capacity(ty.cons.len());
    for source in std::mem::take(&mut ty.cons) {
        let replacement = targets
            .iter()
            .find(|target| applied.contains(&cast_key(&source, target)))
            .cloned();
        normalized.push(replacement.unwrap_or(source));
    }
    ty.cons = merge_cons(polarity.is_positive(), Vec::new(), normalized);
}

fn cast_key(source: &CompactCon, target: &CompactCon) -> CompactCastKey {
    CompactCastKey {
        source: source.path.clone(),
        source_arity: source.args.len(),
        target: target.path.clone(),
        target_arity: target.args.len(),
    }
}
