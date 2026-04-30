use crate::ids::{NegId, PosId};
use crate::lower::LowerState;
use crate::scheme::compact_scheme_from_pos_body_in_arena;
use crate::symbols::Path;
use crate::types::arena::TypeArena;
use crate::types::{Neg, Pos};
use rustc_hash::FxHashSet;

pub(crate) fn transform_copied_frozen_scheme(
    _state: &LowerState,
    source: &crate::scheme::FrozenScheme,
    subst: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
    source_path: &Path,
    dest_path: &Path,
    dest_args: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
) -> crate::scheme::FrozenScheme {
    let mut frozen_subst =
        source
            .quantified_sources
            .iter()
            .fold(subst.to_vec(), |mut out, (source_tv, frozen_tv)| {
                if let Some((idx, _)) = out
                    .iter()
                    .enumerate()
                    .find(|(_, (from, _))| *from == *source_tv)
                {
                    out[idx].0 = *frozen_tv;
                }
                out
            });
    for (from, to) in effect_path_frozen_subst(source, source_path, dest_args) {
        if let Some(existing) = frozen_subst.iter_mut().find(|(tv, _)| *tv == from) {
            existing.1 = to;
        } else {
            frozen_subst.push((from, to));
        }
    }
    let fixed_tvs = dest_args
        .iter()
        .flat_map(|(pos, neg)| [*pos, *neg])
        .collect::<std::collections::HashSet<_>>();
    let fixed_frozen_tvs = frozen_subst
        .iter()
        .filter_map(|(from, to)| fixed_tvs.contains(to).then_some(*from))
        .collect::<std::collections::HashSet<_>>();
    let mut quantified_sources = source
        .quantified_sources
        .iter()
        .map(|(source_tv, frozen_tv)| {
            (
                super::super::lookup_small_subst(subst, *source_tv),
                *frozen_tv,
            )
        })
        .filter(|(tv, frozen_tv)| !fixed_tvs.contains(tv) && !fixed_frozen_tvs.contains(frozen_tv))
        .collect::<crate::scheme::SmallSubst>();
    quantified_sources.sort_by_key(|(tv, _)| tv.0);
    quantified_sources.dedup();
    let quantified = source
        .quantified
        .iter()
        .copied()
        .filter(|tv| !fixed_frozen_tvs.contains(tv))
        .filter(|tv| {
            quantified_sources
                .iter()
                .any(|(_, frozen_tv)| *frozen_tv == *tv)
        })
        .collect::<Vec<_>>();
    let through = source
        .through
        .iter()
        .copied()
        .filter(|tv| quantified.contains(tv))
        .collect();
    let arena = std::rc::Rc::new(TypeArena::new());
    let frozen_body = super::super::clone_replace_effect_path_pos_between_arenas(
        &source.arena,
        &arena,
        source.body,
        frozen_subst.as_slice(),
        source_path,
        dest_path,
        dest_args,
    );
    std::rc::Rc::new(crate::scheme::Scheme {
        arena: arena.clone(),
        compact: compact_scheme_from_pos_body_in_arena(&arena, frozen_body),
        body: frozen_body,
        quantified,
        quantified_sources,
        through,
    })
}

fn effect_path_frozen_subst(
    source: &crate::scheme::FrozenScheme,
    source_path: &Path,
    dest_args: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
) -> Vec<(crate::ids::TypeVar, crate::ids::TypeVar)> {
    let mut out = Vec::new();
    let mut seen_pos = FxHashSet::default();
    let mut seen_neg = FxHashSet::default();

    visit_pos(
        &source.arena,
        &mut out,
        &mut seen_pos,
        &mut seen_neg,
        source.body,
        source_path,
        dest_args,
    );
    out.sort_by_key(|(from, _)| from.0);
    out.dedup();
    out
}

fn visit_pos(
    arena: &TypeArena,
    out: &mut Vec<(crate::ids::TypeVar, crate::ids::TypeVar)>,
    seen_pos: &mut FxHashSet<PosId>,
    seen_neg: &mut FxHashSet<NegId>,
    id: PosId,
    source_path: &Path,
    dest_args: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
) {
    if !seen_pos.insert(id) {
        return;
    }
    match arena.get_pos(id) {
        Pos::Atom(atom) => {
            if atom.path == *source_path {
                for ((pos, neg), (dst_pos, dst_neg)) in atom.args.iter().zip(dest_args.iter()) {
                    out.push((*pos, *dst_pos));
                    out.push((*neg, *dst_neg));
                }
            }
        }
        Pos::Forall(_, body) => {
            visit_pos(arena, out, seen_pos, seen_neg, body, source_path, dest_args)
        }
        Pos::Con(_, args) => {
            for (p, n) in args {
                visit_pos(arena, out, seen_pos, seen_neg, p, source_path, dest_args);
                visit_neg(arena, out, seen_pos, seen_neg, n, source_path, dest_args);
            }
        }
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            visit_neg(arena, out, seen_pos, seen_neg, arg, source_path, dest_args);
            visit_neg(
                arena,
                out,
                seen_pos,
                seen_neg,
                arg_eff,
                source_path,
                dest_args,
            );
            visit_pos(
                arena,
                out,
                seen_pos,
                seen_neg,
                ret_eff,
                source_path,
                dest_args,
            );
            visit_pos(arena, out, seen_pos, seen_neg, ret, source_path, dest_args);
        }
        Pos::Record(fields) => {
            for field in fields {
                visit_pos(
                    arena,
                    out,
                    seen_pos,
                    seen_neg,
                    field.value,
                    source_path,
                    dest_args,
                );
            }
        }
        Pos::RecordTailSpread { fields, tail } => {
            for field in fields {
                visit_pos(
                    arena,
                    out,
                    seen_pos,
                    seen_neg,
                    field.value,
                    source_path,
                    dest_args,
                );
            }
            visit_pos(arena, out, seen_pos, seen_neg, tail, source_path, dest_args);
        }
        Pos::RecordHeadSpread { tail, fields } => {
            visit_pos(arena, out, seen_pos, seen_neg, tail, source_path, dest_args);
            for field in fields {
                visit_pos(
                    arena,
                    out,
                    seen_pos,
                    seen_neg,
                    field.value,
                    source_path,
                    dest_args,
                );
            }
        }
        Pos::PolyVariant(items) => {
            for (_, items) in items {
                for item in items {
                    visit_pos(arena, out, seen_pos, seen_neg, item, source_path, dest_args);
                }
            }
        }
        Pos::Tuple(items) | Pos::Row(items, _) => {
            for item in items {
                visit_pos(arena, out, seen_pos, seen_neg, item, source_path, dest_args);
            }
            if let Pos::Row(_, tail) = arena.get_pos(id) {
                visit_pos(arena, out, seen_pos, seen_neg, tail, source_path, dest_args);
            }
        }
        Pos::Union(lhs, rhs) => {
            visit_pos(arena, out, seen_pos, seen_neg, lhs, source_path, dest_args);
            visit_pos(arena, out, seen_pos, seen_neg, rhs, source_path, dest_args);
        }
        Pos::Bot | Pos::Var(_) | Pos::Raw(_) => {}
    }
}

fn visit_neg(
    arena: &TypeArena,
    out: &mut Vec<(crate::ids::TypeVar, crate::ids::TypeVar)>,
    seen_pos: &mut FxHashSet<PosId>,
    seen_neg: &mut FxHashSet<NegId>,
    id: NegId,
    source_path: &Path,
    dest_args: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
) {
    if !seen_neg.insert(id) {
        return;
    }
    match arena.get_neg(id) {
        Neg::Atom(atom) => {
            if atom.path == *source_path {
                for ((pos, neg), (dst_pos, dst_neg)) in atom.args.iter().zip(dest_args.iter()) {
                    out.push((*pos, *dst_pos));
                    out.push((*neg, *dst_neg));
                }
            }
        }
        Neg::Forall(_, body) => {
            visit_neg(arena, out, seen_pos, seen_neg, body, source_path, dest_args)
        }
        Neg::Con(_, args) => {
            for (p, n) in args {
                visit_pos(arena, out, seen_pos, seen_neg, p, source_path, dest_args);
                visit_neg(arena, out, seen_pos, seen_neg, n, source_path, dest_args);
            }
        }
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            visit_pos(arena, out, seen_pos, seen_neg, arg, source_path, dest_args);
            visit_pos(
                arena,
                out,
                seen_pos,
                seen_neg,
                arg_eff,
                source_path,
                dest_args,
            );
            visit_neg(
                arena,
                out,
                seen_pos,
                seen_neg,
                ret_eff,
                source_path,
                dest_args,
            );
            visit_neg(arena, out, seen_pos, seen_neg, ret, source_path, dest_args);
        }
        Neg::Record(fields) => {
            for field in fields {
                visit_neg(
                    arena,
                    out,
                    seen_pos,
                    seen_neg,
                    field.value,
                    source_path,
                    dest_args,
                );
            }
        }
        Neg::PolyVariant(items) => {
            for (_, items) in items {
                for item in items {
                    visit_neg(arena, out, seen_pos, seen_neg, item, source_path, dest_args);
                }
            }
        }
        Neg::Tuple(items) | Neg::Row(items, _) => {
            for item in items {
                visit_neg(arena, out, seen_pos, seen_neg, item, source_path, dest_args);
            }
            if let Neg::Row(_, tail) = arena.get_neg(id) {
                visit_neg(arena, out, seen_pos, seen_neg, tail, source_path, dest_args);
            }
        }
        Neg::Intersection(lhs, rhs) => {
            visit_neg(arena, out, seen_pos, seen_neg, lhs, source_path, dest_args);
            visit_neg(arena, out, seen_pos, seen_neg, rhs, source_path, dest_args);
        }
        Neg::Top | Neg::Var(_) => {}
    }
}
