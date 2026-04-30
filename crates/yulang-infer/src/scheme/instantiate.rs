use std::collections::HashMap;
use std::time::Duration;

use crate::profile::ProfileClock as Instant;

use crate::ids::{NegId, PosId, TypeVar, fresh_type_var};
use crate::solve::Infer;
use crate::types::RecordField;
use crate::types::{EffectAtom, Neg, Pos};

use super::view::{SchemeInstance, materialize_body};
use super::{FrozenScheme, SmallSubst};

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct InstantiateFrozenProfile {
    pub build_subst: Duration,
    pub subst_body: Duration,
}

pub fn instantiate_frozen_scheme(infer: &Infer, scheme: &FrozenScheme, target: TypeVar) {
    let _ = instantiate_frozen_scheme_with_subst(infer, scheme, target, &[]);
}

pub fn instantiate_frozen_scheme_with_subst(
    infer: &Infer,
    scheme: &FrozenScheme,
    target: TypeVar,
    preset: &[(TypeVar, TypeVar)],
) -> SmallSubst {
    instantiate_frozen_scheme_with_subst_profiled(infer, scheme, target, preset).0
}

pub fn instantiate_frozen_scheme_with_subst_profiled(
    infer: &Infer,
    scheme: &FrozenScheme,
    target: TypeVar,
    preset: &[(TypeVar, TypeVar)],
) -> (SmallSubst, InstantiateFrozenProfile) {
    let (instance, profile) =
        instantiate_as_view_with_subst_profiled(infer, scheme, infer.level_of(target), preset);
    let subst = instance.subst.clone();
    infer.constrain_instantiated_ref_instance(instance, target);
    (subst, profile)
}

pub fn instantiate_frozen_body(infer: &Infer, scheme: &FrozenScheme, level: u32) -> PosId {
    let mut subst = SmallSubst::with_capacity(scheme.quantified.len());
    for quantified in &scheme.quantified {
        let fresh = fresh_type_var();
        infer.register_level(fresh, level);
        if scheme.through.contains(quantified) {
            infer.mark_through(fresh);
        }
        subst.push((*quantified, fresh));
    }
    let instance = SchemeInstance {
        scheme: scheme.clone(),
        subst,
        level,
    };
    materialize_body(infer, &instance)
}

pub fn instantiate_frozen_body_with_subst(
    infer: &Infer,
    scheme: &FrozenScheme,
    level: u32,
    preset: &[(TypeVar, TypeVar)],
) -> (PosId, SmallSubst) {
    instantiate_frozen_body_with_subst_profiled(infer, scheme, level, preset).0
}

pub fn instantiate_frozen_body_with_subst_profiled(
    infer: &Infer,
    scheme: &FrozenScheme,
    level: u32,
    preset: &[(TypeVar, TypeVar)],
) -> ((PosId, SmallSubst), InstantiateFrozenProfile) {
    let mut profile = InstantiateFrozenProfile::default();
    let build_subst_start = Instant::now();
    let mut subst = SmallSubst::with_capacity(preset.len() + scheme.quantified.len());
    subst.extend(preset.iter().copied());
    for quantified in &scheme.quantified {
        if let Some(mapped) = subst_lookup_small_opt(subst.as_slice(), *quantified) {
            if scheme.through.contains(quantified) {
                infer.mark_through(mapped);
            }
            continue;
        }
        let fresh = fresh_type_var();
        infer.register_level(fresh, level);
        if scheme.through.contains(quantified) {
            infer.mark_through(fresh);
        }
        subst.push((*quantified, fresh));
    }
    profile.build_subst += build_subst_start.elapsed();

    let subst_body_start = Instant::now();
    let body = materialize_body(
        infer,
        &SchemeInstance {
            scheme: scheme.clone(),
            subst: subst.clone(),
            level,
        },
    );
    profile.subst_body += subst_body_start.elapsed();
    ((body, subst), profile)
}

pub fn instantiate_as_view(infer: &Infer, scheme: &FrozenScheme, level: u32) -> SchemeInstance {
    instantiate_as_view_with_subst(infer, scheme, level, &[])
}

pub fn instantiate_as_view_with_subst(
    infer: &Infer,
    scheme: &FrozenScheme,
    level: u32,
    preset: &[(TypeVar, TypeVar)],
) -> SchemeInstance {
    instantiate_as_view_with_subst_profiled(infer, scheme, level, preset).0
}

pub fn instantiate_as_view_with_subst_profiled(
    infer: &Infer,
    scheme: &FrozenScheme,
    level: u32,
    preset: &[(TypeVar, TypeVar)],
) -> (SchemeInstance, InstantiateFrozenProfile) {
    let mut subst = SmallSubst::with_capacity(scheme.quantified.len());
    let mut profile = InstantiateFrozenProfile::default();
    let build_subst_start = Instant::now();
    subst.extend(preset.iter().copied());
    for quantified in &scheme.quantified {
        if let Some(mapped) = subst_lookup_small_opt(subst.as_slice(), *quantified) {
            if scheme.through.contains(quantified) {
                infer.mark_through(mapped);
            }
            continue;
        }
        let fresh = fresh_type_var();
        infer.register_level(fresh, level);
        if scheme.through.contains(quantified) {
            infer.mark_through(fresh);
        }
        subst.push((*quantified, fresh));
    }
    profile.build_subst += build_subst_start.elapsed();
    (
        SchemeInstance {
            scheme: scheme.clone(),
            subst,
            level,
        },
        profile,
    )
}

pub(crate) fn subst_pos_id(infer: &Infer, id: PosId, subst: &[(TypeVar, TypeVar)]) -> PosId {
    let node = infer.arena.get_pos(id);
    infer.arena.alloc_pos(subst_pos_node(infer, node, subst))
}

pub(crate) fn subst_neg_id(infer: &Infer, id: NegId, subst: &[(TypeVar, TypeVar)]) -> NegId {
    let node = infer.arena.get_neg(id);
    infer.arena.alloc_neg(subst_neg_node(infer, node, subst))
}

pub(crate) fn subst_pos_id_map(
    infer: &Infer,
    id: PosId,
    subst: &HashMap<TypeVar, TypeVar>,
) -> PosId {
    let node = infer.arena.get_pos(id);
    infer
        .arena
        .alloc_pos(subst_pos_node_map(infer, node, subst))
}

pub(crate) fn subst_neg_id_map(
    infer: &Infer,
    id: NegId,
    subst: &HashMap<TypeVar, TypeVar>,
) -> NegId {
    let node = infer.arena.get_neg(id);
    infer
        .arena
        .alloc_neg(subst_neg_node_map(infer, node, subst))
}

fn subst_pos_node(infer: &Infer, pos: Pos, subst: &[(TypeVar, TypeVar)]) -> Pos {
    match pos {
        Pos::Bot => Pos::Bot,
        Pos::Var(tv) => Pos::Var(subst_lookup_small(subst, tv)),
        Pos::Atom(atom) => Pos::Atom(subst_atom_small(atom, subst)),
        Pos::Forall(vars, body) => Pos::Forall(vars, subst_pos_id(infer, body, subst)),
        Pos::Con(path, args) => Pos::Con(
            path,
            args.into_iter()
                .map(|(p, n)| (subst_pos_id(infer, p, subst), subst_neg_id(infer, n, subst)))
                .collect(),
        ),
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => Pos::Fun {
            arg: subst_neg_id(infer, arg, subst),
            arg_eff: subst_neg_id(infer, arg_eff, subst),
            ret_eff: subst_pos_id(infer, ret_eff, subst),
            ret: subst_pos_id(infer, ret, subst),
        },
        Pos::Record(fields) => Pos::Record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: subst_pos_id(infer, field.value, subst),
                    optional: field.optional,
                })
                .collect(),
        ),
        Pos::RecordTailSpread { fields, tail } => Pos::RecordTailSpread {
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: subst_pos_id(infer, field.value, subst),
                    optional: field.optional,
                })
                .collect(),
            tail: subst_pos_id(infer, tail, subst),
        },
        Pos::RecordHeadSpread { tail, fields } => Pos::RecordHeadSpread {
            tail: subst_pos_id(infer, tail, subst),
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: subst_pos_id(infer, field.value, subst),
                    optional: field.optional,
                })
                .collect(),
        },
        Pos::PolyVariant(items) => Pos::PolyVariant(
            items
                .into_iter()
                .map(|(name, ps)| {
                    (
                        name,
                        ps.into_iter()
                            .map(|p| subst_pos_id(infer, p, subst))
                            .collect(),
                    )
                })
                .collect(),
        ),
        Pos::Tuple(items) => Pos::Tuple(
            items
                .into_iter()
                .map(|p| subst_pos_id(infer, p, subst))
                .collect(),
        ),
        Pos::Row(items, tail) => Pos::Row(
            items
                .into_iter()
                .map(|p| subst_pos_id(infer, p, subst))
                .collect(),
            subst_pos_id(infer, tail, subst),
        ),
        Pos::Union(lhs, rhs) => Pos::Union(
            subst_pos_id(infer, lhs, subst),
            subst_pos_id(infer, rhs, subst),
        ),
        Pos::Raw(tv) => Pos::Raw(subst_lookup_small(subst, tv)),
    }
}

fn subst_neg_node(infer: &Infer, neg: Neg, subst: &[(TypeVar, TypeVar)]) -> Neg {
    match neg {
        Neg::Top => Neg::Top,
        Neg::Var(tv) => Neg::Var(subst_lookup_small(subst, tv)),
        Neg::Atom(atom) => Neg::Atom(subst_atom_small(atom, subst)),
        Neg::Forall(vars, body) => Neg::Forall(vars, subst_neg_id(infer, body, subst)),
        Neg::Con(path, args) => Neg::Con(
            path,
            args.into_iter()
                .map(|(p, n)| (subst_pos_id(infer, p, subst), subst_neg_id(infer, n, subst)))
                .collect(),
        ),
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => Neg::Fun {
            arg: subst_pos_id(infer, arg, subst),
            arg_eff: subst_pos_id(infer, arg_eff, subst),
            ret_eff: subst_neg_id(infer, ret_eff, subst),
            ret: subst_neg_id(infer, ret, subst),
        },
        Neg::Record(fields) => Neg::Record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: subst_neg_id(infer, field.value, subst),
                    optional: field.optional,
                })
                .collect(),
        ),
        Neg::PolyVariant(items) => Neg::PolyVariant(
            items
                .into_iter()
                .map(|(name, ns)| {
                    (
                        name,
                        ns.into_iter()
                            .map(|n| subst_neg_id(infer, n, subst))
                            .collect(),
                    )
                })
                .collect(),
        ),
        Neg::Tuple(items) => Neg::Tuple(
            items
                .into_iter()
                .map(|n| subst_neg_id(infer, n, subst))
                .collect(),
        ),
        Neg::Row(items, tail) => Neg::Row(
            items
                .into_iter()
                .map(|n| subst_neg_id(infer, n, subst))
                .collect(),
            subst_neg_id(infer, tail, subst),
        ),
        Neg::Intersection(lhs, rhs) => Neg::Intersection(
            subst_neg_id(infer, lhs, subst),
            subst_neg_id(infer, rhs, subst),
        ),
    }
}

fn subst_pos_node_map(infer: &Infer, pos: Pos, subst: &HashMap<TypeVar, TypeVar>) -> Pos {
    match pos {
        Pos::Bot => Pos::Bot,
        Pos::Var(tv) => Pos::Var(subst.get(&tv).copied().unwrap_or(tv)),
        Pos::Atom(atom) => Pos::Atom(subst_atom(atom, subst)),
        Pos::Forall(vars, body) => Pos::Forall(vars, subst_pos_id_map(infer, body, subst)),
        Pos::Con(path, args) => Pos::Con(
            path,
            args.into_iter()
                .map(|(p, n)| {
                    (
                        subst_pos_id_map(infer, p, subst),
                        subst_neg_id_map(infer, n, subst),
                    )
                })
                .collect(),
        ),
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => Pos::Fun {
            arg: subst_neg_id_map(infer, arg, subst),
            arg_eff: subst_neg_id_map(infer, arg_eff, subst),
            ret_eff: subst_pos_id_map(infer, ret_eff, subst),
            ret: subst_pos_id_map(infer, ret, subst),
        },
        Pos::Record(fields) => Pos::Record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: subst_pos_id_map(infer, field.value, subst),
                    optional: field.optional,
                })
                .collect(),
        ),
        Pos::RecordTailSpread { fields, tail } => Pos::RecordTailSpread {
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: subst_pos_id_map(infer, field.value, subst),
                    optional: field.optional,
                })
                .collect(),
            tail: subst_pos_id_map(infer, tail, subst),
        },
        Pos::RecordHeadSpread { tail, fields } => Pos::RecordHeadSpread {
            tail: subst_pos_id_map(infer, tail, subst),
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: subst_pos_id_map(infer, field.value, subst),
                    optional: field.optional,
                })
                .collect(),
        },
        Pos::PolyVariant(items) => Pos::PolyVariant(
            items
                .into_iter()
                .map(|(name, ps)| {
                    (
                        name,
                        ps.into_iter()
                            .map(|p| subst_pos_id_map(infer, p, subst))
                            .collect(),
                    )
                })
                .collect(),
        ),
        Pos::Tuple(items) => Pos::Tuple(
            items
                .into_iter()
                .map(|p| subst_pos_id_map(infer, p, subst))
                .collect(),
        ),
        Pos::Row(items, tail) => Pos::Row(
            items
                .into_iter()
                .map(|p| subst_pos_id_map(infer, p, subst))
                .collect(),
            subst_pos_id_map(infer, tail, subst),
        ),
        Pos::Union(lhs, rhs) => Pos::Union(
            subst_pos_id_map(infer, lhs, subst),
            subst_pos_id_map(infer, rhs, subst),
        ),
        Pos::Raw(tv) => Pos::Raw(subst.get(&tv).copied().unwrap_or(tv)),
    }
}

fn subst_neg_node_map(infer: &Infer, neg: Neg, subst: &HashMap<TypeVar, TypeVar>) -> Neg {
    match neg {
        Neg::Top => Neg::Top,
        Neg::Var(tv) => Neg::Var(subst.get(&tv).copied().unwrap_or(tv)),
        Neg::Atom(atom) => Neg::Atom(subst_atom(atom, subst)),
        Neg::Forall(vars, body) => Neg::Forall(vars, subst_neg_id_map(infer, body, subst)),
        Neg::Con(path, args) => Neg::Con(
            path,
            args.into_iter()
                .map(|(p, n)| {
                    (
                        subst_pos_id_map(infer, p, subst),
                        subst_neg_id_map(infer, n, subst),
                    )
                })
                .collect(),
        ),
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => Neg::Fun {
            arg: subst_pos_id_map(infer, arg, subst),
            arg_eff: subst_pos_id_map(infer, arg_eff, subst),
            ret_eff: subst_neg_id_map(infer, ret_eff, subst),
            ret: subst_neg_id_map(infer, ret, subst),
        },
        Neg::Record(fields) => Neg::Record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: subst_neg_id_map(infer, field.value, subst),
                    optional: field.optional,
                })
                .collect(),
        ),
        Neg::PolyVariant(items) => Neg::PolyVariant(
            items
                .into_iter()
                .map(|(name, ns)| {
                    (
                        name,
                        ns.into_iter()
                            .map(|n| subst_neg_id_map(infer, n, subst))
                            .collect(),
                    )
                })
                .collect(),
        ),
        Neg::Tuple(items) => Neg::Tuple(
            items
                .into_iter()
                .map(|n| subst_neg_id_map(infer, n, subst))
                .collect(),
        ),
        Neg::Row(items, tail) => Neg::Row(
            items
                .into_iter()
                .map(|n| subst_neg_id_map(infer, n, subst))
                .collect(),
            subst_neg_id_map(infer, tail, subst),
        ),
        Neg::Intersection(lhs, rhs) => Neg::Intersection(
            subst_neg_id_map(infer, lhs, subst),
            subst_neg_id_map(infer, rhs, subst),
        ),
    }
}

fn subst_atom_small(atom: EffectAtom, subst: &[(TypeVar, TypeVar)]) -> EffectAtom {
    EffectAtom {
        path: atom.path,
        args: atom
            .args
            .into_iter()
            .map(|(pos, neg)| {
                (
                    subst_lookup_small(subst, pos),
                    subst_lookup_small(subst, neg),
                )
            })
            .collect(),
    }
}

fn subst_atom(atom: EffectAtom, subst: &HashMap<TypeVar, TypeVar>) -> EffectAtom {
    EffectAtom {
        path: atom.path,
        args: atom
            .args
            .into_iter()
            .map(|(pos, neg)| {
                (
                    subst.get(&pos).copied().unwrap_or(pos),
                    subst.get(&neg).copied().unwrap_or(neg),
                )
            })
            .collect(),
    }
}

fn subst_lookup_small(subst: &[(TypeVar, TypeVar)], tv: TypeVar) -> TypeVar {
    match subst {
        [] => tv,
        [(from, to)] => {
            if *from == tv {
                *to
            } else {
                tv
            }
        }
        [(from0, to0), (from1, to1)] => {
            if *from0 == tv {
                *to0
            } else if *from1 == tv {
                *to1
            } else {
                tv
            }
        }
        [(from0, to0), (from1, to1), (from2, to2)] => {
            if *from0 == tv {
                *to0
            } else if *from1 == tv {
                *to1
            } else if *from2 == tv {
                *to2
            } else {
                tv
            }
        }
        _ => {
            for (from, to) in subst {
                if *from == tv {
                    return *to;
                }
            }
            tv
        }
    }
}

fn subst_lookup_small_opt(subst: &[(TypeVar, TypeVar)], tv: TypeVar) -> Option<TypeVar> {
    let mapped = subst_lookup_small(subst, tv);
    (mapped != tv).then_some(mapped)
}
