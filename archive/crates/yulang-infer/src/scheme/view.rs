use crate::ids::{NegId, PosId, TypeVar};
use crate::solve::Infer;
use crate::types::RecordField;
use crate::types::arena::TypeArena;
use crate::types::{EffectAtom, Neg, Pos};

use super::{FrozenScheme, SmallSubst};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchemeInstance {
    pub scheme: FrozenScheme,
    pub subst: SmallSubst,
    pub level: u32,
}

pub type OwnedSchemeInstance = SchemeInstance;

pub fn materialize_body(infer: &Infer, instance: &SchemeInstance) -> PosId {
    infer.alloc_pos(read_pos_with_subst(
        &instance.scheme.arena,
        infer,
        instance.scheme.body,
        instance.subst.as_slice(),
    ))
}

pub fn read_pos_with_subst(
    arena: &TypeArena,
    infer: &Infer,
    id: PosId,
    subst: &[(TypeVar, TypeVar)],
) -> Pos {
    match arena.get_pos(id) {
        Pos::Bot => Pos::Bot,
        Pos::Var(tv) => Pos::Var(subst_lookup(subst, tv)),
        Pos::Atom(atom) => Pos::Atom(read_atom_with_subst(atom, subst)),
        Pos::Forall(vars, body) => Pos::Forall(
            vars,
            infer.alloc_pos(read_pos_with_subst(arena, infer, body, subst)),
        ),
        Pos::Con(path, args) => Pos::Con(
            path,
            args.into_iter()
                .map(|(p, n)| {
                    (
                        infer.alloc_pos(read_pos_with_subst(arena, infer, p, subst)),
                        infer.alloc_neg(read_neg_with_subst(arena, infer, n, subst)),
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
            arg: infer.alloc_neg(read_neg_with_subst(arena, infer, arg, subst)),
            arg_eff: infer.alloc_neg(read_neg_with_subst(arena, infer, arg_eff, subst)),
            ret_eff: infer.alloc_pos(read_pos_with_subst(arena, infer, ret_eff, subst)),
            ret: infer.alloc_pos(read_pos_with_subst(arena, infer, ret, subst)),
        },
        Pos::Record(fields) => Pos::Record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: infer.alloc_pos(read_pos_with_subst(arena, infer, field.value, subst)),
                    optional: field.optional,
                })
                .collect(),
        ),
        Pos::RecordTailSpread { fields, tail } => Pos::RecordTailSpread {
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: infer.alloc_pos(read_pos_with_subst(arena, infer, field.value, subst)),
                    optional: field.optional,
                })
                .collect(),
            tail: infer.alloc_pos(read_pos_with_subst(arena, infer, tail, subst)),
        },
        Pos::RecordHeadSpread { tail, fields } => Pos::RecordHeadSpread {
            tail: infer.alloc_pos(read_pos_with_subst(arena, infer, tail, subst)),
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: infer.alloc_pos(read_pos_with_subst(arena, infer, field.value, subst)),
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
                            .map(|p| infer.alloc_pos(read_pos_with_subst(arena, infer, p, subst)))
                            .collect(),
                    )
                })
                .collect(),
        ),
        Pos::Tuple(items) => Pos::Tuple(
            items
                .into_iter()
                .map(|p| infer.alloc_pos(read_pos_with_subst(arena, infer, p, subst)))
                .collect(),
        ),
        Pos::Row(items, tail) => Pos::Row(
            items
                .into_iter()
                .map(|p| infer.alloc_pos(read_pos_with_subst(arena, infer, p, subst)))
                .collect(),
            infer.alloc_pos(read_pos_with_subst(arena, infer, tail, subst)),
        ),
        Pos::Union(lhs, rhs) => Pos::Union(
            infer.alloc_pos(read_pos_with_subst(arena, infer, lhs, subst)),
            infer.alloc_pos(read_pos_with_subst(arena, infer, rhs, subst)),
        ),
        Pos::Raw(tv) => Pos::Raw(subst_lookup(subst, tv)),
    }
}

pub fn read_neg_with_subst(
    arena: &TypeArena,
    infer: &Infer,
    id: NegId,
    subst: &[(TypeVar, TypeVar)],
) -> Neg {
    match arena.get_neg(id) {
        Neg::Top => Neg::Top,
        Neg::Var(tv) => Neg::Var(subst_lookup(subst, tv)),
        Neg::Atom(atom) => Neg::Atom(read_atom_with_subst(atom, subst)),
        Neg::Forall(vars, body) => Neg::Forall(
            vars,
            infer.alloc_neg(read_neg_with_subst(arena, infer, body, subst)),
        ),
        Neg::Con(path, args) => Neg::Con(
            path,
            args.into_iter()
                .map(|(p, n)| {
                    (
                        infer.alloc_pos(read_pos_with_subst(arena, infer, p, subst)),
                        infer.alloc_neg(read_neg_with_subst(arena, infer, n, subst)),
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
            arg: infer.alloc_pos(read_pos_with_subst(arena, infer, arg, subst)),
            arg_eff: infer.alloc_pos(read_pos_with_subst(arena, infer, arg_eff, subst)),
            ret_eff: infer.alloc_neg(read_neg_with_subst(arena, infer, ret_eff, subst)),
            ret: infer.alloc_neg(read_neg_with_subst(arena, infer, ret, subst)),
        },
        Neg::Record(fields) => Neg::Record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: infer.alloc_neg(read_neg_with_subst(arena, infer, field.value, subst)),
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
                            .map(|n| infer.alloc_neg(read_neg_with_subst(arena, infer, n, subst)))
                            .collect(),
                    )
                })
                .collect(),
        ),
        Neg::Tuple(items) => Neg::Tuple(
            items
                .into_iter()
                .map(|n| infer.alloc_neg(read_neg_with_subst(arena, infer, n, subst)))
                .collect(),
        ),
        Neg::Row(items, tail) => Neg::Row(
            items
                .into_iter()
                .map(|n| infer.alloc_neg(read_neg_with_subst(arena, infer, n, subst)))
                .collect(),
            infer.alloc_neg(read_neg_with_subst(arena, infer, tail, subst)),
        ),
        Neg::Intersection(lhs, rhs) => Neg::Intersection(
            infer.alloc_neg(read_neg_with_subst(arena, infer, lhs, subst)),
            infer.alloc_neg(read_neg_with_subst(arena, infer, rhs, subst)),
        ),
    }
}

fn read_atom_with_subst(atom: EffectAtom, subst: &[(TypeVar, TypeVar)]) -> EffectAtom {
    EffectAtom {
        path: atom.path,
        args: atom
            .args
            .into_iter()
            .map(|(pos, neg)| (subst_lookup(subst, pos), subst_lookup(subst, neg)))
            .collect(),
    }
}

fn subst_lookup(subst: &[(TypeVar, TypeVar)], tv: TypeVar) -> TypeVar {
    for (from, to) in subst {
        if *from == tv {
            return *to;
        }
    }
    tv
}
