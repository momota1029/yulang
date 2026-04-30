use crate::ids::{NegId, PosId};
use crate::symbols::Path;
use crate::types::RecordField;
use crate::types::{EffectAtom, Neg, Pos};

pub(crate) fn replace_effect_path_pos(
    infer: &crate::solve::Infer,
    pos: PosId,
    source_path: &Path,
    dest_path: &Path,
    dest_args: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
) -> PosId {
    match infer.arena.get_pos(pos) {
        Pos::Bot => infer.arena.bot,
        Pos::Var(tv) => infer.alloc_pos(Pos::Var(tv)),
        Pos::Atom(atom) => infer.alloc_pos(Pos::Atom(replace_effect_atom_path(
            atom,
            source_path,
            dest_path,
            dest_args,
        ))),
        Pos::Forall(vars, body) => infer.alloc_pos(Pos::Forall(
            vars,
            replace_effect_path_pos(infer, body, source_path, dest_path, dest_args),
        )),
        Pos::Con(path, args) => infer.alloc_pos(Pos::Con(
            replace_path_prefix(&path, source_path, dest_path),
            args.into_iter()
                .map(|(p, n)| {
                    (
                        replace_effect_path_pos(infer, p, source_path, dest_path, dest_args),
                        replace_effect_path_neg(infer, n, source_path, dest_path, dest_args),
                    )
                })
                .collect(),
        )),
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => infer.alloc_pos(Pos::Fun {
            arg: replace_effect_path_neg(infer, arg, source_path, dest_path, dest_args),
            arg_eff: replace_effect_path_neg(infer, arg_eff, source_path, dest_path, dest_args),
            ret_eff: replace_effect_path_pos(infer, ret_eff, source_path, dest_path, dest_args),
            ret: replace_effect_path_pos(infer, ret, source_path, dest_path, dest_args),
        }),
        Pos::Record(fields) => infer.alloc_pos(Pos::Record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: replace_effect_path_pos(
                        infer,
                        field.value,
                        source_path,
                        dest_path,
                        dest_args,
                    ),
                    optional: field.optional,
                })
                .collect(),
        )),
        Pos::RecordTailSpread { fields, tail } => infer.alloc_pos(Pos::RecordTailSpread {
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: replace_effect_path_pos(
                        infer,
                        field.value,
                        source_path,
                        dest_path,
                        dest_args,
                    ),
                    optional: field.optional,
                })
                .collect(),
            tail: replace_effect_path_pos(infer, tail, source_path, dest_path, dest_args),
        }),
        Pos::RecordHeadSpread { tail, fields } => infer.alloc_pos(Pos::RecordHeadSpread {
            tail: replace_effect_path_pos(infer, tail, source_path, dest_path, dest_args),
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: replace_effect_path_pos(
                        infer,
                        field.value,
                        source_path,
                        dest_path,
                        dest_args,
                    ),
                    optional: field.optional,
                })
                .collect(),
        }),
        Pos::PolyVariant(items) => infer.alloc_pos(Pos::PolyVariant(
            items
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| {
                                replace_effect_path_pos(
                                    infer,
                                    payload,
                                    source_path,
                                    dest_path,
                                    dest_args,
                                )
                            })
                            .collect(),
                    )
                })
                .collect(),
        )),
        Pos::Tuple(items) => infer.alloc_pos(Pos::Tuple(
            items
                .into_iter()
                .map(|item| replace_effect_path_pos(infer, item, source_path, dest_path, dest_args))
                .collect(),
        )),
        Pos::Row(items, tail) => infer.alloc_pos(Pos::Row(
            items
                .into_iter()
                .map(|item| replace_effect_path_pos(infer, item, source_path, dest_path, dest_args))
                .collect(),
            replace_effect_path_pos(infer, tail, source_path, dest_path, dest_args),
        )),
        Pos::Union(lhs, rhs) => infer.alloc_pos(Pos::Union(
            replace_effect_path_pos(infer, lhs, source_path, dest_path, dest_args),
            replace_effect_path_pos(infer, rhs, source_path, dest_path, dest_args),
        )),
        Pos::Raw(tv) => infer.alloc_pos(Pos::Raw(tv)),
    }
}

pub(crate) fn clone_replace_effect_path_pos_between_arenas(
    src: &crate::types::arena::TypeArena,
    dst: &crate::types::arena::TypeArena,
    pos: PosId,
    subst: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
    source_path: &Path,
    dest_path: &Path,
    dest_args: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
) -> PosId {
    match src.get_pos(pos) {
        Pos::Bot => dst.bot,
        Pos::Var(tv) => dst.alloc_pos(Pos::Var(super::lookup_small_subst(subst, tv))),
        Pos::Atom(atom) => dst.alloc_pos(Pos::Atom(replace_effect_atom_path_with_subst(
            atom,
            subst,
            source_path,
            dest_path,
            dest_args,
        ))),
        Pos::Forall(vars, body) => dst.alloc_pos(Pos::Forall(
            vars,
            clone_replace_effect_path_pos_between_arenas(
                src,
                dst,
                body,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
        )),
        Pos::Con(path, args) => dst.alloc_pos(Pos::Con(
            replace_path_prefix(&path, source_path, dest_path),
            args.into_iter()
                .map(|(p, n)| {
                    (
                        clone_replace_effect_path_pos_between_arenas(
                            src,
                            dst,
                            p,
                            subst,
                            source_path,
                            dest_path,
                            dest_args,
                        ),
                        clone_replace_effect_path_neg_between_arenas(
                            src,
                            dst,
                            n,
                            subst,
                            source_path,
                            dest_path,
                            dest_args,
                        ),
                    )
                })
                .collect(),
        )),
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => dst.alloc_pos(Pos::Fun {
            arg: clone_replace_effect_path_neg_between_arenas(
                src,
                dst,
                arg,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
            arg_eff: clone_replace_effect_path_neg_between_arenas(
                src,
                dst,
                arg_eff,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
            ret_eff: clone_replace_effect_path_pos_between_arenas(
                src,
                dst,
                ret_eff,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
            ret: clone_replace_effect_path_pos_between_arenas(
                src,
                dst,
                ret,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
        }),
        Pos::Record(fields) => dst.alloc_pos(Pos::Record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: clone_replace_effect_path_pos_between_arenas(
                        src,
                        dst,
                        field.value,
                        subst,
                        source_path,
                        dest_path,
                        dest_args,
                    ),
                    optional: field.optional,
                })
                .collect(),
        )),
        Pos::RecordTailSpread { fields, tail } => dst.alloc_pos(Pos::RecordTailSpread {
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: clone_replace_effect_path_pos_between_arenas(
                        src,
                        dst,
                        field.value,
                        subst,
                        source_path,
                        dest_path,
                        dest_args,
                    ),
                    optional: field.optional,
                })
                .collect(),
            tail: clone_replace_effect_path_pos_between_arenas(
                src,
                dst,
                tail,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
        }),
        Pos::RecordHeadSpread { tail, fields } => dst.alloc_pos(Pos::RecordHeadSpread {
            tail: clone_replace_effect_path_pos_between_arenas(
                src,
                dst,
                tail,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: clone_replace_effect_path_pos_between_arenas(
                        src,
                        dst,
                        field.value,
                        subst,
                        source_path,
                        dest_path,
                        dest_args,
                    ),
                    optional: field.optional,
                })
                .collect(),
        }),
        Pos::PolyVariant(items) => dst.alloc_pos(Pos::PolyVariant(
            items
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| {
                                clone_replace_effect_path_pos_between_arenas(
                                    src,
                                    dst,
                                    payload,
                                    subst,
                                    source_path,
                                    dest_path,
                                    dest_args,
                                )
                            })
                            .collect(),
                    )
                })
                .collect(),
        )),
        Pos::Tuple(items) => dst.alloc_pos(Pos::Tuple(
            items
                .into_iter()
                .map(|item| {
                    clone_replace_effect_path_pos_between_arenas(
                        src,
                        dst,
                        item,
                        subst,
                        source_path,
                        dest_path,
                        dest_args,
                    )
                })
                .collect(),
        )),
        Pos::Row(items, tail) => dst.alloc_pos(Pos::Row(
            items
                .into_iter()
                .map(|item| {
                    clone_replace_effect_path_pos_between_arenas(
                        src,
                        dst,
                        item,
                        subst,
                        source_path,
                        dest_path,
                        dest_args,
                    )
                })
                .collect(),
            clone_replace_effect_path_pos_between_arenas(
                src,
                dst,
                tail,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
        )),
        Pos::Union(lhs, rhs) => dst.alloc_pos(Pos::Union(
            clone_replace_effect_path_pos_between_arenas(
                src,
                dst,
                lhs,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
            clone_replace_effect_path_pos_between_arenas(
                src,
                dst,
                rhs,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
        )),
        Pos::Raw(tv) => dst.alloc_pos(Pos::Raw(super::lookup_small_subst(subst, tv))),
    }
}

fn clone_replace_effect_path_neg_between_arenas(
    src: &crate::types::arena::TypeArena,
    dst: &crate::types::arena::TypeArena,
    neg: NegId,
    subst: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
    source_path: &Path,
    dest_path: &Path,
    dest_args: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
) -> NegId {
    match src.get_neg(neg) {
        Neg::Top => dst.top,
        Neg::Var(tv) => dst.alloc_neg(Neg::Var(super::lookup_small_subst(subst, tv))),
        Neg::Atom(atom) => dst.alloc_neg(Neg::Atom(replace_effect_atom_path_with_subst(
            atom,
            subst,
            source_path,
            dest_path,
            dest_args,
        ))),
        Neg::Forall(vars, body) => dst.alloc_neg(Neg::Forall(
            vars,
            clone_replace_effect_path_neg_between_arenas(
                src,
                dst,
                body,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
        )),
        Neg::Con(path, args) => dst.alloc_neg(Neg::Con(
            replace_path_prefix(&path, source_path, dest_path),
            args.into_iter()
                .map(|(p, n)| {
                    (
                        clone_replace_effect_path_pos_between_arenas(
                            src,
                            dst,
                            p,
                            subst,
                            source_path,
                            dest_path,
                            dest_args,
                        ),
                        clone_replace_effect_path_neg_between_arenas(
                            src,
                            dst,
                            n,
                            subst,
                            source_path,
                            dest_path,
                            dest_args,
                        ),
                    )
                })
                .collect(),
        )),
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => dst.alloc_neg(Neg::Fun {
            arg: clone_replace_effect_path_pos_between_arenas(
                src,
                dst,
                arg,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
            arg_eff: clone_replace_effect_path_pos_between_arenas(
                src,
                dst,
                arg_eff,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
            ret_eff: clone_replace_effect_path_neg_between_arenas(
                src,
                dst,
                ret_eff,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
            ret: clone_replace_effect_path_neg_between_arenas(
                src,
                dst,
                ret,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
        }),
        Neg::Record(fields) => dst.alloc_neg(Neg::Record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: clone_replace_effect_path_neg_between_arenas(
                        src,
                        dst,
                        field.value,
                        subst,
                        source_path,
                        dest_path,
                        dest_args,
                    ),
                    optional: field.optional,
                })
                .collect(),
        )),
        Neg::PolyVariant(items) => dst.alloc_neg(Neg::PolyVariant(
            items
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| {
                                clone_replace_effect_path_neg_between_arenas(
                                    src,
                                    dst,
                                    payload,
                                    subst,
                                    source_path,
                                    dest_path,
                                    dest_args,
                                )
                            })
                            .collect(),
                    )
                })
                .collect(),
        )),
        Neg::Tuple(items) => dst.alloc_neg(Neg::Tuple(
            items
                .into_iter()
                .map(|item| {
                    clone_replace_effect_path_neg_between_arenas(
                        src,
                        dst,
                        item,
                        subst,
                        source_path,
                        dest_path,
                        dest_args,
                    )
                })
                .collect(),
        )),
        Neg::Row(items, tail) => dst.alloc_neg(Neg::Row(
            items
                .into_iter()
                .map(|item| {
                    clone_replace_effect_path_neg_between_arenas(
                        src,
                        dst,
                        item,
                        subst,
                        source_path,
                        dest_path,
                        dest_args,
                    )
                })
                .collect(),
            clone_replace_effect_path_neg_between_arenas(
                src,
                dst,
                tail,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
        )),
        Neg::Intersection(lhs, rhs) => dst.alloc_neg(Neg::Intersection(
            clone_replace_effect_path_neg_between_arenas(
                src,
                dst,
                lhs,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
            clone_replace_effect_path_neg_between_arenas(
                src,
                dst,
                rhs,
                subst,
                source_path,
                dest_path,
                dest_args,
            ),
        )),
    }
}

pub(crate) fn replace_effect_path_neg(
    infer: &crate::solve::Infer,
    neg: NegId,
    source_path: &Path,
    dest_path: &Path,
    dest_args: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
) -> NegId {
    match infer.arena.get_neg(neg) {
        Neg::Top => infer.arena.top,
        Neg::Var(tv) => infer.alloc_neg(Neg::Var(tv)),
        Neg::Atom(atom) => infer.alloc_neg(Neg::Atom(replace_effect_atom_path(
            atom,
            source_path,
            dest_path,
            dest_args,
        ))),
        Neg::Forall(vars, body) => infer.alloc_neg(Neg::Forall(
            vars,
            replace_effect_path_neg(infer, body, source_path, dest_path, dest_args),
        )),
        Neg::Con(path, args) => infer.alloc_neg(Neg::Con(
            replace_path_prefix(&path, source_path, dest_path),
            args.into_iter()
                .map(|(p, n)| {
                    (
                        replace_effect_path_pos(infer, p, source_path, dest_path, dest_args),
                        replace_effect_path_neg(infer, n, source_path, dest_path, dest_args),
                    )
                })
                .collect(),
        )),
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => infer.alloc_neg(Neg::Fun {
            arg: replace_effect_path_pos(infer, arg, source_path, dest_path, dest_args),
            arg_eff: replace_effect_path_pos(infer, arg_eff, source_path, dest_path, dest_args),
            ret_eff: replace_effect_path_neg(infer, ret_eff, source_path, dest_path, dest_args),
            ret: replace_effect_path_neg(infer, ret, source_path, dest_path, dest_args),
        }),
        Neg::Record(fields) => infer.alloc_neg(Neg::Record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: replace_effect_path_neg(
                        infer,
                        field.value,
                        source_path,
                        dest_path,
                        dest_args,
                    ),
                    optional: field.optional,
                })
                .collect(),
        )),
        Neg::PolyVariant(items) => infer.alloc_neg(Neg::PolyVariant(
            items
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| {
                                replace_effect_path_neg(
                                    infer,
                                    payload,
                                    source_path,
                                    dest_path,
                                    dest_args,
                                )
                            })
                            .collect(),
                    )
                })
                .collect(),
        )),
        Neg::Tuple(items) => infer.alloc_neg(Neg::Tuple(
            items
                .into_iter()
                .map(|item| replace_effect_path_neg(infer, item, source_path, dest_path, dest_args))
                .collect(),
        )),
        Neg::Row(items, tail) => infer.alloc_neg(Neg::Row(
            items
                .into_iter()
                .map(|item| replace_effect_path_neg(infer, item, source_path, dest_path, dest_args))
                .collect(),
            replace_effect_path_neg(infer, tail, source_path, dest_path, dest_args),
        )),
        Neg::Intersection(lhs, rhs) => infer.alloc_neg(Neg::Intersection(
            replace_effect_path_neg(infer, lhs, source_path, dest_path, dest_args),
            replace_effect_path_neg(infer, rhs, source_path, dest_path, dest_args),
        )),
    }
}

fn replace_path_prefix(path: &Path, source_path: &Path, dest_path: &Path) -> Path {
    if path.segments.starts_with(&source_path.segments) {
        let mut segments = dest_path.segments.clone();
        segments.extend_from_slice(&path.segments[source_path.segments.len()..]);
        Path { segments }
    } else if source_path.segments.len() == 1 {
        if let Some(index) = path
            .segments
            .iter()
            .position(|segment| segment == &source_path.segments[0])
        {
            let mut segments = dest_path.segments.clone();
            segments.extend_from_slice(&path.segments[index + 1..]);
            Path { segments }
        } else {
            path.clone()
        }
    } else {
        path.clone()
    }
}

fn replace_effect_atom_path(
    atom: EffectAtom,
    source_path: &Path,
    dest_path: &Path,
    dest_args: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
) -> EffectAtom {
    if atom.path == *source_path {
        EffectAtom {
            path: dest_path.clone(),
            args: dest_args.to_vec(),
        }
    } else {
        atom
    }
}

fn replace_effect_atom_path_with_subst(
    atom: EffectAtom,
    subst: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
    source_path: &Path,
    dest_path: &Path,
    dest_args: &[(crate::ids::TypeVar, crate::ids::TypeVar)],
) -> EffectAtom {
    if atom.path == *source_path {
        EffectAtom {
            path: dest_path.clone(),
            args: dest_args.to_vec(),
        }
    } else {
        EffectAtom {
            path: atom.path,
            args: atom
                .args
                .into_iter()
                .map(|(pos, neg)| {
                    (
                        super::lookup_small_subst(subst, pos),
                        super::lookup_small_subst(subst, neg),
                    )
                })
                .collect(),
        }
    }
}
