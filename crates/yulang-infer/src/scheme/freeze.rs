use std::collections::HashSet;
use std::rc::Rc;

use crate::ids::{NegId, PosId, TypeVar, fresh_frozen_type_var};
use crate::simplify::compact::{
    CompactBounds, CompactCon, CompactFun, CompactRecord, CompactRecordSpread, CompactRow,
    CompactType, CompactTypeScheme, CompactVariant,
    coalesce_nested_tail_function_effect_residuals_in_scheme, compact_root_fun_body_lower,
    compact_type_var, merge_compact_types, normalize_compact_scheme_rows, subst_compact_bounds,
    subst_lookup_small,
};
use crate::simplify::cooccur::CompactRoleConstraint;
use crate::simplify::cooccur::coalesce_by_co_occurrence_with_role_constraint_inputs_and_boundary_vars;
use crate::solve::{EffectSubtractability, Infer};
use crate::symbols::Path;
use crate::types::RecordField;
use crate::types::arena::TypeArena;
use crate::types::{EffectAtom, Neg, Pos};

use super::{FrozenArena, FrozenScheme, Scheme, SmallSubst};

pub fn freeze_type_var(infer: &Infer, root: TypeVar) -> FrozenScheme {
    freeze_type_var_with_non_generic(infer, root, &HashSet::new())
}

pub fn freeze_pos_scheme(infer: &Infer, body: PosId) -> FrozenScheme {
    freeze_pos_scheme_with_non_generic(infer, body, &HashSet::new())
}

pub fn freeze_type_var_with_non_generic(
    infer: &Infer,
    root: TypeVar,
    non_generic_roots: &HashSet<TypeVar>,
) -> FrozenScheme {
    let compact = compact_type_var(infer, root);
    let scheme = coalesce_compact_scheme_for_freeze(infer, compact, non_generic_roots);
    freeze_compact_scheme_owned_with_non_generic(infer, scheme, non_generic_roots)
}

fn coalesce_compact_scheme_for_freeze(
    infer: &Infer,
    mut compact: CompactTypeScheme,
    non_generic_roots: &HashSet<TypeVar>,
) -> CompactTypeScheme {
    let exposed_boundary_vars =
        coalesce_nested_tail_function_effect_residuals_in_scheme(&mut compact);
    let mut boundary = collect_non_generic_vars(infer, non_generic_roots);
    boundary.extend(exposed_boundary_vars);
    let (mut scheme, _) = coalesce_by_co_occurrence_with_role_constraint_inputs_and_boundary_vars(
        &compact,
        &[],
        |_| None,
        &boundary,
    );
    normalize_compact_scheme_rows(&mut scheme);
    scheme
}

pub fn freeze_pos_scheme_with_non_generic(
    infer: &Infer,
    body: PosId,
    non_generic_roots: &HashSet<TypeVar>,
) -> FrozenScheme {
    let compact = compact_scheme_from_pos_body(infer, body);
    freeze_live_pos_body_with_non_generic(infer, &infer.arena, body, compact, non_generic_roots)
}

pub fn freeze_compact_scheme_with_non_generic(
    infer: &Infer,
    scheme: &CompactTypeScheme,
    non_generic_roots: &HashSet<TypeVar>,
) -> FrozenScheme {
    freeze_compact_scheme_owned_with_non_generic_and_extra_vars(
        infer,
        scheme.clone(),
        &[],
        non_generic_roots,
    )
}

pub(crate) fn freeze_compact_scheme_owned_with_non_generic(
    infer: &Infer,
    scheme: CompactTypeScheme,
    non_generic_roots: &HashSet<TypeVar>,
) -> FrozenScheme {
    freeze_compact_scheme_owned_with_non_generic_and_extra_vars(
        infer,
        scheme,
        &[],
        non_generic_roots,
    )
}

pub(crate) fn freeze_compact_scheme_with_non_generic_and_extra_vars(
    infer: &Infer,
    scheme: &CompactTypeScheme,
    extra_quantified: &[TypeVar],
    non_generic_roots: &HashSet<TypeVar>,
) -> FrozenScheme {
    freeze_compact_scheme_owned_with_non_generic_and_extra_vars(
        infer,
        scheme.clone(),
        extra_quantified,
        non_generic_roots,
    )
}

pub(crate) fn freeze_compact_scheme_owned_with_non_generic_and_extra_vars(
    infer: &Infer,
    scheme: CompactTypeScheme,
    extra_quantified: &[TypeVar],
    non_generic_roots: &HashSet<TypeVar>,
) -> FrozenScheme {
    let mut quantified = collect_compact_root_body_free_vars(&scheme);
    quantified.extend_from_slice(extra_quantified);
    let quantification = prepare_freeze_quantification(infer, quantified, non_generic_roots);
    let mut compact = if quantification.quantified_sources.is_empty() {
        scheme
    } else {
        subst_compact_scheme_vars(scheme, quantification.quantified_sources.as_slice())
    };
    normalize_compact_scheme_rows(&mut compact);
    let scheme_arena: FrozenArena = Rc::new(TypeArena::new());
    let body = compact_root_fun_pos_body(&scheme_arena, &compact)
        .unwrap_or_else(|| compact_pos_type(&scheme_arena, &compact.cty.lower, &compact, false));
    finish_frozen_scheme(scheme_arena, compact, body, quantification)
}

pub(crate) fn collect_compact_role_constraint_free_vars(
    constraints: &[CompactRoleConstraint],
) -> Vec<TypeVar> {
    let mut out = Vec::new();
    for constraint in constraints {
        for arg in &constraint.args {
            collect_compact_bounds_free_vars(arg, &mut out);
        }
    }
    out
}

fn freeze_live_pos_body_with_non_generic(
    infer: &Infer,
    src_arena: &TypeArena,
    body: PosId,
    compact: CompactTypeScheme,
    non_generic_roots: &HashSet<TypeVar>,
) -> FrozenScheme {
    let quantification = prepare_freeze_quantification(
        infer,
        collect_pos_free_vars_in_arena(src_arena, body),
        non_generic_roots,
    );
    let scheme_arena: FrozenArena = Rc::new(TypeArena::new());
    let frozen_body = clone_pos_between_arenas_with_subst(
        src_arena,
        &scheme_arena,
        body,
        quantification.quantified_sources.as_slice(),
    );
    let mut compact = if quantification.quantified_sources.is_empty() {
        compact
    } else {
        subst_compact_scheme_vars(compact, quantification.quantified_sources.as_slice())
    };
    normalize_compact_scheme_rows(&mut compact);
    finish_frozen_scheme(scheme_arena, compact, frozen_body, quantification)
}

pub fn compact_scheme_from_pos_body(infer: &Infer, body: PosId) -> CompactTypeScheme {
    compact_scheme_from_pos_body_in_arena(&infer.arena, body)
}

pub fn compact_scheme_from_pos_body_in_arena(arena: &TypeArena, body: PosId) -> CompactTypeScheme {
    CompactTypeScheme {
        cty: CompactBounds {
            self_var: None,
            lower: compact_pos_expr_in_arena(arena, body),
            upper: CompactType::default(),
        },
        rec_vars: std::collections::HashMap::new(),
    }
}

struct FreezeQuantification {
    quantified: Vec<TypeVar>,
    quantified_sources: SmallSubst,
    through: HashSet<TypeVar>,
    eff_binds: Vec<(TypeVar, Vec<EffectAtom>)>,
    effect_subtractabilities: Vec<(TypeVar, EffectSubtractability)>,
}

fn prepare_freeze_quantification(
    infer: &Infer,
    mut quantified: Vec<TypeVar>,
    non_generic_roots: &HashSet<TypeVar>,
) -> FreezeQuantification {
    if !non_generic_roots.is_empty() {
        let non_generic = collect_non_generic_vars(infer, non_generic_roots);
        quantified.retain(|tv| !non_generic.contains(tv));
    }
    quantified.sort_by_key(|tv| tv.0);
    quantified.dedup();

    let quantified_sources = quantified
        .iter()
        .copied()
        .map(|tv| (tv, fresh_frozen_type_var()))
        .collect::<SmallSubst>();
    let through = quantified_sources
        .iter()
        .filter_map(|(source, frozen)| infer.is_through(*source).then_some(*frozen))
        .collect();
    let eff_binds: Vec<(TypeVar, Vec<EffectAtom>)> = quantified_sources
        .iter()
        .filter_map(|(source, frozen)| {
            let handled = infer.eff_binds_of(*source);
            if handled.is_empty() {
                None
            } else {
                Some((
                    *frozen,
                    handled
                        .into_iter()
                        .map(|atom| subst_effect_atom_vars(atom, quantified_sources.as_slice()))
                        .collect(),
                ))
            }
        })
        .collect();
    let effect_subtractabilities = quantified_sources
        .iter()
        .filter_map(|(source, frozen)| {
            infer
                .effect_subtractability(*source)
                .map(|subtractability| (*frozen, subtractability))
        })
        .collect();
    let quantified = quantified_sources
        .iter()
        .map(|(_, frozen)| *frozen)
        .collect();
    FreezeQuantification {
        quantified,
        quantified_sources,
        through,
        eff_binds,
        effect_subtractabilities,
    }
}

fn finish_frozen_scheme(
    arena: FrozenArena,
    compact: CompactTypeScheme,
    body: PosId,
    quantification: FreezeQuantification,
) -> FrozenScheme {
    Rc::new(Scheme {
        arena,
        compact,
        body,
        quantified: quantification.quantified,
        quantified_sources: quantification.quantified_sources,
        through: quantification.through,
        eff_binds: quantification.eff_binds,
        effect_subtractabilities: quantification.effect_subtractabilities,
    })
}

fn subst_effect_atom_vars(atom: EffectAtom, subst: &[(TypeVar, TypeVar)]) -> EffectAtom {
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

fn compact_pos_expr_in_arena(arena: &TypeArena, id: PosId) -> CompactType {
    match arena.get_pos(id) {
        Pos::Bot => CompactType::default(),
        Pos::Var(tv) | Pos::Raw(tv) => compact_type_from_var(tv),
        Pos::Atom(atom) => compact_effect_atom(atom),
        Pos::Forall(_, body) => compact_pos_expr_in_arena(arena, body),
        Pos::Con(path, args) => compact_type_from_con(
            path,
            args.into_iter()
                .map(|(p, n)| CompactBounds {
                    self_var: None,
                    lower: compact_pos_expr_in_arena(arena, p),
                    upper: compact_neg_expr_in_arena(arena, n),
                })
                .collect(),
        ),
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => compact_type_from_fun(CompactFun {
            arg: compact_neg_expr_in_arena(arena, arg),
            arg_eff: compact_neg_expr_in_arena(arena, arg_eff),
            ret_eff: compact_pos_expr_in_arena(arena, ret_eff),
            ret: compact_pos_expr_in_arena(arena, ret),
        }),
        Pos::Record(fields) => compact_type_from_record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: compact_pos_expr_in_arena(arena, field.value),
                    optional: field.optional,
                })
                .collect(),
        ),
        Pos::RecordTailSpread { fields, tail } => compact_type_from_record_spread(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: compact_pos_expr_in_arena(arena, field.value),
                    optional: field.optional,
                })
                .collect(),
            compact_pos_expr_in_arena(arena, tail),
            true,
        ),
        Pos::RecordHeadSpread { tail, fields } => compact_type_from_record_spread(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: compact_pos_expr_in_arena(arena, field.value),
                    optional: field.optional,
                })
                .collect(),
            compact_pos_expr_in_arena(arena, tail),
            false,
        ),
        Pos::PolyVariant(items) => compact_type_from_variant(
            items
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| compact_pos_expr_in_arena(arena, payload))
                            .collect(),
                    )
                })
                .collect(),
        ),
        Pos::Tuple(items) => compact_type_from_tuple(
            items
                .into_iter()
                .map(|item| compact_pos_expr_in_arena(arena, item))
                .collect(),
        ),
        Pos::Row(items, tail) => compact_type_from_row(
            items
                .into_iter()
                .map(|item| compact_pos_expr_in_arena(arena, item))
                .collect(),
            compact_pos_expr_in_arena(arena, tail),
        ),
        Pos::Union(lhs, rhs) => merge_compact_types(
            true,
            compact_pos_expr_in_arena(arena, lhs),
            compact_pos_expr_in_arena(arena, rhs),
        ),
    }
}

fn compact_neg_expr_in_arena(arena: &TypeArena, id: NegId) -> CompactType {
    match arena.get_neg(id) {
        Neg::Top => CompactType::default(),
        Neg::Var(tv) => compact_type_from_var(tv),
        Neg::Atom(atom) => compact_effect_atom(atom),
        Neg::Forall(_, body) => compact_neg_expr_in_arena(arena, body),
        Neg::Con(path, args) => compact_type_from_con(
            path,
            args.into_iter()
                .map(|(p, n)| CompactBounds {
                    self_var: None,
                    lower: compact_pos_expr_in_arena(arena, p),
                    upper: compact_neg_expr_in_arena(arena, n),
                })
                .collect(),
        ),
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => compact_type_from_fun(CompactFun {
            arg: compact_pos_expr_in_arena(arena, arg),
            arg_eff: compact_pos_expr_in_arena(arena, arg_eff),
            ret_eff: compact_neg_expr_in_arena(arena, ret_eff),
            ret: compact_neg_expr_in_arena(arena, ret),
        }),
        Neg::Record(fields) => compact_type_from_record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: compact_neg_expr_in_arena(arena, field.value),
                    optional: field.optional,
                })
                .collect(),
        ),
        Neg::PolyVariant(items) => compact_type_from_variant(
            items
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| compact_neg_expr_in_arena(arena, payload))
                            .collect(),
                    )
                })
                .collect(),
        ),
        Neg::Tuple(items) => compact_type_from_tuple(
            items
                .into_iter()
                .map(|item| compact_neg_expr_in_arena(arena, item))
                .collect(),
        ),
        Neg::Row(items, tail) => compact_type_from_row(
            items
                .into_iter()
                .map(|item| compact_neg_expr_in_arena(arena, item))
                .collect(),
            compact_neg_expr_in_arena(arena, tail),
        ),
        Neg::Intersection(lhs, rhs) => merge_compact_types(
            false,
            compact_neg_expr_in_arena(arena, lhs),
            compact_neg_expr_in_arena(arena, rhs),
        ),
    }
}

fn compact_effect_atom(atom: EffectAtom) -> CompactType {
    if atom.args.is_empty() {
        compact_type_from_prim(atom.path)
    } else {
        compact_type_from_con(
            atom.path,
            atom.args
                .into_iter()
                .map(|(pos_tv, neg_tv)| CompactBounds {
                    self_var: None,
                    lower: compact_type_from_var(pos_tv),
                    upper: compact_type_from_var(neg_tv),
                })
                .collect(),
        )
    }
}

fn compact_type_from_var(tv: TypeVar) -> CompactType {
    let mut vars = std::collections::HashSet::new();
    vars.insert(tv);
    CompactType {
        vars,
        ..CompactType::default()
    }
}

fn compact_type_from_prim(path: Path) -> CompactType {
    let mut prims = std::collections::HashSet::new();
    prims.insert(path);
    CompactType {
        prims,
        ..CompactType::default()
    }
}

fn compact_type_from_con(path: Path, args: Vec<CompactBounds>) -> CompactType {
    CompactType {
        cons: vec![CompactCon { path, args }],
        ..CompactType::default()
    }
}

fn compact_type_from_fun(fun: CompactFun) -> CompactType {
    CompactType {
        funs: vec![fun],
        ..CompactType::default()
    }
}

fn compact_type_from_record(fields: Vec<RecordField<CompactType>>) -> CompactType {
    CompactType {
        records: vec![CompactRecord { fields }],
        ..CompactType::default()
    }
}

fn compact_type_from_record_spread(
    fields: Vec<RecordField<CompactType>>,
    tail: CompactType,
    tail_wins: bool,
) -> CompactType {
    CompactType {
        record_spreads: vec![CompactRecordSpread {
            fields,
            tail: Box::new(tail),
            tail_wins,
        }],
        ..CompactType::default()
    }
}

fn compact_type_from_variant(items: Vec<(crate::symbols::Name, Vec<CompactType>)>) -> CompactType {
    CompactType {
        variants: vec![CompactVariant { items }],
        ..CompactType::default()
    }
}

fn compact_type_from_tuple(items: Vec<CompactType>) -> CompactType {
    CompactType {
        tuples: vec![items],
        ..CompactType::default()
    }
}

fn compact_type_from_row(items: Vec<CompactType>, tail: CompactType) -> CompactType {
    CompactType {
        rows: vec![CompactRow {
            items,
            tail: Box::new(tail),
        }],
        ..CompactType::default()
    }
}

fn subst_compact_scheme_vars(
    mut scheme: CompactTypeScheme,
    subst: &[(TypeVar, TypeVar)],
) -> CompactTypeScheme {
    scheme.cty = subst_compact_bounds(&scheme.cty, subst);
    scheme.rec_vars = scheme
        .rec_vars
        .into_iter()
        .map(|(tv, bounds)| {
            (
                subst_lookup_small(subst, tv),
                subst_compact_bounds(&bounds, subst),
            )
        })
        .collect();
    scheme
}

pub fn clone_pos_between_arenas(src: &TypeArena, dst: &TypeArena, id: PosId) -> PosId {
    clone_pos_between_arenas_with_subst(src, dst, id, &[])
}

pub fn clone_neg_between_arenas(src: &TypeArena, dst: &TypeArena, id: NegId) -> NegId {
    clone_neg_between_arenas_with_subst(src, dst, id, &[])
}

fn clone_pos_between_arenas_with_subst(
    src: &TypeArena,
    dst: &TypeArena,
    id: PosId,
    subst: &[(TypeVar, TypeVar)],
) -> PosId {
    let pos = src.get_pos(id);
    dst.alloc_pos(clone_pos_node_between_arenas(src, dst, pos, subst))
}

fn clone_neg_between_arenas_with_subst(
    src: &TypeArena,
    dst: &TypeArena,
    id: NegId,
    subst: &[(TypeVar, TypeVar)],
) -> NegId {
    let neg = src.get_neg(id);
    dst.alloc_neg(clone_neg_node_between_arenas(src, dst, neg, subst))
}

fn clone_pos_node_between_arenas(
    src: &TypeArena,
    dst: &TypeArena,
    pos: Pos,
    subst: &[(TypeVar, TypeVar)],
) -> Pos {
    match pos {
        Pos::Bot => Pos::Bot,
        Pos::Var(tv) => Pos::Var(subst_lookup_small(subst, tv)),
        Pos::Atom(atom) => Pos::Atom(subst_effect_atom(atom, subst)),
        Pos::Forall(vars, body) => Pos::Forall(
            vars.into_iter()
                .map(|tv| subst_lookup_small(subst, tv))
                .collect(),
            clone_pos_between_arenas_with_subst(src, dst, body, subst),
        ),
        Pos::Con(path, args) => Pos::Con(
            path,
            args.into_iter()
                .map(|(p, n)| {
                    (
                        clone_pos_between_arenas_with_subst(src, dst, p, subst),
                        clone_neg_between_arenas_with_subst(src, dst, n, subst),
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
            arg: clone_neg_between_arenas_with_subst(src, dst, arg, subst),
            arg_eff: clone_neg_between_arenas_with_subst(src, dst, arg_eff, subst),
            ret_eff: clone_pos_between_arenas_with_subst(src, dst, ret_eff, subst),
            ret: clone_pos_between_arenas_with_subst(src, dst, ret, subst),
        },
        Pos::Record(fields) => Pos::Record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: clone_pos_between_arenas_with_subst(src, dst, field.value, subst),
                    optional: field.optional,
                })
                .collect(),
        ),
        Pos::RecordTailSpread { fields, tail } => Pos::RecordTailSpread {
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: clone_pos_between_arenas_with_subst(src, dst, field.value, subst),
                    optional: field.optional,
                })
                .collect(),
            tail: clone_pos_between_arenas_with_subst(src, dst, tail, subst),
        },
        Pos::RecordHeadSpread { tail, fields } => Pos::RecordHeadSpread {
            tail: clone_pos_between_arenas_with_subst(src, dst, tail, subst),
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: clone_pos_between_arenas_with_subst(src, dst, field.value, subst),
                    optional: field.optional,
                })
                .collect(),
        },
        Pos::PolyVariant(items) => Pos::PolyVariant(
            items
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| {
                                clone_pos_between_arenas_with_subst(src, dst, payload, subst)
                            })
                            .collect(),
                    )
                })
                .collect(),
        ),
        Pos::Tuple(items) => Pos::Tuple(
            items
                .into_iter()
                .map(|item| clone_pos_between_arenas_with_subst(src, dst, item, subst))
                .collect(),
        ),
        Pos::Row(items, tail) => Pos::Row(
            items
                .into_iter()
                .map(|item| clone_pos_between_arenas_with_subst(src, dst, item, subst))
                .collect(),
            clone_pos_between_arenas_with_subst(src, dst, tail, subst),
        ),
        Pos::Union(lhs, rhs) => Pos::Union(
            clone_pos_between_arenas_with_subst(src, dst, lhs, subst),
            clone_pos_between_arenas_with_subst(src, dst, rhs, subst),
        ),
        Pos::Raw(tv) => Pos::Raw(subst_lookup_small(subst, tv)),
    }
}

fn clone_neg_node_between_arenas(
    src: &TypeArena,
    dst: &TypeArena,
    neg: Neg,
    subst: &[(TypeVar, TypeVar)],
) -> Neg {
    match neg {
        Neg::Top => Neg::Top,
        Neg::Var(tv) => Neg::Var(subst_lookup_small(subst, tv)),
        Neg::Atom(atom) => Neg::Atom(subst_effect_atom(atom, subst)),
        Neg::Forall(vars, body) => Neg::Forall(
            vars.into_iter()
                .map(|tv| subst_lookup_small(subst, tv))
                .collect(),
            clone_neg_between_arenas_with_subst(src, dst, body, subst),
        ),
        Neg::Con(path, args) => Neg::Con(
            path,
            args.into_iter()
                .map(|(p, n)| {
                    (
                        clone_pos_between_arenas_with_subst(src, dst, p, subst),
                        clone_neg_between_arenas_with_subst(src, dst, n, subst),
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
            arg: clone_pos_between_arenas_with_subst(src, dst, arg, subst),
            arg_eff: clone_pos_between_arenas_with_subst(src, dst, arg_eff, subst),
            ret_eff: clone_neg_between_arenas_with_subst(src, dst, ret_eff, subst),
            ret: clone_neg_between_arenas_with_subst(src, dst, ret, subst),
        },
        Neg::Record(fields) => Neg::Record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: clone_neg_between_arenas_with_subst(src, dst, field.value, subst),
                    optional: field.optional,
                })
                .collect(),
        ),
        Neg::PolyVariant(items) => Neg::PolyVariant(
            items
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| {
                                clone_neg_between_arenas_with_subst(src, dst, payload, subst)
                            })
                            .collect(),
                    )
                })
                .collect(),
        ),
        Neg::Tuple(items) => Neg::Tuple(
            items
                .into_iter()
                .map(|item| clone_neg_between_arenas_with_subst(src, dst, item, subst))
                .collect(),
        ),
        Neg::Row(items, tail) => Neg::Row(
            items
                .into_iter()
                .map(|item| clone_neg_between_arenas_with_subst(src, dst, item, subst))
                .collect(),
            clone_neg_between_arenas_with_subst(src, dst, tail, subst),
        ),
        Neg::Intersection(lhs, rhs) => Neg::Intersection(
            clone_neg_between_arenas_with_subst(src, dst, lhs, subst),
            clone_neg_between_arenas_with_subst(src, dst, rhs, subst),
        ),
    }
}

fn subst_effect_atom(atom: EffectAtom, subst: &[(TypeVar, TypeVar)]) -> EffectAtom {
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

pub(crate) fn collect_non_generic_vars(
    infer: &Infer,
    roots: &HashSet<TypeVar>,
) -> HashSet<TypeVar> {
    let mut out = HashSet::new();
    for root in roots {
        out.insert(*root);
        let scheme = compact_type_var(infer, *root);
        let mut free = Vec::new();
        collect_compact_type_free_vars(&scheme.cty.lower, &mut free);
        collect_compact_type_free_vars(&scheme.cty.upper, &mut free);
        for bounds in scheme.rec_vars.values() {
            collect_compact_bounds_free_vars(bounds, &mut free);
        }
        out.extend(free);
    }
    out
}

fn compact_root_fun_pos_body(arena: &TypeArena, scheme: &CompactTypeScheme) -> Option<PosId> {
    let body = compact_root_fun_body_lower(scheme)?;
    let [fun] = body.funs.as_slice() else {
        return None;
    };

    Some(arena.alloc_pos(Pos::Fun {
        arg: compact_neg_type(arena, &fun.arg, scheme, false),
        arg_eff: compact_neg_type(arena, &fun.arg_eff, scheme, false),
        ret_eff: compact_pos_type(arena, &fun.ret_eff, scheme, false),
        ret: compact_pos_type(arena, &fun.ret, scheme, false),
    }))
}

fn compact_con_as_effect_atom(con: &CompactCon) -> Option<EffectAtom> {
    let args = con
        .args
        .iter()
        .map(|arg| {
            Some((
                single_compact_var(&arg.lower)?,
                single_compact_var(&arg.upper)?,
            ))
        })
        .collect::<Option<Vec<_>>>()?;
    Some(EffectAtom {
        path: con.path.clone(),
        args,
    })
}

fn collect_compact_root_body_free_vars(scheme: &CompactTypeScheme) -> Vec<TypeVar> {
    let mut out = Vec::new();
    if let Some(body) = compact_root_fun_body_lower(scheme) {
        collect_compact_type_free_vars(&body, &mut out);
    } else {
        collect_compact_type_free_vars(&scheme.cty.lower, &mut out);
    }
    // Root upper evidence is installed as a use-site upper constraint, not
    // folded into the positive body.  Quantify variables that occur inside
    // upper constructors so that this delayed evidence is freshened too.
    collect_compact_root_upper_child_free_vars(&scheme.cty.upper, &mut out);
    out
}

fn collect_compact_bounds_free_vars(bounds: &CompactBounds, out: &mut Vec<TypeVar>) {
    collect_compact_type_free_vars(&bounds.lower, out);
    collect_compact_type_free_vars(&bounds.upper, out);
}

fn collect_compact_root_upper_child_free_vars(ty: &CompactType, out: &mut Vec<TypeVar>) {
    for con in &ty.cons {
        for arg in &con.args {
            collect_compact_bounds_free_vars(arg, out);
        }
    }
    for fun in &ty.funs {
        collect_compact_type_free_vars(&fun.arg, out);
        collect_compact_type_free_vars(&fun.arg_eff, out);
        collect_compact_type_free_vars(&fun.ret_eff, out);
        collect_compact_type_free_vars(&fun.ret, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_compact_type_free_vars(&field.value, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_compact_type_free_vars(&field.value, out);
        }
        collect_compact_type_free_vars(&spread.tail, out);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_compact_type_free_vars(payload, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            collect_compact_type_free_vars(item, out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_compact_type_free_vars(item, out);
        }
        collect_compact_type_free_vars(&row.tail, out);
    }
}

fn collect_compact_type_free_vars(ty: &CompactType, out: &mut Vec<TypeVar>) {
    for tv in ty.vars.iter().copied() {
        if !out.contains(&tv) {
            out.push(tv);
        }
    }
    for con in &ty.cons {
        for arg in &con.args {
            collect_compact_bounds_free_vars(arg, out);
        }
    }
    for fun in &ty.funs {
        collect_compact_type_free_vars(&fun.arg, out);
        collect_compact_type_free_vars(&fun.arg_eff, out);
        collect_compact_type_free_vars(&fun.ret_eff, out);
        collect_compact_type_free_vars(&fun.ret, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_compact_type_free_vars(&field.value, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_compact_type_free_vars(&field.value, out);
        }
        collect_compact_type_free_vars(&spread.tail, out);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_compact_type_free_vars(payload, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            collect_compact_type_free_vars(item, out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_compact_type_free_vars(item, out);
        }
        collect_compact_type_free_vars(&row.tail, out);
    }
}

fn single_compact_var(ty: &CompactType) -> Option<TypeVar> {
    (ty.vars.len() == 1
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty())
    .then(|| ty.vars.iter().copied().next())
    .flatten()
}

pub(crate) fn compact_pos_type(
    arena: &TypeArena,
    ty: &CompactType,
    scheme: &CompactTypeScheme,
    in_row: bool,
) -> PosId {
    let _ = scheme;
    let mut parts = Vec::new();
    let mut vars = ty.vars.iter().copied().collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    parts.extend(vars.into_iter().map(|tv| arena.alloc_pos(Pos::Var(tv))));
    let mut prims = ty.prims.iter().cloned().collect::<Vec<_>>();
    prims.sort_by_key(path_key);
    parts.extend(prims.into_iter().map(|path| {
        if in_row {
            arena.alloc_pos(Pos::Atom(EffectAtom { path, args: vec![] }))
        } else {
            arena.alloc_pos(Pos::Con(path, vec![]))
        }
    }));
    for con in &ty.cons {
        if in_row {
            if let Some(atom) = compact_con_as_effect_atom(con) {
                parts.push(arena.alloc_pos(Pos::Atom(atom)));
                continue;
            }
        }
        parts.push(
            arena.alloc_pos(Pos::Con(
                con.path.clone(),
                con.args
                    .iter()
                    .map(|arg| {
                        (
                            compact_pos_type(arena, &arg.lower, scheme, false),
                            compact_neg_type(arena, &arg.upper, scheme, false),
                        )
                    })
                    .collect(),
            )),
        );
    }
    for CompactFun {
        arg,
        arg_eff,
        ret_eff,
        ret,
    } in &ty.funs
    {
        parts.push(arena.alloc_pos(Pos::Fun {
            arg: compact_neg_type(arena, arg, scheme, false),
            arg_eff: compact_neg_type(arena, arg_eff, scheme, false),
            ret_eff: compact_pos_type(arena, ret_eff, scheme, false),
            ret: compact_pos_type(arena, ret, scheme, false),
        }));
    }
    for CompactRecord { fields } in &ty.records {
        parts.push(
            arena.alloc_pos(Pos::Record(
                fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: compact_pos_type(arena, &field.value, scheme, false),
                        optional: field.optional,
                    })
                    .collect(),
            )),
        );
    }
    for spread in &ty.record_spreads {
        let fields = spread
            .fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: compact_pos_type(arena, &field.value, scheme, false),
                optional: field.optional,
            })
            .collect();
        let tail = compact_pos_type(arena, &spread.tail, scheme, false);
        let pos = if spread.tail_wins {
            Pos::RecordTailSpread { fields, tail }
        } else {
            Pos::RecordHeadSpread { tail, fields }
        };
        parts.push(arena.alloc_pos(pos));
    }
    for CompactVariant { items } in &ty.variants {
        parts.push(
            arena.alloc_pos(Pos::PolyVariant(
                items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|p| compact_pos_type(arena, p, scheme, false))
                                .collect(),
                        )
                    })
                    .collect(),
            )),
        );
    }
    for tuple in &ty.tuples {
        parts.push(
            arena.alloc_pos(Pos::Tuple(
                tuple
                    .iter()
                    .map(|item| compact_pos_type(arena, item, scheme, false))
                    .collect(),
            )),
        );
    }
    for CompactRow { items, tail } in &ty.rows {
        let tail_id = compact_pos_type(arena, tail, scheme, false);
        parts.push(
            arena.alloc_pos(Pos::Row(
                items
                    .iter()
                    .map(|item| compact_pos_type(arena, item, scheme, true))
                    .collect(),
                tail_id,
            )),
        );
    }
    fold_pos_union_id(arena, parts)
}

pub(crate) fn compact_neg_type(
    arena: &TypeArena,
    ty: &CompactType,
    scheme: &CompactTypeScheme,
    in_row: bool,
) -> NegId {
    let _ = scheme;
    let mut parts = Vec::new();
    let mut vars = ty.vars.iter().copied().collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    parts.extend(vars.into_iter().map(|tv| arena.alloc_neg(Neg::Var(tv))));
    let mut prims = ty.prims.iter().cloned().collect::<Vec<_>>();
    prims.sort_by_key(path_key);
    parts.extend(prims.into_iter().map(|path| {
        if in_row {
            arena.alloc_neg(Neg::Atom(EffectAtom { path, args: vec![] }))
        } else {
            arena.alloc_neg(Neg::Con(path, vec![]))
        }
    }));
    for con in &ty.cons {
        if in_row {
            if let Some(atom) = compact_con_as_effect_atom(con) {
                parts.push(arena.alloc_neg(Neg::Atom(atom)));
                continue;
            }
        }
        parts.push(
            arena.alloc_neg(Neg::Con(
                con.path.clone(),
                con.args
                    .iter()
                    .map(|arg| {
                        (
                            compact_pos_type(arena, &arg.lower, scheme, false),
                            compact_neg_type(arena, &arg.upper, scheme, false),
                        )
                    })
                    .collect(),
            )),
        );
    }
    for CompactFun {
        arg,
        arg_eff,
        ret_eff,
        ret,
    } in &ty.funs
    {
        parts.push(arena.alloc_neg(Neg::Fun {
            arg: compact_pos_type(arena, arg, scheme, false),
            arg_eff: compact_pos_type(arena, arg_eff, scheme, false),
            ret_eff: compact_neg_type(arena, ret_eff, scheme, false),
            ret: compact_neg_type(arena, ret, scheme, false),
        }));
    }
    for CompactRecord { fields } in &ty.records {
        parts.push(
            arena.alloc_neg(Neg::Record(
                fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: compact_neg_type(arena, &field.value, scheme, false),
                        optional: field.optional,
                    })
                    .collect(),
            )),
        );
    }
    for spread in &ty.record_spreads {
        // Neg has no RecordTailSpread / RecordHeadSpread variant. Emit the
        // explicit fields as a Neg::Record so downstream constraint
        // propagation still sees the known shape; the tail demand cannot
        // be represented on the negative side and is dropped here.
        parts.push(
            arena.alloc_neg(Neg::Record(
                spread
                    .fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: compact_neg_type(arena, &field.value, scheme, false),
                        optional: field.optional,
                    })
                    .collect(),
            )),
        );
    }
    for CompactVariant { items } in &ty.variants {
        parts.push(
            arena.alloc_neg(Neg::PolyVariant(
                items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|p| compact_neg_type(arena, p, scheme, false))
                                .collect(),
                        )
                    })
                    .collect(),
            )),
        );
    }
    for tuple in &ty.tuples {
        parts.push(
            arena.alloc_neg(Neg::Tuple(
                tuple
                    .iter()
                    .map(|item| compact_neg_type(arena, item, scheme, false))
                    .collect(),
            )),
        );
    }
    for CompactRow { items, tail } in &ty.rows {
        let tail_id = compact_neg_type(arena, tail, scheme, false);
        parts.push(
            arena.alloc_neg(Neg::Row(
                items
                    .iter()
                    .map(|item| compact_neg_type(arena, item, scheme, true))
                    .collect(),
                tail_id,
            )),
        );
    }
    fold_neg_intersection_id(arena, parts)
}

fn fold_pos_union_id(arena: &TypeArena, parts: Vec<PosId>) -> PosId {
    let mut it = parts.into_iter();
    let Some(first) = it.next() else {
        return arena.bot;
    };
    it.fold(first, |lhs, rhs| arena.alloc_pos(Pos::Union(lhs, rhs)))
}

fn fold_neg_intersection_id(arena: &TypeArena, parts: Vec<NegId>) -> NegId {
    let mut it = parts.into_iter();
    let Some(first) = it.next() else {
        return arena.top;
    };
    it.fold(first, |lhs, rhs| {
        arena.alloc_neg(Neg::Intersection(lhs, rhs))
    })
}

fn path_key(path: &Path) -> String {
    path.segments
        .iter()
        .map(|name| name.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

pub fn collect_pos_free_vars(infer: &Infer, id: PosId) -> Vec<TypeVar> {
    collect_pos_free_vars_in_arena(&infer.arena, id)
}

pub fn collect_neg_free_vars(infer: &Infer, id: NegId) -> Vec<TypeVar> {
    collect_neg_free_vars_in_arena(&infer.arena, id)
}

pub fn collect_pos_free_vars_in_arena(arena: &TypeArena, id: PosId) -> Vec<TypeVar> {
    let mut out = Vec::new();
    collect_pos_free_vars_inner_in_arena(arena, id, &mut out);
    out
}

pub fn collect_neg_free_vars_in_arena(arena: &TypeArena, id: NegId) -> Vec<TypeVar> {
    let mut out = Vec::new();
    collect_neg_free_vars_inner_in_arena(arena, id, &mut out);
    out
}

fn collect_pos_free_vars_inner_in_arena(arena: &TypeArena, id: PosId, out: &mut Vec<TypeVar>) {
    match arena.get_pos(id) {
        Pos::Bot => {}
        Pos::Var(tv) | Pos::Raw(tv) => {
            if !out.contains(&tv) {
                out.push(tv);
            }
        }
        Pos::Atom(a) => a.args.iter().for_each(|(p, n)| {
            if !out.contains(p) {
                out.push(*p);
            }
            if !out.contains(n) {
                out.push(*n);
            }
        }),
        Pos::Forall(bound, body) => {
            let mut inner = Vec::new();
            collect_pos_free_vars_inner_in_arena(arena, body, &mut inner);
            for tv in inner {
                if !bound.contains(&tv) && !out.contains(&tv) {
                    out.push(tv);
                }
            }
        }
        Pos::Con(_, args) => args.iter().for_each(|(p, n)| {
            collect_pos_free_vars_inner_in_arena(arena, *p, out);
            collect_neg_free_vars_inner_in_arena(arena, *n, out);
        }),
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_neg_free_vars_inner_in_arena(arena, arg, out);
            collect_neg_free_vars_inner_in_arena(arena, arg_eff, out);
            collect_pos_free_vars_inner_in_arena(arena, ret_eff, out);
            collect_pos_free_vars_inner_in_arena(arena, ret, out);
        }
        Pos::Record(fields) => fields
            .iter()
            .for_each(|field| collect_pos_free_vars_inner_in_arena(arena, field.value, out)),
        Pos::RecordTailSpread { fields, tail } => {
            fields
                .iter()
                .for_each(|field| collect_pos_free_vars_inner_in_arena(arena, field.value, out));
            collect_pos_free_vars_inner_in_arena(arena, tail, out);
        }
        Pos::RecordHeadSpread { tail, fields } => {
            collect_pos_free_vars_inner_in_arena(arena, tail, out);
            fields
                .iter()
                .for_each(|field| collect_pos_free_vars_inner_in_arena(arena, field.value, out));
        }
        Pos::PolyVariant(items) => items.iter().for_each(|(_, ps)| {
            ps.iter()
                .for_each(|p| collect_pos_free_vars_inner_in_arena(arena, *p, out));
        }),
        Pos::Tuple(items) => items
            .iter()
            .for_each(|p| collect_pos_free_vars_inner_in_arena(arena, *p, out)),
        Pos::Row(items, tail) => {
            items
                .iter()
                .for_each(|p| collect_pos_free_vars_inner_in_arena(arena, *p, out));
            collect_pos_free_vars_inner_in_arena(arena, tail, out);
        }
        Pos::Union(a, b) => {
            collect_pos_free_vars_inner_in_arena(arena, a, out);
            collect_pos_free_vars_inner_in_arena(arena, b, out);
        }
    }
}

fn collect_neg_free_vars_inner_in_arena(arena: &TypeArena, id: NegId, out: &mut Vec<TypeVar>) {
    match arena.get_neg(id) {
        Neg::Top => {}
        Neg::Var(tv) => {
            if !out.contains(&tv) {
                out.push(tv);
            }
        }
        Neg::Atom(a) => a.args.iter().for_each(|(p, n)| {
            if !out.contains(p) {
                out.push(*p);
            }
            if !out.contains(n) {
                out.push(*n);
            }
        }),
        Neg::Forall(bound, body) => {
            let mut inner = Vec::new();
            collect_neg_free_vars_inner_in_arena(arena, body, &mut inner);
            for tv in inner {
                if !bound.contains(&tv) && !out.contains(&tv) {
                    out.push(tv);
                }
            }
        }
        Neg::Con(_, args) => args.iter().for_each(|(p, n)| {
            collect_pos_free_vars_inner_in_arena(arena, *p, out);
            collect_neg_free_vars_inner_in_arena(arena, *n, out);
        }),
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_pos_free_vars_inner_in_arena(arena, arg, out);
            collect_pos_free_vars_inner_in_arena(arena, arg_eff, out);
            collect_neg_free_vars_inner_in_arena(arena, ret_eff, out);
            collect_neg_free_vars_inner_in_arena(arena, ret, out);
        }
        Neg::Record(fields) => fields
            .iter()
            .for_each(|field| collect_neg_free_vars_inner_in_arena(arena, field.value, out)),
        Neg::PolyVariant(items) => items.iter().for_each(|(_, ns)| {
            ns.iter()
                .for_each(|n| collect_neg_free_vars_inner_in_arena(arena, *n, out));
        }),
        Neg::Tuple(items) => items
            .iter()
            .for_each(|n| collect_neg_free_vars_inner_in_arena(arena, *n, out)),
        Neg::Row(items, tail) => {
            items
                .iter()
                .for_each(|n| collect_neg_free_vars_inner_in_arena(arena, *n, out));
            collect_neg_free_vars_inner_in_arena(arena, tail, out);
        }
        Neg::Intersection(a, b) => {
            collect_neg_free_vars_inner_in_arena(arena, a, out);
            collect_neg_free_vars_inner_in_arena(arena, b, out);
        }
    }
}
