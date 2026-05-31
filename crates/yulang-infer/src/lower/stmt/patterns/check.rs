use std::collections::HashMap;

use crate::profile::ProfileClock as Instant;

use rowan::TextRange;
use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{PatKind, RecordPatField, RecordPatSpread, TypedPat};
use crate::diagnostic::{ConstraintCause, ConstraintReason};
use crate::ids::{DefId, TypeVar};
use crate::lower::builtin_types::builtin_source_type_path;
use crate::lower::{EnumVariantPatternPayload, LowerState, SyntaxNode};
use crate::symbols::{Name, Path};
use crate::types::RecordField;
use crate::types::{Neg, Pos};

pub(crate) fn connect_let_pattern(
    state: &mut LowerState,
    pat: &TypedPat,
    body_tv: TypeVar,
    body_eff_tv: TypeVar,
    body_span: Option<TextRange>,
    recursive_self_used: bool,
) {
    let cause = ConstraintCause {
        span: body_span,
        reason: ConstraintReason::BindingBody,
    };
    if let PatKind::UnresolvedName(name) = &pat.kind {
        if let Some(def) = state.ctx.resolve_bound_value(name) {
            if let Some(&def_tv) = state.def_tvs.get(&def) {
                state.infer.constrain_with_cause(
                    Pos::Var(body_tv),
                    Neg::Var(def_tv),
                    cause.clone(),
                );
                if !recursive_self_used {
                    state
                        .infer
                        .constrain_with_cause(Pos::Var(def_tv), Neg::Var(body_tv), cause);
                }
                return;
            }
        }
    }
    state
        .infer
        .constrain_with_cause(Pos::Var(body_tv), Neg::Var(pat.tv), cause.clone());
    state
        .infer
        .constrain_with_cause(Pos::Var(pat.tv), Neg::Var(body_tv), cause);
    connect_pat_shape_and_locals(state, pat, body_eff_tv);
}

pub(crate) fn connect_pat_shape_and_locals(
    state: &mut LowerState,
    pat: &TypedPat,
    ambient_eff_tv: TypeVar,
) {
    let start = Instant::now();
    match &pat.kind {
        PatKind::UnresolvedName(name) => {
            let branch_start = Instant::now();
            if let Some(def) = state.ctx.resolve_bound_value(name) {
                if let Some(&def_tv) = state.def_tvs.get(&def) {
                    state.infer.constrain(Pos::Var(def_tv), Neg::Var(pat.tv));
                    state.infer.constrain(Pos::Var(pat.tv), Neg::Var(def_tv));
                }
            }
            state.lower_detail.connect_pat_name += branch_start.elapsed();
        }
        PatKind::Tuple(items) => {
            let branch_start = Instant::now();
            state.infer.constrain(
                state.pos_tuple(items.iter().map(|item| Pos::Var(item.tv)).collect()),
                Neg::Var(pat.tv),
            );
            state.infer.constrain(
                Pos::Var(pat.tv),
                Neg::Tuple(
                    items
                        .iter()
                        .map(|item| state.infer.alloc_neg(Neg::Var(item.tv)))
                        .collect(),
                ),
            );
            for item in items {
                connect_pat_shape_and_locals(state, item, ambient_eff_tv);
            }
            state.lower_detail.connect_pat_tuple += branch_start.elapsed();
        }
        PatKind::List {
            prefix,
            spread,
            suffix,
        } => {
            let branch_start = Instant::now();
            let item_tv = state.fresh_tv();
            let list_path = state.builtin_source_type_path("list");
            let list_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
            state.infer.constrain(
                state.pos_con(list_path.clone(), list_args.clone()),
                Neg::Var(pat.tv),
            );
            state
                .infer
                .constrain(Pos::Var(pat.tv), state.neg_con(list_path, list_args));

            for item in prefix.iter().chain(suffix.iter()) {
                state.infer.constrain(Pos::Var(item.tv), Neg::Var(item_tv));
                state.infer.constrain(Pos::Var(item_tv), Neg::Var(item.tv));
                connect_pat_shape_and_locals(state, item, ambient_eff_tv);
            }
            if let Some(spread) = spread {
                let spread_args = vec![(Pos::Var(item_tv), Neg::Var(item_tv))];
                let spread_list_path = state.builtin_source_type_path("list");
                state.infer.constrain(
                    state.pos_con(spread_list_path.clone(), spread_args.clone()),
                    Neg::Var(spread.tv),
                );
                state.infer.constrain(
                    Pos::Var(spread.tv),
                    state.neg_con(spread_list_path, spread_args),
                );
                connect_pat_shape_and_locals(state, spread, ambient_eff_tv);
            }
            state.lower_detail.connect_pat_tuple += branch_start.elapsed();
        }
        PatKind::Record { spread, fields } => {
            let branch_start = Instant::now();
            connect_record_pat_shape_and_locals(
                state,
                pat.tv,
                spread.as_ref(),
                fields,
                ambient_eff_tv,
            );
            state.lower_detail.connect_pat_record += branch_start.elapsed();
        }
        PatKind::PolyVariant(name, payloads) => {
            let branch_start = Instant::now();
            state.infer.constrain(
                state.pos_variant(vec![(
                    name.clone(),
                    payloads
                        .iter()
                        .map(|payload| Pos::Var(payload.tv))
                        .collect(),
                )]),
                Neg::Var(pat.tv),
            );
            state.infer.constrain(
                Pos::Var(pat.tv),
                Neg::PolyVariant(vec![(
                    name.clone(),
                    payloads
                        .iter()
                        .map(|payload| state.infer.alloc_neg(Neg::Var(payload.tv)))
                        .collect(),
                )]),
            );
            for payload in payloads {
                connect_pat_shape_and_locals(state, payload, ambient_eff_tv);
            }
            state.lower_detail.connect_pat_poly_variant += branch_start.elapsed();
        }
        PatKind::Con(ref_id, Some(inner)) => {
            if let Some(resolved) = state.ctx.refs.resolved().get(ref_id) {
                let def_id = resolved.def_id;
                let ctor_tv = resolved.ref_tv;
                if !constrain_enum_variant_pattern_shape(state, def_id, pat.tv, Some(inner.tv)) {
                    let arg_eff_tv = state.fresh_exact_pure_eff_tv();
                    let ret_eff_tv = state.fresh_exact_pure_eff_tv();
                    let neg_fun = state.neg_fun(
                        Pos::Var(inner.tv),
                        Pos::Var(arg_eff_tv),
                        Neg::Var(ret_eff_tv),
                        Neg::Var(pat.tv),
                    );
                    let pos_fun = state.pos_fun(
                        Neg::Var(inner.tv),
                        Neg::Var(arg_eff_tv),
                        Pos::Var(ret_eff_tv),
                        Pos::Var(pat.tv),
                    );
                    state.infer.constrain(Pos::Var(ctor_tv), neg_fun);
                    state.infer.constrain(pos_fun, Neg::Var(ctor_tv));
                }
            }
            connect_pat_shape_and_locals(state, inner, ambient_eff_tv);
        }
        PatKind::As(inner, def) => {
            let branch_start = Instant::now();
            if let PatKind::Record {
                spread: None,
                fields,
            } = &inner.kind
            {
                connect_record_pat_shape_and_locals(state, pat.tv, None, fields, ambient_eff_tv);
            } else {
                state.infer.constrain(Pos::Var(inner.tv), Neg::Var(pat.tv));
                state.infer.constrain(Pos::Var(pat.tv), Neg::Var(inner.tv));
                connect_pat_shape_and_locals(state, inner, ambient_eff_tv);
            }
            let has_direct_record_alias_body = matches!(inner.kind, PatKind::Record { .. })
                && state.principal_bodies.contains_key(def);
            if !has_direct_record_alias_body && let Some(&def_tv) = state.def_tvs.get(def) {
                state.infer.constrain(Pos::Var(def_tv), Neg::Var(pat.tv));
                state.infer.constrain(Pos::Var(pat.tv), Neg::Var(def_tv));
            }
            state.lower_detail.connect_pat_alias += branch_start.elapsed();
        }
        PatKind::Or(lhs, rhs) => {
            let branch_start = Instant::now();
            connect_pat_shape_and_locals(state, lhs, ambient_eff_tv);
            connect_pat_shape_and_locals(state, rhs, ambient_eff_tv);
            state.lower_detail.connect_pat_or += branch_start.elapsed();
        }
        PatKind::Lit(lit) => {
            constrain_pat_literal_type(state, pat.tv, lit);
        }
        PatKind::Con(ref_id, None) => {
            if let Some(resolved) = state.ctx.refs.resolved().get(ref_id) {
                let def_id = resolved.def_id;
                let ctor_tv = resolved.ref_tv;
                if !constrain_enum_variant_pattern_shape(state, def_id, pat.tv, None) {
                    state.infer.constrain(Pos::Var(ctor_tv), Neg::Var(pat.tv));
                    state.infer.constrain(Pos::Var(pat.tv), Neg::Var(ctor_tv));
                }
            }
        }
        PatKind::Wild => {}
    }
    state.lower_detail.connect_pat_shape_and_locals += start.elapsed();
}

fn connect_record_pat_shape_and_locals(
    state: &mut LowerState,
    pat_tv: TypeVar,
    spread: Option<&RecordPatSpread>,
    fields: &[RecordPatField],
    ambient_eff_tv: TypeVar,
) {
    let has_default = fields.iter().any(|field| field.default.is_some());
    let pos_fields = fields
        .iter()
        .map(|field| {
            if field.default.is_some() {
                RecordField::optional(field.name.clone(), Pos::Var(field.pat.tv))
            } else {
                RecordField::required(field.name.clone(), Pos::Var(field.pat.tv))
            }
        })
        .collect::<Vec<_>>();
    if let Some(spread) = spread {
        let spread_pat = super::record_pat_spread_pat(spread);
        state
            .infer
            .constrain(Pos::Var(pat_tv), Neg::Var(spread_pat.tv));
    } else if !has_default {
        state
            .infer
            .constrain(state.pos_record(pos_fields), Neg::Var(pat_tv));
    }
    state.infer.constrain(
        Pos::Var(pat_tv),
        state.neg_record(
            fields
                .iter()
                .map(|field| {
                    if field.default.is_some() {
                        RecordField::optional(field.name.clone(), Neg::Var(field.pat.tv))
                    } else {
                        RecordField::required(field.name.clone(), Neg::Var(field.pat.tv))
                    }
                })
                .collect(),
        ),
    );
    for field in fields {
        if let Some(default) = &field.default {
            state
                .infer
                .constrain(Pos::Var(default.tv), Neg::Var(field.pat.tv));
            state
                .infer
                .constrain(Pos::Var(field.pat.tv), Neg::Var(default.tv));
            state
                .infer
                .constrain(Pos::Var(default.eff), Neg::Var(ambient_eff_tv));
        }
        connect_pat_shape_and_locals(state, &field.pat, ambient_eff_tv);
    }
    if let Some(spread_pat) = spread.map(super::record_pat_spread_pat) {
        connect_pat_shape_and_locals(state, spread_pat, ambient_eff_tv);
    }
}

fn constrain_enum_variant_pattern_shape(
    state: &mut LowerState,
    ctor_def: DefId,
    pat_tv: TypeVar,
    payload_tv: Option<TypeVar>,
) -> bool {
    let Some(shape) = state.enum_variant_patterns.get(&ctor_def).cloned() else {
        return false;
    };

    match shape.payload {
        EnumVariantPatternPayload::Source {
            type_param_names,
            payload_sig,
        } => {
            let scope = crate::lower::signature::fresh_type_scope(state, &type_param_names);
            let type_arg_tvs =
                crate::lower::signature::ordered_type_vars(&type_param_names, &scope);
            constrain_enum_variant_result_type(state, shape.enum_path, &type_arg_tvs, pat_tv);

            if let (Some(payload_sig), Some(payload_tv)) = (payload_sig, payload_tv) {
                let mut pos_scope = scope.clone();
                let mut neg_scope = scope;
                let payload_pos = crate::lower::signature::lower_pure_sig_type(
                    state,
                    &payload_sig,
                    &mut pos_scope,
                );
                let payload_neg = crate::lower::signature::lower_pure_sig_neg_type(
                    state,
                    &payload_sig,
                    &mut neg_scope,
                );
                state.infer.constrain(payload_pos, Neg::Var(payload_tv));
                state.infer.constrain(Pos::Var(payload_tv), payload_neg);
            }
        }
        EnumVariantPatternPayload::Imported {
            type_params,
            payload,
        } => {
            let mut scope = HashMap::new();
            let type_arg_tvs = type_params
                .iter()
                .map(|param| {
                    *scope
                        .entry(param.clone())
                        .or_insert_with(|| state.fresh_tv())
                })
                .collect::<Vec<_>>();
            constrain_enum_variant_result_type(state, shape.enum_path, &type_arg_tvs, pat_tv);

            if let (Some(payload), Some(payload_tv)) = (payload, payload_tv) {
                let payload_pos = imported_core_type_pos(state, &payload, &mut scope);
                let payload_neg = imported_core_type_neg(state, &payload, &mut scope);
                state.infer.constrain(payload_pos, Neg::Var(payload_tv));
                state.infer.constrain(Pos::Var(payload_tv), payload_neg);
            }
        }
    }

    true
}

fn constrain_enum_variant_result_type(
    state: &mut LowerState,
    enum_path: Path,
    type_arg_tvs: &[TypeVar],
    pat_tv: TypeVar,
) {
    let enum_pos = state.pos_con(
        enum_path.clone(),
        super::super::invariant_args(type_arg_tvs),
    );
    let enum_neg = state.neg_con(enum_path, super::super::invariant_args(type_arg_tvs));
    state.infer.constrain(enum_pos, Neg::Var(pat_tv));
    state.infer.constrain(Pos::Var(pat_tv), enum_neg);
}

fn imported_core_type_var(
    state: &LowerState,
    scope: &mut HashMap<yulang_typed_ir::TypeVar, TypeVar>,
    var: &yulang_typed_ir::TypeVar,
) -> TypeVar {
    *scope.entry(var.clone()).or_insert_with(|| state.fresh_tv())
}

fn imported_core_type_pos(
    state: &LowerState,
    ty: &yulang_typed_ir::Type,
    scope: &mut HashMap<yulang_typed_ir::TypeVar, TypeVar>,
) -> Pos {
    match ty {
        yulang_typed_ir::Type::Unknown => Pos::Var(state.fresh_tv()),
        yulang_typed_ir::Type::Never => Pos::Bot,
        yulang_typed_ir::Type::Any => Pos::Bot,
        yulang_typed_ir::Type::Var(var) => Pos::Var(imported_core_type_var(state, scope, var)),
        yulang_typed_ir::Type::Named { path, args } => state.pos_con(
            source_path_from_core_path(path),
            args.iter()
                .map(|arg| imported_core_type_arg(state, arg, scope))
                .collect(),
        ),
        yulang_typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => state.pos_fun(
            imported_core_type_neg(state, param, scope),
            imported_core_type_neg(state, param_effect, scope),
            imported_core_type_pos(state, ret_effect, scope),
            imported_core_type_pos(state, ret, scope),
        ),
        yulang_typed_ir::Type::Tuple(items) => state.pos_tuple(
            items
                .iter()
                .map(|item| imported_core_type_pos(state, item, scope))
                .collect(),
        ),
        yulang_typed_ir::Type::Record(record) => imported_core_record_pos(state, record, scope),
        yulang_typed_ir::Type::Variant(variant) => state.pos_variant(
            variant
                .cases
                .iter()
                .map(|case| {
                    (
                        Name(case.name.0.clone()),
                        case.payloads
                            .iter()
                            .map(|payload| imported_core_type_pos(state, payload, scope))
                            .collect(),
                    )
                })
                .collect(),
        ),
        yulang_typed_ir::Type::Row { items, tail } => state.pos_row(
            items
                .iter()
                .map(|item| imported_core_type_pos(state, item, scope))
                .collect(),
            imported_core_type_pos(state, tail, scope),
        ),
        yulang_typed_ir::Type::Union(items) => imported_core_type_pos_union(state, items, scope),
        yulang_typed_ir::Type::Inter(items) => {
            imported_core_type_pos_intersection(state, items, scope)
        }
        yulang_typed_ir::Type::Recursive { body, .. } => imported_core_type_pos(state, body, scope),
    }
}

fn imported_core_type_neg(
    state: &LowerState,
    ty: &yulang_typed_ir::Type,
    scope: &mut HashMap<yulang_typed_ir::TypeVar, TypeVar>,
) -> Neg {
    match ty {
        yulang_typed_ir::Type::Unknown => Neg::Var(state.fresh_tv()),
        yulang_typed_ir::Type::Never => Neg::Top,
        yulang_typed_ir::Type::Any => Neg::Top,
        yulang_typed_ir::Type::Var(var) => Neg::Var(imported_core_type_var(state, scope, var)),
        yulang_typed_ir::Type::Named { path, args } => state.neg_con(
            source_path_from_core_path(path),
            args.iter()
                .map(|arg| imported_core_type_arg(state, arg, scope))
                .collect(),
        ),
        yulang_typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => state.neg_fun(
            imported_core_type_pos(state, param, scope),
            imported_core_type_pos(state, param_effect, scope),
            imported_core_type_neg(state, ret_effect, scope),
            imported_core_type_neg(state, ret, scope),
        ),
        yulang_typed_ir::Type::Tuple(items) => Neg::Tuple(
            items
                .iter()
                .map(|item| {
                    state
                        .infer
                        .alloc_neg(imported_core_type_neg(state, item, scope))
                })
                .collect(),
        ),
        yulang_typed_ir::Type::Record(record) => state.neg_record(
            record
                .fields
                .iter()
                .map(|field| RecordField {
                    name: Name(field.name.0.clone()),
                    value: imported_core_type_neg(state, &field.value, scope),
                    optional: field.optional,
                })
                .collect(),
        ),
        yulang_typed_ir::Type::Variant(variant) => Neg::PolyVariant(
            variant
                .cases
                .iter()
                .map(|case| {
                    (
                        Name(case.name.0.clone()),
                        case.payloads
                            .iter()
                            .map(|payload| {
                                state
                                    .infer
                                    .alloc_neg(imported_core_type_neg(state, payload, scope))
                            })
                            .collect(),
                    )
                })
                .collect(),
        ),
        yulang_typed_ir::Type::Row { items, tail } => state.neg_row(
            items
                .iter()
                .map(|item| imported_core_type_neg(state, item, scope))
                .collect(),
            imported_core_type_neg(state, tail, scope),
        ),
        yulang_typed_ir::Type::Union(items) => imported_core_type_neg_union(state, items, scope),
        yulang_typed_ir::Type::Inter(items) => {
            imported_core_type_neg_intersection(state, items, scope)
        }
        yulang_typed_ir::Type::Recursive { body, .. } => imported_core_type_neg(state, body, scope),
    }
}

fn imported_core_type_arg(
    state: &LowerState,
    arg: &yulang_typed_ir::TypeArg,
    scope: &mut HashMap<yulang_typed_ir::TypeVar, TypeVar>,
) -> (Pos, Neg) {
    match arg {
        yulang_typed_ir::TypeArg::Type(ty) => (
            imported_core_type_pos(state, ty, scope),
            imported_core_type_neg(state, ty, scope),
        ),
        yulang_typed_ir::TypeArg::Bounds(bounds) => (
            bounds
                .lower
                .as_deref()
                .map(|ty| imported_core_type_pos(state, ty, scope))
                .unwrap_or(Pos::Bot),
            bounds
                .upper
                .as_deref()
                .map(|ty| imported_core_type_neg(state, ty, scope))
                .unwrap_or(Neg::Top),
        ),
    }
}

fn imported_core_record_pos(
    state: &LowerState,
    record: &yulang_typed_ir::RecordType,
    scope: &mut HashMap<yulang_typed_ir::TypeVar, TypeVar>,
) -> Pos {
    let fields = record
        .fields
        .iter()
        .map(|field| RecordField {
            name: Name(field.name.0.clone()),
            value: imported_core_type_pos(state, &field.value, scope),
            optional: field.optional,
        })
        .collect::<Vec<_>>();
    match &record.spread {
        None => state.pos_record(fields),
        Some(yulang_typed_ir::RecordSpread::Tail(tail)) => {
            state.pos_record_tail_spread(fields, imported_core_type_pos(state, tail, scope))
        }
        Some(yulang_typed_ir::RecordSpread::Head(tail)) => {
            state.pos_record_head_spread(imported_core_type_pos(state, tail, scope), fields)
        }
    }
}

fn imported_core_type_pos_union(
    state: &LowerState,
    items: &[yulang_typed_ir::Type],
    scope: &mut HashMap<yulang_typed_ir::TypeVar, TypeVar>,
) -> Pos {
    let mut iter = items.iter().map(|item| {
        state
            .infer
            .alloc_pos(imported_core_type_pos(state, item, scope))
    });
    let Some(first) = iter.next() else {
        return Pos::Bot;
    };
    iter.fold(state.infer.arena.get_pos(first).clone(), |acc, item| {
        Pos::Union(state.infer.alloc_pos(acc), item)
    })
}

fn imported_core_type_pos_intersection(
    state: &LowerState,
    items: &[yulang_typed_ir::Type],
    scope: &mut HashMap<yulang_typed_ir::TypeVar, TypeVar>,
) -> Pos {
    items
        .first()
        .map(|item| imported_core_type_pos(state, item, scope))
        .unwrap_or(Pos::Bot)
}

fn imported_core_type_neg_union(
    state: &LowerState,
    items: &[yulang_typed_ir::Type],
    scope: &mut HashMap<yulang_typed_ir::TypeVar, TypeVar>,
) -> Neg {
    items
        .first()
        .map(|item| imported_core_type_neg(state, item, scope))
        .unwrap_or(Neg::Top)
}

fn imported_core_type_neg_intersection(
    state: &LowerState,
    items: &[yulang_typed_ir::Type],
    scope: &mut HashMap<yulang_typed_ir::TypeVar, TypeVar>,
) -> Neg {
    let mut iter = items.iter().map(|item| {
        state
            .infer
            .alloc_neg(imported_core_type_neg(state, item, scope))
    });
    let Some(first) = iter.next() else {
        return Neg::Top;
    };
    iter.fold(state.infer.arena.get_neg(first).clone(), |acc, item| {
        Neg::Intersection(state.infer.alloc_neg(acc), item)
    })
}

fn source_path_from_core_path(path: &yulang_typed_ir::Path) -> Path {
    Path {
        segments: path
            .segments
            .iter()
            .map(|segment| Name(segment.0.clone()))
            .collect(),
    }
}

fn constrain_pat_literal_type(
    state: &mut LowerState,
    pat_tv: TypeVar,
    lit: &crate::ast::expr::Lit,
) {
    let name = match lit {
        crate::ast::expr::Lit::Int(_) => "int",
        crate::ast::expr::Lit::Float(_) => "float",
        crate::ast::expr::Lit::Str(_) => "str",
        crate::ast::expr::Lit::Bool(_) => "bool",
        crate::ast::expr::Lit::Unit => "unit",
    };
    let path = builtin_source_type_path(name);
    state
        .infer
        .constrain(Pos::Con(path.clone(), vec![]), Neg::Var(pat_tv));
    state
        .infer
        .constrain(Pos::Var(pat_tv), Neg::Con(path, vec![]));
}

pub(crate) fn bind_pattern_locals(state: &mut LowerState, node: &SyntaxNode) {
    match node.kind() {
        SyntaxKind::PatField => {
            for child in node.children() {
                if child.kind() != SyntaxKind::Expr {
                    bind_pattern_locals(state, &child);
                }
            }
            let has_nested_pat = node.children().any(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::Pattern | SyntaxKind::PatOr | SyntaxKind::PatAs
                )
            });
            if has_nested_pat {
                return;
            }
            if let Some(name) = super::super::ident_name(node) {
                let def = state.fresh_def();
                let tv = state.fresh_tv();
                state.register_def_tv(def, tv);
                if let Some(owner) = state.current_owner {
                    state.register_def_owner(def, owner);
                }
                state.register_def_name(def, name.clone());
                state.ctx.bind_local(name, def);
            }
        }
        SyntaxKind::PatSpread => {
            for child in node.children() {
                if child.kind() != SyntaxKind::Expr {
                    bind_pattern_locals(state, &child);
                }
            }
        }
        SyntaxKind::Pattern
        | SyntaxKind::PatOr
        | SyntaxKind::PatAs
        | SyntaxKind::PatParenGroup
        | SyntaxKind::PatList
        | SyntaxKind::PatRecord
        | SyntaxKind::ApplyML
        | SyntaxKind::ApplyC => {
            for child in node.children() {
                if child.kind() != SyntaxKind::Expr {
                    bind_pattern_locals(state, &child);
                }
            }
            let has_path_sep = node
                .children()
                .any(|child| child.kind() == SyntaxKind::PathSep);
            if !has_path_sep && !pattern_has_poly_variant_colon(node) {
                if pattern_resolves_to_constructor(state, node) {
                    return;
                }
                if let Some(name) = super::pattern_binding_name(node) {
                    let def = state.fresh_def();
                    let tv = state.fresh_tv();
                    state.register_def_tv(def, tv);
                    if let Some(owner) = state.current_owner {
                        state.register_def_owner(def, owner);
                    }
                    state.register_def_name(def, name.clone());
                    state.ctx.bind_local(name, def);
                }
            }
        }
        _ => {}
    }
}

fn pattern_has_poly_variant_colon(node: &SyntaxNode) -> bool {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .any(|token| matches!(token.kind(), SyntaxKind::Colon | SyntaxKind::Symbol))
}

fn pattern_resolves_to_constructor(state: &LowerState, node: &SyntaxNode) -> bool {
    super::pattern_ctor_path(node)
        .and_then(|path| super::enum_variant_def_for_pattern(state, &path))
        .is_some()
}
