use crate::profile::ProfileClock as Instant;

use rowan::TextRange;
use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{PatKind, TypedPat};
use crate::diagnostic::{ConstraintCause, ConstraintReason};
use crate::ids::{DefId, TypeVar};
use crate::lower::builtin_types::builtin_source_type_path;
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, Path};
use crate::types::RecordField;
use crate::types::{Neg, Pos};

pub(crate) fn connect_let_pattern(
    state: &mut LowerState,
    pat: &TypedPat,
    body_tv: TypeVar,
    body_eff_tv: TypeVar,
    body_span: Option<TextRange>,
    _recursive_self_used: bool,
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
                state
                    .infer
                    .constrain_with_cause(Pos::Var(def_tv), Neg::Var(body_tv), cause);
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
            let list_path = Path {
                segments: vec![
                    Name("std".to_string()),
                    Name("list".to_string()),
                    Name("list".to_string()),
                ],
            };
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
                let spread_list_path = Path {
                    segments: vec![
                        Name("std".to_string()),
                        Name("list".to_string()),
                        Name("list".to_string()),
                    ],
                };
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
            if !has_default {
                state
                    .infer
                    .constrain(state.pos_record(pos_fields), Neg::Var(pat.tv));
            }
            state.infer.constrain(
                Pos::Var(pat.tv),
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
            if let Some(spread_pat) = spread.as_ref().map(super::record_pat_spread_pat) {
                connect_pat_shape_and_locals(state, spread_pat, ambient_eff_tv);
            }
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
            state.infer.constrain(Pos::Var(inner.tv), Neg::Var(pat.tv));
            state.infer.constrain(Pos::Var(pat.tv), Neg::Var(inner.tv));
            if let Some(&def_tv) = state.def_tvs.get(def) {
                state.infer.constrain(Pos::Var(def_tv), Neg::Var(pat.tv));
                state.infer.constrain(Pos::Var(pat.tv), Neg::Var(def_tv));
            }
            connect_pat_shape_and_locals(state, inner, ambient_eff_tv);
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

fn constrain_enum_variant_pattern_shape(
    state: &mut LowerState,
    ctor_def: DefId,
    pat_tv: TypeVar,
    payload_tv: Option<TypeVar>,
) -> bool {
    let Some(shape) = state.enum_variant_patterns.get(&ctor_def).cloned() else {
        return false;
    };

    let scope = crate::lower::signature::fresh_type_scope(state, &shape.type_param_names);
    let type_arg_tvs = crate::lower::signature::ordered_type_vars(&shape.type_param_names, &scope);
    let enum_pos = state.pos_con(
        shape.enum_path.clone(),
        super::super::invariant_args(&type_arg_tvs),
    );
    let enum_neg = state.neg_con(shape.enum_path, super::super::invariant_args(&type_arg_tvs));
    state.infer.constrain(enum_pos, Neg::Var(pat_tv));
    state.infer.constrain(Pos::Var(pat_tv), enum_neg);

    if let (Some(payload_sig), Some(payload_tv)) = (shape.payload_sig, payload_tv) {
        let mut pos_scope = scope.clone();
        let mut neg_scope = scope;
        let payload_pos =
            crate::lower::signature::lower_pure_sig_type(state, &payload_sig, &mut pos_scope);
        let payload_neg =
            crate::lower::signature::lower_pure_sig_neg_type(state, &payload_sig, &mut neg_scope);
        state.infer.constrain(payload_pos, Neg::Var(payload_tv));
        state.infer.constrain(Pos::Var(payload_tv), payload_neg);
    }

    true
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
            if !has_path_sep {
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
