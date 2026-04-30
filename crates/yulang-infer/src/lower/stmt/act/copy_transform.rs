use std::collections::HashMap;

use crate::ast::expr::{
    CatchArmKind, ExprKind, PatKind, RecordPatField, RecordPatSpread, RecordSpread, TypedBlock,
    TypedCatchArm, TypedExpr, TypedPat, TypedStmt,
};
use crate::ids::DefId;
use crate::lower::LowerState;
use crate::symbols::Path;

pub(crate) fn transform_copied_principal_body(
    state: &LowerState,
    expr: &TypedExpr,
    def_subst: &HashMap<DefId, DefId>,
    source_path: &Path,
    dest_path: &Path,
) -> TypedExpr {
    TypedExpr {
        tv: expr.tv,
        eff: expr.eff,
        kind: transform_copied_expr_kind(state, &expr.kind, def_subst, source_path, dest_path),
    }
}

fn transform_copied_expr_kind(
    state: &LowerState,
    kind: &ExprKind,
    def_subst: &HashMap<DefId, DefId>,
    source_path: &Path,
    dest_path: &Path,
) -> ExprKind {
    match kind {
        ExprKind::PrimitiveOp(op) => ExprKind::PrimitiveOp(*op),
        ExprKind::Lit(lit) => ExprKind::Lit(lit.clone()),
        ExprKind::Var(def) => ExprKind::Var(def_subst.get(def).copied().unwrap_or(*def)),
        ExprKind::Ref(ref_id) => state
            .ctx
            .refs
            .get(*ref_id)
            .and_then(|def| def_subst.get(&def).copied())
            .map(ExprKind::Var)
            .unwrap_or(ExprKind::Ref(*ref_id)),
        ExprKind::App(callee, arg) => ExprKind::App(
            Box::new(transform_copied_principal_body(
                state,
                callee,
                def_subst,
                source_path,
                dest_path,
            )),
            Box::new(transform_copied_principal_body(
                state,
                arg,
                def_subst,
                source_path,
                dest_path,
            )),
        ),
        ExprKind::Lam(def, body) => ExprKind::Lam(
            *def,
            Box::new(transform_copied_principal_body(
                state,
                body,
                def_subst,
                source_path,
                dest_path,
            )),
        ),
        ExprKind::Tuple(items) => ExprKind::Tuple(
            items
                .iter()
                .map(|item| {
                    transform_copied_principal_body(state, item, def_subst, source_path, dest_path)
                })
                .collect(),
        ),
        ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .iter()
                .map(|(name, value)| {
                    (
                        name.clone(),
                        transform_copied_principal_body(
                            state,
                            value,
                            def_subst,
                            source_path,
                            dest_path,
                        ),
                    )
                })
                .collect(),
            spread: spread.as_ref().map(|spread| match spread {
                RecordSpread::Head(expr) => RecordSpread::Head(Box::new(
                    transform_copied_principal_body(state, expr, def_subst, source_path, dest_path),
                )),
                RecordSpread::Tail(expr) => RecordSpread::Tail(Box::new(
                    transform_copied_principal_body(state, expr, def_subst, source_path, dest_path),
                )),
            }),
        },
        ExprKind::PolyVariant(tag, payloads) => ExprKind::PolyVariant(
            tag.clone(),
            payloads
                .iter()
                .map(|payload| {
                    transform_copied_principal_body(
                        state,
                        payload,
                        def_subst,
                        source_path,
                        dest_path,
                    )
                })
                .collect(),
        ),
        ExprKind::Select { recv, name } => ExprKind::Select {
            recv: Box::new(transform_copied_principal_body(
                state,
                recv,
                def_subst,
                source_path,
                dest_path,
            )),
            name: name.clone(),
        },
        ExprKind::Match(scrutinee, arms) => ExprKind::Match(
            Box::new(transform_copied_principal_body(
                state,
                scrutinee,
                def_subst,
                source_path,
                dest_path,
            )),
            arms.iter()
                .map(|arm| crate::ast::expr::TypedMatchArm {
                    pat: transform_copied_pat(&arm.pat, state, def_subst, source_path, dest_path),
                    guard: arm.guard.as_ref().map(|guard| {
                        transform_copied_principal_body(
                            state,
                            guard,
                            def_subst,
                            source_path,
                            dest_path,
                        )
                    }),
                    body: transform_copied_principal_body(
                        state,
                        &arm.body,
                        def_subst,
                        source_path,
                        dest_path,
                    ),
                })
                .collect(),
        ),
        ExprKind::Catch(body, arms) => ExprKind::Catch(
            Box::new(transform_copied_principal_body(
                state,
                body,
                def_subst,
                source_path,
                dest_path,
            )),
            arms.iter()
                .map(|arm| TypedCatchArm {
                    tv: arm.tv,
                    guard: arm.guard.as_ref().map(|guard| {
                        transform_copied_principal_body(
                            state,
                            guard,
                            def_subst,
                            source_path,
                            dest_path,
                        )
                    }),
                    kind: match &arm.kind {
                        CatchArmKind::Value(pat, body) => CatchArmKind::Value(
                            transform_copied_pat(pat, state, def_subst, source_path, dest_path),
                            transform_copied_principal_body(
                                state,
                                body,
                                def_subst,
                                source_path,
                                dest_path,
                            ),
                        ),
                        CatchArmKind::Effect {
                            op_path,
                            pat,
                            k,
                            body,
                        } => CatchArmKind::Effect {
                            op_path: replace_copied_effect_path(op_path, source_path, dest_path),
                            pat: transform_copied_pat(
                                pat,
                                state,
                                def_subst,
                                source_path,
                                dest_path,
                            ),
                            k: *k,
                            body: transform_copied_principal_body(
                                state,
                                body,
                                def_subst,
                                source_path,
                                dest_path,
                            ),
                        },
                    },
                })
                .collect(),
        ),
        ExprKind::Block(block) => ExprKind::Block(transform_copied_block(
            block,
            state,
            def_subst,
            source_path,
            dest_path,
        )),
        ExprKind::Coerce {
            actual_tv,
            expected_tv,
            expr,
        } => ExprKind::Coerce {
            actual_tv: *actual_tv,
            expected_tv: *expected_tv,
            expr: Box::new(transform_copied_principal_body(
                state,
                expr,
                def_subst,
                source_path,
                dest_path,
            )),
        },
        ExprKind::PackForall(var, expr) => ExprKind::PackForall(
            *var,
            Box::new(transform_copied_principal_body(
                state,
                expr,
                def_subst,
                source_path,
                dest_path,
            )),
        ),
    }
}

fn transform_copied_block(
    block: &TypedBlock,
    state: &LowerState,
    def_subst: &HashMap<DefId, DefId>,
    source_path: &Path,
    dest_path: &Path,
) -> TypedBlock {
    TypedBlock {
        tv: block.tv,
        eff: block.eff,
        stmts: block
            .stmts
            .iter()
            .map(|stmt| match stmt {
                TypedStmt::Let(pat, value) => TypedStmt::Let(
                    transform_copied_pat(pat, state, def_subst, source_path, dest_path),
                    transform_copied_principal_body(
                        state,
                        value,
                        def_subst,
                        source_path,
                        dest_path,
                    ),
                ),
                TypedStmt::Expr(expr) => TypedStmt::Expr(transform_copied_principal_body(
                    state,
                    expr,
                    def_subst,
                    source_path,
                    dest_path,
                )),
                TypedStmt::Module(def, body) => TypedStmt::Module(
                    def_subst.get(def).copied().unwrap_or(*def),
                    transform_copied_block(body, state, def_subst, source_path, dest_path),
                ),
            })
            .collect(),
        tail: block.tail.as_ref().map(|tail| {
            Box::new(transform_copied_principal_body(
                state,
                tail,
                def_subst,
                source_path,
                dest_path,
            ))
        }),
    }
}

fn transform_copied_pat(
    pat: &TypedPat,
    state: &LowerState,
    def_subst: &HashMap<DefId, DefId>,
    source_path: &Path,
    dest_path: &Path,
) -> TypedPat {
    TypedPat {
        tv: pat.tv,
        kind: match &pat.kind {
            PatKind::Wild => PatKind::Wild,
            PatKind::Lit(lit) => PatKind::Lit(lit.clone()),
            PatKind::Tuple(items) => PatKind::Tuple(
                items
                    .iter()
                    .map(|item| {
                        transform_copied_pat(item, state, def_subst, source_path, dest_path)
                    })
                    .collect(),
            ),
            PatKind::List {
                prefix,
                spread,
                suffix,
            } => PatKind::List {
                prefix: prefix
                    .iter()
                    .map(|item| {
                        transform_copied_pat(item, state, def_subst, source_path, dest_path)
                    })
                    .collect(),
                spread: spread.as_ref().map(|spread| {
                    Box::new(transform_copied_pat(
                        spread,
                        state,
                        def_subst,
                        source_path,
                        dest_path,
                    ))
                }),
                suffix: suffix
                    .iter()
                    .map(|item| {
                        transform_copied_pat(item, state, def_subst, source_path, dest_path)
                    })
                    .collect(),
            },
            PatKind::Record { spread, fields } => PatKind::Record {
                spread: spread.as_ref().map(|spread| match spread {
                    RecordPatSpread::Head(pat) => RecordPatSpread::Head(Box::new(
                        transform_copied_pat(pat, state, def_subst, source_path, dest_path),
                    )),
                    RecordPatSpread::Tail(pat) => RecordPatSpread::Tail(Box::new(
                        transform_copied_pat(pat, state, def_subst, source_path, dest_path),
                    )),
                }),
                fields: fields
                    .iter()
                    .map(|field| RecordPatField {
                        name: field.name.clone(),
                        pat: transform_copied_pat(
                            &field.pat,
                            state,
                            def_subst,
                            source_path,
                            dest_path,
                        ),
                        default: field.default.as_ref().map(|default| {
                            transform_copied_principal_body(
                                state,
                                default,
                                def_subst,
                                source_path,
                                dest_path,
                            )
                        }),
                    })
                    .collect(),
            },
            PatKind::PolyVariant(tag, items) => PatKind::PolyVariant(
                tag.clone(),
                items
                    .iter()
                    .map(|item| {
                        transform_copied_pat(item, state, def_subst, source_path, dest_path)
                    })
                    .collect(),
            ),
            PatKind::Con(ref_id, payload) => PatKind::Con(
                *ref_id,
                payload.as_ref().map(|payload| {
                    Box::new(transform_copied_pat(
                        payload,
                        state,
                        def_subst,
                        source_path,
                        dest_path,
                    ))
                }),
            ),
            PatKind::UnresolvedName(name) => PatKind::UnresolvedName(name.clone()),
            PatKind::Or(lhs, rhs) => PatKind::Or(
                Box::new(transform_copied_pat(
                    lhs,
                    state,
                    def_subst,
                    source_path,
                    dest_path,
                )),
                Box::new(transform_copied_pat(
                    rhs,
                    state,
                    def_subst,
                    source_path,
                    dest_path,
                )),
            ),
            PatKind::As(pattern, def) => PatKind::As(
                Box::new(transform_copied_pat(
                    pattern,
                    state,
                    def_subst,
                    source_path,
                    dest_path,
                )),
                *def,
            ),
        },
    }
}

fn replace_copied_effect_path(path: &Path, source_path: &Path, dest_path: &Path) -> Path {
    if path.segments.starts_with(&source_path.segments) {
        let mut segments = dest_path.segments.clone();
        segments.extend_from_slice(&path.segments[source_path.segments.len()..]);
        Path { segments }
    } else {
        path.clone()
    }
}
