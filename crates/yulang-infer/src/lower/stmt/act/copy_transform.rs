use std::collections::{HashMap, HashSet};

use crate::ast::expr::{
    CatchArmKind, ExprKind, PatKind, RecordPatField, RecordPatSpread, RecordSpread, TypedBlock,
    TypedCatchArm, TypedExpr, TypedPat, TypedStmt,
};
use crate::ids::{DefId, NegId, PosId, TypeVar};
use crate::lower::LowerState;
use crate::solve::{
    EffectSubtractFact, EffectSubtractId, EffectSubtractability, RefFieldProjection,
    ResolvedRoleMethodSelection, RoleMethodCallSelection, TypeFieldInfo,
};
use crate::symbols::{Name, Path};
use crate::types::{EffectAtom, Neg, Pos, RecordField};

pub(crate) struct CopiedPrincipalBody {
    pub(crate) body: TypedExpr,
    pub(crate) type_subst: Vec<(TypeVar, TypeVar)>,
}

pub(crate) fn transform_copied_principal_body_with_subst(
    state: &mut LowerState,
    expr: &TypedExpr,
    def_subst: &HashMap<DefId, DefId>,
    tv_subst: &[(TypeVar, TypeVar)],
    source_path: &Path,
    source_path_aliases: &[Path],
    dest_path: &Path,
    dest_args: &[(TypeVar, TypeVar)],
) -> CopiedPrincipalBody {
    let mut types = CopiedTypeVars::new(
        state,
        tv_subst,
        source_path,
        source_path_aliases,
        dest_path,
        dest_args,
    );
    let body = transform_copied_principal_body_inner(&mut types, expr, def_subst);
    CopiedPrincipalBody {
        body,
        type_subst: types.into_subst(),
    }
}

fn transform_copied_principal_body_inner(
    types: &mut CopiedTypeVars<'_>,
    expr: &TypedExpr,
    def_subst: &HashMap<DefId, DefId>,
) -> TypedExpr {
    let tv = types.copy_tv(expr.tv);
    let eff = types.copy_tv(expr.eff);
    copy_resolved_expr_info(types, expr.tv, tv, def_subst);
    match &expr.kind {
        ExprKind::Var(def) => types.link_local_var_ref(*def, tv),
        ExprKind::Ref(ref_id) => {
            if let Some(def) = types.state.ctx.refs.get(*ref_id) {
                types.link_local_var_ref(def, tv);
            }
        }
        _ => {}
    }
    TypedExpr {
        tv,
        eff,
        kind: transform_copied_expr_kind(types, &expr.kind, def_subst),
    }
}

fn copy_resolved_expr_info(
    types: &mut CopiedTypeVars<'_>,
    source_tv: TypeVar,
    dest_tv: TypeVar,
    def_subst: &HashMap<DefId, DefId>,
) {
    if let Some(def) = types.state.infer.resolved_selection_def(source_tv) {
        types
            .state
            .infer
            .resolved_selections
            .borrow_mut()
            .insert(dest_tv, def_subst.get(&def).copied().unwrap_or(def));
    }
    if let Some(projection) = types.state.infer.resolved_ref_field_projection(source_tv) {
        types
            .state
            .infer
            .resolved_ref_field_projections
            .borrow_mut()
            .insert(dest_tv, subst_ref_field_projection(projection, def_subst));
    }
    if let Some(selection) = types.state.infer.resolved_role_method_selection(source_tv) {
        types
            .state
            .infer
            .resolved_role_method_selections
            .borrow_mut()
            .insert(
                dest_tv,
                subst_resolved_role_method_selection(selection, def_subst),
            );
    }
    if let Some(selection) = types.state.infer.role_method_call_selection(source_tv) {
        let selection = subst_role_method_call_selection(selection, types, def_subst, dest_tv);
        types
            .state
            .infer
            .role_method_call_selections
            .borrow_mut()
            .insert(dest_tv, selection);
    }
}

fn subst_resolved_role_method_selection(
    selection: ResolvedRoleMethodSelection,
    def_subst: &HashMap<DefId, DefId>,
) -> ResolvedRoleMethodSelection {
    ResolvedRoleMethodSelection {
        role: selection.role,
        member: def_subst
            .get(&selection.member)
            .copied()
            .unwrap_or(selection.member),
        impl_member: def_subst
            .get(&selection.impl_member)
            .copied()
            .unwrap_or(selection.impl_member),
    }
}

fn subst_role_method_call_selection(
    selection: RoleMethodCallSelection,
    types: &mut CopiedTypeVars<'_>,
    def_subst: &HashMap<DefId, DefId>,
    dest_tv: TypeVar,
) -> RoleMethodCallSelection {
    RoleMethodCallSelection {
        role: selection.role,
        member: def_subst
            .get(&selection.member)
            .copied()
            .unwrap_or(selection.member),
        recv_tv: types.copy_tv(selection.recv_tv),
        arg_tvs: selection
            .arg_tvs
            .into_iter()
            .map(|tv| types.copy_tv(tv))
            .collect(),
        result_tv: dest_tv,
    }
}

fn subst_ref_field_projection(
    projection: RefFieldProjection,
    def_subst: &HashMap<DefId, DefId>,
) -> RefFieldProjection {
    RefFieldProjection {
        type_path: projection.type_path,
        field: subst_type_field_info(projection.field, def_subst),
        fields: projection
            .fields
            .into_iter()
            .map(|field| subst_type_field_info(field, def_subst))
            .collect(),
        constructor: def_subst
            .get(&projection.constructor)
            .copied()
            .unwrap_or(projection.constructor),
    }
}

fn subst_type_field_info(field: TypeFieldInfo, def_subst: &HashMap<DefId, DefId>) -> TypeFieldInfo {
    TypeFieldInfo {
        name: field.name,
        def: def_subst.get(&field.def).copied().unwrap_or(field.def),
    }
}

fn transform_copied_expr_kind(
    types: &mut CopiedTypeVars<'_>,
    kind: &ExprKind,
    def_subst: &HashMap<DefId, DefId>,
) -> ExprKind {
    match kind {
        ExprKind::PrimitiveOp(op) => ExprKind::PrimitiveOp(*op),
        ExprKind::Lit(lit) => ExprKind::Lit(lit.clone()),
        ExprKind::Var(def) => ExprKind::Var(types.subst_expr_def(*def, def_subst)),
        ExprKind::Ref(ref_id) => types
            .state
            .ctx
            .refs
            .get(*ref_id)
            .map(|def| types.subst_expr_def(def, def_subst))
            .map(ExprKind::Var)
            .unwrap_or(ExprKind::Ref(*ref_id)),
        ExprKind::App {
            callee,
            arg,
            callee_edge_id: _,
            expected_callee_tv,
            arg_edge_id: _,
            expected_arg_tv,
        } => ExprKind::App {
            callee: Box::new(transform_copied_principal_body_inner(
                types, callee, def_subst,
            )),
            arg: Box::new(transform_copied_principal_body_inner(types, arg, def_subst)),
            callee_edge_id: None,
            expected_callee_tv: types.copy_tv(*expected_callee_tv),
            arg_edge_id: None,
            expected_arg_tv: types.copy_tv(*expected_arg_tv),
        },
        ExprKind::RefSet { reference, value } => ExprKind::RefSet {
            reference: Box::new(transform_copied_principal_body_inner(
                types, reference, def_subst,
            )),
            value: Box::new(transform_copied_principal_body_inner(
                types, value, def_subst,
            )),
        },
        ExprKind::Lam(def, body) => {
            let copied_def = types.copy_local_def(*def);
            let source_local_defs = types
                .state
                .lambda_local_defs
                .get(def)
                .cloned()
                .unwrap_or_default();
            let copied_local_defs = source_local_defs
                .iter()
                .map(|local_def| types.copy_local_def(*local_def))
                .collect::<Vec<_>>();
            if !copied_local_defs.is_empty() {
                types
                    .state
                    .lambda_local_defs
                    .insert(copied_def, copied_local_defs);
            }
            if let Some(pat) = types.state.lambda_param_pats.get(def).cloned() {
                let pat = transform_copied_pat(&pat, types, def_subst);
                types.state.lambda_param_pats.insert(copied_def, pat);
            }
            if let Some(annotation) = types
                .state
                .lambda_param_effect_annotations
                .get(def)
                .cloned()
            {
                types
                    .state
                    .lambda_param_effect_annotations
                    .insert(copied_def, annotation);
            }
            if let Some(hint) = types
                .state
                .lambda_param_function_sig_hints
                .get(def)
                .cloned()
            {
                let hint = types.copy_function_sig_effect_hint(hint);
                types
                    .state
                    .lambda_param_function_sig_hints
                    .insert(copied_def, hint);
            }
            if let Some(allowed) = types
                .state
                .lambda_param_function_allowed_effects
                .get(def)
                .cloned()
            {
                types
                    .state
                    .lambda_param_function_allowed_effects
                    .insert(copied_def, allowed);
            }
            if let Some(source_eff) = types.state.lambda_param_source_eff_tvs.get(def).copied() {
                let copied_source_eff = types.copy_tv(source_eff);
                types
                    .state
                    .lambda_param_source_eff_tvs
                    .insert(copied_def, copied_source_eff);
            }
            let mut local_defs = vec![*def];
            local_defs.extend(source_local_defs);
            let previous = types.enter_local_defs(local_defs.as_slice());
            let body = transform_copied_principal_body_inner(types, body, def_subst);
            types.restore_local_defs(previous);
            ExprKind::Lam(copied_def, Box::new(body))
        }
        ExprKind::Tuple(items) => ExprKind::Tuple(
            items
                .iter()
                .map(|item| transform_copied_principal_body_inner(types, item, def_subst))
                .collect(),
        ),
        ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .iter()
                .map(|(name, value)| {
                    (
                        name.clone(),
                        transform_copied_principal_body_inner(types, value, def_subst),
                    )
                })
                .collect(),
            spread: spread.as_ref().map(|spread| match spread {
                RecordSpread::Head(expr) => RecordSpread::Head(Box::new(
                    transform_copied_principal_body_inner(types, expr, def_subst),
                )),
                RecordSpread::Tail(expr) => RecordSpread::Tail(Box::new(
                    transform_copied_principal_body_inner(types, expr, def_subst),
                )),
            }),
        },
        ExprKind::PolyVariant(tag, payloads, origin) => ExprKind::PolyVariant(
            tag.clone(),
            payloads
                .iter()
                .map(|payload| transform_copied_principal_body_inner(types, payload, def_subst))
                .collect(),
            *origin,
        ),
        ExprKind::Select { recv, name } => ExprKind::Select {
            recv: Box::new(transform_copied_principal_body_inner(
                types, recv, def_subst,
            )),
            name: name.clone(),
        },
        ExprKind::Match(scrutinee, arms) => ExprKind::Match(
            Box::new(transform_copied_principal_body_inner(
                types, scrutinee, def_subst,
            )),
            arms.iter()
                .map(|arm| transform_copied_match_arm(types, arm, def_subst))
                .collect(),
        ),
        ExprKind::Catch(body, arms) => ExprKind::Catch(
            Box::new(transform_copied_principal_body_inner(
                types, body, def_subst,
            )),
            arms.iter()
                .map(|arm| transform_copied_catch_arm(types, arm, def_subst))
                .collect(),
        ),
        ExprKind::Block(block) => ExprKind::Block(transform_copied_block(block, types, def_subst)),
        ExprKind::BindHere(expr) => ExprKind::BindHere(Box::new(
            transform_copied_principal_body_inner(types, expr, def_subst),
        )),
        ExprKind::Coerce {
            edge_id: _,
            actual_tv,
            expected_tv,
            expr,
        } => ExprKind::Coerce {
            edge_id: None,
            actual_tv: types.copy_tv(*actual_tv),
            expected_tv: types.copy_tv(*expected_tv),
            expr: Box::new(transform_copied_principal_body_inner(
                types, expr, def_subst,
            )),
        },
        ExprKind::PackForall(var, expr) => ExprKind::PackForall(
            types.copy_tv(*var),
            Box::new(transform_copied_principal_body_inner(
                types, expr, def_subst,
            )),
        ),
    }
}

fn transform_copied_match_arm(
    types: &mut CopiedTypeVars<'_>,
    arm: &crate::ast::expr::TypedMatchArm,
    def_subst: &HashMap<DefId, DefId>,
) -> crate::ast::expr::TypedMatchArm {
    let pat = transform_copied_pat(&arm.pat, types, def_subst);
    let source_local_defs = pat_local_defs(&arm.pat);
    let previous = types.enter_local_defs(source_local_defs.as_slice());
    let guard = arm
        .guard
        .as_ref()
        .map(|guard| transform_copied_principal_body_inner(types, guard, def_subst));
    let body = transform_copied_principal_body_inner(types, &arm.body, def_subst);
    types.restore_local_defs(previous);
    crate::ast::expr::TypedMatchArm { pat, guard, body }
}

fn transform_copied_catch_arm(
    types: &mut CopiedTypeVars<'_>,
    arm: &TypedCatchArm,
    def_subst: &HashMap<DefId, DefId>,
) -> TypedCatchArm {
    let tv = types.copy_tv(arm.tv);
    match &arm.kind {
        CatchArmKind::Value(pat, body) => {
            let source_local_defs = pat_local_defs(pat);
            let pat = transform_copied_pat(pat, types, def_subst);
            let previous = types.enter_local_defs(source_local_defs.as_slice());
            let guard = arm
                .guard
                .as_ref()
                .map(|guard| transform_copied_principal_body_inner(types, guard, def_subst));
            let body = transform_copied_principal_body_inner(types, body, def_subst);
            types.restore_local_defs(previous);
            TypedCatchArm {
                tv,
                guard,
                kind: CatchArmKind::Value(pat, body),
            }
        }
        CatchArmKind::Effect {
            op_path,
            pat,
            k,
            body,
        } => {
            let mut source_local_defs = pat_local_defs(pat);
            let pat = transform_copied_pat(pat, types, def_subst);
            let copied_k = types.copy_local_def(*k);
            source_local_defs.push(*k);
            let previous = types.enter_local_defs(source_local_defs.as_slice());
            let guard = arm
                .guard
                .as_ref()
                .map(|guard| transform_copied_principal_body_inner(types, guard, def_subst));
            let body = transform_copied_principal_body_inner(types, body, def_subst);
            types.restore_local_defs(previous);
            TypedCatchArm {
                tv,
                guard,
                kind: CatchArmKind::Effect {
                    op_path: replace_copied_catch_op_path(
                        op_path,
                        types.source_path,
                        types.source_path_aliases,
                        types.dest_path,
                    ),
                    pat,
                    k: copied_k,
                    body,
                },
            }
        }
    }
}

fn pat_local_defs(pat: &TypedPat) -> Vec<DefId> {
    let mut out = Vec::new();
    collect_pat_local_defs(pat, &mut out);
    out
}

fn collect_pat_local_defs(pat: &TypedPat, out: &mut Vec<DefId>) {
    match &pat.kind {
        PatKind::Tuple(items) | PatKind::PolyVariant(_, items) => {
            for item in items {
                collect_pat_local_defs(item, out);
            }
        }
        PatKind::List {
            prefix,
            spread,
            suffix,
        } => {
            for item in prefix {
                collect_pat_local_defs(item, out);
            }
            if let Some(spread) = spread {
                collect_pat_local_defs(spread, out);
            }
            for item in suffix {
                collect_pat_local_defs(item, out);
            }
        }
        PatKind::Record { spread, fields } => {
            if let Some(spread) = spread {
                match spread {
                    RecordPatSpread::Head(pat) | RecordPatSpread::Tail(pat) => {
                        collect_pat_local_defs(pat, out);
                    }
                }
            }
            for field in fields {
                collect_pat_local_defs(&field.pat, out);
            }
        }
        PatKind::Con(_, Some(payload)) => collect_pat_local_defs(payload, out),
        PatKind::Or(lhs, rhs) => {
            collect_pat_local_defs(lhs, out);
            collect_pat_local_defs(rhs, out);
        }
        PatKind::As(inner, def) => {
            collect_pat_local_defs(inner, out);
            if !out.contains(def) {
                out.push(*def);
            }
        }
        PatKind::Wild | PatKind::Lit(_) | PatKind::Con(_, None) | PatKind::UnresolvedName(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::expr::Lit;
    use crate::diagnostic::ExpectedEdgeId;

    #[test]
    fn copied_coerce_drops_source_edge_id() {
        let mut state = LowerState::new();
        let tv = state.fresh_tv();
        let eff = state.fresh_tv();
        let actual_tv = state.fresh_tv();
        let expected_tv = state.fresh_tv();
        let expr = TypedExpr {
            tv: expected_tv,
            eff,
            kind: ExprKind::Coerce {
                edge_id: Some(ExpectedEdgeId(7)),
                actual_tv,
                expected_tv,
                expr: Box::new(TypedExpr {
                    tv,
                    eff,
                    kind: ExprKind::Lit(Lit::Unit),
                }),
            },
        };

        let copied = copy_expr(&mut state, &expr);

        let ExprKind::Coerce { edge_id, .. } = copied.kind else {
            panic!("expected copied coerce");
        };
        assert_eq!(edge_id, None);
    }

    #[test]
    fn copied_app_drops_argument_edge_id() {
        let mut state = LowerState::new();
        let callee_tv = state.fresh_tv();
        let arg_tv = state.fresh_tv();
        let result_tv = state.fresh_tv();
        let expected_arg_tv = state.fresh_tv();
        let expected_callee_tv = state.fresh_tv();
        let eff = state.fresh_tv();
        let expr = TypedExpr {
            tv: result_tv,
            eff,
            kind: ExprKind::App {
                callee: Box::new(unit_expr(callee_tv, eff)),
                arg: Box::new(unit_expr(arg_tv, eff)),
                callee_edge_id: Some(ExpectedEdgeId(8)),
                expected_callee_tv,
                arg_edge_id: Some(ExpectedEdgeId(9)),
                expected_arg_tv,
            },
        };

        let copied = copy_expr(&mut state, &expr);

        let ExprKind::App {
            callee_edge_id,
            expected_callee_tv: copied_expected_callee_tv,
            arg_edge_id,
            expected_arg_tv: copied_expected_arg_tv,
            ..
        } = copied.kind
        else {
            panic!("expected copied app");
        };
        assert_eq!(callee_edge_id, None);
        assert_eq!(arg_edge_id, None);
        assert_ne!(copied_expected_callee_tv, expected_callee_tv);
        assert_ne!(copied_expected_arg_tv, expected_arg_tv);
    }

    fn copy_expr(state: &mut LowerState, expr: &TypedExpr) -> TypedExpr {
        transform_copied_principal_body_with_subst(
            state,
            expr,
            &HashMap::new(),
            &[],
            &Path {
                segments: Vec::new(),
            },
            &[],
            &Path {
                segments: Vec::new(),
            },
            &[],
        )
        .body
    }

    fn unit_expr(tv: TypeVar, eff: TypeVar) -> TypedExpr {
        TypedExpr {
            tv,
            eff,
            kind: ExprKind::Lit(Lit::Unit),
        }
    }
}

fn transform_copied_block(
    block: &TypedBlock,
    types: &mut CopiedTypeVars<'_>,
    def_subst: &HashMap<DefId, DefId>,
) -> TypedBlock {
    TypedBlock {
        tv: types.copy_tv(block.tv),
        eff: types.copy_tv(block.eff),
        stmts: block
            .stmts
            .iter()
            .map(|stmt| match stmt {
                TypedStmt::Let(pat, value) => {
                    if let PatKind::UnresolvedName(name) = &pat.kind {
                        types.enter_named_local(name.clone());
                    }
                    TypedStmt::Let(
                        transform_copied_pat(pat, types, def_subst),
                        transform_copied_principal_body_inner(types, value, def_subst),
                    )
                }
                TypedStmt::Expr(expr) => TypedStmt::Expr(transform_copied_principal_body_inner(
                    types, expr, def_subst,
                )),
                TypedStmt::Module(def, body) => TypedStmt::Module(
                    types.subst_expr_def(*def, def_subst),
                    transform_copied_block(body, types, def_subst),
                ),
            })
            .collect(),
        tail: block.tail.as_ref().map(|tail| {
            Box::new(transform_copied_principal_body_inner(
                types, tail, def_subst,
            ))
        }),
    }
}

fn transform_copied_pat(
    pat: &TypedPat,
    types: &mut CopiedTypeVars<'_>,
    def_subst: &HashMap<DefId, DefId>,
) -> TypedPat {
    TypedPat {
        tv: types.copy_tv(pat.tv),
        kind: match &pat.kind {
            PatKind::Wild => PatKind::Wild,
            PatKind::Lit(lit) => PatKind::Lit(lit.clone()),
            PatKind::Tuple(items) => PatKind::Tuple(
                items
                    .iter()
                    .map(|item| transform_copied_pat(item, types, def_subst))
                    .collect(),
            ),
            PatKind::List {
                prefix,
                spread,
                suffix,
            } => PatKind::List {
                prefix: prefix
                    .iter()
                    .map(|item| transform_copied_pat(item, types, def_subst))
                    .collect(),
                spread: spread
                    .as_ref()
                    .map(|spread| Box::new(transform_copied_pat(spread, types, def_subst))),
                suffix: suffix
                    .iter()
                    .map(|item| transform_copied_pat(item, types, def_subst))
                    .collect(),
            },
            PatKind::Record { spread, fields } => PatKind::Record {
                spread: spread.as_ref().map(|spread| match spread {
                    RecordPatSpread::Head(pat) => {
                        RecordPatSpread::Head(Box::new(transform_copied_pat(pat, types, def_subst)))
                    }
                    RecordPatSpread::Tail(pat) => {
                        RecordPatSpread::Tail(Box::new(transform_copied_pat(pat, types, def_subst)))
                    }
                }),
                fields: fields
                    .iter()
                    .map(|field| RecordPatField {
                        name: field.name.clone(),
                        pat: transform_copied_pat(&field.pat, types, def_subst),
                        default: field.default.as_ref().map(|default| {
                            transform_copied_principal_body_inner(types, default, def_subst)
                        }),
                    })
                    .collect(),
            },
            PatKind::PolyVariant(tag, items) => PatKind::PolyVariant(
                tag.clone(),
                items
                    .iter()
                    .map(|item| transform_copied_pat(item, types, def_subst))
                    .collect(),
            ),
            PatKind::Con(ref_id, payload) => PatKind::Con(
                *ref_id,
                payload
                    .as_ref()
                    .map(|payload| Box::new(transform_copied_pat(payload, types, def_subst))),
            ),
            PatKind::UnresolvedName(name) => PatKind::UnresolvedName(name.clone()),
            PatKind::Or(lhs, rhs) => PatKind::Or(
                Box::new(transform_copied_pat(lhs, types, def_subst)),
                Box::new(transform_copied_pat(rhs, types, def_subst)),
            ),
            PatKind::As(pattern, def) => PatKind::As(
                Box::new(transform_copied_pat(pattern, types, def_subst)),
                types.copy_local_def(*def),
            ),
        },
    }
}

fn replace_copied_effect_path(
    path: &Path,
    source_path: &Path,
    source_path_aliases: &[Path],
    dest_path: &Path,
) -> Path {
    if path.segments.starts_with(&source_path.segments) {
        let mut segments = dest_path.segments.clone();
        segments.extend_from_slice(&path.segments[source_path.segments.len()..]);
        Path { segments }
    } else {
        for alias in source_path_aliases {
            if path.segments.starts_with(&alias.segments) {
                let mut segments = dest_path.segments.clone();
                segments.extend_from_slice(&path.segments[alias.segments.len()..]);
                return Path { segments };
            }
        }
        path.clone()
    }
}

fn replace_copied_catch_op_path(
    path: &Path,
    source_path: &Path,
    source_path_aliases: &[Path],
    dest_path: &Path,
) -> Path {
    if path.segments.len() == 1 {
        let mut segments = dest_path.segments.clone();
        segments.extend_from_slice(&path.segments);
        return Path { segments };
    }
    replace_copied_effect_path(path, source_path, source_path_aliases, dest_path)
}

struct CopiedTypeVars<'a> {
    state: &'a mut LowerState,
    fixed: HashMap<TypeVar, TypeVar>,
    copied: HashMap<TypeVar, TypeVar>,
    copied_effect_subtract_ids: HashMap<EffectSubtractId, EffectSubtractId>,
    copied_tv_side_tables: HashSet<TypeVar>,
    copied_handler_matches: HashSet<usize>,
    local_def_subst: HashMap<DefId, DefId>,
    local_name_subst: HashMap<Name, DefId>,
    local_defs: HashSet<DefId>,
    source_path: &'a Path,
    source_path_aliases: &'a [Path],
    dest_path: &'a Path,
    dest_args: &'a [(TypeVar, TypeVar)],
}

impl<'a> CopiedTypeVars<'a> {
    fn new(
        state: &'a mut LowerState,
        fixed: &[(TypeVar, TypeVar)],
        source_path: &'a Path,
        source_path_aliases: &'a [Path],
        dest_path: &'a Path,
        dest_args: &'a [(TypeVar, TypeVar)],
    ) -> Self {
        Self {
            state,
            fixed: fixed.iter().copied().collect(),
            copied: HashMap::new(),
            copied_effect_subtract_ids: HashMap::new(),
            copied_tv_side_tables: HashSet::new(),
            copied_handler_matches: HashSet::new(),
            local_def_subst: HashMap::new(),
            local_name_subst: HashMap::new(),
            local_defs: HashSet::new(),
            source_path,
            source_path_aliases,
            dest_path,
            dest_args,
        }
    }

    fn enter_local_defs(&mut self, defs: &[DefId]) -> Vec<(DefId, bool)> {
        defs.iter()
            .map(|def| (*def, self.local_defs.insert(*def)))
            .collect()
    }

    fn restore_local_defs(&mut self, previous: Vec<(DefId, bool)>) {
        for (def, inserted) in previous.into_iter().rev() {
            if inserted {
                self.local_defs.remove(&def);
            }
        }
    }

    fn link_local_var_ref(&mut self, def: DefId, tv: TypeVar) {
        if !self.local_defs.contains(&def) {
            return;
        }
        let Some(def_tv) = self.state.def_tvs.get(&def).copied() else {
            return;
        };
        let copied_def_tv = self.copy_tv(def_tv);
        self.state
            .infer
            .constrain(Pos::Var(copied_def_tv), Neg::Var(tv));
        self.state
            .infer
            .constrain(Pos::Var(tv), Neg::Var(copied_def_tv));
    }

    fn enter_named_local(&mut self, name: Name) -> DefId {
        let copied = self.state.fresh_def();
        self.state.register_def_name(copied, name.clone());
        self.local_name_subst.insert(name, copied);
        copied
    }

    fn subst_expr_def(&mut self, def: DefId, def_subst: &HashMap<DefId, DefId>) -> DefId {
        if let Some(copied) = def_subst.get(&def).copied() {
            return copied;
        }
        if let Some(copied) = self.local_def_subst.get(&def).copied() {
            return copied;
        }
        if let Some(name) = self.state.def_name(def).cloned()
            && let Some(copied) = self.local_name_subst.get(&name).copied()
        {
            self.local_def_subst.insert(def, copied);
            self.copy_local_def_data_into(def, copied);
            return copied;
        }
        def
    }

    fn copy_local_def(&mut self, def: DefId) -> DefId {
        if let Some(copied) = self.local_def_subst.get(&def).copied() {
            return copied;
        }
        let copied = self.state.fresh_def();
        self.local_def_subst.insert(def, copied);
        self.copy_local_def_data_into(def, copied);
        copied
    }

    fn copy_local_def_data_into(&mut self, def: DefId, copied: DefId) {
        if let Some(tv) = self.state.def_tvs.get(&def).copied() {
            let copied_tv = self.copy_tv(tv);
            self.state.def_tvs.entry(copied).or_insert(copied_tv);
        }
        if let Some(name) = self.state.def_name(def).cloned() {
            self.state.register_def_name(copied, name);
        }
        if let Some(eff) = self.state.def_eff_tvs.get(&def).copied() {
            let copied_eff = self.copy_tv(eff);
            self.state.def_eff_tvs.insert(copied, copied_eff);
        }
        if let Some(source_eff) = self.state.lambda_param_source_eff_tvs.get(&def).copied() {
            let copied_source_eff = self.copy_tv(source_eff);
            self.state
                .lambda_param_source_eff_tvs
                .insert(copied, copied_source_eff);
        }
        if self.state.let_bound_defs.contains(&def) {
            self.state.let_bound_defs.insert(copied);
        }
        if self.state.continuation_defs.contains(&def) {
            self.state.continuation_defs.insert(copied);
        }
        if let Some(eff) = self.state.continuation_result_eff_tvs.get(&def).copied() {
            let copied_eff = self.copy_tv(eff);
            self.state
                .continuation_result_eff_tvs
                .insert(copied, copied_eff);
        }
        if let Some(owner) = self.state.def_owners.get(&def).copied() {
            let copied_owner = self.local_def_subst.get(&owner).copied().unwrap_or(owner);
            self.state.register_def_owner(copied, copied_owner);
        }
        if let Some(act) = self.state.var_ref_acts.get(&def).cloned() {
            self.state.var_ref_acts.insert(copied, act);
        }
    }

    fn copy_tv(&mut self, tv: TypeVar) -> TypeVar {
        if let Some(mapped) = self.fixed.get(&tv).copied() {
            self.copy_tv_side_tables(tv, mapped);
            return mapped;
        }
        if let Some(mapped) = self.copied.get(&tv).copied() {
            return mapped;
        }

        let level = self.state.infer.level_of(tv);
        let mapped = match self.state.infer.origin_of(tv) {
            Some(origin) => self.state.fresh_tv_at_origin(level, origin),
            None => self.state.fresh_tv_at(level),
        };
        self.copied.insert(tv, mapped);

        let lowers = self.state.infer.lowers_of(tv);
        for lower in lowers {
            let lower = self.copy_pos(lower);
            self.state.infer.constrain(lower, Neg::Var(mapped));
        }

        let uppers = self.state.infer.uppers_of(tv);
        for upper in uppers {
            let upper = self.copy_neg(upper);
            self.state.infer.constrain(Pos::Var(mapped), upper);
        }

        if self.state.infer.effect_is_all_subtractable(tv) {
            self.state
                .infer
                .record_effect_subtractability(mapped, EffectSubtractability::All);
        }
        self.copy_tv_side_tables(tv, mapped);

        mapped
    }

    fn copy_tv_side_tables(&mut self, tv: TypeVar, mapped: TypeVar) {
        if !self.copied_tv_side_tables.insert(tv) {
            return;
        }
        if let Some(keep) = self
            .state
            .infer
            .effect_boundary_keeps
            .borrow()
            .get(&tv)
            .cloned()
        {
            self.state.infer.record_effect_boundary_keep(mapped, keep);
        }
        for fact in self.state.infer.effect_subtract_facts(tv) {
            let fact = self.copy_effect_subtract_fact(fact);
            self.state.infer.record_effect_subtract_fact(mapped, fact);
        }
        for id in self.state.infer.effect_non_subtract_ids(tv) {
            let id = self.copy_effect_subtract_id(id);
            self.state.infer.record_effect_non_subtract(mapped, id);
        }
        self.copy_handler_matches_for(tv);
    }

    fn copy_effect_subtract_fact(&mut self, fact: EffectSubtractFact) -> EffectSubtractFact {
        EffectSubtractFact {
            id: self.copy_effect_subtract_id(fact.id),
            subtractability: self.copy_effect_subtractability(fact.subtractability),
        }
    }

    fn copy_effect_subtract_id(&mut self, id: EffectSubtractId) -> EffectSubtractId {
        if let Some(mapped) = self.copied_effect_subtract_ids.get(&id).copied() {
            return mapped;
        }
        let mapped = self.state.infer.fresh_effect_subtract_id();
        self.copied_effect_subtract_ids.insert(id, mapped);
        if self
            .state
            .infer
            .effect_subtract_id_needs_call_non_subtract(id)
        {
            self.state
                .infer
                .record_effect_subtract_call_non_subtract_id(mapped);
        }
        mapped
    }

    fn copy_effect_subtractability(
        &mut self,
        subtractability: EffectSubtractability,
    ) -> EffectSubtractability {
        match subtractability {
            EffectSubtractability::Empty => EffectSubtractability::Empty,
            EffectSubtractability::All => EffectSubtractability::All,
            EffectSubtractability::AllExcept(atoms) => EffectSubtractability::all_except(
                atoms
                    .into_iter()
                    .map(|atom| self.copy_effect_atom(atom))
                    .collect(),
            ),
            EffectSubtractability::Set(atoms) => EffectSubtractability::Set(
                atoms
                    .into_iter()
                    .map(|atom| self.copy_effect_atom(atom))
                    .collect(),
            ),
        }
    }

    fn copy_handler_matches_for(&mut self, tv: TypeVar) {
        let indices = self
            .state
            .infer
            .handler_match_dependents
            .borrow()
            .get(&tv)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .collect::<Vec<_>>();
        for index in indices {
            if !self.copied_handler_matches.insert(index) {
                continue;
            }
            let Some(edge) = self
                .state
                .infer
                .handler_matches
                .borrow()
                .get(index)
                .cloned()
            else {
                continue;
            };
            let actual = self.copy_tv(edge.actual);
            let residual = self.copy_tv(edge.residual);
            self.state
                .infer
                .record_effect_boundary_keep(actual, edge.keep.clone());
            let handled = edge
                .handled
                .into_iter()
                .map(|handled| self.copy_neg_id(handled))
                .collect();
            if edge.solve_open_rows {
                self.state
                    .infer
                    .record_open_handler_match(actual, handled, residual, edge.cause);
            } else {
                self.state
                    .infer
                    .record_handler_match(actual, handled, residual, edge.cause);
            }
        }
    }

    fn copy_function_sig_effect_hint(
        &mut self,
        hint: crate::lower::FunctionSigEffectHint,
    ) -> crate::lower::FunctionSigEffectHint {
        match hint {
            crate::lower::FunctionSigEffectHint::Pure => crate::lower::FunctionSigEffectHint::Pure,
            crate::lower::FunctionSigEffectHint::AllSubtractable {
                subtract_ids,
                non_subtract_targets,
            } => crate::lower::FunctionSigEffectHint::AllSubtractable {
                subtract_ids: subtract_ids
                    .into_iter()
                    .map(|id| self.copy_effect_subtract_id(id))
                    .collect(),
                non_subtract_targets: non_subtract_targets
                    .into_iter()
                    .map(|tv| self.copy_tv(tv))
                    .collect(),
            },
            crate::lower::FunctionSigEffectHint::LowerBound(lower) => {
                crate::lower::FunctionSigEffectHint::LowerBound(self.copy_pos_id(lower))
            }
            crate::lower::FunctionSigEffectHint::Bounds {
                lower,
                upper,
                subtract_ids,
                non_subtract_targets,
            } => crate::lower::FunctionSigEffectHint::Bounds {
                lower: self.copy_pos_id(lower),
                upper: self.copy_neg_id(upper),
                subtract_ids: subtract_ids
                    .into_iter()
                    .map(|id| self.copy_effect_subtract_id(id))
                    .collect(),
                non_subtract_targets: non_subtract_targets
                    .into_iter()
                    .map(|tv| self.copy_tv(tv))
                    .collect(),
            },
        }
    }

    fn into_subst(self) -> Vec<(TypeVar, TypeVar)> {
        self.fixed.into_iter().chain(self.copied).collect()
    }

    fn copy_pos_id(&mut self, id: PosId) -> PosId {
        let pos = self.state.infer.arena.get_pos(id);
        let pos = self.copy_pos(pos);
        self.state.infer.alloc_pos(pos)
    }

    fn copy_neg_id(&mut self, id: NegId) -> NegId {
        let neg = self.state.infer.arena.get_neg(id);
        let neg = self.copy_neg(neg);
        self.state.infer.alloc_neg(neg)
    }

    fn copy_pos(&mut self, pos: Pos) -> Pos {
        match pos {
            Pos::Bot => Pos::Bot,
            Pos::Var(tv) => Pos::Var(self.copy_tv(tv)),
            Pos::Atom(atom) => Pos::Atom(self.copy_effect_atom(atom)),
            Pos::Forall(vars, body) => Pos::Forall(
                vars.into_iter().map(|var| self.copy_tv(var)).collect(),
                self.copy_pos_id(body),
            ),
            Pos::Con(path, args) => Pos::Con(
                replace_copied_effect_path(
                    &path,
                    self.source_path,
                    self.source_path_aliases,
                    self.dest_path,
                ),
                args.into_iter()
                    .map(|(pos, neg)| (self.copy_pos_id(pos), self.copy_neg_id(neg)))
                    .collect(),
            ),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Pos::Fun {
                arg: self.copy_neg_id(arg),
                arg_eff: self.copy_neg_id(arg_eff),
                ret_eff: self.copy_pos_id(ret_eff),
                ret: self.copy_pos_id(ret),
            },
            Pos::Record(fields) => Pos::Record(
                fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.copy_pos_id(field.value),
                        optional: field.optional,
                    })
                    .collect(),
            ),
            Pos::RecordTailSpread { fields, tail } => Pos::RecordTailSpread {
                fields: fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.copy_pos_id(field.value),
                        optional: field.optional,
                    })
                    .collect(),
                tail: self.copy_pos_id(tail),
            },
            Pos::RecordHeadSpread { tail, fields } => Pos::RecordHeadSpread {
                tail: self.copy_pos_id(tail),
                fields: fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.copy_pos_id(field.value),
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
                                .map(|payload| self.copy_pos_id(payload))
                                .collect(),
                        )
                    })
                    .collect(),
            ),
            Pos::Tuple(items) => Pos::Tuple(
                items
                    .into_iter()
                    .map(|item| self.copy_pos_id(item))
                    .collect(),
            ),
            Pos::Row(items, tail) => Pos::Row(
                items
                    .into_iter()
                    .map(|item| self.copy_pos_id(item))
                    .collect(),
                self.copy_pos_id(tail),
            ),
            Pos::Union(lhs, rhs) => Pos::Union(self.copy_pos_id(lhs), self.copy_pos_id(rhs)),
            Pos::Raw(tv) => Pos::Raw(self.copy_tv(tv)),
        }
    }

    fn copy_neg(&mut self, neg: Neg) -> Neg {
        match neg {
            Neg::Top => Neg::Top,
            Neg::Var(tv) => Neg::Var(self.copy_tv(tv)),
            Neg::Atom(atom) => Neg::Atom(self.copy_effect_atom(atom)),
            Neg::Forall(vars, body) => Neg::Forall(
                vars.into_iter().map(|var| self.copy_tv(var)).collect(),
                self.copy_neg_id(body),
            ),
            Neg::Con(path, args) => Neg::Con(
                replace_copied_effect_path(
                    &path,
                    self.source_path,
                    self.source_path_aliases,
                    self.dest_path,
                ),
                args.into_iter()
                    .map(|(pos, neg)| (self.copy_pos_id(pos), self.copy_neg_id(neg)))
                    .collect(),
            ),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => Neg::Fun {
                arg: self.copy_pos_id(arg),
                arg_eff: self.copy_pos_id(arg_eff),
                ret_eff: self.copy_neg_id(ret_eff),
                ret: self.copy_neg_id(ret),
            },
            Neg::Record(fields) => Neg::Record(
                fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.copy_neg_id(field.value),
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
                                .map(|payload| self.copy_neg_id(payload))
                                .collect(),
                        )
                    })
                    .collect(),
            ),
            Neg::Tuple(items) => Neg::Tuple(
                items
                    .into_iter()
                    .map(|item| self.copy_neg_id(item))
                    .collect(),
            ),
            Neg::Row(items, tail) => Neg::Row(
                items
                    .into_iter()
                    .map(|item| self.copy_neg_id(item))
                    .collect(),
                self.copy_neg_id(tail),
            ),
            Neg::Intersection(lhs, rhs) => {
                Neg::Intersection(self.copy_neg_id(lhs), self.copy_neg_id(rhs))
            }
        }
    }

    fn copy_effect_atom(&mut self, atom: EffectAtom) -> EffectAtom {
        if atom.path == *self.source_path {
            return EffectAtom {
                path: self.dest_path.clone(),
                args: self.dest_args.to_vec(),
            };
        }
        EffectAtom {
            path: replace_copied_effect_path(
                &atom.path,
                self.source_path,
                self.source_path_aliases,
                self.dest_path,
            ),
            args: atom
                .args
                .into_iter()
                .map(|(pos, neg)| (self.copy_tv(pos), self.copy_tv(neg)))
                .collect(),
        }
    }
}
