use std::collections::BTreeSet;
use std::collections::HashMap;

use crate::diagnostic::ExpectedEdgeId;

use yulang_core_ir as core_ir;

use crate::ast::expr::{
    CatchArmKind, ExprKind, Lit as TirLit, PatKind, RecordPatSpread, RecordSpread, TypedBlock,
    TypedCatchArm, TypedExpr, TypedPat, TypedStmt,
};
use crate::ids::{DefId, RefId, TypeVar};
use crate::lower::LowerState;
use crate::solve::RefFieldProjection;
use crate::solve::role::role_method_info_for_path;
use crate::symbols::{Name, Path};

use super::complete_principal::{
    ApplySlotBounds, ExpectedEdgeEvidence, complete_apply_principal_evidence_from_slot_bounds,
    complete_coerce_principal_evidence, residual_apply_principal_scheme,
};
use super::names::{export_name, export_path};
use super::paths::collect_canonical_binding_paths;
use super::roles::canonical_runtime_export_def;
use super::spine::{collect_apply_spine_with_apps, strip_transparent_wrappers};
use super::types::{
    collect_core_type_vars, export_coalesced_apply_evidence_bounds_with_expected_arg,
    export_relevant_type_bounds_for_tv, export_scheme,
};

pub fn export_expr(
    state: &LowerState,
    expr: &TypedExpr,
    relevant_vars: BTreeSet<core_ir::TypeVar>,
    edge_evidence: &HashMap<ExpectedEdgeId, ExpectedEdgeEvidence>,
) -> core_ir::Expr {
    ExprExporter::new(state, relevant_vars, edge_evidence).export_expr(expr)
}

pub(super) struct ExprExporter<'a> {
    state: &'a LowerState,
    globals: HashMap<DefId, Path>,
    locals: HashMap<DefId, Path>,
    principal_scheme_cache: HashMap<DefId, Option<core_ir::Scheme>>,
    principal_callee_scheme_cache: HashMap<TypeVar, Option<core_ir::Scheme>>,
    relevant_bounds_cache: HashMap<TypeVar, core_ir::TypeBounds>,
    relevant_vars: BTreeSet<core_ir::TypeVar>,
    edge_evidence: &'a HashMap<ExpectedEdgeId, ExpectedEdgeEvidence>,
}

impl<'a> ExprExporter<'a> {
    pub(super) fn new(
        state: &'a LowerState,
        relevant_vars: BTreeSet<core_ir::TypeVar>,
        edge_evidence: &'a HashMap<ExpectedEdgeId, ExpectedEdgeEvidence>,
    ) -> Self {
        Self {
            state,
            globals: collect_canonical_binding_paths(state),
            locals: HashMap::new(),
            principal_scheme_cache: HashMap::new(),
            principal_callee_scheme_cache: HashMap::new(),
            relevant_bounds_cache: HashMap::new(),
            relevant_vars,
            edge_evidence,
        }
    }

    fn lookup_edge_evidence(
        &self,
        id: Option<crate::diagnostic::ExpectedEdgeId>,
    ) -> Option<&ExpectedEdgeEvidence> {
        self.edge_evidence.get(&id?)
    }

    fn export_relevant_bounds_for_tv(&mut self, tv: TypeVar) -> core_ir::TypeBounds {
        if let Some(bounds) = self.relevant_bounds_cache.get(&tv) {
            return bounds.clone();
        }
        let bounds = export_relevant_type_bounds_for_tv(&self.state.infer, tv, &self.relevant_vars);
        self.relevant_bounds_cache.insert(tv, bounds.clone());
        bounds
    }

    pub(super) fn export_expr(&mut self, expr: &TypedExpr) -> core_ir::Expr {
        if let Some(exported) = self.export_resolved_role_method_call(expr) {
            return exported;
        }
        match &expr.kind {
            ExprKind::PrimitiveOp(op) => core_ir::Expr::PrimitiveOp(*op),
            ExprKind::Lit(lit) => core_ir::Expr::Lit(export_lit(lit)),
            ExprKind::Var(def) => core_ir::Expr::Var(self.path_for_def(*def)),
            ExprKind::Ref(ref_id) => core_ir::Expr::Var(self.path_for_ref(*ref_id)),
            ExprKind::App {
                callee,
                arg,
                callee_edge_id,
                expected_callee_tv,
                arg_edge_id,
                expected_arg_tv,
            } => core_ir::Expr::Apply {
                callee: Box::new(self.export_expr(callee)),
                arg: Box::new(self.export_expr(arg)),
                evidence: Some(self.export_apply_evidence(
                    callee,
                    arg,
                    expr,
                    *callee_edge_id,
                    *expected_callee_tv,
                    *arg_edge_id,
                    *expected_arg_tv,
                    true,
                )),
            },
            ExprKind::RefSet { reference, value } => self.export_ref_set(expr, reference, value),
            ExprKind::Lam(def, body) => {
                let param = self.local_name_for_def(*def);
                let param_effect_annotation =
                    self.state.lambda_param_effect_annotations.get(def).cloned();
                let param_function_allowed_effects = self
                    .state
                    .lambda_param_function_allowed_effects
                    .get(def)
                    .cloned();
                let body = self.with_lambda_scope(*def, |this| this.export_expr(body));
                let body = self.wrap_lambda_param_pattern(*def, &param, body);
                core_ir::Expr::Lambda {
                    param,
                    param_effect_annotation,
                    param_function_allowed_effects,
                    body: Box::new(body),
                }
            }
            ExprKind::Tuple(items) => {
                core_ir::Expr::Tuple(items.iter().map(|item| self.export_expr(item)).collect())
            }
            ExprKind::Record { fields, spread } => core_ir::Expr::Record {
                fields: fields
                    .iter()
                    .map(|(name, value)| core_ir::RecordExprField {
                        name: export_name(name),
                        value: self.export_expr(value),
                    })
                    .collect(),
                spread: spread.as_ref().map(|spread| match spread {
                    RecordSpread::Head(expr) => {
                        core_ir::RecordSpreadExpr::Head(Box::new(self.export_expr(expr)))
                    }
                    RecordSpread::Tail(expr) => {
                        core_ir::RecordSpreadExpr::Tail(Box::new(self.export_expr(expr)))
                    }
                }),
            },
            ExprKind::PolyVariant(name, payloads) => core_ir::Expr::Variant {
                tag: export_name(name),
                value: payloads
                    .first()
                    .map(|payload| Box::new(self.export_expr(payload))),
            },
            ExprKind::Select { recv, name } => {
                if let Some(projection) = self.state.infer.resolved_ref_field_projection(expr.tv) {
                    self.export_ref_field_projection(expr, recv, name, &projection)
                } else if let Some(def) = self.state.infer.resolved_selection_def(expr.tv) {
                    let def = canonical_runtime_export_def(self.state, def);
                    let callee_tv = self.state.def_tvs.get(&def).copied().unwrap_or(expr.tv);
                    core_ir::Expr::Apply {
                        callee: Box::new(core_ir::Expr::Var(self.path_for_def(def))),
                        arg: Box::new(self.export_expr(recv)),
                        evidence: Some(core_ir::ApplyEvidence {
                            callee_source_edge: None,
                            arg_source_edge: None,
                            callee: self.export_relevant_bounds_for_tv(callee_tv),
                            expected_callee: None,
                            arg: self.export_relevant_bounds_for_tv(recv.tv),
                            expected_arg: None,
                            result: self.export_relevant_bounds_for_tv(expr.tv),
                            principal_callee: None,
                            substitutions: Vec::new(),
                            substitution_candidates: Vec::new(),
                            role_method: false,
                            principal_elaboration: None,
                        }),
                    }
                } else if let Some(def) = self.state.infer.resolve_extension_method_def(name) {
                    let def = canonical_runtime_export_def(self.state, def);
                    let callee_tv = self.state.def_tvs.get(&def).copied().unwrap_or(expr.tv);
                    core_ir::Expr::Apply {
                        callee: Box::new(core_ir::Expr::Var(self.path_for_def(def))),
                        arg: Box::new(self.export_expr(recv)),
                        evidence: Some(core_ir::ApplyEvidence {
                            callee_source_edge: None,
                            arg_source_edge: None,
                            callee: self.export_relevant_bounds_for_tv(callee_tv),
                            expected_callee: None,
                            arg: self.export_relevant_bounds_for_tv(recv.tv),
                            expected_arg: None,
                            result: self.export_relevant_bounds_for_tv(expr.tv),
                            principal_callee: None,
                            substitutions: Vec::new(),
                            substitution_candidates: Vec::new(),
                            role_method: false,
                            principal_elaboration: None,
                        }),
                    }
                } else {
                    core_ir::Expr::Select {
                        base: Box::new(self.export_expr(recv)),
                        field: export_name(name),
                    }
                }
            }
            ExprKind::Match(scrutinee, arms) => core_ir::Expr::Match {
                scrutinee: Box::new(self.export_expr(scrutinee)),
                arms: arms
                    .iter()
                    .map(|arm| core_ir::MatchArm {
                        pattern: self.export_pat(&arm.pat),
                        guard: arm.guard.as_ref().map(|guard| self.export_expr(guard)),
                        body: self.export_expr(&arm.body),
                    })
                    .collect(),
                evidence: Some(core_ir::JoinEvidence {
                    result: self.export_relevant_bounds_for_tv(expr.tv),
                }),
            },
            ExprKind::Catch(body, arms) => core_ir::Expr::Handle {
                body: Box::new(self.export_expr(body)),
                arms: arms.iter().map(|arm| self.export_catch_arm(arm)).collect(),
                evidence: Some(core_ir::JoinEvidence {
                    result: self.export_relevant_bounds_for_tv(expr.tv),
                }),
            },
            ExprKind::Block(block) => self.export_block(block),
            ExprKind::Coerce {
                edge_id,
                actual_tv,
                expected_tv,
                expr,
            } => core_ir::Expr::Coerce {
                expr: Box::new(self.export_expr(expr)),
                evidence: Some(complete_coerce_principal_evidence(
                    &self.state.infer,
                    *edge_id,
                    *actual_tv,
                    *expected_tv,
                )),
            },
            ExprKind::PackForall(var, expr) => core_ir::Expr::Pack {
                var: core_ir::TypeVar(format!("t{}", var.0)),
                expr: Box::new(self.export_expr(expr)),
            },
        }
    }

    fn export_ref_field_projection(
        &mut self,
        expr: &TypedExpr,
        recv: &TypedExpr,
        name: &Name,
        projection: &RefFieldProjection,
    ) -> core_ir::Expr {
        let parent_name = core_ir::Name(format!("__ref_field_parent_t{}", expr.tv.0));
        let unit_get = core_ir::Name(format!("__ref_field_get_unit_t{}", expr.tv.0));
        let unit_update = core_ir::Name(format!("__ref_field_update_unit_t{}", expr.tv.0));
        let old_name = core_ir::Name(format!("__ref_field_old_t{}", expr.tv.0));
        let resume_name = core_ir::Name(format!("__ref_field_resume_t{}", expr.tv.0));
        let new_field_name = core_ir::Name(format!("__ref_field_new_t{}", expr.tv.0));

        let get_body = apply_expr(
            core_ir::Expr::Var(self.path_for_def(projection.field.def)),
            apply_unit(apply_expr(
                core_ir::Expr::Var(std_var_ref_get_path()),
                local_var(&parent_name),
            )),
        );

        let update_body = core_ir::Expr::Handle {
            body: Box::new(apply_unit(apply_expr(
                core_ir::Expr::Var(std_var_ref_update_effect_path()),
                local_var(&parent_name),
            ))),
            arms: vec![core_ir::HandleArm {
                effect: std_ref_update_update_path(),
                payload: core_ir::Pattern::Bind(old_name.clone()),
                resume: Some(resume_name.clone()),
                guard: None,
                body: core_ir::Expr::Block {
                    stmts: vec![core_ir::Stmt::Let {
                        pattern: core_ir::Pattern::Bind(new_field_name.clone()),
                        value: apply_expr(
                            core_ir::Expr::Var(std_ref_update_update_path()),
                            self.export_ref_field_old_value(projection, name, &old_name),
                        ),
                    }],
                    tail: Some(Box::new(apply_expr(
                        local_var(&resume_name),
                        self.export_ref_field_reconstruction(
                            projection,
                            name,
                            &old_name,
                            local_var(&new_field_name),
                        ),
                    ))),
                },
            }],
            evidence: Some(core_ir::JoinEvidence {
                result: core_ir::TypeBounds::exact(core_unit_type()),
            }),
        };

        let child_ref = apply_expr(
            core_ir::Expr::Var(std_var_ref_path()),
            core_ir::Expr::Record {
                fields: vec![
                    core_ir::RecordExprField {
                        name: core_ir::Name("get".to_string()),
                        value: core_ir::Expr::Lambda {
                            param: unit_get,
                            param_effect_annotation: None,
                            param_function_allowed_effects: None,
                            body: Box::new(get_body),
                        },
                    },
                    core_ir::RecordExprField {
                        name: core_ir::Name("update_effect".to_string()),
                        value: core_ir::Expr::Lambda {
                            param: unit_update,
                            param_effect_annotation: None,
                            param_function_allowed_effects: None,
                            body: Box::new(update_body),
                        },
                    },
                ],
                spread: None,
            },
        );

        core_ir::Expr::Block {
            stmts: vec![core_ir::Stmt::Let {
                pattern: core_ir::Pattern::Bind(parent_name),
                value: self.export_expr(recv),
            }],
            tail: Some(Box::new(child_ref)),
        }
    }

    fn export_apply_evidence(
        &mut self,
        callee: &TypedExpr,
        arg: &TypedExpr,
        result: &TypedExpr,
        callee_source_edge: Option<crate::diagnostic::ExpectedEdgeId>,
        expected_callee_tv: TypeVar,
        arg_source_edge: Option<crate::diagnostic::ExpectedEdgeId>,
        expected_arg_tv: TypeVar,
        include_principal: bool,
    ) -> core_ir::ApplyEvidence {
        let role_method = self.is_role_method_callee(callee);
        let expected_callee = self.export_relevant_bounds_for_tv(expected_callee_tv);
        let expected_arg = self.export_relevant_bounds_for_tv(expected_arg_tv);
        let mut evidence = if std::env::var_os("YULANG_COALESCE_APPLY_EVIDENCE").is_some() {
            let (callee_bounds, arg, expected_arg, result) =
                export_coalesced_apply_evidence_bounds_with_expected_arg(
                    &self.state.infer,
                    callee.tv,
                    arg.tv,
                    expected_arg_tv,
                    result.tv,
                    &self.relevant_vars,
                );
            core_ir::ApplyEvidence {
                callee_source_edge: callee_source_edge.map(|id| id.0),
                arg_source_edge: arg_source_edge.map(|id| id.0),
                callee: callee_bounds,
                expected_callee: Some(expected_callee),
                arg,
                expected_arg: Some(expected_arg),
                result,
                principal_callee: None,
                substitutions: Vec::new(),
                substitution_candidates: Vec::new(),
                role_method,
                principal_elaboration: None,
            }
        } else {
            core_ir::ApplyEvidence {
                callee_source_edge: callee_source_edge.map(|id| id.0),
                arg_source_edge: arg_source_edge.map(|id| id.0),
                callee: if self.relevant_vars.is_empty() && !role_method {
                    core_ir::TypeBounds::default()
                } else {
                    self.export_relevant_bounds_for_tv(callee.tv)
                },
                expected_callee: Some(expected_callee),
                arg: self.export_relevant_bounds_for_tv(arg.tv),
                expected_arg: Some(expected_arg),
                result: self.export_relevant_bounds_for_tv(result.tv),
                principal_callee: None,
                substitutions: Vec::new(),
                substitution_candidates: Vec::new(),
                role_method,
                principal_elaboration: None,
            }
        };
        let principal_target = self.principal_callee_target(callee);
        if include_principal
            && export_apply_substitutions_enabled()
            && let Some(principal_scheme) = self.principal_callee_scheme(callee)
        {
            evidence.principal_callee = Some(principal_scheme.body.clone());
            let slot_bounds = ApplySlotBounds {
                callee: evidence.callee.clone(),
                arg: evidence.arg.clone(),
                result: evidence.result.clone(),
            };
            if let Some(principal) = complete_apply_principal_evidence_from_slot_bounds(
                &self.state.infer,
                principal_scheme,
                arg.tv,
                result.tv,
                &slot_bounds,
                self.lookup_edge_evidence(callee_source_edge),
                self.lookup_edge_evidence(arg_source_edge),
            ) {
                evidence.principal_callee = Some(principal.principal_callee);
                evidence.substitutions = principal.substitutions;
                evidence.substitution_candidates = principal.substitution_candidates;
            }
        }
        if include_principal
            && export_principal_elaboration_plans_enabled()
            && principal_elaboration_plan_needed(&evidence)
        {
            evidence.principal_elaboration =
                build_principal_elaboration_plan(&evidence, principal_target);
        }
        evidence
    }

    fn principal_callee_scheme(&mut self, expr: &TypedExpr) -> Option<core_ir::Scheme> {
        if let Some(cached) = self.principal_callee_scheme_cache.get(&expr.tv) {
            return cached.clone();
        }
        let scheme = match &expr.kind {
            ExprKind::Var(def) => {
                self.intern_principal_scheme_for_def(canonical_runtime_export_def(self.state, *def))
            }
            ExprKind::Ref(ref_id) => self.state.ctx.refs.get(*ref_id).and_then(|def| {
                self.intern_principal_scheme_for_def(canonical_runtime_export_def(self.state, def))
            }),
            ExprKind::App {
                callee: app_callee,
                arg,
                expected_callee_tv: _,
                expected_arg_tv: _,
                ..
            } => {
                let scheme = self.principal_callee_scheme(app_callee)?;
                residual_apply_principal_scheme(
                    &self.state.infer,
                    &scheme,
                    app_callee.tv,
                    arg.tv,
                    expr.tv,
                )
            }
            _ => None,
        }?;
        self.principal_callee_scheme_cache
            .insert(expr.tv, Some(scheme.clone()));
        Some(scheme)
    }

    fn principal_callee_target(&self, expr: &TypedExpr) -> Option<core_ir::Path> {
        match &strip_transparent_wrappers(expr).kind {
            ExprKind::Var(def) => {
                Some(self.path_for_def(canonical_runtime_export_def(self.state, *def)))
            }
            ExprKind::Ref(ref_id) => self
                .state
                .ctx
                .refs
                .get(*ref_id)
                .map(|def| self.path_for_def(canonical_runtime_export_def(self.state, def))),
            ExprKind::App { callee, .. } => self.principal_callee_target(callee),
            _ => None,
        }
    }

    fn export_ref_set(
        &mut self,
        expr: &TypedExpr,
        reference: &TypedExpr,
        value: &TypedExpr,
    ) -> core_ir::Expr {
        let ref_name = core_ir::Name(format!("__ref_set_ref_t{}", expr.tv.0));
        let old_name = core_ir::Name(format!("__ref_set_old_t{}", expr.tv.0));
        let resume_name = core_ir::Name(format!("__ref_set_resume_t{}", expr.tv.0));
        core_ir::Expr::Block {
            stmts: vec![core_ir::Stmt::Let {
                pattern: core_ir::Pattern::Bind(ref_name.clone()),
                value: self
                    .export_ref_index_projection(reference)
                    .unwrap_or_else(|| self.export_expr(reference)),
            }],
            tail: Some(Box::new(core_ir::Expr::Handle {
                body: Box::new(apply_unit(apply_expr(
                    core_ir::Expr::Var(std_var_ref_update_effect_path()),
                    local_var(&ref_name),
                ))),
                arms: vec![core_ir::HandleArm {
                    effect: std_ref_update_update_path(),
                    payload: core_ir::Pattern::Bind(old_name),
                    resume: Some(resume_name.clone()),
                    guard: None,
                    body: apply_expr(local_var(&resume_name), self.export_expr(value)),
                }],
                evidence: Some(core_ir::JoinEvidence {
                    result: core_ir::TypeBounds::exact(core_unit_type()),
                }),
            })),
        }
    }

    fn export_ref_index_projection(&mut self, expr: &TypedExpr) -> Option<core_ir::Expr> {
        let (recv, index) = ref_index_projection_parts(expr)?;
        if !self.is_ref_projection_receiver(recv) {
            return None;
        }
        let parent_name = core_ir::Name(format!("__ref_index_parent_t{}", expr.tv.0));
        let index_name = core_ir::Name(format!("__ref_index_key_t{}", expr.tv.0));
        let unit_get = core_ir::Name(format!("__ref_index_get_unit_t{}", expr.tv.0));
        let unit_update = core_ir::Name(format!("__ref_index_update_unit_t{}", expr.tv.0));
        let old_name = core_ir::Name(format!("__ref_index_old_t{}", expr.tv.0));
        let resume_name = core_ir::Name(format!("__ref_index_resume_t{}", expr.tv.0));
        let new_item_name = core_ir::Name(format!("__ref_index_new_t{}", expr.tv.0));

        let get_body = apply_expr(
            apply_expr(
                core_ir::Expr::Var(std_list_index_raw_path()),
                apply_unit(apply_expr(
                    core_ir::Expr::Var(std_var_ref_get_path()),
                    local_var(&parent_name),
                )),
            ),
            local_var(&index_name),
        );

        let old_item = apply_expr(
            apply_expr(
                core_ir::Expr::Var(std_list_index_raw_path()),
                local_var(&old_name),
            ),
            local_var(&index_name),
        );
        let end_index = apply_expr(
            apply_expr(
                core_ir::Expr::PrimitiveOp(core_ir::PrimitiveOp::IntAdd),
                local_var(&index_name),
            ),
            core_ir::Expr::Lit(core_ir::Lit::Int("1".to_string())),
        );
        let replacement = apply_expr(
            core_ir::Expr::PrimitiveOp(core_ir::PrimitiveOp::ListSingleton),
            local_var(&new_item_name),
        );
        let rebuilt_parent = apply_expr(
            apply_expr(
                apply_expr(
                    apply_expr(
                        core_ir::Expr::PrimitiveOp(core_ir::PrimitiveOp::ListSpliceRaw),
                        local_var(&old_name),
                    ),
                    local_var(&index_name),
                ),
                end_index,
            ),
            replacement,
        );

        let update_body = core_ir::Expr::Handle {
            body: Box::new(apply_unit(apply_expr(
                core_ir::Expr::Var(std_var_ref_update_effect_path()),
                local_var(&parent_name),
            ))),
            arms: vec![core_ir::HandleArm {
                effect: std_ref_update_update_path(),
                payload: core_ir::Pattern::Bind(old_name),
                resume: Some(resume_name.clone()),
                guard: None,
                body: core_ir::Expr::Block {
                    stmts: vec![core_ir::Stmt::Let {
                        pattern: core_ir::Pattern::Bind(new_item_name),
                        value: apply_expr(
                            core_ir::Expr::Var(std_ref_update_update_path()),
                            old_item,
                        ),
                    }],
                    tail: Some(Box::new(apply_expr(
                        local_var(&resume_name),
                        rebuilt_parent,
                    ))),
                },
            }],
            evidence: Some(core_ir::JoinEvidence {
                result: core_ir::TypeBounds::exact(core_unit_type()),
            }),
        };

        let child_ref = apply_expr(
            core_ir::Expr::Var(std_var_ref_path()),
            core_ir::Expr::Record {
                fields: vec![
                    core_ir::RecordExprField {
                        name: core_ir::Name("get".to_string()),
                        value: core_ir::Expr::Lambda {
                            param: unit_get,
                            param_effect_annotation: None,
                            param_function_allowed_effects: None,
                            body: Box::new(get_body),
                        },
                    },
                    core_ir::RecordExprField {
                        name: core_ir::Name("update_effect".to_string()),
                        value: core_ir::Expr::Lambda {
                            param: unit_update,
                            param_effect_annotation: None,
                            param_function_allowed_effects: None,
                            body: Box::new(update_body),
                        },
                    },
                ],
                spread: None,
            },
        );

        Some(core_ir::Expr::Block {
            stmts: vec![
                core_ir::Stmt::Let {
                    pattern: core_ir::Pattern::Bind(parent_name),
                    value: self.export_expr(recv),
                },
                core_ir::Stmt::Let {
                    pattern: core_ir::Pattern::Bind(index_name),
                    value: self.export_expr(index),
                },
            ],
            tail: Some(Box::new(child_ref)),
        })
    }

    fn is_ref_projection_receiver(&self, expr: &TypedExpr) -> bool {
        match &strip_transparent_wrappers(expr).kind {
            ExprKind::Ref(_) => true,
            ExprKind::Var(def) => self
                .state
                .def_name(*def)
                .is_some_and(|name| name.0.starts_with('&')),
            _ => false,
        }
    }

    fn export_ref_field_reconstruction(
        &mut self,
        projection: &RefFieldProjection,
        target_name: &Name,
        old_name: &core_ir::Name,
        target_value: core_ir::Expr,
    ) -> core_ir::Expr {
        let old = local_var(old_name);
        let mut fields = Vec::new();
        for field in &projection.fields {
            let selected_old_field = apply_expr(
                core_ir::Expr::Var(self.path_for_def(field.def)),
                old.clone(),
            );
            let value = if field.name == *target_name {
                target_value.clone()
            } else {
                selected_old_field
            };
            fields.push(core_ir::RecordExprField {
                name: export_name(&field.name),
                value,
            });
        }
        apply_expr(
            core_ir::Expr::Var(self.path_for_def(projection.constructor)),
            core_ir::Expr::Record {
                fields,
                spread: None,
            },
        )
    }

    fn export_ref_field_old_value(
        &mut self,
        projection: &RefFieldProjection,
        target_name: &Name,
        old_name: &core_ir::Name,
    ) -> core_ir::Expr {
        let old = local_var(old_name);
        let field = projection
            .fields
            .iter()
            .find(|field| field.name == *target_name)
            .unwrap_or(&projection.field);
        apply_expr(core_ir::Expr::Var(self.path_for_def(field.def)), old)
    }

    fn export_block(&mut self, block: &TypedBlock) -> core_ir::Expr {
        core_ir::Expr::Block {
            stmts: block
                .stmts
                .iter()
                .map(|stmt| self.export_stmt(stmt))
                .collect(),
            tail: block
                .tail
                .as_ref()
                .map(|tail| Box::new(self.export_expr(tail))),
        }
    }

    fn export_stmt(&mut self, stmt: &TypedStmt) -> core_ir::Stmt {
        match stmt {
            TypedStmt::Let(pattern, value) => core_ir::Stmt::Let {
                pattern: self.export_pat(pattern),
                value: self.export_expr(value),
            },
            TypedStmt::Expr(expr) => core_ir::Stmt::Expr(self.export_expr(expr)),
            TypedStmt::Module(def, body) => core_ir::Stmt::Module {
                def: self.path_for_def(*def),
                body: Box::new(self.export_block(body)),
            },
        }
    }

    fn export_catch_arm(&mut self, arm: &TypedCatchArm) -> core_ir::HandleArm {
        match &arm.kind {
            CatchArmKind::Value(pattern, body) => core_ir::HandleArm {
                effect: core_ir::Path::default(),
                payload: self.export_pat(pattern),
                resume: None,
                guard: arm.guard.as_ref().map(|guard| self.export_expr(guard)),
                body: self.export_expr(body),
            },
            CatchArmKind::Effect {
                op_path,
                pat,
                k,
                body,
            } => core_ir::HandleArm {
                effect: export_path(op_path),
                payload: self.export_pat(pat),
                resume: Some(self.local_name_for_def(*k)),
                guard: arm.guard.as_ref().map(|guard| self.export_expr(guard)),
                body: self.with_local(*k, |this| this.export_expr(body)),
            },
        }
    }

    fn export_pat(&mut self, pat: &TypedPat) -> core_ir::Pattern {
        match &pat.kind {
            PatKind::Wild => core_ir::Pattern::Wildcard,
            PatKind::Lit(lit) => core_ir::Pattern::Lit(export_lit(lit)),
            PatKind::Tuple(items) => {
                core_ir::Pattern::Tuple(items.iter().map(|item| self.export_pat(item)).collect())
            }
            PatKind::List {
                prefix,
                spread,
                suffix,
            } => core_ir::Pattern::List {
                prefix: prefix.iter().map(|item| self.export_pat(item)).collect(),
                spread: spread
                    .as_ref()
                    .map(|spread| Box::new(self.export_pat(spread))),
                suffix: suffix.iter().map(|item| self.export_pat(item)).collect(),
            },
            PatKind::Record { spread, fields } => core_ir::Pattern::Record {
                fields: fields
                    .iter()
                    .map(|field| core_ir::RecordPatternField {
                        name: export_name(&field.name),
                        pattern: self.export_pat(&field.pat),
                        default: field
                            .default
                            .as_ref()
                            .map(|default| self.export_expr(default)),
                    })
                    .collect(),
                spread: spread.as_ref().map(|spread| match spread {
                    RecordPatSpread::Head(pat) => {
                        core_ir::RecordSpreadPattern::Head(Box::new(self.export_pat(pat)))
                    }
                    RecordPatSpread::Tail(pat) => {
                        core_ir::RecordSpreadPattern::Tail(Box::new(self.export_pat(pat)))
                    }
                }),
            },
            PatKind::PolyVariant(name, items) => core_ir::Pattern::Variant {
                tag: export_name(name),
                value: items.first().map(|item| Box::new(self.export_pat(item))),
            },
            PatKind::Con(ref_id, payload) => core_ir::Pattern::Variant {
                tag: self
                    .path_for_ref(*ref_id)
                    .segments
                    .last()
                    .cloned()
                    .unwrap_or(core_ir::Name("unknown".into())),
                value: payload
                    .as_ref()
                    .map(|payload| Box::new(self.export_pat(payload))),
            },
            PatKind::UnresolvedName(name) => core_ir::Pattern::Bind(export_name(name)),
            PatKind::Or(lhs, rhs) => core_ir::Pattern::Or {
                left: Box::new(self.export_pat(lhs)),
                right: Box::new(self.export_pat(rhs)),
            },
            PatKind::As(pattern, def) => core_ir::Pattern::As {
                pattern: Box::new(self.export_pat(pattern)),
                name: self.local_name_for_def(*def),
            },
        }
    }

    fn with_local<T>(&mut self, def: DefId, f: impl FnOnce(&mut Self) -> T) -> T {
        let previous = self.locals.insert(def, self.scoped_local_path(def));
        let out = f(self);
        if let Some(previous) = previous {
            self.locals.insert(def, previous);
        } else {
            self.locals.remove(&def);
        }
        out
    }

    fn with_lambda_scope<T>(&mut self, def: DefId, f: impl FnOnce(&mut Self) -> T) -> T {
        let mut previous = Vec::new();
        previous.push((def, self.locals.insert(def, self.scoped_local_path(def))));
        if let Some(local_defs) = self.state.lambda_local_defs.get(&def) {
            for &local_def in local_defs {
                previous.push((
                    local_def,
                    self.locals
                        .insert(local_def, self.scoped_local_path(local_def)),
                ));
            }
        }
        let out = f(self);
        for (local_def, old) in previous.into_iter().rev() {
            if let Some(old) = old {
                self.locals.insert(local_def, old);
            } else {
                self.locals.remove(&local_def);
            }
        }
        out
    }

    fn wrap_lambda_param_pattern(
        &mut self,
        def: DefId,
        param: &core_ir::Name,
        body: core_ir::Expr,
    ) -> core_ir::Expr {
        let Some(pat) = self.state.lambda_param_pats.get(&def).cloned() else {
            return body;
        };
        if matches!(&pat.kind, PatKind::UnresolvedName(name) if export_name(name) == *param) {
            return body;
        }
        core_ir::Expr::Block {
            stmts: vec![core_ir::Stmt::Let {
                pattern: self.export_pat(&pat),
                value: core_ir::Expr::Var(core_ir::Path::from_name(param.clone())),
            }],
            tail: Some(Box::new(body)),
        }
    }

    fn local_name_for_def(&self, def: DefId) -> core_ir::Name {
        if let Some(name) = self.state.def_name(def) {
            return export_name(name);
        }
        self.path_for_def(def)
            .segments
            .last()
            .cloned()
            .unwrap_or(core_ir::Name(format!("local_{}", def.0)))
    }

    fn path_for_ref(&self, ref_id: RefId) -> core_ir::Path {
        self.state
            .ctx
            .refs
            .get(ref_id)
            .map(|def| self.path_for_def(def))
            .unwrap_or_else(|| core_ir::Path::from_name(core_ir::Name(format!("ref_{}", ref_id.0))))
    }

    fn path_for_def(&self, def: DefId) -> core_ir::Path {
        if let Some(path) = self.locals.get(&def) {
            return export_path(path);
        }
        if let Some(path) = self.globals.get(&def) {
            return export_path(path);
        }
        if let Some(name) = self.state.def_name(def) {
            return core_ir::Path::from_name(export_name(name));
        }
        export_path(&self.synthetic_local_path(def))
    }

    fn synthetic_local_path(&self, def: DefId) -> Path {
        Path {
            segments: vec![Name(format!("local_{}", def.0))],
        }
    }

    fn scoped_local_path(&self, def: DefId) -> Path {
        if let Some(name) = self.state.def_name(def) {
            return Path {
                segments: vec![name.clone()],
            };
        }
        self.synthetic_local_path(def)
    }

    fn export_resolved_role_method_call(&mut self, expr: &TypedExpr) -> Option<core_ir::Expr> {
        let (head, apps) = collect_apply_spine_with_apps(expr);
        let args = apps
            .iter()
            .filter_map(|app| {
                let ExprKind::App { arg, .. } = &app.kind else {
                    return None;
                };
                Some(arg.as_ref())
            })
            .collect::<Vec<_>>();
        let head = strip_transparent_wrappers(head);
        match &head.kind {
            ExprKind::Select { recv, name } => {
                let def = if let Some(def) = self.state.infer.resolved_selection_def(expr.tv) {
                    def
                } else if let Some(def) = self.state.infer.resolved_selection_def(head.tv) {
                    def
                } else {
                    let _ = name;
                    return None;
                };
                let def = canonical_runtime_export_def(self.state, def);
                let mut concrete_callee_type = self
                    .intern_principal_scheme_for_def(def)
                    .map(|scheme| scheme.body);
                let mut out = core_ir::Expr::Var(self.path_for_def(def));
                let _ = concrete_callee_type
                    .as_mut()
                    .and_then(take_rewritten_apply_slot_evidence);
                let slot = concrete_callee_type
                    .as_mut()
                    .and_then(take_rewritten_apply_slot_evidence);
                out = self.export_synthetic_selected_apply(out, def, recv, head, slot);
                for app in apps {
                    let slot = concrete_callee_type
                        .as_mut()
                        .and_then(take_rewritten_apply_slot_evidence);
                    out = self.export_rewritten_apply(out, app, slot);
                }
                Some(out)
            }
            ExprKind::Var(def) => {
                if let Some(resolved) = self.state.infer.resolved_selection_def(expr.tv) {
                    let resolved = self
                        .concrete_role_method_application_def(resolved, head, &args)
                        .unwrap_or(resolved);
                    let resolved = canonical_runtime_export_def(self.state, resolved);
                    let mut concrete_callee_type = self
                        .intern_principal_scheme_for_def(resolved)
                        .map(|scheme| scheme.body);
                    let mut out = core_ir::Expr::Var(self.path_for_def(resolved));
                    for app in apps {
                        let slot = concrete_callee_type
                            .as_mut()
                            .and_then(take_rewritten_apply_slot_evidence);
                        out = self.export_rewritten_apply(out, app, slot);
                    }
                    return Some(out);
                }
                let _ = def;
                None
            }
            _ => None,
        }
    }

    fn export_rewritten_apply(
        &mut self,
        callee_expr: core_ir::Expr,
        app: &TypedExpr,
        concrete_slot: Option<RewrittenApplySlotEvidence>,
    ) -> core_ir::Expr {
        let ExprKind::App {
            arg,
            callee_edge_id,
            expected_callee_tv,
            arg_edge_id,
            expected_arg_tv,
            callee,
            ..
        } = &app.kind
        else {
            return callee_expr;
        };
        if !export_rewritten_apply_slot_evidence_enabled() {
            return core_ir::Expr::Apply {
                callee: Box::new(callee_expr),
                arg: Box::new(self.export_expr(arg)),
                evidence: Some(source_only_apply_evidence(*callee_edge_id, *arg_edge_id)),
            };
        }
        core_ir::Expr::Apply {
            callee: Box::new(callee_expr),
            arg: Box::new(self.export_expr(arg)),
            evidence: Some(self.rewritten_apply_evidence(
                callee,
                arg,
                app,
                *callee_edge_id,
                *expected_callee_tv,
                *arg_edge_id,
                *expected_arg_tv,
                concrete_slot,
            )),
        }
    }

    fn export_synthetic_selected_apply(
        &mut self,
        callee_expr: core_ir::Expr,
        def: DefId,
        recv: &TypedExpr,
        result: &TypedExpr,
        concrete_slot: Option<RewrittenApplySlotEvidence>,
    ) -> core_ir::Expr {
        let principal_scheme = self.intern_principal_scheme_for_def(def);
        let principal_callee = principal_scheme.as_ref().map(|scheme| scheme.body.clone());
        let mut evidence = core_ir::ApplyEvidence {
            callee_source_edge: None,
            arg_source_edge: None,
            callee: principal_callee
                .clone()
                .map(core_ir::TypeBounds::exact)
                .unwrap_or_default(),
            expected_callee: None,
            arg: self.export_relevant_bounds_for_tv(recv.tv),
            expected_arg: None,
            result: self.export_relevant_bounds_for_tv(result.tv),
            principal_callee,
            substitutions: Vec::new(),
            substitution_candidates: Vec::new(),
            role_method: false,
            principal_elaboration: None,
        };
        if let Some(slot) = concrete_slot {
            apply_rewritten_slot_evidence(&mut evidence, slot);
        }
        if export_apply_substitutions_enabled()
            && let Some(principal_scheme) = principal_scheme
        {
            let slot_bounds = ApplySlotBounds {
                callee: evidence.callee.clone(),
                arg: evidence.arg.clone(),
                result: evidence.result.clone(),
            };
            if let Some(principal) = complete_apply_principal_evidence_from_slot_bounds(
                &self.state.infer,
                principal_scheme,
                recv.tv,
                result.tv,
                &slot_bounds,
                None,
                None,
            ) {
                evidence.principal_callee = Some(principal.principal_callee);
                evidence.substitutions = principal.substitutions;
                evidence.substitution_candidates = principal.substitution_candidates;
            }
        }
        core_ir::Expr::Apply {
            callee: Box::new(callee_expr),
            arg: Box::new(self.export_expr(recv)),
            evidence: Some(evidence),
        }
    }

    fn rewritten_apply_evidence(
        &mut self,
        callee: &TypedExpr,
        arg: &TypedExpr,
        app: &TypedExpr,
        callee_source_edge: Option<crate::diagnostic::ExpectedEdgeId>,
        expected_callee_tv: TypeVar,
        arg_source_edge: Option<crate::diagnostic::ExpectedEdgeId>,
        expected_arg_tv: TypeVar,
        concrete_slot: Option<RewrittenApplySlotEvidence>,
    ) -> core_ir::ApplyEvidence {
        let mut evidence = self.export_apply_evidence(
            callee,
            arg,
            app,
            callee_source_edge,
            expected_callee_tv,
            arg_source_edge,
            expected_arg_tv,
            false,
        );
        if let Some(slot) = concrete_slot {
            apply_rewritten_slot_evidence(&mut evidence, slot);
        }
        evidence
    }

    fn concrete_role_method_application_def(
        &self,
        resolved: DefId,
        head: &TypedExpr,
        args: &[&TypedExpr],
    ) -> Option<DefId> {
        if !self.state.infer.is_role_method_def(resolved) {
            return None;
        }
        let ExprKind::Var(_) = &head.kind else {
            return None;
        };
        let info = self.state.infer.role_method_info_for_def(resolved)?;
        let (recv, _) = args.split_first()?;
        self.state
            .infer
            .resolve_concrete_role_method_call_def(&info, Some(recv.tv), &[])
    }

    fn intern_principal_scheme_for_def(&mut self, def: DefId) -> Option<core_ir::Scheme> {
        if let Some(cached) = self.principal_scheme_cache.get(&def) {
            return cached.clone();
        }
        let scheme = self
            .state
            .runtime_export_schemes
            .get(&def)
            .cloned()
            .or_else(|| {
                self.state.compact_scheme_of(def).map(|scheme| {
                    let constraints = self.state.infer.compact_role_constraints_of(def);
                    export_scheme(&self.state.infer, &scheme, &constraints)
                })
            });
        self.principal_scheme_cache.insert(def, scheme.clone());
        scheme
    }

    fn is_role_method_callee(&self, expr: &TypedExpr) -> bool {
        match &strip_transparent_wrappers(expr).kind {
            ExprKind::Var(def) => {
                self.state.infer.is_role_method_def(*def) || self.role_method_path_for_def(*def)
            }
            ExprKind::Ref(ref_id) => {
                self.state
                    .ctx
                    .refs
                    .get(*ref_id)
                    .is_some_and(|def| self.state.infer.is_role_method_def(def))
                    || self
                        .state
                        .ctx
                        .refs
                        .get(*ref_id)
                        .is_some_and(|def| self.role_method_path_for_def(def))
            }
            _ => false,
        }
    }

    fn role_method_path_for_def(&self, def: DefId) -> bool {
        self.globals
            .get(&def)
            .or_else(|| self.locals.get(&def))
            .is_some_and(|path| {
                role_method_info_for_path(&self.state.infer.role_methods, path).is_some()
            })
    }
}

fn apply_unit(callee: core_ir::Expr) -> core_ir::Expr {
    apply_expr(callee, core_ir::Expr::Lit(core_ir::Lit::Unit))
}

fn apply_expr(callee: core_ir::Expr, arg: core_ir::Expr) -> core_ir::Expr {
    core_ir::Expr::Apply {
        callee: Box::new(callee),
        arg: Box::new(arg),
        evidence: None,
    }
}

fn local_var(name: &core_ir::Name) -> core_ir::Expr {
    core_ir::Expr::Var(core_ir::Path::from_name(name.clone()))
}

fn ref_index_projection_parts(expr: &TypedExpr) -> Option<(&TypedExpr, &TypedExpr)> {
    let ExprKind::App {
        callee, arg: index, ..
    } = &strip_transparent_wrappers(expr).kind
    else {
        return None;
    };
    match &strip_transparent_wrappers(callee).kind {
        ExprKind::Select { recv, name } if name.0 == "index" => Some((recv, index)),
        _ => None,
    }
}

fn core_unit_type() -> core_ir::Type {
    core_ir::Type::Named {
        path: core_ir::Path::from_name(core_ir::Name("unit".to_string())),
        args: Vec::new(),
    }
}

fn source_only_apply_evidence(
    callee_source_edge: Option<crate::diagnostic::ExpectedEdgeId>,
    arg_source_edge: Option<crate::diagnostic::ExpectedEdgeId>,
) -> core_ir::ApplyEvidence {
    core_ir::ApplyEvidence {
        callee_source_edge: callee_source_edge.map(|id| id.0),
        arg_source_edge: arg_source_edge.map(|id| id.0),
        callee: core_ir::TypeBounds::default(),
        expected_callee: None,
        arg: core_ir::TypeBounds::default(),
        expected_arg: None,
        result: core_ir::TypeBounds::default(),
        principal_callee: None,
        substitutions: Vec::new(),
        substitution_candidates: Vec::new(),
        role_method: false,
        principal_elaboration: None,
    }
}

#[derive(Debug, Clone)]
struct RewrittenApplySlotEvidence {
    expected_callee: core_ir::Type,
    expected_arg: core_ir::Type,
}

fn take_rewritten_apply_slot_evidence(
    callee: &mut core_ir::Type,
) -> Option<RewrittenApplySlotEvidence> {
    let core_ir::Type::Fun { param, ret, .. } = callee.clone() else {
        return None;
    };
    let expected_callee = callee.clone();
    let expected_arg = *param;
    let result = *ret;
    *callee = result.clone();
    Some(RewrittenApplySlotEvidence {
        expected_callee,
        expected_arg,
    })
}

fn apply_rewritten_slot_evidence(
    evidence: &mut core_ir::ApplyEvidence,
    slot: RewrittenApplySlotEvidence,
) {
    evidence.expected_callee = Some(core_ir::TypeBounds::exact(slot.expected_callee));
    evidence.expected_arg = Some(core_ir::TypeBounds::exact(slot.expected_arg));
}

fn build_principal_elaboration_plan(
    evidence: &core_ir::ApplyEvidence,
    target: Option<core_ir::Path>,
) -> Option<core_ir::PrincipalElaborationPlan> {
    let principal_callee = evidence.principal_callee.clone()?;
    let mut incomplete_reasons = Vec::new();
    if target.is_none() {
        incomplete_reasons.push(core_ir::PrincipalElaborationIncompleteReason::MissingTarget);
    }
    let mut principal_vars = BTreeSet::new();
    collect_core_type_vars(&principal_callee, &mut principal_vars);
    for substitution in &evidence.substitutions {
        principal_vars.remove(&substitution.var);
    }
    for var in principal_vars {
        if evidence
            .substitution_candidates
            .iter()
            .any(|candidate| candidate.var == var)
        {
            incomplete_reasons
                .push(core_ir::PrincipalElaborationIncompleteReason::OpenCandidate(var));
        } else {
            incomplete_reasons
                .push(core_ir::PrincipalElaborationIncompleteReason::MissingSubstitution(var));
        }
    }
    if evidence.expected_arg.is_none() {
        incomplete_reasons.push(core_ir::PrincipalElaborationIncompleteReason::OpenArgType(
            0,
        ));
    }
    if type_bounds_empty(&evidence.result) {
        incomplete_reasons.push(core_ir::PrincipalElaborationIncompleteReason::OpenResultType);
    }
    let complete = incomplete_reasons.is_empty();
    Some(core_ir::PrincipalElaborationPlan {
        target,
        principal_callee,
        substitutions: evidence.substitutions.clone(),
        args: vec![core_ir::PrincipalElaborationArg {
            index: 0,
            intrinsic: evidence.arg.clone(),
            contextual: evidence.expected_arg.clone(),
            expected_runtime: None,
            source_edge: evidence.arg_source_edge,
        }],
        result: core_ir::PrincipalElaborationResult {
            intrinsic: evidence.result.clone(),
            contextual: None,
            expected_runtime: None,
        },
        adapters: Vec::new(),
        complete,
        incomplete_reasons,
    })
}

fn principal_elaboration_plan_needed(evidence: &core_ir::ApplyEvidence) -> bool {
    if evidence.role_method
        || !evidence.substitutions.is_empty()
        || !evidence.substitution_candidates.is_empty()
    {
        return true;
    }
    let Some(principal_callee) = &evidence.principal_callee else {
        return false;
    };
    let mut vars = BTreeSet::new();
    collect_core_type_vars(principal_callee, &mut vars);
    !vars.is_empty()
}

fn type_bounds_empty(bounds: &core_ir::TypeBounds) -> bool {
    bounds.lower.is_none() && bounds.upper.is_none()
}

fn std_var_ref_path() -> core_ir::Path {
    core_ir::Path::new(vec![
        core_ir::Name("std".to_string()),
        core_ir::Name("var".to_string()),
        core_ir::Name("ref".to_string()),
    ])
}

fn std_var_ref_get_path() -> core_ir::Path {
    core_ir::Path::new(vec![
        core_ir::Name("std".to_string()),
        core_ir::Name("var".to_string()),
        core_ir::Name("ref".to_string()),
        core_ir::Name("get".to_string()),
    ])
}

fn std_var_ref_update_effect_path() -> core_ir::Path {
    core_ir::Path::new(vec![
        core_ir::Name("std".to_string()),
        core_ir::Name("var".to_string()),
        core_ir::Name("ref".to_string()),
        core_ir::Name("update_effect".to_string()),
    ])
}

fn std_ref_update_update_path() -> core_ir::Path {
    core_ir::Path::new(vec![
        core_ir::Name("std".to_string()),
        core_ir::Name("var".to_string()),
        core_ir::Name("ref_update".to_string()),
        core_ir::Name("update".to_string()),
    ])
}

fn std_list_index_raw_path() -> core_ir::Path {
    core_ir::Path::new(vec![
        core_ir::Name("std".to_string()),
        core_ir::Name("list".to_string()),
        core_ir::Name("index_raw".to_string()),
    ])
}

fn export_apply_substitutions_enabled() -> bool {
    std::env::var_os("YULANG_DISABLE_PRINCIPAL_ELABORATE").is_none()
        || std::env::var_os("YULANG_EXPORT_APPLY_SUBSTITUTIONS").is_some()
}

fn export_principal_elaboration_plans_enabled() -> bool {
    std::env::var_os("YULANG_DISABLE_PRINCIPAL_ELABORATE").is_none()
        || std::env::var_os("YULANG_EXPORT_PRINCIPAL_ELABORATION_PLANS").is_some()
        || std::env::var_os("YULANG_DEBUG_PRINCIPAL_ELABORATE").is_some()
}

fn export_rewritten_apply_slot_evidence_enabled() -> bool {
    export_apply_substitutions_enabled()
}

fn export_lit(lit: &TirLit) -> core_ir::Lit {
    match lit {
        TirLit::Int(value) => core_ir::Lit::Int(value.to_string()),
        TirLit::Float(value) => core_ir::Lit::Float(value.to_string()),
        TirLit::Str(value) => core_ir::Lit::String(value.clone()),
        TirLit::Bool(value) => core_ir::Lit::Bool(*value),
        TirLit::Unit => core_ir::Lit::Unit,
    }
}
