//! Extracted body lowering methods.

use super::super::*;
use super::*;

impl BodyLowerer {
    pub(super) fn lower_role_method_binding(
        &mut self,
        node: &Cst,
        module: ModuleId,
        role: &ModuleTypeDecl,
        method: &RoleMethodDecl,
        role_inputs: &[String],
        role_associated: &[String],
    ) {
        let Some(expr) = binding_body_expr(node) else {
            self.push_missing_body_for_decl(method.def, method.name.clone());
            return;
        };
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(method.def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: method.def,
                root,
            }));

        let role_path = self
            .modules
            .type_decl_path(role)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        let lowered = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            module,
            method.order,
            method.def,
            &mut self.labels,
        )
        .with_local_method_scope(self.local_method_scope)
        .lower_role_method_body_expr(
            &expr,
            &binding_arg_patterns(node),
            method.receiver.clone(),
            role_path,
            role_inputs,
            role_associated,
            binding_type_expr(node),
        );
        match lowered {
            Ok(computation) => {
                self.finish_binding(method.def, method.name.clone(), root, computation, true);
            }
            Err(error) => self.push_registered_expr_error(method.def, method.name.clone(), error),
        }
        self.session.infer.restore_level(previous_level);
    }

    pub(super) fn lower_act_method_binding_with_aliases(
        &mut self,
        node: &Cst,
        module: ModuleId,
        method: &ActMethodDecl,
        type_var_aliases: &[(String, String)],
        type_name_aliases: &[(String, TypeDeclId)],
    ) {
        let Some(expr) = binding_body_expr(node) else {
            self.push_missing_body_for_decl(method.def, method.name.clone());
            return;
        };
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(method.def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: method.def,
                root,
            }));

        let lowered = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            module,
            method.order,
            method.def,
            &mut self.labels,
        )
        .with_local_method_scope(self.local_method_scope)
        .with_type_var_aliases(type_var_aliases)
        .with_type_name_aliases(type_name_aliases)
        .lower_act_method_body_expr(
            &expr,
            &binding_arg_patterns(node),
            method.receiver.clone(),
            method.owner,
            binding_type_expr(node),
        );
        match lowered {
            Ok(computation) => {
                self.finish_binding(method.def, method.name.clone(), root, computation, true);
            }
            Err(error) => self.push_registered_expr_error(method.def, method.name.clone(), error),
        }
        self.session.infer.restore_level(previous_level);
    }

    pub(super) fn lower_type_method_binding(
        &mut self,
        node: &Cst,
        module: ModuleId,
        owner: &ModuleTypeDecl,
        method: &TypeMethodDecl,
        type_vars: &[String],
    ) {
        let Some(expr) = binding_body_expr(node) else {
            self.push_missing_body_for_decl(method.def, method.name.clone());
            return;
        };
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(method.def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: method.def,
                root,
            }));

        let self_alias = AnnSelfAlias {
            owner: owner.id,
            type_vars: type_vars.to_vec(),
        };
        let lowered = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            module,
            method.order,
            method.def,
            &mut self.labels,
        )
        .with_local_method_scope(self.local_method_scope)
        .with_self_alias(Some(self_alias.clone()))
        .lower_type_method_body_expr(
            &expr,
            &binding_arg_patterns(node),
            method.receiver.clone(),
            method.receiver_kind,
            owner.id,
            &self_alias.type_vars,
            binding_type_expr(node),
        );
        match lowered {
            Ok(computation) => {
                self.finish_binding(method.def, method.name.clone(), root, computation, true);
            }
            Err(error) => self.push_registered_expr_error(method.def, method.name.clone(), error),
        }
        self.session.infer.restore_level(previous_level);
    }

    pub(super) fn connect_binding_annotation(
        &mut self,
        node: &Cst,
        module: ModuleId,
        site: ModuleOrder,
        self_alias: Option<AnnSelfAlias>,
        type_var_aliases: &[(String, String)],
        type_name_aliases: &[(String, TypeDeclId)],
        root: TypeVar,
        computation: Computation,
    ) -> Result<(), LoweringError> {
        let Some(type_expr) = binding_type_expr(node) else {
            return Ok(());
        };
        let mut builder = ann_type_builder(&self.modules, module, site, self_alias);
        add_type_var_aliases(&mut builder, type_var_aliases);
        add_type_name_aliases(&mut builder, type_name_aliases);
        let ann = builder
            .build_type_expr(&type_expr)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        self.check_binding_annotation_type(computation.value, &ann)?;
        AnnConstraintLowerer::new(&mut self.session.infer, &self.modules)
            .connect_computation(
                AnnComputationTarget {
                    value: root,
                    effect: computation.effect,
                },
                &ann,
            )
            .map_err(|error| LoweringError::AnnotationConstraint { error })?;
        Ok(())
    }

    pub(super) fn check_binding_annotation_type(
        &self,
        value: TypeVar,
        ann: &AnnType,
    ) -> Result<(), LoweringError> {
        let expected = signature_from_ann_type(ann);
        let actual = compact_type_var(self.session.infer.constraints(), value);
        if let Some((actual, expected)) = builtin_annotation_mismatch(&actual.root, &expected) {
            return Err(LoweringError::TypeMismatch {
                actual: actual.surface_name().to_string(),
                expected: expected.surface_name().to_string(),
            });
        }
        Ok(())
    }

    pub(super) fn finish_binding(
        &mut self,
        def: poly::expr::DefId,
        name: Name,
        root: TypeVar,
        computation: Computation,
        connect_body: bool,
    ) {
        let Some(current) = self.session.poly.defs.get_mut(def) else {
            self.errors.push(BodyLoweringError::NonLetDef { def, name });
            self.finish_failed_def(def);
            return;
        };
        let Def::Let { body, .. } = current else {
            self.errors.push(BodyLoweringError::NonLetDef { def, name });
            self.finish_failed_def(def);
            return;
        };

        *body = Some(computation.expr);
        if connect_body {
            self.constrain_def_body(root, computation.value);
        }
        let fetch = BindingFetch::from_evaluation(computation.evaluation);
        self.session.record_binding_fetch(def, fetch);
        if fetch.runs_computation() && !self.suppress_runtime_roots {
            self.session
                .poly
                .runtime_roots
                .push(poly::expr::RuntimeRoot::ComputedDef(def));
        }
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::DefFinished { def }));
    }

    pub(super) fn register_failed_def(&mut self, def: poly::expr::DefId) {
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef { def, root }));
        self.finish_failed_def(def);
        self.session.infer.restore_level(previous_level);
    }

    pub(super) fn push_registered_expr_error(
        &mut self,
        def: poly::expr::DefId,
        name: Name,
        error: LoweringError,
    ) {
        self.errors
            .push(BodyLoweringError::Expr { def, name, error });
        self.finish_failed_def(def);
    }

    pub(super) fn push_missing_body_for_decl(&mut self, def: poly::expr::DefId, name: Name) {
        self.errors
            .push(BodyLoweringError::MissingBody { def, name });
        self.register_failed_def(def);
    }

    pub(super) fn finish_failed_def(&mut self, def: poly::expr::DefId) {
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::DefFinished { def }));
    }

    pub(super) fn constrain_def_body(&mut self, root: TypeVar, body: TypeVar) {
        let body_pos = self.session.infer.alloc_pos(Pos::Var(body));
        let root_neg = self.session.infer.alloc_neg(Neg::Var(root));
        self.session.infer.subtype(body_pos, root_neg);
    }

    pub(super) fn next_value_decl(
        &mut self,
        module: ModuleId,
        name: &Name,
    ) -> Option<crate::ModuleValueDecl> {
        let key = (module, name.clone());
        let cursor = self.value_cursors.entry(key).or_default();
        let decls = self.modules.value_decls(module, name);
        while let Some(decl) = decls.get(*cursor).cloned() {
            *cursor += 1;
            if !self.modules.is_act_operation_def(decl.def) {
                return Some(decl);
            }
        }
        None
    }

    pub(super) fn next_module_decl(
        &mut self,
        module: ModuleId,
        name: &Name,
    ) -> Option<ModuleChildDecl> {
        let key = (module, name.clone());
        let cursor = self.module_cursors.entry(key).or_default();
        let decl = self
            .modules
            .module_decls(module, name)
            .get(*cursor)
            .cloned();
        *cursor += usize::from(decl.is_some());
        decl
    }

    pub(super) fn next_type_decl(
        &mut self,
        module: ModuleId,
        name: &Name,
    ) -> Option<ModuleTypeDecl> {
        let key = (module, name.clone());
        let cursor = self.type_cursors.entry(key).or_default();
        let decl = self.modules.type_decls(module, name).get(*cursor).cloned();
        *cursor += usize::from(decl.is_some());
        decl
    }

    pub(super) fn next_role_impl_decl(&mut self, module: ModuleId) -> Option<RoleImplDecl> {
        let cursor = self.impl_cursors.entry(module).or_default();
        let decl = self.modules.role_impls(module).get(*cursor).cloned();
        *cursor += usize::from(decl.is_some());
        decl
    }

    pub(super) fn next_cast_decl(&mut self, module: ModuleId) -> Option<CastDecl> {
        let cursor = self.cast_cursors.entry(module).or_default();
        let decl = self.modules.cast_decls(module).get(*cursor).cloned();
        *cursor += usize::from(decl.is_some());
        decl
    }
}
