//! Extracted body lowering methods.

use super::super::*;
use super::*;

impl BodyLowerer {
    pub(super) fn lower_act_decl_body(&mut self, node: &Cst, module: ModuleId) {
        let Some(name) = crate::type_decl_name(node) else {
            return;
        };
        let Some(decl) = self.next_type_decl(module, &name) else {
            return;
        };
        let Some(companion) = self.modules.type_companion(decl.id) else {
            return;
        };
        let mut method_cursor = 0usize;
        let previous_scope = self.local_method_scope.replace(companion);
        if let Some(copy) = self.act_copy_lowering_context(module, &decl) {
            self.lower_act_body_contents(
                &copy.body,
                companion,
                &decl,
                &mut method_cursor,
                copy.type_var_aliases.as_slice(),
                copy.type_name_aliases.as_slice(),
            );
        }
        if let Some(body) = crate::act_decl_body(node) {
            self.lower_act_body_contents(&body, companion, &decl, &mut method_cursor, &[], &[]);
        }
        self.local_method_scope = previous_scope;
    }

    pub(super) fn lower_act_operation_binding(
        &mut self,
        node: &Cst,
        companion: ModuleId,
        decl: &ModuleTypeDecl,
        type_var_aliases: &[(String, String)],
        type_name_aliases: &[(String, TypeDeclId)],
    ) {
        let Some(name) = crate::binding_name(node) else {
            return;
        };
        let Some(def) = self
            .modules
            .value_at(companion, &name, signature_module_path_site())
        else {
            self.errors
                .push(BodyLoweringError::MissingBindingDecl { name });
            return;
        };
        let Some(signature) = binding_type_expr(node) else {
            self.errors.push(BodyLoweringError::Expr {
                def,
                name,
                error: LoweringError::SignatureShapeMismatch {
                    expected: SignatureShape::Function,
                },
            });
            return;
        };
        let Some(operation_decl) = self.modules.act_operation_decl_by_def(def) else {
            self.errors.push(BodyLoweringError::NonLetDef { def, name });
            return;
        };
        let operation_path = self.operation_path(&operation_decl);
        self.session.poly.effect_operations.insert(
            def,
            poly::expr::EffectOperation {
                path: operation_path,
            },
        );

        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef { def, root }));

        let lowered = self.lower_act_operation_type(
            &operation_decl,
            &signature,
            type_var_aliases,
            type_name_aliases,
        );
        match lowered {
            Ok(predicate) => {
                let root_upper = self.session.infer.alloc_neg(Neg::Var(root));
                self.session.infer.subtype(predicate, root_upper);
                self.session
                    .enqueue(AnalysisWork::Scc(SccInput::DefFinished { def }));
            }
            Err(error) => self
                .errors
                .push(BodyLoweringError::Expr { def, name, error }),
        }

        self.session.infer.restore_level(previous_level);

        debug_assert_eq!(decl.id, operation_decl.effect.id);
    }

    pub(super) fn operation_path(&self, operation_decl: &ActOperationDecl) -> Vec<String> {
        self.modules
            .type_decl_path(&operation_decl.effect)
            .segments
            .into_iter()
            .chain(std::iter::once(operation_decl.name.clone()))
            .map(|name| name.0)
            .collect()
    }

    pub(super) fn lower_act_operation_type(
        &mut self,
        operation_decl: &ActOperationDecl,
        signature: &Cst,
        type_var_aliases: &[(String, String)],
        type_name_aliases: &[(String, TypeDeclId)],
    ) -> Result<PosId, LoweringError> {
        let signature = self.act_operation_signature_type(
            operation_decl,
            signature,
            type_var_aliases,
            type_name_aliases,
        )?;
        let mut lowerer = SignatureLowerer::new(&mut self.session.infer, &self.modules);
        lowerer
            .lower_pos(&signature)
            .map_err(|error| LoweringError::SignatureConstraint { error })
    }

    pub(super) fn act_operation_signature_type(
        &self,
        operation_decl: &ActOperationDecl,
        signature: &Cst,
        type_var_aliases: &[(String, String)],
        type_name_aliases: &[(String, TypeDeclId)],
    ) -> Result<SignatureType, LoweringError> {
        let effect_type_vars = self.act_effect_type_var_names(operation_decl.effect.id);
        let mut builder = ann_type_builder(
            &self.modules,
            operation_decl.effect.module,
            operation_decl.effect.order,
            None,
        );
        for name in &effect_type_vars {
            builder.add_bare_type_var(name.clone());
        }
        add_type_var_aliases(&mut builder, type_var_aliases);
        add_type_name_aliases(&mut builder, type_name_aliases);

        let signature = build_signature_type_expr(&mut builder, signature)
            .map_err(|error| LoweringError::AnnotationBuild { error })?;
        let effect_ann = builder.type_decl_application(operation_decl.effect.id, &effect_type_vars);
        let effect = signature_from_ann_type(&effect_ann);
        operation_signature_with_effect(signature, effect).ok_or(
            LoweringError::SignatureShapeMismatch {
                expected: SignatureShape::Function,
            },
        )
    }

    pub(super) fn act_effect_type_var_names(&self, id: TypeDeclId) -> Vec<String> {
        if let Some(type_vars) = self.modules.act_template(id).map(crate::act_type_var_names)
            && !type_vars.is_empty()
        {
            return type_vars;
        }
        let Some(copy) = self.modules.resolved_act_copy(id) else {
            return Vec::new();
        };
        let aliases = copy
            .type_var_aliases
            .iter()
            .cloned()
            .collect::<FxHashMap<_, _>>();
        self.modules
            .act_template(copy.source)
            .map(crate::act_type_var_names)
            .unwrap_or_default()
            .into_iter()
            .map(|source| aliases.get(&source).cloned().unwrap_or(source))
            .collect()
    }

    pub(super) fn lower_synthetic_act_copy_bodies(&mut self) {
        let mut ids = self.modules.synthetic_var_act_copy_ids();
        ids.extend(self.modules.synthetic_sub_label_act_copy_ids());
        for id in ids {
            let Some(decl) = self.modules.type_decl_by_id(id) else {
                continue;
            };
            let Some(companion) = self.modules.type_companion(id) else {
                continue;
            };
            let Some(copy) = self.act_copy_lowering_context(decl.module, &decl) else {
                continue;
            };
            let previous_scope = self.local_method_scope.replace(companion);
            let previous_suppression = std::mem::replace(&mut self.suppress_runtime_roots, true);
            let mut method_cursor = 0usize;
            self.lower_act_body_contents(
                &copy.body,
                companion,
                &decl,
                &mut method_cursor,
                copy.type_var_aliases.as_slice(),
                copy.type_name_aliases.as_slice(),
            );
            self.suppress_runtime_roots = previous_suppression;
            self.local_method_scope = previous_scope;
        }
    }

    pub(super) fn lower_act_body_contents(
        &mut self,
        body: &Cst,
        companion: ModuleId,
        decl: &ModuleTypeDecl,
        method_cursor: &mut usize,
        type_var_aliases: &[(String, String)],
        type_name_aliases: &[(String, TypeDeclId)],
    ) {
        for child in body.children() {
            match child.kind() {
                SyntaxKind::Binding if crate::act_operation_binding(&child) => {
                    self.lower_act_operation_binding(
                        &child,
                        companion,
                        decl,
                        type_var_aliases,
                        type_name_aliases,
                    );
                }
                SyntaxKind::Binding if crate::type_method_binding(&child).is_some() => {
                    let method = self
                        .modules
                        .act_methods(decl.id)
                        .get(*method_cursor)
                        .cloned();
                    *method_cursor += usize::from(method.is_some());
                    if let Some(method) = method {
                        self.lower_act_method_binding_with_aliases(
                            &child,
                            companion,
                            &method,
                            type_var_aliases,
                            type_name_aliases,
                        );
                    }
                }
                SyntaxKind::Binding => self.lower_binding_with_context(
                    &child,
                    companion,
                    None,
                    type_var_aliases,
                    type_name_aliases,
                ),
                SyntaxKind::ModDecl => self.lower_mod_decl(&child, companion),
                SyntaxKind::ActDecl => self.lower_act_decl_body(&child, companion),
                SyntaxKind::TypeDecl
                | SyntaxKind::StructDecl
                | SyntaxKind::EnumDecl
                | SyntaxKind::ErrorDecl => self.lower_type_decl(&child, companion),
                SyntaxKind::RoleDecl => self.lower_role_decl_body(&child, companion),
                SyntaxKind::ImplDecl => self.lower_role_impl_decl(&child, companion, None),
                SyntaxKind::CastDecl => self.lower_cast_decl(&child, companion),
                _ => {}
            }
        }
    }

    pub(super) fn act_copy_lowering_context(
        &self,
        _module: ModuleId,
        decl: &ModuleTypeDecl,
    ) -> Option<ActCopyLoweringContext> {
        let copy = self.modules.resolved_act_copy(decl.id)?;
        let source_node = self.modules.act_template(copy.source)?;
        let body = crate::act_decl_body(source_node)?;
        Some(ActCopyLoweringContext {
            body,
            type_var_aliases: copy.type_var_aliases.clone(),
            type_name_aliases: self.act_copy_type_name_aliases(decl, copy.source),
        })
    }

    pub(super) fn act_copy_type_name_aliases(
        &self,
        dest: &ModuleTypeDecl,
        source: TypeDeclId,
    ) -> Vec<(String, TypeDeclId)> {
        self.modules
            .type_decl_by_id(source)
            .map(|source| vec![(source.name.0, dest.id)])
            .unwrap_or_default()
    }
}
