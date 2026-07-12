//! Extracted body lowering methods.

use super::super::*;
use super::*;

impl BodyLowerer {
    pub(super) fn lower_role_impl_decl(
        &mut self,
        node: &Cst,
        module: ModuleId,
        self_alias: Option<AnnSelfAlias>,
    ) {
        let Some(impl_decl) = self.next_role_impl_decl(module) else {
            return;
        };
        let mut context = match self.register_role_impl_candidate(
            node,
            impl_decl.def,
            module,
            impl_decl.order,
            self_alias,
        ) {
            Ok(context) => context,
            Err(error) => {
                self.errors.push(BodyLoweringError::Expr {
                    def: impl_decl.def,
                    name: Name("impl".into()),
                    error,
                });
                return;
            }
        };

        let Some(body) = crate::role_impl_body(node) else {
            return;
        };
        let previous_scope = self.local_method_scope.replace(impl_decl.body_module);
        let mut method_cursor = 0usize;
        for child in body.children() {
            match child.kind() {
                SyntaxKind::Binding if crate::role_impl_method_binding(&child).is_some() => {
                    let method_info = crate::role_impl_method_binding(&child)
                        .expect("checked role method binding");
                    let decl = self.next_value_decl(impl_decl.body_module, &method_info.name);
                    if let Some(decl) = decl {
                        let impl_method = impl_decl.methods.get(method_cursor).cloned();
                        method_cursor += usize::from(
                            impl_method
                                .as_ref()
                                .is_some_and(|method| method.def == decl.def),
                        );
                        let requirement =
                            self.role_impl_method_requirement(&context, method_info.name.clone());
                        self.lower_role_impl_method_binding(
                            &child,
                            impl_decl.def,
                            impl_decl.body_module,
                            &RoleImplMethodDecl {
                                name: method_info.name,
                                receiver: method_info.receiver,
                                def: decl.def,
                                vis: impl_method
                                    .as_ref()
                                    .map(|method| method.vis)
                                    .unwrap_or(poly::expr::Vis::My),
                                order: decl.order,
                            },
                            &context.target_ann,
                            &context.type_var_bindings,
                            &mut context.ann_solver_vars,
                            requirement,
                        );
                    }
                }
                SyntaxKind::Binding => self.lower_binding(&child, impl_decl.body_module),
                SyntaxKind::ModDecl => self.lower_mod_decl(&child, impl_decl.body_module),
                SyntaxKind::TypeDecl
                | SyntaxKind::StructDecl
                | SyntaxKind::EnumDecl
                | SyntaxKind::ErrorDecl => self.lower_type_decl(&child, impl_decl.body_module),
                SyntaxKind::RoleDecl => self.lower_role_decl_body(&child, impl_decl.body_module),
                SyntaxKind::ActDecl => self.lower_act_decl_body(&child, impl_decl.body_module),
                SyntaxKind::CastDecl => self.lower_cast_decl(&child, impl_decl.body_module),
                _ => {}
            }
        }
        self.local_method_scope = previous_scope;
    }

    pub(in crate::lowering) fn register_role_impl_candidate(
        &mut self,
        node: &Cst,
        impl_def: DefId,
        module: ModuleId,
        site: ModuleOrder,
        self_alias: Option<AnnSelfAlias>,
    ) -> Result<RoleImplLoweringContext, LoweringError> {
        let Some(head) = impl_head_type_expr(node) else {
            return Err(LoweringError::UnsupportedSyntax { kind: node.kind() });
        };
        let mut ann_builder = ann_type_builder(&self.modules, module, site, self_alias);
        let attached_target_ann = ann_builder.self_alias_type();
        let head_ann = ann_builder
            .build_type_expr(&head)
            .map_err(|error| LoweringError::annotation_build(error, &head))?;
        let description_ann = impl_description_type_expr(node)
            .map(|type_expr| {
                ann_builder
                    .build_type_expr(&type_expr)
                    .map_err(|error| LoweringError::annotation_build(error, &type_expr))
            })
            .transpose()?;
        let spec = role_impl_ann_spec(
            &self.modules,
            head_ann,
            description_ann,
            attached_target_ann,
        )
        .ok_or(LoweringError::UnsupportedSyntax { kind: node.kind() })?;
        let role_input_names = self.modules.role_inputs(spec.role).to_vec();
        let role_associated_names = self.modules.role_associated(spec.role).to_vec();
        let explicit_associated = role_impl_associated_type_exprs(node);
        let mut candidate_associated_anns = Vec::with_capacity(role_associated_names.len());
        let mut contract_associated = Vec::with_capacity(role_associated_names.len());
        let mut next_inferred_associated = 0u32;
        for name in &role_associated_names {
            if let Some(type_expr) = explicit_associated.get(name) {
                let ann = ann_builder
                    .build_type_expr(type_expr)
                    .map_err(|error| LoweringError::annotation_build(error, type_expr))?;
                contract_associated.push(
                    crate::role_impl_conformance::AssociatedAssignment::Explicit {
                        name: name.clone(),
                        ty: crate::role_impl_conformance::DeclaredType::new(ann.clone()),
                        source: crate::node_source_range(type_expr),
                    },
                );
                candidate_associated_anns.push((name.clone(), ann));
            } else {
                let ann_var = ann_builder.ann_type_var_for_role(name);
                contract_associated.push(
                    crate::role_impl_conformance::AssociatedAssignment::Inferred {
                        name: name.clone(),
                        binder: crate::role_impl_conformance::AssociatedInferenceBinder {
                            id: crate::role_impl_conformance::AssociatedInferenceBinderId(
                                next_inferred_associated,
                            ),
                            annotation_var: ann_var.id,
                        },
                    },
                );
                next_inferred_associated = next_inferred_associated.saturating_add(1);
                candidate_associated_anns.push((name.clone(), AnnType::Var(ann_var)));
            }
        }
        let requirement_associated_anns = role_associated_names
            .iter()
            .map(|name| {
                (
                    name.clone(),
                    AnnType::Var(ann_builder.ann_type_var_for_role(name)),
                )
            })
            .collect::<Vec<_>>();
        let type_var_bindings = ann_builder.type_var_bindings();
        let role = self
            .modules
            .type_decl_by_id(spec.role)
            .map(|role| {
                self.modules
                    .type_decl_path(&role)
                    .segments
                    .into_iter()
                    .map(|name| name.0)
                    .collect::<Vec<_>>()
            })
            .ok_or(LoweringError::UnsupportedSyntax { kind: node.kind() })?;
        let conformance_contract =
            crate::role_impl_conformance::RoleImplConformanceContract::capture(
                impl_def,
                role.clone(),
                self.modules
                    .def_source_range(impl_def)
                    .unwrap_or_else(|| crate::node_source_range(node)),
                spec.inputs.clone(),
                contract_associated,
            );
        let explicit_associated_complete = role_associated_names
            .iter()
            .all(|name| explicit_associated.contains_key(name));
        let (candidate_inputs, candidate_associated, ann_solver_vars) =
            if explicit_associated_complete {
                let (candidate_inputs, candidate_associated, ann_solver_vars) =
                    self.lower_role_impl_args(&spec.inputs, &candidate_associated_anns)?;
                let ann_solver_vars = self.lower_role_impl_associated_vars(
                    &requirement_associated_anns,
                    ann_solver_vars,
                )?;
                (candidate_inputs, candidate_associated, ann_solver_vars)
            } else {
                self.lower_role_impl_args(&spec.inputs, &candidate_associated_anns)?
            };
        let candidate = RoleImplCandidate {
            impl_def: Some(impl_def),
            role,
            inputs: candidate_inputs,
            associated: candidate_associated,
            prerequisites: Vec::new(),
            methods: Vec::new(),
        };
        self.session.role_impls.insert(candidate);
        #[cfg(not(test))]
        drop(conformance_contract);
        Ok(RoleImplLoweringContext {
            #[cfg(test)]
            conformance_contract: Some(conformance_contract),
            role: spec.role,
            target_ann: spec.target,
            input_names: role_input_names,
            input_signatures: spec.inputs.iter().map(signature_from_ann_type).collect(),
            associated_signatures: requirement_associated_anns
                .iter()
                .map(|(name, ann)| (name.clone(), signature_from_ann_type(ann)))
                .collect(),
            type_var_bindings,
            ann_solver_vars,
        })
    }

    pub(super) fn lower_role_impl_args(
        &mut self,
        inputs: &[AnnType],
        associated_anns: &[(String, AnnType)],
    ) -> Result<
        (
            Vec<RoleConstraintArg>,
            Vec<RoleAssociatedConstraint>,
            FxHashMap<AnnTypeVarId, TypeVar>,
        ),
        LoweringError,
    > {
        let mut lowerer = AnnConstraintLowerer::new(&mut self.session.infer, &self.modules);
        let mut lowered_inputs = Vec::with_capacity(inputs.len());
        for input in inputs {
            lowered_inputs.push(
                lowerer
                    .lower_role_arg(input)
                    .map_err(|error| LoweringError::AnnotationConstraint { error })?,
            );
        }
        let mut lowered_associated = Vec::with_capacity(associated_anns.len());
        for (name, ann) in associated_anns {
            lowered_associated.push(RoleAssociatedConstraint {
                name: name.clone(),
                value: lowerer
                    .lower_role_arg(ann)
                    .map_err(|error| LoweringError::AnnotationConstraint { error })?,
            });
        }
        Ok((lowered_inputs, lowered_associated, lowerer.into_vars()))
    }

    pub(super) fn lower_role_impl_associated_vars(
        &mut self,
        associated_anns: &[(String, AnnType)],
        ann_solver_vars: FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Result<FxHashMap<AnnTypeVarId, TypeVar>, LoweringError> {
        if associated_anns.is_empty() {
            return Ok(ann_solver_vars);
        }
        let mut lowerer = AnnConstraintLowerer::with_vars(
            &mut self.session.infer,
            &self.modules,
            ann_solver_vars,
        );
        for (_, ann) in associated_anns {
            lowerer
                .lower_role_arg(ann)
                .map_err(|error| LoweringError::AnnotationConstraint { error })?;
        }
        Ok(lowerer.into_vars())
    }

    pub(super) fn role_impl_method_requirement(
        &self,
        context: &RoleImplLoweringContext,
        name: Name,
    ) -> Option<ResolvedRoleMethodRequirement> {
        let method = self
            .modules
            .role_methods(context.role)
            .iter()
            .find(|method| method.name == name)?;
        let requirement = self.role_requirements.get(&method.def)?;
        let role = self.modules.type_decl_by_id(context.role).map(|role| {
            self.modules
                .type_decl_path(&role)
                .segments
                .into_iter()
                .map(|name| name.0)
                .collect::<Vec<_>>()
        })?;
        Some(ResolvedRoleMethodRequirement {
            role_method: method.def,
            role,
            inputs: context.input_signatures.clone(),
            associated: context.associated_signatures.clone(),
            signature: substitute_role_requirement_signature(requirement, context),
        })
    }

    pub(super) fn lower_role_impl_method_binding(
        &mut self,
        node: &Cst,
        impl_def: DefId,
        module: ModuleId,
        method: &RoleImplMethodDecl,
        target_ann: &AnnType,
        type_var_bindings: &[(String, AnnTypeVarId)],
        ann_solver_vars: &mut FxHashMap<AnnTypeVarId, TypeVar>,
        requirement: Option<ResolvedRoleMethodRequirement>,
    ) {
        let Some(expr) = binding_body_expr(node) else {
            self.push_missing_body_for_decl(method.def, method.name.clone());
            return;
        };
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(method.def, root);
        if method.vis != Vis::My {
            self.session.register_role_impl_member(method.def, impl_def);
        }
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: method.def,
                root,
            }));
        if let Some(requirement) = &requirement {
            self.session
                .register_role_impl_member_requirement(method.def, requirement.role_method);
            self.session.role_impls.add_method_for_impl(
                impl_def,
                requirement.role_method,
                method.def,
            );
        }

        let recursive_self_possible = self.body_may_select_method(&expr, &method.name);
        let lowered = ExprLowerer::with_labels(
            &mut self.session,
            &self.modules,
            module,
            method.order,
            method.def,
            &mut self.labels,
        )
        .with_source_file(self.source_file.clone())
        .with_source_spans(self.record_source_spans)
        .with_local_method_scope(self.local_method_scope)
        .lower_impl_method_body_expr(
            &expr,
            &binding_arg_patterns(node),
            method.receiver.clone(),
            target_ann,
            binding_type_expr(node),
            type_var_bindings,
            ann_solver_vars,
            requirement.as_ref(),
            recursive_self_possible,
        );
        match lowered {
            Ok(computation) => {
                self.finish_binding(method.def, method.name.clone(), root, computation, true)
            }
            Err(error) => self.push_registered_expr_error(method.def, method.name.clone(), error),
        }
        self.session.infer.restore_level(previous_level);
    }

    pub(super) fn lower_role_method_signature(
        &mut self,
        module: ModuleId,
        role: &ModuleTypeDecl,
        method: &RoleMethodDecl,
        role_inputs: &[String],
        role_associated: &[String],
    ) {
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(method.def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: method.def,
                root,
            }));

        let result = self.connect_role_method_signature(
            module,
            role,
            method,
            role_inputs,
            role_associated,
            root,
        );
        if let Err(error) = result {
            self.errors.push(BodyLoweringError::Expr {
                def: method.def,
                name: method.name.clone(),
                error,
            });
        }
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::DefFinished { def: method.def }));
        self.session.infer.restore_level(previous_level);
    }

    pub(super) fn connect_role_method_signature(
        &mut self,
        module: ModuleId,
        role: &ModuleTypeDecl,
        method: &RoleMethodDecl,
        role_inputs: &[String],
        role_associated: &[String],
        root: TypeVar,
    ) -> Result<(), LoweringError> {
        let Some(signature) = method.signature.as_ref() else {
            return Ok(());
        };
        let mut builder = ann_type_builder(&self.modules, module, method.order, None);
        for name in role_inputs.iter().chain(role_associated.iter()) {
            builder.add_bare_type_var(name.clone());
        }
        if let Some(first) = role_inputs.first() {
            builder.add_bare_type_var_alias("self", first.clone());
        }
        let signature =
            build_stored_signature_type_expr(&mut builder, signature).map_err(|error| {
                LoweringError::annotation_build_for_stored_signature(error, signature)
            })?;
        let signature = role_method_signature_with_receiver(
            method.receiver.as_ref(),
            role_inputs.first(),
            signature,
        );
        let role_arg_names = role_inputs
            .iter()
            .chain(role_associated.iter())
            .cloned()
            .collect::<Vec<_>>();
        let role_arg_signatures = role_arg_names
            .iter()
            .map(|name| SignatureType::Var(SignatureVar { name: name.clone() }))
            .collect::<Vec<_>>();

        let (pos, role_args) = {
            let mut lowerer = SignatureLowerer::new(&mut self.session.infer, &self.modules);
            let pos = lowerer
                .lower_pos(&signature)
                .map_err(|error| LoweringError::SignatureConstraint { error })?;
            let mut role_args = Vec::with_capacity(role_arg_signatures.len());
            for signature in &role_arg_signatures {
                role_args.push(
                    lowerer
                        .lower_role_arg(signature)
                        .map_err(|error| LoweringError::SignatureConstraint { error })?,
                );
            }
            (pos, role_args)
        };
        let upper = self.session.infer.alloc_neg(Neg::Var(root));
        self.session.infer.subtype(pos, upper);

        let path = self
            .modules
            .type_decl_path(role)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        let inputs = role_args[..role_inputs.len()].to_vec();
        let associated = role_associated
            .iter()
            .cloned()
            .zip(role_args[role_inputs.len()..].iter().copied())
            .map(|(name, value)| RoleAssociatedConstraint { name, value })
            .collect();
        self.session.roles.insert(
            method.def,
            RoleConstraint {
                role: path,
                inputs,
                associated,
            },
        );
        Ok(())
    }
}
