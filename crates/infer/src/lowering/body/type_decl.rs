//! Extracted body lowering methods.

use super::super::*;
use super::*;

impl BodyLowerer {
    pub(super) fn lower_type_decl(&mut self, node: &Cst, module: ModuleId) {
        let Some(name) = crate::type_decl_name(node) else {
            return;
        };
        let Some(decl) = self.next_type_decl(module, &name) else {
            return;
        };
        self.lower_type_constructors(node, module, &decl);
        self.lower_type_decl_with_body(node, &decl);
    }

    pub(super) fn lower_type_decl_with_body(&mut self, node: &Cst, decl: &ModuleTypeDecl) {
        let Some(body) = crate::type_with_body(node) else {
            return;
        };
        let Some(companion) = self.modules.type_companion(decl.id) else {
            return;
        };
        let self_alias = AnnSelfAlias {
            owner: decl.id,
            type_vars: crate::type_var_names(node),
        };
        let type_vars = self_alias.type_vars.clone();
        let mut method_cursor = 0usize;
        let previous_scope = self.local_method_scope.replace(companion);
        for child in body.children() {
            match child.kind() {
                SyntaxKind::Binding if crate::type_method_binding(&child).is_some() => {
                    let method = self
                        .modules
                        .type_methods(decl.id)
                        .get(method_cursor)
                        .cloned();
                    method_cursor += usize::from(method.is_some());
                    if let Some(method) = method {
                        self.lower_type_method_binding(
                            &child, companion, &decl, &method, &type_vars,
                        );
                    }
                }
                SyntaxKind::Binding => {
                    self.lower_binding_with_self_alias(&child, companion, Some(self_alias.clone()));
                }
                SyntaxKind::ModDecl => self.lower_mod_decl(&child, companion),
                SyntaxKind::CastDecl => self.lower_cast_decl(&child, companion),
                _ => {}
            }
        }
        self.local_method_scope = previous_scope;
    }

    pub(super) fn lower_type_constructors(
        &mut self,
        node: &Cst,
        module: ModuleId,
        decl: &ModuleTypeDecl,
    ) {
        match decl.kind {
            ModuleTypeKind::TypeAlias => {
                if let Some(self_struct) = crate::type_self_struct_node(node) {
                    let payload = ConstructorPayload::from_struct(&self_struct);
                    self.lower_constructor_def(node, module, decl, decl.name.clone(), payload);
                    self.lower_type_field_methods(node, &self_struct, module, decl);
                }
            }
            ModuleTypeKind::Struct => {
                let payload = ConstructorPayload::from_struct(node);
                self.lower_constructor_def(node, module, decl, decl.name.clone(), payload);
                self.lower_type_field_methods(node, node, module, decl);
            }
            ModuleTypeKind::Enum | ModuleTypeKind::Error => {
                // constructor の decl は型 companion module に登録されている。
                let Some(companion) = self.modules.type_companion(decl.id) else {
                    return;
                };
                for variant in crate::enum_variant_nodes(node) {
                    let Some(name) = crate::enum_variant_name(&variant) else {
                        continue;
                    };
                    let payload = ConstructorPayload::from_enum_variant(&variant);
                    self.lower_constructor_def(node, companion, decl, name, payload);
                }
            }
            ModuleTypeKind::Role | ModuleTypeKind::Act => {}
        }
    }

    pub(super) fn lower_type_field_methods(
        &mut self,
        owner_node: &Cst,
        fields_node: &Cst,
        module: ModuleId,
        owner: &ModuleTypeDecl,
    ) {
        let methods = self.modules.type_field_methods(owner.id).to_vec();
        let mut cursor = 0usize;
        let type_vars = crate::type_var_names(owner_node);

        for field in crate::struct_field_nodes(fields_node) {
            if crate::struct_field_name(&field).is_none() {
                continue;
            }
            let Some(type_expr) = crate::field_type_expr(&field) else {
                for method in methods[cursor..methods.len().min(cursor + 2)].iter() {
                    self.errors.push(BodyLoweringError::Expr {
                        def: method.def,
                        name: method.name.clone(),
                        error: LoweringError::UnsupportedSyntax { kind: field.kind() },
                    });
                }
                cursor += 2;
                continue;
            };
            let signature = match NegSignatureBuilder::with_self_alias(
                &self.modules,
                module,
                owner.order,
                SignatureSelfAlias {
                    owner: owner.id,
                    type_vars: type_vars.clone(),
                },
            )
            .build_type_expr(&type_expr)
            {
                Ok(signature) => signature,
                Err(error) => {
                    for method in methods[cursor..methods.len().min(cursor + 2)].iter() {
                        self.errors.push(BodyLoweringError::Expr {
                            def: method.def,
                            name: method.name.clone(),
                            error: LoweringError::NegSignatureBuild {
                                error: error.clone(),
                            },
                        });
                    }
                    cursor += 2;
                    continue;
                }
            };
            for _ in 0..2 {
                let Some(method) = methods.get(cursor).cloned() else {
                    return;
                };
                cursor += 1;
                self.lower_type_field_method_def(owner_node, owner, &method, &signature);
            }
        }
    }

    pub(super) fn lower_type_field_method_def(
        &mut self,
        owner_node: &Cst,
        owner: &ModuleTypeDecl,
        method: &TypeFieldMethodDecl,
        field_signature: &NegSignature,
    ) {
        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(method.def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: method.def,
                root,
            }));

        let lowered = self.lower_type_field_method_type(owner_node, owner, method, field_signature);
        match lowered {
            Ok(predicate) => {
                let root_upper = self.session.infer.alloc_neg(Neg::Var(root));
                self.session.infer.subtype(predicate, root_upper);
                self.session
                    .enqueue(AnalysisWork::Scc(SccInput::DefFinished { def: method.def }));
            }
            Err(error) => self.errors.push(BodyLoweringError::Expr {
                def: method.def,
                name: method.name.clone(),
                error,
            }),
        }

        self.session.infer.restore_level(previous_level);
    }

    pub(super) fn lower_type_field_method_type(
        &mut self,
        owner_node: &Cst,
        owner: &ModuleTypeDecl,
        method: &TypeFieldMethodDecl,
        field_signature: &NegSignature,
    ) -> Result<PosId, LoweringError> {
        let type_vars = crate::type_var_names(owner_node);
        let owner_arg_vars = type_vars
            .iter()
            .map(|_| self.session.infer.fresh_type_var())
            .collect::<Vec<_>>();
        let signature_vars = type_vars
            .iter()
            .cloned()
            .zip(owner_arg_vars.iter().copied())
            .collect::<FxHashMap<_, _>>();
        let owner_signature = owner_signature_type(owner.id, &type_vars);

        match method.receiver_kind {
            TypeMethodReceiver::Value => {
                let mut lowerer = SignatureLowerer::with_vars(
                    &mut self.session.infer,
                    &self.modules,
                    signature_vars,
                );
                let arg = lowerer
                    .lower_neg(&owner_signature)
                    .map_err(|error| LoweringError::SignatureConstraint { error })?;
                let ret = lowerer
                    .lower_data_pos(field_signature.as_type())
                    .map_err(|error| LoweringError::SignatureConstraint { error })?;
                let arg_eff = lowerer.alloc_neg(Neg::Bot);
                let ret_eff = lowerer.alloc_pos(Pos::Bot);
                Ok(lowerer.alloc_pos(Pos::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                }))
            }
            TypeMethodReceiver::Ref => {
                let ref_effect = self.session.infer.fresh_type_var();
                let ref_effect_arg = self.invariant_var_arg(ref_effect);
                let mut lowerer = SignatureLowerer::with_vars(
                    &mut self.session.infer,
                    &self.modules,
                    signature_vars,
                );
                let owner_arg = lowerer
                    .lower_invariant_arg(&owner_signature)
                    .map_err(|error| LoweringError::SignatureConstraint { error })?;
                let field_arg = lowerer
                    .lower_invariant_arg(field_signature.as_type())
                    .map_err(|error| LoweringError::SignatureConstraint { error })?;
                let ref_path = crate::std_paths::control_var_ref_type();
                let arg =
                    lowerer.alloc_neg(Neg::Con(ref_path.clone(), vec![ref_effect_arg, owner_arg]));
                let ret = lowerer.alloc_pos(Pos::Con(ref_path, vec![ref_effect_arg, field_arg]));
                let arg_eff = lowerer.alloc_neg(Neg::Bot);
                let ret_eff = lowerer.alloc_pos(Pos::Bot);
                Ok(lowerer.alloc_pos(Pos::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                }))
            }
        }
    }

    pub(super) fn lower_constructor_def(
        &mut self,
        owner_node: &Cst,
        module: ModuleId,
        owner: &ModuleTypeDecl,
        name: Name,
        payload: ConstructorPayload,
    ) {
        let Some(constructor) = self.next_value_decl(module, &name) else {
            self.errors
                .push(BodyLoweringError::MissingBindingDecl { name });
            return;
        };

        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(constructor.def, root);
        let owner_path = self
            .modules
            .type_decl_path(owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect();
        self.session.poly.constructors.insert(
            constructor.def,
            Constructor {
                owner_path,
                name: name.0.clone(),
                arity: constructor_payload_arity(&payload),
            },
        );
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: constructor.def,
                root,
            }));

        let lowered = self.lower_constructor_type(owner_node, module, owner, payload);
        match lowered {
            Ok(predicate) => {
                let root_upper = self.session.infer.alloc_neg(Neg::Var(root));
                self.session.infer.subtype(predicate, root_upper);
                self.session
                    .enqueue(AnalysisWork::Scc(SccInput::DefFinished {
                        def: constructor.def,
                    }));
            }
            Err(error) => self.errors.push(BodyLoweringError::Expr {
                def: constructor.def,
                name,
                error,
            }),
        }

        self.session.infer.restore_level(previous_level);
    }

    pub(super) fn lower_constructor_type(
        &mut self,
        owner_node: &Cst,
        module: ModuleId,
        owner: &ModuleTypeDecl,
        payload: ConstructorPayload,
    ) -> Result<PosId, LoweringError> {
        let type_vars = crate::type_var_names(owner_node);
        let owner_arg_vars = type_vars
            .iter()
            .map(|_| self.session.infer.fresh_type_var())
            .collect::<Vec<_>>();
        let signature_builder = NegSignatureBuilder::with_self_alias(
            &self.modules,
            module,
            owner.order,
            SignatureSelfAlias {
                owner: owner.id,
                type_vars: type_vars.clone(),
            },
        );
        let signature_vars = type_vars
            .iter()
            .cloned()
            .zip(owner_arg_vars.iter().copied())
            .collect::<FxHashMap<_, _>>();
        let payload = build_constructor_payload_signatures(payload, &signature_builder)?;

        let owner_args = owner_arg_vars
            .into_iter()
            .map(|var| self.invariant_var_arg(var))
            .collect::<Vec<_>>();
        let args = prepare_constructor_args(&mut self.session.infer, payload);
        connect_constructor_arg_signatures(
            &mut self.session.infer,
            &self.modules,
            signature_vars,
            &args,
        )?;

        constrain_constructor_arg_shapes(&mut self.session.infer, &args);
        let path = self
            .modules
            .type_decl_path(owner)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        let ret = self.session.infer.alloc_pos(Pos::Con(path, owner_args));
        Ok(self.constructor_function_type(args, ret))
    }

    pub(super) fn constructor_function_type(
        &mut self,
        args: Vec<ConstructorArg>,
        ret: PosId,
    ) -> PosId {
        args.into_iter().rev().fold(ret, |ret, arg| {
            let arg = self.session.infer.alloc_neg(Neg::Var(arg.value()));
            let arg_eff = self.session.infer.alloc_neg(Neg::Bot);
            let ret_eff = self.session.infer.alloc_pos(Pos::Bot);
            self.session.infer.alloc_pos(Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            })
        })
    }

    pub(super) fn invariant_var_arg(&mut self, var: TypeVar) -> NeuId {
        let lower = self.session.infer.alloc_pos(Pos::Var(var));
        let upper = self.session.infer.alloc_neg(Neg::Var(var));
        self.session.infer.alloc_neu(Neu::Bounds(lower, upper))
    }
}
