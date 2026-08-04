//! Extracted body lowering methods.

use super::super::*;
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ActBodyLoweringMode {
    Direct,
    CopiedSourceExport,
    CopiedSourceInternal,
}

impl ActBodyLoweringMode {
    fn includes_child(self, child: &Cst) -> bool {
        match self {
            ActBodyLoweringMode::Direct | ActBodyLoweringMode::CopiedSourceInternal => true,
            ActBodyLoweringMode::CopiedSourceExport => crate::act_copy_source_exports_child(child),
        }
    }
}

impl BodyLowerer {
    pub(super) fn lower_act_decl_body(&mut self, node: &Cst, module: ModuleId) {
        let Some(name) = crate::type_decl_name(node) else {
            return;
        };
        let Some(decl) = self.next_type_decl(module, &name) else {
            return;
        };
        self.register_effect_family(&decl);
        let Some(companion) = self.modules.type_companion(decl.id) else {
            return;
        };
        let mut method_cursor = 0usize;
        let previous_scope = self.local_method_scope.replace(companion);
        if let Some(copy) = self.act_copy_lowering_context(module, &decl) {
            let previous_source_module = self.copied_source_module.replace(copy.source_module);
            self.lower_act_body_contents(
                &copy.body,
                companion,
                &decl,
                &mut method_cursor,
                copy.type_var_aliases.as_slice(),
                copy.type_name_aliases.as_slice(),
                ActBodyLoweringMode::CopiedSourceExport,
            );
            self.copied_source_module = previous_source_module;
        }
        if let Some(body) = crate::act_decl_body(node) {
            self.lower_act_body_contents(
                &body,
                companion,
                &decl,
                &mut method_cursor,
                &[],
                &[],
                ActBodyLoweringMode::Direct,
            );
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
            .value_at(companion, companion, &name, signature_module_path_site())
            .found()
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
            self.register_failed_def(def);
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
                self.session.infer.subtype(
                    predicate,
                    root_upper,
                    crate::constraints::OriginId::unknown_internal(),
                );
                self.session
                    .enqueue(AnalysisWork::Scc(SccInput::DefFinished { def }));
            }
            Err(error) => self.push_registered_expr_error(def, name, error),
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
            .map_err(|error| LoweringError::annotation_build(error, signature))?;
        let effect_ann = builder.type_decl_application(operation_decl.effect.id, &effect_type_vars);
        let effect = signature_from_ann_type(&effect_ann);
        operation_signature_with_effect(signature, effect).ok_or(
            LoweringError::SignatureShapeMismatch {
                expected: SignatureShape::Function,
            },
        )
    }

    pub(super) fn act_effect_type_var_names(&self, id: TypeDeclId) -> Vec<String> {
        if let Some(error) = self.modules.error_decl(id) {
            return error.type_vars.clone();
        }
        if let Some(type_vars) = self.modules.act_type_vars(id).map(|vars| vars.to_vec())
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
            .act_type_vars(copy.source)
            .map(|vars| vars.to_vec())
            .unwrap_or_default()
            .into_iter()
            .map(|source| aliases.get(&source).cloned().unwrap_or(source))
            .collect()
    }

    pub(super) fn lower_synthetic_act_copy_bodies(&mut self) {
        let ids = self.modules.synthetic_var_act_copy_ids();
        let sub_label_ids = self.modules.synthetic_sub_label_act_copy_ids();
        self.lower_synthetic_act_copy_bodies_for(
            ids,
            sub_label_ids,
            super::act_copy_census::ActTemplateCatalogSource::Embedded,
        );
    }

    pub(super) fn lower_synthetic_act_copy_bodies_for(
        &mut self,
        ids: Vec<TypeDeclId>,
        sub_label_ids: Vec<TypeDeclId>,
        catalog_source: super::act_copy_census::ActTemplateCatalogSource,
    ) {
        let copies = ids
            .into_iter()
            .map(|id| (super::act_copy_census::SyntheticActCopyKind::Var, id))
            .chain(
                sub_label_ids
                    .into_iter()
                    .map(|id| (super::act_copy_census::SyntheticActCopyKind::LabelSub, id)),
            )
            .collect::<Vec<_>>();
        let mut catalog = crate::module_table::typed_act_catalog::TypedActTemplateCatalog::new();
        let embedded_shadow_active = catalog_source
            == super::act_copy_census::ActTemplateCatalogSource::Embedded
            && crate::typed_act_bundle::has_current_cold_shadow_profile();
        let embedded_catalog = embedded_shadow_active.then(|| {
            crate::typed_act_bundle::current_cold_shadow_catalog(&self.modules)
                .map_err(|error| format!("catalog rehydration: {error:?}"))?
                .ok_or_else(|| "catalog rehydration: scoped profile missing".to_string())
        });
        let mut catalog_misses = FxHashSet::default();
        if catalog_source == super::act_copy_census::ActTemplateCatalogSource::Prefix {
            for (kind, id) in &copies {
                let Some(substitution) = self.modules.nominal_act_instance_substitution(*id) else {
                    continue;
                };
                let key = (*kind, substitution.template_root_act);
                if catalog.entry(key.0, key.1).is_some() || catalog_misses.contains(&key) {
                    continue;
                }
                let Some(identity) = self
                    .modules
                    .nominal_act_template_identity(substitution.template_root_act)
                    .cloned()
                else {
                    catalog_misses.insert(key);
                    continue;
                };
                let captured = catalog.capture(
                    *kind,
                    identity,
                    &self.session.poly,
                    &self.modules,
                    &self.labels,
                );
                let eligible = captured.is_ok()
                    && catalog.entry(key.0, key.1).is_some_and(|entry| {
                        entry
                            .source_definitions_are_prefix_owned(|def| {
                                self.prefix_runtime.contains_def(def)
                            })
                            .is_ok()
                    });
                if !eligible {
                    catalog_misses.insert(key);
                }
            }
        }

        for (kind, id) in copies {
            let Some(decl) = self.modules.type_decl_by_id(id) else {
                continue;
            };
            let Some(companion) = self.modules.type_companion(id) else {
                continue;
            };
            let Some(copy) = self.act_copy_lowering_context(decl.module, &decl) else {
                continue;
            };
            let embedded_shadow = if embedded_shadow_active {
                Some((|| {
                    let catalog = embedded_catalog
                        .as_ref()
                        .expect("active embedded shadow initializes a catalog result")
                        .as_ref()
                        .map_err(Clone::clone)?;
                    let substitution = self
                        .modules
                        .nominal_act_instance_substitution(id)
                        .ok_or_else(|| "entry lookup: instance substitution missing".to_string())?;
                    let entry = catalog
                        .entry(kind, substitution.template_root_act)
                        .ok_or_else(|| {
                            format!(
                                "entry lookup: missing {kind:?}/{:?}",
                                substitution.template_root_act
                            )
                        })?;
                    entry
                        .prepare(substitution, &self.modules, |_| true)
                        .map_err(|error| format!("prepare: {error:?}"))?;
                    crate::typed_act_bundle::applied_catalog_entry_snapshot(entry, substitution)
                        .map_err(|error| format!("snapshot build: {error:?}"))
                })())
            } else {
                None
            };
            if catalog_source == super::act_copy_census::ActTemplateCatalogSource::Prefix
                && !super::act_copy_census::force_legacy_typed_act_template_path()
            {
                let substitution = self.modules.nominal_act_instance_substitution(id);
                let entry = substitution.and_then(|substitution| {
                    let key = (kind, substitution.template_root_act);
                    (!catalog_misses.contains(&key))
                        .then(|| catalog.entry(key.0, key.1))
                        .flatten()
                });
                if let (Some(substitution), Some(entry)) = (substitution, entry) {
                    let prepared = if super::act_copy_census::force_typed_act_template_fallback() {
                        None
                    } else {
                        entry
                            .prepare(substitution, &self.modules, |def| {
                                self.prefix_runtime.contains_def(def)
                            })
                            .ok()
                    };
                    if let Some(prepared) = prepared {
                        prepared.commit(&mut self.session, &mut self.labels);
                        super::act_copy_census::record_act_template_attempt(
                            kind,
                            catalog_source,
                            super::act_copy_census::ActTemplateAttemptOutcome::Eligible,
                        );
                        continue;
                    }
                    super::act_copy_census::record_act_template_attempt(
                        kind,
                        catalog_source,
                        super::act_copy_census::ActTemplateAttemptOutcome::Fallback,
                    );
                } else {
                    super::act_copy_census::record_act_template_attempt(
                        kind,
                        catalog_source,
                        super::act_copy_census::ActTemplateAttemptOutcome::Miss,
                    );
                }
            } else {
                super::act_copy_census::record_act_template_attempt(
                    kind,
                    catalog_source,
                    super::act_copy_census::ActTemplateAttemptOutcome::NotAttempted,
                );
            }
            let previous_scope = self.local_method_scope.replace(companion);
            let previous_source_module = self.copied_source_module.replace(copy.source_module);
            let previous_suppression = std::mem::replace(&mut self.suppress_runtime_roots, true);
            let previous_source_spans = std::mem::replace(&mut self.record_source_spans, false);
            let mut method_cursor = 0usize;
            super::act_copy_census::record_legacy_act_copy_lowering(kind, catalog_source);
            self.lower_act_body_contents(
                &copy.body,
                companion,
                &decl,
                &mut method_cursor,
                copy.type_var_aliases.as_slice(),
                copy.type_name_aliases.as_slice(),
                ActBodyLoweringMode::CopiedSourceInternal,
            );
            self.record_source_spans = previous_source_spans;
            self.suppress_runtime_roots = previous_suppression;
            self.copied_source_module = previous_source_module;
            self.local_method_scope = previous_scope;
            if embedded_shadow_active {
                self.pending_cold_typed_act_shadows
                    .push(super::PendingColdTypedActShadow {
                        kind,
                        destination: id,
                        embedded: embedded_shadow
                            .expect("active embedded shadow records an attempt"),
                    });
            }
        }
    }

    pub(super) fn compare_pending_cold_typed_act_shadows(&mut self) {
        for pending in std::mem::take(&mut self.pending_cold_typed_act_shadows) {
            let comparison = pending.embedded.and_then(|embedded| {
                let legacy = crate::typed_act_bundle::legacy_instance_snapshot(
                    pending.destination,
                    &self.modules,
                    &self.session.poly,
                    &self.labels,
                )
                .map_err(|error| format!("legacy capture after analysis drain: {error:?}"))?;
                crate::typed_act_bundle::compare_shadow_snapshots(&embedded, &legacy)
            });
            match comparison {
                Ok(()) => {
                    super::act_copy_census::record_embedded_shadow_comparison(pending.kind, true)
                }
                Err(detail) => {
                    super::act_copy_census::record_embedded_shadow_failure(pending.kind, detail)
                }
            }
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
        mode: ActBodyLoweringMode,
    ) {
        for child in body.children() {
            if !mode.includes_child(&child) {
                continue;
            }
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
        let source = self.modules.type_decl_by_id(copy.source)?;
        let source_node = self.modules.act_template(source.id)?;
        let body = crate::act_decl_body(source_node)?;
        Some(ActCopyLoweringContext {
            body,
            source_module: source.module,
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
