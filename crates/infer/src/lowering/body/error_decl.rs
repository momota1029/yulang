//! Synthetic lowering for `error E:` declarations.
//!
//! Error declarations are data constructors at the surface, but `fail` needs a
//! corresponding effect operation for each variant.  The operation is kept out
//! of the value namespace so `E::variant` remains an ordinary constructor; the
//! generated helpers and `Throw` impl use the hidden operation metadata.

use super::super::*;
use super::*;
use crate::{ErrorDecl, ErrorVariantDecl, module_path_site};
use parser::sink::YulangLanguage;
use rowan::SyntaxNode;

impl BodyLowerer {
    pub(super) fn lower_error_synthetic_decls(&mut self, node: &Cst, decl: &ModuleTypeDecl) {
        let Some(error) = self.modules.error_decl(decl.id).cloned() else {
            return;
        };
        self.lower_error_operations(node, decl, &error);
        self.lower_error_throw_impl(node, decl, &error);
        self.lower_error_display_impl(node, decl, &error);
        self.lower_error_wrap_helper(node, decl, &error);
        self.lower_error_up_helper(node, decl, &error);
    }

    fn lower_error_operations(&mut self, node: &Cst, decl: &ModuleTypeDecl, error: &ErrorDecl) {
        for variant in &error.variants {
            let previous_level = self.session.infer.enter_child_level();
            let root = self.session.infer.fresh_type_var();
            self.typing.set_def(variant.operation_def, root);
            self.session
                .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                    def: variant.operation_def,
                    root,
                }));

            let lowered = self.error_operation_signature(node, decl, error, variant);
            match lowered {
                Ok(signature) => {
                    let vars = error_type_var_slots(&mut self.session.infer, &error.type_vars);
                    let mut lowerer =
                        SignatureLowerer::with_vars(&mut self.session.infer, &self.modules, vars);
                    match lowerer.lower_pos(&signature) {
                        Ok(predicate) => {
                            let root_upper = self.session.infer.alloc_neg(Neg::Var(root));
                            self.session.infer.subtype(predicate, root_upper);
                            self.session.poly.effect_operations.insert(
                                variant.operation_def,
                                poly::expr::EffectOperation {
                                    path: self.error_operation_path(decl, &variant.name),
                                },
                            );
                            self.session
                                .enqueue(AnalysisWork::Scc(SccInput::DefFinished {
                                    def: variant.operation_def,
                                }));
                        }
                        Err(error) => self.push_registered_expr_error(
                            variant.operation_def,
                            variant.name.clone(),
                            LoweringError::SignatureConstraint { error },
                        ),
                    }
                }
                Err(error) => self.push_registered_expr_error(
                    variant.operation_def,
                    variant.name.clone(),
                    error,
                ),
            }

            self.session.infer.restore_level(previous_level);
        }
    }

    fn error_operation_signature(
        &self,
        node: &Cst,
        decl: &ModuleTypeDecl,
        error: &ErrorDecl,
        variant: &ErrorVariantDecl,
    ) -> Result<SignatureType, LoweringError> {
        let payload = self.error_variant_payload_signature(node, decl, error, variant)?;
        let effect = owner_signature_type(error.owner, &error.type_vars);
        let ret_eff = SignatureEffectRow {
            items: vec![SignatureEffectAtom::Type(effect)],
            tail: None,
        };
        Ok(SignatureType::Function {
            param: Box::new(payload),
            arg_eff: None,
            ret_eff: Some(ret_eff),
            ret: Box::new(SignatureType::Builtin(BuiltinType::Never)),
        })
    }

    fn error_variant_payload_signature(
        &self,
        node: &Cst,
        decl: &ModuleTypeDecl,
        error: &ErrorDecl,
        variant: &ErrorVariantDecl,
    ) -> Result<SignatureType, LoweringError> {
        let builder = NegSignatureBuilder::with_self_alias(
            &self.modules,
            error.module,
            decl.order,
            SignatureSelfAlias {
                owner: error.owner,
                type_vars: error.type_vars.clone(),
            },
        );
        match &variant.payload {
            ConstructorPayload::Unit => Ok(SignatureType::Builtin(BuiltinType::Unit)),
            ConstructorPayload::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| {
                        item.ty.as_ref().map_or_else(
                            || Ok(SignatureType::Builtin(BuiltinType::Unit)),
                            |ty| stored_neg_signature_type(ty, &builder),
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                match items.as_slice() {
                    [] => Ok(SignatureType::Builtin(BuiltinType::Unit)),
                    [item] => Ok(item.clone()),
                    _ => Ok(SignatureType::Tuple(items)),
                }
            }
            ConstructorPayload::Record(_) => {
                Err(LoweringError::UnsupportedSyntax { kind: node.kind() })
            }
        }
    }

    fn error_operation_path(&self, decl: &ModuleTypeDecl, name: &Name) -> Vec<String> {
        self.modules
            .type_decl_path(decl)
            .segments
            .into_iter()
            .chain(std::iter::once(name.clone()))
            .map(|name| name.0)
            .collect()
    }

    fn lower_error_throw_impl(&mut self, node: &Cst, decl: &ModuleTypeDecl, error: &ErrorDecl) {
        let Some(throw_role) = self.throw_role_decl(error.module) else {
            return;
        };
        if self.modules.role_inputs(throw_role.id).len() != 1 {
            return;
        }
        let Some(throw_method) = self
            .modules
            .role_methods(throw_role.id)
            .iter()
            .find(|method| method.name.0 == "throw")
            .cloned()
        else {
            return;
        };

        let impl_def = self.session.poly.defs.fresh();
        let method_def = self.session.poly.defs.fresh();
        self.session.poly.defs.set(
            impl_def,
            Def::Mod {
                vis: Vis::My,
                children: vec![method_def],
            },
        );
        self.session.poly.defs.set(
            method_def,
            Def::Let {
                vis: Vis::Our,
                scheme: None,
                body: None,
                children: Vec::new(),
            },
        );
        self.labels
            .set_def_label(method_def, format!("{}::throw#error", decl.name.0));

        if let Some(candidate) =
            self.error_throw_candidate(impl_def, &throw_role, error, throw_method.def, method_def)
        {
            self.session.register_role_impl_candidate(candidate);
            self.session
                .role_impls
                .add_method_for_impl(impl_def, throw_method.def, method_def);
            self.session.register_role_impl_member(method_def, impl_def);
            self.session
                .register_role_impl_member_requirement(method_def, throw_method.def);
        }

        let previous_level = self.session.infer.enter_child_level();
        let root = self.session.infer.fresh_type_var();
        self.typing.set_def(method_def, root);
        self.session
            .enqueue(AnalysisWork::Scc(SccInput::RegisterDef {
                def: method_def,
                root,
            }));

        let computation = {
            let mut lowerer = ExprLowerer::with_labels(
                &mut self.session,
                &self.modules,
                error.companion,
                module_path_site(),
                method_def,
                &mut self.labels,
            )
            .with_source_file(self.source_file.clone())
            .with_source_spans(false);
            lowerer.lower_synthetic_error_throw_body(node, decl, error)
        };
        match computation {
            Ok(computation) => {
                self.finish_binding(method_def, Name("throw".into()), root, computation, true)
            }
            Err(error) => self.push_registered_expr_error(method_def, Name("throw".into()), error),
        }
        self.session.infer.restore_level(previous_level);
    }

    fn lower_error_display_impl(&mut self, node: &Cst, decl: &ModuleTypeDecl, error: &ErrorDecl) {
        let Some(display_role) = self.display_role_decl(error.module) else {
            return;
        };
        if self.modules.role_inputs(display_role.id).len() != 1 {
            return;
        }
        let Some(display_method) = self
            .modules
            .role_methods(display_role.id)
            .iter()
            .find(|method| method.name.0 == "show")
            .cloned()
        else {
            return;
        };

        let impl_def = self.session.poly.defs.fresh();
        let method_def = self.session.poly.defs.fresh();
        self.session.poly.defs.set(
            impl_def,
            Def::Mod {
                vis: Vis::My,
                children: vec![method_def],
            },
        );
        self.session.poly.defs.set(
            method_def,
            Def::Let {
                vis: Vis::Our,
                scheme: None,
                body: None,
                children: Vec::new(),
            },
        );
        self.labels
            .set_def_label(method_def, format!("{}::show#error", decl.name.0));

        let Some(source) = synthetic_error_display_source(error) else {
            self.push_registered_expr_error(
                method_def,
                display_method.name,
                LoweringError::UnsupportedSyntax { kind: node.kind() },
            );
            return;
        };
        let Some(binding) = synthetic_binding(&source) else {
            self.push_registered_expr_error(
                method_def,
                display_method.name,
                LoweringError::UnsupportedSyntax {
                    kind: SyntaxKind::Binding,
                },
            );
            return;
        };

        let Some(mut context) = self.error_display_context(impl_def, &display_role, error) else {
            return;
        };
        let requirement = self.role_impl_method_requirement(&context, display_method.name.clone());
        self.lower_role_impl_method_binding(
            &binding,
            impl_def,
            error.companion,
            &RoleImplMethodDecl {
                name: display_method.name,
                receiver: Some(Name("__error_value".into())),
                def: method_def,
                vis: Vis::Our,
                order: module_path_site(),
            },
            &context.target_ann,
            &context.type_var_bindings,
            &mut context.ann_solver_vars,
            requirement,
            None,
        );
    }

    fn error_display_context(
        &mut self,
        impl_def: DefId,
        role: &ModuleTypeDecl,
        error: &ErrorDecl,
    ) -> Option<RoleImplLoweringContext> {
        let role_path = self
            .modules
            .type_decl_path(role)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        let role_inputs = self.modules.role_inputs(role.id).to_vec();
        let role_associated = self.modules.role_associated(role.id).to_vec();
        let mut builder =
            ann_type_builder(&self.modules, error.companion, module_path_site(), None);
        let target_ann = builder.type_decl_application(error.owner, &error.type_vars);
        let input_anns = vec![target_ann.clone()];
        let associated_anns = role_associated
            .iter()
            .map(|name| {
                (
                    name.clone(),
                    AnnType::Var(builder.ann_type_var_for_role(name)),
                )
            })
            .collect::<Vec<_>>();
        let type_var_bindings = builder.type_var_bindings();
        let (inputs, associated, ann_solver_vars) = self
            .lower_role_impl_args(&input_anns, &associated_anns)
            .ok()?;
        let input_signatures = input_anns
            .iter()
            .map(signature_from_ann_type)
            .collect::<Vec<_>>();
        let associated_signatures = associated_anns
            .iter()
            .map(|(name, ann)| (name.clone(), signature_from_ann_type(ann)))
            .collect::<Vec<_>>();
        self.session
            .register_role_impl_candidate(RoleImplCandidate {
                impl_def: Some(impl_def),
                role: role_path,
                inputs,
                associated,
                prerequisites: Vec::new(),
                methods: Vec::new(),
            });
        Some(RoleImplLoweringContext {
            conformance_contract: None,
            conformance_shadow_targets: FxHashMap::default(),
            role: role.id,
            target_ann,
            input_names: role_inputs,
            input_signatures,
            associated_signatures,
            type_var_bindings,
            ann_solver_vars,
        })
    }

    fn lower_error_wrap_helper(&mut self, node: &Cst, decl: &ModuleTypeDecl, error: &ErrorDecl) {
        let Some(def) = error.wrap_def else {
            return;
        };
        if !self.std_result_constructor_available(error.module, "ok")
            || !self.std_result_constructor_available(error.module, "err")
        {
            return;
        }
        let sources = self.error_lift_sources(error);
        let source = synthetic_error_wrap_source(&self.modules, decl, error, &sources);
        match source {
            Some(source) => self.lower_synthetic_error_helper_binding(
                def,
                Name("wrap".into()),
                error.companion,
                &source,
            ),
            None => self.push_registered_expr_error(
                def,
                Name("wrap".into()),
                LoweringError::UnsupportedSyntax { kind: node.kind() },
            ),
        }
    }

    fn lower_error_up_helper(&mut self, node: &Cst, decl: &ModuleTypeDecl, error: &ErrorDecl) {
        let Some(def) = error.up_def else {
            return;
        };
        let sources = self.error_lift_sources(error);
        if sources.is_empty() {
            return;
        }
        if let Err(error) = self.register_error_up_casts(def, error, &sources) {
            self.push_registered_expr_error(def, Name("up".into()), error);
            return;
        }
        let source = synthetic_error_up_source(&self.modules, decl, error, &sources);
        match source {
            Some(source) => self.lower_synthetic_error_helper_binding(
                def,
                Name("up".into()),
                error.companion,
                &source,
            ),
            None => self.push_registered_expr_error(
                def,
                Name("up".into()),
                LoweringError::UnsupportedSyntax { kind: node.kind() },
            ),
        }
    }

    fn register_error_up_casts(
        &mut self,
        def: DefId,
        error: &ErrorDecl,
        sources: &[ErrorLiftSource],
    ) -> Result<(), LoweringError> {
        let mut builder =
            ann_type_builder(&self.modules, error.companion, module_path_site(), None);
        let target_ann = builder.type_decl_application(error.owner, &error.type_vars);
        for source in sources {
            let source_ann =
                builder.type_decl_application(source.source.owner, &source.source.type_vars);
            let cast_scheme = build_cast_scheme_from_ann(
                &mut self.session.poly,
                &self.modules,
                &source_ann,
                &target_ann,
            )?;
            self.session.casts.insert_effect_up(
                def,
                cast_scheme.source.clone(),
                cast_scheme.target.clone(),
                cast_scheme.scheme.clone(),
            );
            self.session.poly.cast_rules.push(poly::expr::CastRule {
                def,
                source: cast_scheme.source,
                target: cast_scheme.target,
                scheme: cast_scheme.scheme,
                kind: poly::expr::CastRuleKind::EffectUp,
            });
        }
        Ok(())
    }

    fn lower_synthetic_error_helper_binding(
        &mut self,
        def: DefId,
        name: Name,
        module: ModuleId,
        source: &str,
    ) {
        let Some(binding) = synthetic_binding(source) else {
            self.push_registered_expr_error(
                def,
                name,
                LoweringError::UnsupportedSyntax {
                    kind: SyntaxKind::Binding,
                },
            );
            return;
        };
        let record_source_spans = std::mem::replace(&mut self.record_source_spans, false);
        self.lower_binding(&binding, module);
        self.record_source_spans = record_source_spans;
    }

    fn std_result_constructor_available(&self, module: ModuleId, name: &str) -> bool {
        self.modules
            .value_path_at(
                module,
                &std_result_constructor_path(name),
                module_path_site(),
            )
            .is_some()
    }

    fn error_lift_sources(&self, error: &ErrorDecl) -> Vec<ErrorLiftSource> {
        let mut out = Vec::new();
        self.collect_error_lift_sources(error, Vec::new(), &mut Vec::new(), &mut out);
        out
    }

    fn collect_error_lift_sources(
        &self,
        error: &ErrorDecl,
        wrappers: Vec<String>,
        seen: &mut Vec<TypeDeclId>,
        out: &mut Vec<ErrorLiftSource>,
    ) {
        if seen.contains(&error.owner) {
            return;
        }
        seen.push(error.owner);
        for variant in &error.variants {
            if !variant.from {
                continue;
            }
            let Some(source) = self.source_error_for_from_variant(error, variant) else {
                continue;
            };
            let mut next_wrappers = Vec::with_capacity(wrappers.len() + 1);
            next_wrappers.push(error_variant_constructor_path(
                &self.modules,
                error,
                variant,
            ));
            next_wrappers.extend(wrappers.iter().cloned());
            out.push(ErrorLiftSource {
                source: source.clone(),
                wrappers: next_wrappers.clone(),
            });
            self.collect_error_lift_sources(&source, next_wrappers, seen, out);
        }
        seen.pop();
    }

    fn source_error_for_from_variant(
        &self,
        error: &ErrorDecl,
        variant: &ErrorVariantDecl,
    ) -> Option<ErrorDecl> {
        let ConstructorPayload::Tuple(items) = &variant.payload else {
            return None;
        };
        let [item] = items.as_slice() else {
            return None;
        };
        let ty = item.ty.as_ref()?;
        let decl = self.modules.type_decl_by_id(error.owner)?;
        let builder = NegSignatureBuilder::with_self_alias(
            &self.modules,
            error.module,
            decl.order,
            SignatureSelfAlias {
                owner: error.owner,
                type_vars: error.type_vars.clone(),
            },
        );
        let signature = stored_neg_signature_type(ty, &builder).ok()?;
        let id = signature_named_head(&signature)?;
        self.modules.error_decl(id).cloned()
    }

    fn throw_role_decl(&self, module: ModuleId) -> Option<ModuleTypeDecl> {
        let std_path = names(&["std", "control", "throw", "Throw"]);
        self.modules
            .type_path_at(module, &std_path, module_path_site())
            .or_else(|| {
                self.modules
                    .lexical_type_at(module, &Name("Throw".to_string()), module_path_site())
            })
            .filter(|decl| decl.kind == ModuleTypeKind::Role)
    }

    fn display_role_decl(&self, module: ModuleId) -> Option<ModuleTypeDecl> {
        let std_path = names(&["std", "core", "fmt", "Display"]);
        self.modules
            .type_path_at(module, &std_path, module_path_site())
            .or_else(|| {
                self.modules.lexical_type_at(
                    module,
                    &Name("Display".to_string()),
                    module_path_site(),
                )
            })
            .filter(|decl| decl.kind == ModuleTypeKind::Role)
    }

    fn error_throw_candidate(
        &mut self,
        impl_def: DefId,
        role: &ModuleTypeDecl,
        error: &ErrorDecl,
        requirement: DefId,
        implementation: DefId,
    ) -> Option<RoleImplCandidate> {
        let role_path = self
            .modules
            .type_decl_path(role)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        let mut vars = error_type_var_slots(&mut self.session.infer, &error.type_vars);
        let error_sig = owner_signature_type(error.owner, &error.type_vars);
        let throws_sig = SignatureType::EffectRow(SignatureEffectRow {
            items: vec![SignatureEffectAtom::Type(error_sig.clone())],
            tail: None,
        });
        let mut lowerer =
            SignatureLowerer::with_vars(&mut self.session.infer, &self.modules, vars.clone());
        let input = lowerer.lower_role_arg(&error_sig).ok()?;
        vars = lowerer.into_vars();
        let mut lowerer = SignatureLowerer::with_vars(&mut self.session.infer, &self.modules, vars);
        let throws = lowerer.lower_role_arg(&throws_sig).ok()?;
        let associated = self
            .modules
            .role_associated(role.id)
            .iter()
            .filter_map(|name| {
                (name == "throws").then_some(RoleAssociatedConstraint {
                    name: name.clone(),
                    value: throws,
                })
            })
            .collect::<Vec<_>>();
        Some(RoleImplCandidate {
            impl_def: Some(impl_def),
            role: role_path,
            inputs: vec![input],
            associated,
            prerequisites: Vec::new(),
            methods: vec![poly::roles::RoleImplMethod {
                requirement,
                implementation,
            }],
        })
    }
}

#[derive(Clone)]
struct ErrorLiftSource {
    source: ErrorDecl,
    wrappers: Vec<String>,
}

fn synthetic_error_display_source(error: &ErrorDecl) -> Option<String> {
    if error.variants.is_empty() {
        return None;
    }
    let mut out = "our __error_value.show = case __error_value:\n".to_string();
    for (index, variant) in error.variants.iter().enumerate() {
        let pattern = error_variant_pattern_source(&variant.name, &variant.payload, index)?;
        let body = error_display_expr(&variant.name.0, &variant.payload, index, variant.from)?;
        out.push_str("    ");
        out.push_str(&pattern);
        out.push_str(" -> ");
        out.push_str(&body);
        out.push('\n');
    }
    Some(out)
}

fn error_display_expr(
    name: &str,
    payload: &ConstructorPayload,
    index: usize,
    from: bool,
) -> Option<String> {
    match constructor_payload_arity(payload) {
        0 => Some(quoted_string_literal(name)),
        1 if from => Some(format!("{}.show", error_payload_name(index, 0).0)),
        1 => Some(format!(
            "{} + {}.show",
            quoted_string_literal(&format!("{name}: ")),
            error_payload_name(index, 0).0
        )),
        len => {
            let mut parts = Vec::with_capacity(len.saturating_mul(2) + 2);
            parts.push(quoted_string_literal(&format!("{name}(")));
            for payload_index in 0..len {
                if payload_index > 0 {
                    parts.push(quoted_string_literal(", "));
                }
                parts.push(format!(
                    "{}.show",
                    error_payload_name(index, payload_index).0
                ));
            }
            parts.push(quoted_string_literal(")"));
            Some(parts.join(" + "))
        }
    }
}

fn quoted_string_literal(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for ch in text.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(ch),
        }
    }
    out.push('"');
    out
}

fn synthetic_error_wrap_source(
    modules: &ModuleTable,
    decl: &ModuleTypeDecl,
    error: &ErrorDecl,
    sources: &[ErrorLiftSource],
) -> Option<String> {
    if error.variants.is_empty() {
        return None;
    }
    let effect_row = error_effect_row_source(
        modules,
        std::iter::once(error).chain(sources.iter().map(|source| &source.source)),
    )?;
    let mut out = format!("pub wrap(action: [{effect_row}] _) = catch action:\n");
    for (index, variant) in error.variants.iter().enumerate() {
        let pattern = error_operation_pattern(&variant.name.0, &variant.payload, index)?;
        let value = error_constructor_expr(&variant.name.0, &variant.payload, index)?;
        out.push_str("    ");
        out.push_str(&pattern);
        out.push_str(", _ -> std::data::result::result::err (");
        out.push_str(&value);
        out.push_str(")\n");
    }
    for (source_index, source) in sources.iter().enumerate() {
        append_lifted_error_arms(
            modules,
            decl,
            source,
            source_index,
            "std::data::result::result::err",
            &mut out,
        )?;
    }
    out.push_str("    value -> std::data::result::result::ok value\n");
    Some(out)
}

fn synthetic_error_up_source(
    modules: &ModuleTable,
    decl: &ModuleTypeDecl,
    _error: &ErrorDecl,
    sources: &[ErrorLiftSource],
) -> Option<String> {
    if sources.is_empty() {
        return None;
    }
    let effect_row = error_effect_row_source(modules, sources.iter().map(|source| &source.source))?;
    let mut out = format!("pub up(action: [{effect_row}; '__error_up_tail] _) = catch action:\n");
    for (source_index, source) in sources.iter().enumerate() {
        append_lifted_error_arms(modules, decl, source, source_index, "#throw", &mut out)?;
    }
    out.push_str("    value -> value\n");
    Some(out)
}

fn append_lifted_error_arms(
    modules: &ModuleTable,
    decl: &ModuleTypeDecl,
    source: &ErrorLiftSource,
    source_index: usize,
    mode: &str,
    out: &mut String,
) -> Option<()> {
    for (variant_index, variant) in source.source.variants.iter().enumerate() {
        let prefix = format!("{source_index}_{variant_index}");
        let variant_path = error_variant_constructor_path(modules, &source.source, variant);
        let pattern = error_operation_pattern(&variant_path, &variant.payload, source_index)?;
        let mut value = error_constructor_expr(&variant_path, &variant.payload, source_index)?;
        for wrapper in &source.wrappers {
            value = format!("{wrapper} ({value})");
        }
        out.push_str("    ");
        out.push_str(&pattern.replace(
            &format!("__error_payload_{source_index}_"),
            &format!("__error_payload_{prefix}_"),
        ));
        out.push_str(", _ -> ");
        let value = value.replace(
            &format!("__error_payload_{source_index}_"),
            &format!("__error_payload_{prefix}_"),
        );
        if mode == "#throw" {
            out.push('(');
            out.push_str(&value);
            out.push_str(").throw\n");
        } else {
            out.push_str(mode);
            out.push_str(" (");
            out.push_str(&value);
            out.push_str(")\n");
        }
    }
    let _ = decl;
    Some(())
}

fn error_operation_pattern(
    path: &str,
    payload: &ConstructorPayload,
    index: usize,
) -> Option<String> {
    match constructor_payload_arity(payload) {
        0 => Some(path.to_string()),
        1 => Some(format!("{path} {}", error_payload_name(index, 0).0)),
        len => {
            let payloads = (0..len)
                .map(|payload_index| error_payload_name(index, payload_index).0)
                .collect::<Vec<_>>()
                .join(", ");
            Some(format!("{path} ({payloads})"))
        }
    }
}

fn error_constructor_expr(
    path: &str,
    payload: &ConstructorPayload,
    index: usize,
) -> Option<String> {
    match constructor_payload_arity(payload) {
        0 => Some(path.to_string()),
        1 => Some(format!("{path} {}", error_payload_name(index, 0).0)),
        len => {
            let payloads = (0..len)
                .map(|payload_index| error_payload_name(index, payload_index).0)
                .collect::<Vec<_>>()
                .join(", ");
            Some(format!("{path} ({payloads})"))
        }
    }
}

fn error_variant_constructor_path(
    modules: &ModuleTable,
    error: &ErrorDecl,
    variant: &ErrorVariantDecl,
) -> String {
    modules
        .type_decl_by_id(error.owner)
        .map(|decl| {
            modules
                .type_decl_path(&decl)
                .segments
                .into_iter()
                .chain(std::iter::once(variant.name.clone()))
                .map(|name| name.0)
                .collect::<Vec<_>>()
                .join("::")
        })
        .unwrap_or_else(|| variant.name.0.clone())
}

fn error_effect_row_source<'a>(
    modules: &ModuleTable,
    errors: impl IntoIterator<Item = &'a ErrorDecl>,
) -> Option<String> {
    let mut items = Vec::new();
    for error in errors {
        let item = error_type_source(modules, error)?;
        if !items.contains(&item) {
            items.push(item);
        }
    }
    Some(items.join(", "))
}

fn error_type_source(modules: &ModuleTable, error: &ErrorDecl) -> Option<String> {
    let decl = modules.type_decl_by_id(error.owner)?;
    let mut source = modules
        .type_decl_path(&decl)
        .segments
        .into_iter()
        .map(|name| name.0)
        .collect::<Vec<_>>()
        .join("::");
    for var in &error.type_vars {
        source.push(' ');
        source.push_str(&type_var_source(var));
    }
    Some(source)
}

fn type_var_source(var: &str) -> String {
    if var.starts_with('\'') {
        var.to_string()
    } else {
        format!("'{var}")
    }
}

fn signature_named_head(signature: &SignatureType) -> Option<TypeDeclId> {
    match signature {
        SignatureType::Named(id) => Some(*id),
        SignatureType::Apply { callee, .. } => signature_named_head(callee),
        _ => None,
    }
}

fn std_result_constructor_path(name: &str) -> Vec<Name> {
    names(&["std", "data", "result", "result", name])
}

fn synthetic_binding(source: &str) -> Option<Cst> {
    let root = SyntaxNode::<YulangLanguage>::new_root(parser::parse_module_to_green(source));
    root.children()
        .find(|node| node.kind() == SyntaxKind::Binding)
}

fn error_type_var_slots(infer: &mut crate::Arena, names: &[String]) -> FxHashMap<String, TypeVar> {
    names
        .iter()
        .cloned()
        .map(|name| (name, infer.fresh_type_var()))
        .collect()
}

impl<'a> ExprLowerer<'a> {
    fn lower_synthetic_error_throw_body(
        &mut self,
        node: &Cst,
        decl: &ModuleTypeDecl,
        error: &ErrorDecl,
    ) -> Result<Computation, LoweringError> {
        let before_locals = self.locals.len();
        let arg_value = self.fresh_type_var();
        let arg_pat = self.bind_pattern_local(
            Name("error".into()),
            arg_value,
            None,
            LocalCallReturnEffect::Annotated,
        );
        let body = self.lower_synthetic_error_throw_case(node, decl, error)?;
        self.locals.truncate(before_locals);

        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let arg = self.alloc_neg(Neg::Var(arg_value));
        let arg_eff = self.empty_neg_row();
        let ret_eff = self.alloc_pos(Pos::Var(body.effect));
        let ret = self.alloc_pos(Pos::Var(body.value));
        self.constrain_lower(
            value,
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
        );
        let expr = self.session.poly.add_expr(Expr::Lambda(arg_pat, body.expr));
        Ok(Computation::value(expr, value, effect))
    }

    fn lower_synthetic_error_throw_case(
        &mut self,
        node: &Cst,
        decl: &ModuleTypeDecl,
        error: &ErrorDecl,
    ) -> Result<Computation, LoweringError> {
        let scrutinee = self.lower_name(Name("error".into()))?;
        let result_value = self.fresh_type_var();
        let result_effect = self.fresh_type_var();
        let mut arms = Vec::new();
        for (index, variant) in error.variants.iter().enumerate() {
            let before_locals = self.locals.len();
            let pattern_value = self.fresh_type_var();
            let pattern_source =
                error_variant_pattern_source(&variant.name, &variant.payload, index)
                    .ok_or(LoweringError::UnsupportedSyntax { kind: node.kind() })?;
            let pattern = synthetic_case_pattern(&pattern_source)
                .ok_or(LoweringError::UnsupportedSyntax { kind: node.kind() })?;
            let pat = self.lower_match_pattern(&pattern, pattern_value)?;
            self.subtype_var_to_var(scrutinee.value, pattern_value);
            let body = self.lower_error_operation_call(decl, variant, index)?;
            self.subtype_var_to_var(body.value, result_value);
            self.subtype_var_to_var(body.effect, result_effect);
            arms.push(CaseArm {
                pat,
                guard: None,
                body: body.expr,
            });
            self.locals.truncate(before_locals);
        }
        let expr = self.session.poly.add_expr(Expr::Case(scrutinee.expr, arms));
        Ok(Computation::computation(expr, result_value, result_effect))
    }

    fn lower_error_operation_call(
        &mut self,
        decl: &ModuleTypeDecl,
        variant: &ErrorVariantDecl,
        index: usize,
    ) -> Result<Computation, LoweringError> {
        let label = self.error_operation_label(decl, &variant.name);
        let operation = self.lower_resolved_value_ref_at(label, variant.operation_def, None);
        match constructor_payload_arity(&variant.payload) {
            0 => {
                let unit = self.unit_expr();
                Ok(self.make_app(operation, unit))
            }
            1 => {
                let payload = self.lower_name(error_payload_name(index, 0))?;
                Ok(self.make_app(operation, payload))
            }
            len => {
                let payloads = (0..len)
                    .map(|payload_index| self.lower_name(error_payload_name(index, payload_index)))
                    .collect::<Result<Vec<_>, _>>()?;
                let tuple = self.tuple_computation(payloads);
                Ok(self.make_app(operation, tuple))
            }
        }
    }

    fn error_operation_label(&self, decl: &ModuleTypeDecl, name: &Name) -> String {
        self.modules
            .type_decl_path(decl)
            .segments
            .into_iter()
            .chain(std::iter::once(name.clone()))
            .map(|name| name.0)
            .collect::<Vec<_>>()
            .join("::")
    }

    fn tuple_computation(&mut self, items: Vec<Computation>) -> Computation {
        let exprs = items.iter().map(|item| item.expr).collect::<Vec<_>>();
        let value = self.fresh_type_var();
        let expansive = items.iter().any(|item| item.is_expansive());
        let effect = if expansive {
            self.fresh_type_var()
        } else {
            self.fresh_exact_pure_effect()
        };
        let expr = self.session.poly.add_expr(Expr::Tuple(exprs));
        let item_values = items
            .iter()
            .map(|item| self.alloc_pos(Pos::Var(item.value)))
            .collect::<Vec<_>>();
        for item in &items {
            self.subtype_var_to_var(item.effect, effect);
        }
        self.constrain_lower(value, Pos::Tuple(item_values));
        Computation::new(
            expr,
            value,
            effect,
            if expansive {
                Evaluation::Computation
            } else {
                Evaluation::Value
            },
        )
    }
}

fn error_variant_pattern_source(
    name: &Name,
    payload: &ConstructorPayload,
    index: usize,
) -> Option<String> {
    match constructor_payload_arity(payload) {
        0 => Some(name.0.clone()),
        1 => Some(format!("{} {}", name.0, error_payload_name(index, 0).0)),
        len => {
            let payloads = (0..len)
                .map(|payload_index| error_payload_name(index, payload_index).0)
                .collect::<Vec<_>>()
                .join(", ");
            Some(format!("{} ({payloads})", name.0))
        }
    }
}

fn synthetic_case_pattern(pattern: &str) -> Option<Cst> {
    let source = format!("case __error:\n  {pattern} -> ()\n");
    let root = SyntaxNode::<YulangLanguage>::new_root(parser::parse_module_to_green(&source));
    root.descendants()
        .find(|node| node.kind() == SyntaxKind::CaseArm)?
        .children()
        .find(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Pattern
                    | SyntaxKind::PatOr
                    | SyntaxKind::PatAs
                    | SyntaxKind::PatParenGroup
                    | SyntaxKind::PatList
            )
        })
}

fn stored_neg_signature_type(
    signature: &StoredSignature,
    builder: &NegSignatureBuilder,
) -> Result<SignatureType, LoweringError> {
    match signature {
        StoredSignature::Source(ty) => builder
            .build_type_expr(ty)
            .map(|signature| signature.as_type().clone())
            .map_err(|error| LoweringError::NegSignatureBuild { error }),
        StoredSignature::Lowered(signature) => Ok(signature.clone()),
    }
}

fn error_payload_name(variant_index: usize, payload_index: usize) -> Name {
    Name(format!("__error_payload_{variant_index}_{payload_index}"))
}

fn names(segments: &[&str]) -> Vec<Name> {
    segments
        .iter()
        .map(|segment| Name((*segment).to_string()))
        .collect()
}
