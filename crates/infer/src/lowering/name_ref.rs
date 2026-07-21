//! Name and local reference lowering.

use super::*;

impl<'a> ExprLowerer<'a> {
    pub(super) fn lower_path_name_at(
        &mut self,
        path: &[Name],
        source_range: Option<SourceRange>,
    ) -> Result<Computation, LoweringError> {
        if let Some(builtin) = builtin_op_from_path(path) {
            return self.lower_builtin_op(builtin);
        }

        let Some(target) = self.modules.value_path_at(self.module, path, self.site) else {
            return Err(LoweringError::UnresolvedName {
                name: Name(path_label(path)),
                source_range,
            });
        };
        Ok(self.lower_resolved_value_ref_at(path_label(path), target, source_range))
    }

    pub(super) fn lower_std_value_ref(
        &mut self,
        path: Vec<String>,
    ) -> Result<Computation, LoweringError> {
        let path = path.into_iter().map(Name).collect::<Vec<_>>();
        let Some(target) =
            self.modules
                .value_path_at(self.modules.root_id(), &path, module_path_lookup_site())
        else {
            return Err(LoweringError::UnresolvedName {
                name: Name(path_label(&path)),
                source_range: None,
            });
        };
        Ok(self.lower_resolved_value_ref(path_label(&path), target))
    }

    pub(super) fn lower_name(&mut self, name: Name) -> Result<Computation, LoweringError> {
        self.lower_name_at(name, None)
    }

    pub(super) fn lower_name_at(
        &mut self,
        name: Name,
        source_range: Option<SourceRange>,
    ) -> Result<Computation, LoweringError> {
        if name.0 == "return"
            && let Some(target) = self.current_sub_return_target().cloned()
        {
            return Ok(self.lower_sub_return_target(&target));
        }

        if let Some(local) = self.local_binding(&name) {
            return Ok(self.lower_local_name(name, local, source_range));
        }

        match name.0.as_str() {
            "true" => return Ok(self.lower_bool(true)),
            "false" => return Ok(self.lower_bool(false)),
            _ => {}
        }

        let Some(target) = self.modules.lexical_value_at(self.module, &name, self.site) else {
            return Err(LoweringError::UnresolvedName { name, source_range });
        };
        let label = name.0.clone();
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        let reference = self.session.poly.add_ref();
        if let Some(labels) = self.labels.as_mut() {
            labels.set_ref_label(reference, label);
        }
        self.session.refs.insert(
            reference,
            RefUse {
                parent: self.parent,
                value,
                source_span: self.source_span(source_range),
            },
        );
        self.known_ref_targets.insert(reference, target);
        self.session.enqueue(AnalysisWork::ApplyRefResolution {
            ref_id: reference,
            target,
        });

        let expr = self.session.poly.add_expr(Expr::Var(reference));
        Ok(Computation::value(expr, value, effect))
    }

    pub(super) fn lower_sigil_name_at(
        &mut self,
        text: &str,
        source_range: Option<SourceRange>,
    ) -> Result<Computation, LoweringError> {
        let Some(reference_name) = var_read_reference_name(text) else {
            return self.lower_name_at(Name(text.to_string()), source_range);
        };
        let reference = match self.lower_name_at(reference_name, source_range) {
            Ok(reference) => reference,
            Err(LoweringError::UnresolvedName { .. })
                if self
                    .modules
                    .lexical_value_at(self.module, &Name(text.to_string()), self.site)
                    .is_some() =>
            {
                return Err(LoweringError::UnsupportedTopLevelVarBinding {
                    name: Name(text.to_string()),
                    source_range,
                });
            }
            Err(error) => return Err(error),
        };
        let get = self.lower_synthetic_selection(reference, "get".to_string());
        let unit = self.unit_expr();
        Ok(self.make_app(get, unit))
    }

    pub(super) fn lower_local_name(
        &mut self,
        name: Name,
        local: LocalBinding,
        source_range: Option<SourceRange>,
    ) -> Computation {
        let (effect, effect_view) = self.local_effect_slot(local.effect.clone());
        let value = self.instantiate_local_value(&local);
        let reference = self.session.poly.add_ref();
        self.session.poly.resolve_ref(reference, local.def);
        if let Some(labels) = self.labels.as_mut() {
            labels.set_ref_label(reference, name.0);
        }
        self.session.refs.insert(
            reference,
            RefUse {
                parent: self.parent,
                value,
                source_span: self.source_span(source_range),
            },
        );

        let expr = self.session.poly.add_expr(Expr::Var(reference));
        let computation = Computation::value(expr, value, effect);
        match effect_view {
            Some(view) => computation.with_effect_view(view),
            None => computation,
        }
    }

    fn local_effect_slot(
        &mut self,
        effect: Option<LocalEffect>,
    ) -> (TypeVar, Option<EffectViewId>) {
        match effect {
            Some(LocalEffect::Var(effect)) => (effect, None),
            Some(stack @ LocalEffect::Stack { effect, .. }) => {
                let view = self.add_effect_view(stack);
                (effect, Some(view))
            }
            None => (self.fresh_exact_pure_effect(), None),
        }
    }

    fn add_effect_view(&mut self, effect: LocalEffect) -> EffectViewId {
        let id = EffectViewId(self.effect_views.len() as u32);
        self.effect_views.push(effect);
        id
    }

    pub(super) fn effect_view(&self, id: EffectViewId) -> &LocalEffect {
        &self.effect_views[id.0 as usize]
    }

    pub(super) fn subtype_var_to_local_effect(&mut self, source: TypeVar, target: &LocalEffect) {
        match target {
            LocalEffect::Var(target) => self.subtype_var_to_var(source, *target),
            LocalEffect::Stack { effect, .. } => {
                let lower = self.alloc_pos(Pos::Var(source));
                let upper = self.alloc_neg(Neg::Var(*effect));
                self.session.infer.subtype(
                    lower,
                    upper,
                    crate::constraints::OriginId::unknown_internal(),
                );
            }
        }
    }

    pub(super) fn local_binding(&self, name: &Name) -> Option<LocalBinding> {
        self.locals
            .iter()
            .rev()
            .find(|local| &local.name == name)
            .cloned()
    }

    pub(super) fn current_sub_return_target(&self) -> Option<&SubReturnTarget> {
        self.sub_syntax_scopes
            .last()
            .map(|scope| &scope.bare_return)
    }

    pub(super) fn sub_label_return_target(&self, receiver: ExprId) -> Option<&SubReturnTarget> {
        let label_def = self.expr_local_def(receiver)?;
        self.sub_syntax_scopes
            .iter()
            .rev()
            .flat_map(|scope| scope.labels.iter().rev())
            .find(|label| label.label_def == label_def)
            .map(|label| &label.target)
    }

    fn expr_local_def(&self, expr: ExprId) -> Option<DefId> {
        let Expr::Var(reference) = self.session.poly.expr(expr) else {
            return None;
        };
        self.session.poly.ref_target(*reference)
    }

    pub(super) fn lower_sub_return_target(&mut self, target: &SubReturnTarget) -> Computation {
        self.lower_resolved_value_ref(target.label.clone(), target.def)
    }
}
