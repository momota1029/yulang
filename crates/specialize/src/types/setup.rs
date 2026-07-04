use super::*;

impl<'a> SchemeMaterializer<'a> {
    pub(super) fn new(arena: &'a TypeArena, def: poly_expr::DefId, scheme: &Scheme) -> Self {
        Self {
            arena,
            def,
            quantifiers: scheme.quantifiers.iter().copied().collect(),
            substitution: HashMap::new(),
            kinds: HashMap::new(),
            default_kinds: HashMap::new(),
            track_unquantified: false,
            track_empty_bounds: false,
            empty_bound_kinds: Vec::new(),
            empty_bound_types: RefCell::new(VecDeque::new()),
            function_materialization: FunctionMaterialization::Runtime,
            bound_materialization: BoundMaterialization::Structural,
            inline_bound_kinds: HashMap::new(),
            inline_bound_order: Vec::new(),
            inline_bound_substitution: HashMap::new(),
        }
    }

    pub(super) fn new_tracking_all_vars(
        arena: &'a TypeArena,
        def: poly_expr::DefId,
        scheme: &Scheme,
    ) -> Self {
        Self {
            arena,
            def,
            quantifiers: scheme.quantifiers.iter().copied().collect(),
            substitution: HashMap::new(),
            kinds: HashMap::new(),
            default_kinds: HashMap::new(),
            track_unquantified: true,
            track_empty_bounds: true,
            empty_bound_kinds: Vec::new(),
            empty_bound_types: RefCell::new(VecDeque::new()),
            function_materialization: FunctionMaterialization::Runtime,
            bound_materialization: BoundMaterialization::Structural,
            inline_bound_kinds: HashMap::new(),
            inline_bound_order: Vec::new(),
            inline_bound_substitution: HashMap::new(),
        }
    }

    pub(super) fn new_tracking_open_vars(
        arena: &'a TypeArena,
        def: poly_expr::DefId,
        scheme: &Scheme,
    ) -> Self {
        Self {
            arena,
            def,
            quantifiers: scheme.quantifiers.iter().copied().collect(),
            substitution: HashMap::new(),
            kinds: HashMap::new(),
            default_kinds: HashMap::new(),
            track_unquantified: true,
            track_empty_bounds: false,
            empty_bound_kinds: Vec::new(),
            empty_bound_types: RefCell::new(VecDeque::new()),
            function_materialization: FunctionMaterialization::Runtime,
            bound_materialization: BoundMaterialization::Structural,
            inline_bound_kinds: HashMap::new(),
            inline_bound_order: Vec::new(),
            inline_bound_substitution: HashMap::new(),
        }
    }

    pub(super) fn use_inference_functions(&mut self) {
        self.function_materialization = FunctionMaterialization::Inference;
    }

    pub(super) fn use_inline_bounds(&mut self) {
        self.bound_materialization = BoundMaterialization::Fresh;
    }

    pub(super) fn collect_scheme_kinds(&mut self, scheme: &Scheme) {
        self.collect_pos_kind(scheme.predicate, TypeContext::Value);
        for predicate in &scheme.role_predicates {
            for input in &predicate.inputs {
                match input {
                    RolePredicateArg::Covariant(pos) => {
                        self.collect_pos_kind(*pos, TypeContext::Value);
                    }
                    RolePredicateArg::Contravariant(neg) => {
                        self.collect_neg_kind(*neg, TypeContext::Value);
                    }
                    RolePredicateArg::Invariant(neu) => {
                        self.collect_neu_kind(*neu, TypeContext::Value);
                    }
                }
            }
            for associated in &predicate.associated {
                self.collect_neu_kind(associated.value, TypeContext::Value);
            }
        }
    }

    pub(super) fn default_unbound_quantifiers(&mut self) {
        for quantifier in &self.quantifiers {
            if self.substitution.contains_key(quantifier) {
                continue;
            }
            let kind = self.kind_for(*quantifier).unwrap_or(QuantifierKind::Value);
            self.substitution.insert(*quantifier, kind.default_type());
        }
    }

    pub(super) fn bind_var(&mut self, var: TypeVar, ty: &Type) -> Result<(), SpecializeError> {
        let ty = simplify_type(ty.clone());
        if let Some(existing) = self.substitution.get(&var) {
            if existing == &ty {
                return Ok(());
            }
            if matches!(existing, Type::Any) {
                self.substitution.insert(var, ty);
                return Ok(());
            }
            if matches!(ty, Type::OpenVar(_) | Type::Any) {
                return Ok(());
            }
            if matches!(existing, Type::OpenVar(_)) {
                self.substitution.insert(var, ty);
                return Ok(());
            }
            if existing.is_pure_effect() && ty.is_pure_effect() {
                return Ok(());
            }
            if self
                .kind_for(var)
                .is_some_and(|kind| kind == QuantifierKind::Effect)
            {
                let merged = merge_effect_substitution(existing.clone(), ty);
                self.substitution.insert(var, merged);
                return Ok(());
            }
            return Err(SpecializeError::ConflictingTypeSubstitution {
                def: mono::DefId(self.def.0),
                var: var.0,
                existing: existing.clone(),
                incoming: ty,
            });
        }
        self.substitution.insert(var, ty);
        Ok(())
    }

    pub(super) fn record_kind(&mut self, var: TypeVar, context: TypeContext) {
        if !self.track_unquantified && !self.quantifiers.contains(&var) {
            return;
        }
        let incoming = QuantifierKind::from_context(context);
        self.kinds
            .entry(var)
            .and_modify(|kind| {
                if incoming == QuantifierKind::Value {
                    *kind = QuantifierKind::Value;
                }
            })
            .or_insert(incoming);
    }

    pub(super) fn record_default_kind(&mut self, var: TypeVar, context: TypeContext) {
        if !self.track_unquantified && !self.quantifiers.contains(&var) {
            return;
        }
        if self.kinds.contains_key(&var) {
            return;
        }
        let incoming = QuantifierKind::from_context(context);
        self.default_kinds
            .entry(var)
            .and_modify(|kind| {
                if incoming == QuantifierKind::Value {
                    *kind = QuantifierKind::Value;
                }
            })
            .or_insert(incoming);
    }

    pub(super) fn kind_for(&self, var: TypeVar) -> Option<QuantifierKind> {
        self.kinds
            .get(&var)
            .copied()
            .or_else(|| self.default_kinds.get(&var).copied())
    }

    pub(super) fn record_inline_bound_kind(&mut self, id: NeuId, context: TypeContext) {
        if !self.inline_bound_kinds.contains_key(&id) {
            self.inline_bound_order.push(id);
        }
        let incoming = QuantifierKind::from_context(context);
        self.inline_bound_kinds
            .entry(id)
            .and_modify(|kind| {
                if incoming == QuantifierKind::Value {
                    *kind = QuantifierKind::Value;
                }
            })
            .or_insert(incoming);
    }

    pub(super) fn substitute_unbound_tracked_vars(
        &mut self,
        fresh: &mut impl FnMut(SchemeQuantifierKind) -> Type,
    ) {
        let mut vars = self.kinds.keys().copied().collect::<Vec<_>>();
        vars.extend(self.default_kinds.keys().copied());
        vars.sort_by_key(|var| var.0);
        vars.dedup();
        for var in vars {
            if self.substitution.contains_key(&var) {
                continue;
            }
            let kind = self.kind_for(var).unwrap_or(QuantifierKind::Value);
            self.substitution.insert(var, fresh(kind.into()));
        }
    }

    pub(super) fn substitute_empty_bounds(
        &mut self,
        fresh: &mut impl FnMut(SchemeQuantifierKind) -> Type,
    ) {
        self.empty_bound_types = RefCell::new(
            self.empty_bound_kinds
                .iter()
                .copied()
                .map(|context| fresh(QuantifierKind::from_context(context).into()))
                .collect(),
        );
    }

    pub(super) fn substitute_inline_bounds(
        &mut self,
        fresh: &mut impl FnMut(SchemeQuantifierKind) -> Type,
    ) {
        for id in &self.inline_bound_order {
            if self.inline_bound_substitution.contains_key(id) {
                continue;
            }
            let kind = self
                .inline_bound_kinds
                .get(id)
                .copied()
                .unwrap_or(QuantifierKind::Value);
            self.inline_bound_substitution
                .insert(*id, fresh(kind.into()));
        }
    }
}
