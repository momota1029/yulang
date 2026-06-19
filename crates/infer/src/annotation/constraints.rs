use super::*;

pub struct AnnConstraintLowerer<'a> {
    infer: &'a mut InferArena,
    modules: &'a ModuleTable,
    vars: FxHashMap<AnnTypeVarId, TypeVar>,
    new_var_level: Option<TypeLevel>,
}

impl<'a> AnnConstraintLowerer<'a> {
    pub fn new(infer: &'a mut InferArena, modules: &'a ModuleTable) -> Self {
        Self {
            infer,
            modules,
            vars: FxHashMap::default(),
            new_var_level: None,
        }
    }

    pub fn with_vars(
        infer: &'a mut InferArena,
        modules: &'a ModuleTable,
        vars: FxHashMap<AnnTypeVarId, TypeVar>,
    ) -> Self {
        Self {
            infer,
            modules,
            vars,
            new_var_level: None,
        }
    }

    pub fn with_vars_at_level(
        infer: &'a mut InferArena,
        modules: &'a ModuleTable,
        vars: FxHashMap<AnnTypeVarId, TypeVar>,
        new_var_level: TypeLevel,
    ) -> Self {
        Self {
            infer,
            modules,
            vars,
            new_var_level: Some(new_var_level),
        }
    }

    pub fn into_vars(self) -> FxHashMap<AnnTypeVarId, TypeVar> {
        self.vars
    }

    pub fn connect_value(
        &mut self,
        target: TypeVar,
        ann: &AnnType,
    ) -> Result<Vec<StackWeight>, AnnConstraintError> {
        let bounds = self.lower_value_bounds(ann)?;
        let target_upper = self.alloc_neg(Neg::Var(target));
        let target_lower = self.alloc_pos(Pos::Var(target));
        self.infer.subtype(bounds.pos, target_upper);
        self.infer.subtype(target_lower, bounds.neg);
        Ok(bounds.output_subtracts)
    }

    pub fn connect_value_upper(
        &mut self,
        target: TypeVar,
        ann: &AnnType,
    ) -> Result<Vec<StackWeight>, AnnConstraintError> {
        let bounds = self.lower_value_bounds(ann)?;
        let target_lower = self.alloc_pos(Pos::Var(target));
        self.infer.subtype(target_lower, bounds.neg);
        Ok(bounds.output_subtracts)
    }

    pub fn connect_computation(
        &mut self,
        target: AnnComputationTarget,
        ann: &AnnType,
    ) -> Result<Vec<StackWeight>, AnnConstraintError> {
        self.connect_computation_detailed(target, ann)
            .map(|connection| connection.subtracts)
    }

    pub fn connect_computation_detailed(
        &mut self,
        target: AnnComputationTarget,
        ann: &AnnType,
    ) -> Result<AnnComputationConnection, AnnConstraintError> {
        match ann {
            AnnType::Effectful { eff, ret } => {
                let mut subtracts = self.connect_value(target.value, ret)?;
                let effect_stack = self.connect_effectful_annotation_effect(target.effect, eff)?;
                subtracts.extend(predicate_weights(
                    &effect_stack.subtracts,
                    effect_stack_filter(&effect_stack),
                ));
                Ok(AnnComputationConnection {
                    subtracts,
                    effect_stack: Some(effect_stack),
                })
            }
            _ => self
                .connect_value(target.value, ann)
                .map(|subtracts| AnnComputationConnection {
                    subtracts,
                    effect_stack: None,
                }),
        }
    }

    pub fn connect_parameter_computation_detailed(
        &mut self,
        target: AnnComputationTarget,
        ann: &AnnType,
    ) -> Result<AnnComputationConnection, AnnConstraintError> {
        match ann {
            AnnType::Effectful { eff, ret } => {
                let mut subtracts = self.connect_value(target.value, ret)?;
                let effect_stack =
                    self.connect_parameter_effectful_annotation_effect(target.effect, eff)?;
                subtracts.extend(predicate_weights(
                    &effect_stack.subtracts,
                    effect_stack_filter(&effect_stack),
                ));
                Ok(AnnComputationConnection {
                    subtracts,
                    effect_stack: Some(effect_stack),
                })
            }
            _ => self
                .connect_value(target.value, ann)
                .map(|subtracts| AnnComputationConnection {
                    subtracts,
                    effect_stack: None,
                }),
        }
    }

    pub fn lower_role_arg(
        &mut self,
        ann: &AnnType,
    ) -> Result<crate::roles::RoleConstraintArg, AnnConstraintError> {
        let bounds = self.lower_value_bounds(ann)?;
        Ok(crate::roles::RoleConstraintArg {
            lower: bounds.pos,
            upper: bounds.neg,
        })
    }

    pub(in crate::annotation) fn lower_value_bounds(
        &mut self,
        ann: &AnnType,
    ) -> Result<AnnValueBounds, AnnConstraintError> {
        match ann {
            AnnType::Builtin(builtin) => Ok(AnnValueBounds {
                pos: self.lower_builtin_pos(*builtin),
                neg: self.lower_builtin_neg(*builtin),
                output_subtracts: Vec::new(),
            }),
            AnnType::Named(id) => {
                let path = self.type_decl_path(*id)?;
                Ok(AnnValueBounds {
                    pos: self.alloc_pos(Pos::Con(path.clone(), Vec::new())),
                    neg: self.alloc_neg(Neg::Con(path, Vec::new())),
                    output_subtracts: Vec::new(),
                })
            }
            AnnType::Var(var) => {
                let var = self.annotation_var(var);
                Ok(AnnValueBounds {
                    pos: self.alloc_pos(Pos::Var(var)),
                    neg: self.alloc_neg(Neg::Var(var)),
                    output_subtracts: Vec::new(),
                })
            }
            AnnType::Wildcard(_) => Ok(AnnValueBounds {
                pos: self.alloc_pos(Pos::Bot),
                neg: self.alloc_neg(Neg::Top),
                output_subtracts: Vec::new(),
            }),
            AnnType::EffectRow(row) => Ok(AnnValueBounds {
                pos: self.lower_effect_row_pos(row)?,
                neg: self.lower_effect_row_neg(row)?,
                output_subtracts: Vec::new(),
            }),
            AnnType::Effectful { ret, .. } => self.lower_value_bounds(ret),
            AnnType::Tuple(items) => {
                let mut pos_items = Vec::with_capacity(items.len());
                let mut neg_items = Vec::with_capacity(items.len());
                let mut output_subtracts = Vec::new();
                for item in items {
                    let bounds = self.lower_value_bounds(item)?;
                    pos_items.push(bounds.pos);
                    neg_items.push(bounds.neg);
                    output_subtracts.extend(bounds.output_subtracts);
                }
                Ok(AnnValueBounds {
                    pos: self.alloc_pos(Pos::Tuple(pos_items)),
                    neg: self.alloc_neg(Neg::Tuple(neg_items)),
                    output_subtracts,
                })
            }
            AnnType::Apply { callee, args } => {
                let (path, head_args) = self.constructor_path(callee)?;
                let mut neu_args = head_args;
                for arg in args_from_ann(args) {
                    neu_args.push(self.lower_invariant_arg(arg)?);
                }
                Ok(AnnValueBounds {
                    pos: self.alloc_pos(Pos::Con(path.clone(), neu_args.clone())),
                    neg: self.alloc_neg(Neg::Con(path, neu_args)),
                    output_subtracts: Vec::new(),
                })
            }
            AnnType::Function {
                param,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let param = self.lower_value_bounds(param)?;
                let arg_eff = self.lower_arg_effect_bounds(arg_eff.as_ref())?;
                let ret = self.lower_value_bounds(ret)?;
                let ret_eff = self.lower_ret_effect_bounds(ret_eff.as_ref())?;
                let ret_pos = self.wrap_non_subtracts(ret.pos, &ret_eff.subtracts);
                let pos = self.alloc_pos(Pos::Fun {
                    arg: param.neg,
                    arg_eff: arg_eff.neg,
                    ret_eff: ret_eff.pos,
                    ret: ret_pos,
                });
                let neg = self.alloc_neg(Neg::Fun {
                    arg: param.pos,
                    arg_eff: arg_eff.pos,
                    ret_eff: ret_eff.neg,
                    ret: ret.neg,
                });
                Ok(AnnValueBounds {
                    pos,
                    neg,
                    output_subtracts: ret_eff.subtracts,
                })
            }
        }
    }

    fn lower_arg_effect_bounds(
        &mut self,
        row: Option<&AnnEffectRow>,
    ) -> Result<AnnEffectBounds, AnnConstraintError> {
        let Some(row) = row else {
            return Ok(self.pure_effect_bounds());
        };
        if effect_row_has_wildcard(row) {
            let effect = self.infer.fresh_type_var();
            self.connect_effect_tail_exact(effect, row)?;
            let stack = self.effect_row_stack(row)?;
            self.register_stack_facts(effect, &stack.weight);
            let pos = self.alloc_pos(Pos::Var(effect));
            let neg = self.alloc_neg(Neg::Var(effect));
            return Ok(AnnEffectBounds {
                pos: self.wrap_pos_with_stack(pos, &stack.weight),
                neg: self.wrap_neg_with_stack(neg, &stack.weight),
                subtracts: Vec::new(),
            });
        }
        let effect = self.infer.fresh_type_var();
        self.connect_effect_row_lower(effect, row)?;
        Ok(AnnEffectBounds {
            pos: self.alloc_pos(Pos::Var(effect)),
            neg: self.alloc_neg(Neg::Var(effect)),
            subtracts: Vec::new(),
        })
    }

    fn lower_ret_effect_bounds(
        &mut self,
        row: Option<&AnnEffectRow>,
    ) -> Result<AnnEffectBounds, AnnConstraintError> {
        let Some(row) = row else {
            return Ok(self.pure_effect_bounds());
        };
        if row.items.is_empty()
            && let Some(tail) = &row.tail
        {
            let effect = self.annotation_var(tail);
            return Ok(AnnEffectBounds {
                pos: self.alloc_pos(Pos::Var(effect)),
                neg: self.alloc_neg(Neg::Var(effect)),
                subtracts: Vec::new(),
            });
        }

        let effect = self.infer.fresh_type_var();
        self.connect_effect_tail_exact(effect, row)?;
        let stack = self.effect_row_stack(row)?;
        self.register_stack_facts(effect, &stack.weight);
        let effect_pos = self.alloc_pos(Pos::Var(effect));
        let pos = self.wrap_pos_with_stack(effect_pos, &stack.weight);
        let subtracts =
            predicate_weights(&stack.ids, effect_stack_filter_from_weight(&stack.weight));
        Ok(AnnEffectBounds {
            pos,
            neg: self.alloc_neg(Neg::Var(effect)),
            subtracts,
        })
    }

    fn pure_effect_bounds(&mut self) -> AnnEffectBounds {
        let top = self.alloc_neg(Neg::Top);
        AnnEffectBounds {
            pos: self.alloc_pos(Pos::Bot),
            neg: self.alloc_neg(Neg::Row(Vec::new(), top)),
            subtracts: Vec::new(),
        }
    }

    fn connect_effectful_annotation_effect(
        &mut self,
        effect: TypeVar,
        row: &AnnEffectRow,
    ) -> Result<AnnEffectStackConnection, AnnConstraintError> {
        if row.items.is_empty()
            && let Some(tail) = &row.tail
        {
            let tail = self.annotation_var(tail);
            if tail != effect {
                let tail_lower = self.alloc_pos(Pos::Var(tail));
                let effect_upper = self.alloc_neg(Neg::Var(effect));
                self.infer.subtype(tail_lower, effect_upper);
                let effect_lower = self.alloc_pos(Pos::Var(effect));
                let tail_upper = self.alloc_neg(Neg::Var(tail));
                self.infer.subtype(effect_lower, tail_upper);
            }
            return Ok(AnnEffectStackConnection {
                inner: tail,
                arg_eff: self.alloc_neg(Neg::Var(tail)),
                weight: StackWeight::empty(),
                subtracts: Vec::new(),
            });
        }

        // 注釈残差は fresh な内側変数に立て、stack で包んで下から effect を抑える。
        // `stack(effect, push) <: effect` の自己辺は bounds replay で重みが際限なく
        // 合成される（spec の「自分へ戻るだけの制約は無限ループの燃料」）ため作らない。
        let inner = self.infer.fresh_type_var();
        self.connect_effect_tail_exact(inner, row)?;
        let stack = self.effect_row_stack(row)?;
        self.register_stack_facts(inner, &stack.weight);
        let inner_pos = self.alloc_pos(Pos::Var(inner));
        let stacked = self.wrap_pos_with_stack(inner_pos, &stack.weight);
        let upper = self.alloc_neg(Neg::Var(effect));
        self.infer.subtype(stacked, upper);
        let arg_eff = self.alloc_neg(Neg::Var(inner));
        Ok(AnnEffectStackConnection {
            inner,
            arg_eff,
            weight: stack.weight,
            subtracts: stack.ids,
        })
    }

    fn connect_parameter_effectful_annotation_effect(
        &mut self,
        effect: TypeVar,
        row: &AnnEffectRow,
    ) -> Result<AnnEffectStackConnection, AnnConstraintError> {
        if row.items.is_empty()
            && let Some(tail) = &row.tail
        {
            let tail = self.annotation_var(tail);
            if tail != effect {
                let tail_lower = self.alloc_pos(Pos::Var(tail));
                let effect_upper = self.alloc_neg(Neg::Var(effect));
                self.infer.subtype(tail_lower, effect_upper);
                let effect_lower = self.alloc_pos(Pos::Var(effect));
                let tail_upper = self.alloc_neg(Neg::Var(tail));
                self.infer.subtype(effect_lower, tail_upper);
            }
            return Ok(AnnEffectStackConnection {
                inner: tail,
                arg_eff: self.alloc_neg(Neg::Var(tail)),
                weight: StackWeight::empty(),
                subtracts: Vec::new(),
            });
        }

        let inner = self.infer.fresh_type_var();
        let stack = self.effect_row_stack(row)?;
        self.register_stack_facts(inner, &stack.weight);
        let inner_pos = self.alloc_pos(Pos::Var(inner));
        let stacked = self.wrap_pos_with_stack(inner_pos, &stack.weight);
        let upper = self.alloc_neg(Neg::Var(effect));
        self.infer.subtype(stacked, upper);
        let full_eff = self.alloc_neg(Neg::Var(effect));
        let arg_eff = if effect_row_has_wildcard(row) {
            full_eff
        } else {
            let row_eff = self.lower_effect_row_neg(row)?;
            self.alloc_neg(Neg::Intersection(full_eff, row_eff))
        };
        Ok(AnnEffectStackConnection {
            inner,
            arg_eff,
            weight: stack.weight,
            subtracts: stack.ids,
        })
    }

    fn register_stack_facts(&mut self, var: TypeVar, weight: &StackWeight) {
        for entry in weight.entries() {
            for subtractability in &entry.stack {
                self.infer
                    .declared_subtract_fact(var, entry.id, subtractability.clone());
            }
        }
    }

    fn connect_effect_row_lower(
        &mut self,
        effect: TypeVar,
        row: &AnnEffectRow,
    ) -> Result<(), AnnConstraintError> {
        if effect_row_has_wildcard(row) {
            return Ok(());
        }
        let lower = self.lower_effect_row_pos(row)?;
        let effect_upper = self.alloc_neg(Neg::Var(effect));
        self.infer.subtype(lower, effect_upper);
        Ok(())
    }

    fn connect_effect_tail_exact(
        &mut self,
        effect: TypeVar,
        row: &AnnEffectRow,
    ) -> Result<(), AnnConstraintError> {
        let Some(tail) = &row.tail else {
            return Ok(());
        };
        let tail = self.annotation_var(tail);
        if tail == effect {
            return Ok(());
        }
        let tail_lower = self.alloc_pos(Pos::Var(tail));
        let effect_upper = self.alloc_neg(Neg::Var(effect));
        self.infer.subtype(tail_lower, effect_upper);
        let effect_lower = self.alloc_pos(Pos::Var(effect));
        let tail_upper = self.alloc_neg(Neg::Var(tail));
        self.infer.subtype(effect_lower, tail_upper);
        Ok(())
    }

    fn effect_row_stack(&mut self, row: &AnnEffectRow) -> Result<EffectStack, AnnConstraintError> {
        if effect_row_has_wildcard(row) {
            let id = self.infer.fresh_subtract_id();
            return Ok(EffectStack {
                weight: StackWeight::push(id, Subtractability::All),
                ids: vec![id],
            });
        }

        let atoms = row
            .items
            .iter()
            .map(|atom| self.effect_atom_con(atom))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        if atoms.is_empty() {
            if row.tail.is_none() {
                let id = self.infer.fresh_subtract_id();
                return Ok(EffectStack {
                    weight: StackWeight::push(id, Subtractability::Empty),
                    ids: vec![id],
                });
            }
            return Ok(EffectStack::empty());
        }

        let id = self.infer.fresh_subtract_id();
        let subtractability = subtractability_from_atoms(atoms);
        Ok(EffectStack {
            weight: StackWeight::push(id, subtractability),
            ids: vec![id],
        })
    }

    fn lower_effect_row_pos(&mut self, row: &AnnEffectRow) -> Result<PosId, AnnConstraintError> {
        if effect_row_has_wildcard(row) {
            return Err(AnnConstraintError::WildcardEffectRowInTypePosition);
        }
        let mut items = row
            .items
            .iter()
            .map(|atom| self.lower_effect_atom_pos(atom))
            .collect::<Result<Vec<_>, _>>()?;
        if let Some(tail) = &row.tail {
            let tail = self.annotation_var(tail);
            items.push(self.alloc_pos(Pos::Var(tail)));
        }
        Ok(self.alloc_pos(Pos::Row(items)))
    }

    fn lower_effect_row_neg(&mut self, row: &AnnEffectRow) -> Result<NegId, AnnConstraintError> {
        if effect_row_has_wildcard(row) {
            return Err(AnnConstraintError::WildcardEffectRowInTypePosition);
        }
        let items = row
            .items
            .iter()
            .map(|atom| self.lower_effect_atom_neg(atom))
            .collect::<Result<Vec<_>, _>>()?;
        let tail = if let Some(tail) = &row.tail {
            let tail = self.annotation_var(tail);
            self.alloc_neg(Neg::Var(tail))
        } else {
            self.alloc_neg(Neg::Top)
        };
        Ok(self.alloc_neg(Neg::Row(items, tail)))
    }

    fn lower_subtractable_effect_row_neg(
        &mut self,
        row: &AnnEffectRow,
    ) -> Result<NegId, AnnConstraintError> {
        if row.items.is_empty()
            && let Some(tail) = &row.tail
        {
            let tail = self.annotation_var(tail);
            return Ok(self.alloc_neg(Neg::Var(tail)));
        }

        let effect = self.infer.fresh_type_var();
        self.connect_effect_tail_exact(effect, row)?;
        let stack = self.effect_row_stack(row)?;
        self.register_stack_facts(effect, &stack.weight);
        let effect = self.alloc_neg(Neg::Var(effect));
        Ok(self.wrap_neg_with_stack(effect, &stack.weight))
    }

    fn lower_effect_atom_pos(&mut self, atom: &AnnEffectAtom) -> Result<PosId, AnnConstraintError> {
        match atom {
            AnnEffectAtom::Type(ty) => self.lower_value_bounds(ty).map(|bounds| bounds.pos),
            AnnEffectAtom::Wildcard => Err(AnnConstraintError::WildcardEffectRowInTypePosition),
        }
    }

    fn lower_effect_atom_neg(&mut self, atom: &AnnEffectAtom) -> Result<NegId, AnnConstraintError> {
        match atom {
            AnnEffectAtom::Type(ty) => self.lower_value_bounds(ty).map(|bounds| bounds.neg),
            AnnEffectAtom::Wildcard => Err(AnnConstraintError::WildcardEffectRowInTypePosition),
        }
    }

    fn effect_atom_con(
        &mut self,
        atom: &AnnEffectAtom,
    ) -> Result<Option<(Vec<String>, Vec<NeuId>)>, AnnConstraintError> {
        match atom {
            AnnEffectAtom::Type(AnnType::Var(_)) => Ok(None),
            AnnEffectAtom::Type(ty) => self.constructor_path(ty).map(Some),
            AnnEffectAtom::Wildcard => Ok(None),
        }
    }

    fn lower_invariant_arg(&mut self, ann: &AnnType) -> Result<NeuId, AnnConstraintError> {
        let bounds = self.lower_invariant_arg_bounds(ann)?;
        Ok(self.alloc_neu(Neu::Bounds(bounds.pos, bounds.neg)))
    }

    fn lower_invariant_arg_bounds(
        &mut self,
        ann: &AnnType,
    ) -> Result<AnnValueBounds, AnnConstraintError> {
        match ann {
            AnnType::EffectRow(row) => Ok(AnnValueBounds {
                pos: self.lower_effect_row_tail_pos(row)?,
                neg: self.lower_subtractable_effect_row_neg(row)?,
                output_subtracts: Vec::new(),
            }),
            _ => self.lower_value_bounds(ann),
        }
    }

    fn lower_effect_row_tail_pos(
        &mut self,
        row: &AnnEffectRow,
    ) -> Result<PosId, AnnConstraintError> {
        if effect_row_has_wildcard(row) {
            return Err(AnnConstraintError::WildcardEffectRowInTypePosition);
        }
        let mut items = row
            .items
            .iter()
            .map(|atom| self.lower_effect_atom_pos(atom))
            .collect::<Result<Vec<_>, _>>()?;
        if let Some(tail) = &row.tail {
            let tail = self.annotation_var(tail);
            items.push(self.alloc_pos(Pos::Var(tail)));
        }
        Ok(self.union_pos(items))
    }

    fn lower_builtin_pos(&mut self, builtin: BuiltinType) -> PosId {
        match builtin {
            BuiltinType::Never => self.alloc_pos(Pos::Bot),
            BuiltinType::Int
            | BuiltinType::Float
            | BuiltinType::Bool
            | BuiltinType::FileHandle
            | BuiltinType::Unit => self.alloc_pos(Pos::Con(
                vec![builtin.surface_name().to_string()],
                Vec::new(),
            )),
        }
    }

    fn lower_builtin_neg(&mut self, builtin: BuiltinType) -> NegId {
        match builtin {
            BuiltinType::Never => self.alloc_neg(Neg::Bot),
            BuiltinType::Int
            | BuiltinType::Float
            | BuiltinType::Bool
            | BuiltinType::FileHandle
            | BuiltinType::Unit => self.alloc_neg(Neg::Con(
                vec![builtin.surface_name().to_string()],
                Vec::new(),
            )),
        }
    }

    fn constructor_path(
        &mut self,
        ann: &AnnType,
    ) -> Result<(Vec<String>, Vec<NeuId>), AnnConstraintError> {
        match ann {
            AnnType::Builtin(builtin) => Ok((vec![builtin.surface_name().to_string()], Vec::new())),
            AnnType::Named(id) => Ok((self.type_decl_path(*id)?, Vec::new())),
            AnnType::Apply { callee, args } => {
                let (path, mut head_args) = self.constructor_path(callee)?;
                for arg in args_from_ann(args) {
                    head_args.push(self.lower_invariant_arg(arg)?);
                }
                Ok((path, head_args))
            }
            ty => Err(AnnConstraintError::InvalidConstructorCallee { ty: ty.clone() }),
        }
    }

    fn type_decl_path(&mut self, id: TypeDeclId) -> Result<Vec<String>, AnnConstraintError> {
        let decl = self
            .modules
            .type_decl_by_id(id)
            .ok_or(AnnConstraintError::MissingTypeDecl { id })?;
        let path = self
            .modules
            .type_decl_path(&decl)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect::<Vec<_>>();
        if decl.kind == ModuleTypeKind::Act {
            self.infer.register_effect_family_path(path.clone());
        }
        Ok(path)
    }

    fn annotation_var(&mut self, var: &AnnTypeVar) -> TypeVar {
        if let Some(found) = self.vars.get(&var.id) {
            return *found;
        }
        let ty = if let Some(level) = self.new_var_level {
            self.infer.fresh_type_var_at(level)
        } else {
            self.infer.fresh_type_var()
        };
        self.vars.insert(var.id, ty);
        ty
    }

    fn wrap_non_subtracts(&mut self, pos: PosId, subtracts: &[StackWeight]) -> PosId {
        subtracts.iter().fold(pos, |inner, weight| {
            self.alloc_pos(Pos::NonSubtract(inner, weight.clone()))
        })
    }

    fn wrap_pos_with_stack(&mut self, pos: PosId, weight: &StackWeight) -> PosId {
        if weight.is_empty() {
            return pos;
        }
        self.alloc_pos(Pos::Stack {
            inner: pos,
            weight: weight.clone(),
        })
    }

    fn wrap_neg_with_stack(&mut self, neg: NegId, weight: &StackWeight) -> NegId {
        if weight.is_empty() {
            return neg;
        }
        self.alloc_neg(Neg::Stack {
            inner: neg,
            weight: weight.clone(),
        })
    }

    fn union_pos(&mut self, input: Vec<PosId>) -> PosId {
        let mut parts = Vec::new();
        for part in input {
            if matches!(self.infer.constraints().types().pos(part), Pos::Bot)
                || parts.contains(&part)
            {
                continue;
            }
            parts.push(part);
        }
        let Some(first) = parts.first().copied() else {
            return self.alloc_pos(Pos::Bot);
        };
        parts
            .into_iter()
            .skip(1)
            .fold(first, |acc, part| self.alloc_pos(Pos::Union(acc, part)))
    }

    fn alloc_pos(&mut self, pos: Pos) -> PosId {
        self.infer.alloc_pos(pos)
    }

    fn alloc_neg(&mut self, neg: Neg) -> NegId {
        self.infer.alloc_neg(neg)
    }

    fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        self.infer.alloc_neu(neu)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::annotation) struct AnnValueBounds {
    pub(in crate::annotation) pos: PosId,
    pub(in crate::annotation) neg: NegId,
    pub(in crate::annotation) output_subtracts: Vec<StackWeight>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AnnEffectBounds {
    pos: PosId,
    neg: NegId,
    subtracts: Vec<StackWeight>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EffectStack {
    weight: StackWeight,
    ids: Vec<SubtractId>,
}

impl EffectStack {
    fn empty() -> Self {
        Self {
            weight: StackWeight::empty(),
            ids: Vec::new(),
        }
    }
}

fn predicate_weights(ids: &[SubtractId], filter: Subtractability) -> Vec<StackWeight> {
    ids.iter()
        .map(|id| StackWeight::pop(*id).with_filter(filter.clone()))
        .collect()
}

fn effect_stack_filter(stack: &AnnEffectStackConnection) -> Subtractability {
    effect_stack_filter_from_weight(&stack.weight)
}

fn effect_stack_filter_from_weight(weight: &StackWeight) -> Subtractability {
    weight
        .stack_items()
        .cloned()
        .reduce(Subtractability::intersect)
        .unwrap_or(Subtractability::All)
}

fn subtractability_from_atoms(atoms: Vec<(Vec<String>, Vec<NeuId>)>) -> Subtractability {
    match atoms.as_slice() {
        [] => Subtractability::Empty,
        [(path, args)] => Subtractability::Set(path.clone(), args.clone()),
        _ => Subtractability::SetMany(atoms),
    }
}
