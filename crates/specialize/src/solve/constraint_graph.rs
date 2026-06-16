use super::*;

impl<'a> ConstraintGraph<'a> {
    pub(super) fn new(arena: &'a poly_expr::Arena) -> Self {
        Self {
            arena,
            slots: Vec::new(),
            role_demands: Vec::new(),
            pending: VecDeque::new(),
        }
    }

    pub(super) fn fresh_slot(&mut self, kind: TypeSlotKind) -> Type {
        let id = self.slots.len() as u32;
        self.slots.push(TypeSlot::new(kind));
        Type::OpenVar(id)
    }

    pub(super) fn ensure_slot(&self, slot: u32) -> Result<(), SpecializeError> {
        if (slot as usize) < self.slots.len() {
            return Ok(());
        }
        Err(SpecializeError::InvalidTypeSlot { slot })
    }

    pub(super) fn add_role_demands(
        &mut self,
        demands: impl IntoIterator<Item = types::InstantiatedRolePredicate>,
    ) {
        self.role_demands.extend(demands);
    }

    pub(super) fn constrain_recursive_bounds(
        &mut self,
        bounds: impl IntoIterator<Item = types::InstantiatedRecursiveBound>,
    ) -> Result<(), SpecializeError> {
        for bound in bounds {
            self.constrain_subtype(bound.lower, bound.value.clone())?;
            self.constrain_subtype(bound.value, bound.upper)?;
        }
        Ok(())
    }

    pub(super) fn resolve_role_demands(&mut self) -> Result<(), SpecializeError> {
        let mut applied = HashSet::new();
        loop {
            self.solve_constraints()?;
            let mut progressed = false;
            let demands = self.role_demands.clone();
            for demand in demands {
                if applied.contains(&demand) {
                    continue;
                }
                if self.try_apply_role_demand(&demand)? {
                    applied.insert(demand);
                    progressed = true;
                }
            }
            if !progressed {
                return Ok(());
            }
        }
    }

    pub(super) fn try_apply_role_demand(
        &mut self,
        demand: &types::InstantiatedRolePredicate,
    ) -> Result<bool, SpecializeError> {
        let Some(input_types) = self.resolve_role_input_types(demand)? else {
            return Ok(false);
        };
        let applications = self
            .arena
            .role_impls
            .candidates(&demand.role)
            .iter()
            .filter_map(|candidate| {
                roles::candidate_application(&self.arena.typ, demand, candidate, &input_types)
            })
            .collect::<Vec<_>>();
        let [application] = applications.as_slice() else {
            return Ok(false);
        };

        for (lower, candidate, upper) in &application.associated {
            self.constrain_subtype(lower.clone(), candidate.clone())?;
            self.constrain_subtype(candidate.clone(), upper.clone())?;
        }
        self.add_role_demands(application.prerequisites.clone());
        Ok(true)
    }

    pub(super) fn resolve_role_input_types(
        &self,
        demand: &types::InstantiatedRolePredicate,
    ) -> Result<Option<Vec<Type>>, SpecializeError> {
        let mut resolver = TypeResolver::new(self);
        let mut inputs = Vec::with_capacity(demand.inputs.len());
        for input in &demand.inputs {
            let Some(ty) = resolve_role_arg_exact_type(self, &mut resolver, input)? else {
                return Ok(None);
            };
            inputs.push(ty);
        }
        Ok(Some(inputs))
    }

    pub(super) fn slot(&self, slot: u32) -> Result<&TypeSlot, SpecializeError> {
        self.slots
            .get(slot as usize)
            .ok_or(SpecializeError::InvalidTypeSlot { slot })
    }

    pub(super) fn slot_is_value(&self, slot: u32) -> bool {
        self.slots
            .get(slot as usize)
            .is_some_and(|slot| slot.kind == TypeSlotKind::Value)
    }

    #[track_caller]
    pub(super) fn constrain_subtype(
        &mut self,
        lower: Type,
        upper: Type,
    ) -> Result<(), SpecializeError> {
        if lower != upper {
            self.pending.push_back(SubtypeConstraint { lower, upper });
        }
        Ok(())
    }

    pub(super) fn solve_constraints(&mut self) -> Result<(), SpecializeError> {
        while let Some(constraint) = self.pending.pop_front() {
            self.process_subtype(constraint.lower, constraint.upper)?;
        }
        Ok(())
    }

    pub(super) fn solve_type_graph(&self) -> Result<GraphSolution, SpecializeError> {
        let mut solution = GraphSolution::new(self.slots.len());
        loop {
            let mut progressed = false;
            for slot in 0..self.slots.len() {
                if solution.slots[slot].is_some() {
                    continue;
                }
                let mut resolver = TypeResolver::with_solution(self, &solution);
                if let Some(ty) = resolver.try_slot_solution(slot as u32)? {
                    solution.slots[slot] = Some(ty);
                    progressed = true;
                }
            }
            if !progressed {
                return Ok(solution);
            }
        }
    }

    pub(super) fn process_subtype(
        &mut self,
        lower: Type,
        upper: Type,
    ) -> Result<(), SpecializeError> {
        if lower == upper {
            return Ok(());
        }
        match (lower, upper) {
            (Type::Never, _) | (_, Type::Any) => Ok(()),
            (Type::OpenVar(lower), Type::OpenVar(upper)) => self.add_edge(lower, upper),
            (Type::Thunk { value, .. }, Type::OpenVar(slot)) if self.slot_is_value(slot) => {
                self.constrain_subtype(*value, Type::OpenVar(slot))
            }
            (
                Type::OpenVar(slot),
                Type::Thunk {
                    effect: upper_effect,
                    value: upper_value,
                },
            ) if self.slot_is_value(slot) => {
                self.constrain_subtype(Type::OpenVar(slot), *upper_value)?;
                self.constrain_subtype(Type::pure_effect(), *upper_effect)
            }
            (Type::OpenVar(slot), upper) => self.add_upper(slot, upper),
            (lower, Type::OpenVar(slot)) => self.add_lower(slot, lower),
            (
                Type::Fun {
                    arg: lower_arg,
                    arg_effect: lower_arg_eff,
                    ret_effect: lower_ret_eff,
                    ret: lower_ret,
                },
                Type::Fun {
                    arg: upper_arg,
                    arg_effect: upper_arg_eff,
                    ret_effect: upper_ret_eff,
                    ret: upper_ret,
                },
            ) => {
                self.constrain_subtype(*upper_arg, *lower_arg)?;
                self.constrain_subtype(*upper_arg_eff, *lower_arg_eff)?;
                self.constrain_subtype(*lower_ret_eff, *upper_ret_eff)?;
                self.constrain_subtype(*lower_ret, *upper_ret)
            }
            (
                Type::Thunk {
                    effect: lower_effect,
                    value: lower_value,
                },
                Type::Thunk {
                    effect: upper_effect,
                    value: upper_value,
                },
            ) => {
                self.constrain_subtype(*lower_effect, *upper_effect)?;
                self.constrain_subtype(*lower_value, *upper_value)
            }
            (
                lower,
                Type::Thunk {
                    effect: upper_effect,
                    value: upper_value,
                },
            ) => {
                self.constrain_subtype(lower, *upper_value)?;
                self.constrain_subtype(Type::pure_effect(), *upper_effect)
            }
            (
                Type::Thunk {
                    effect: lower_effect,
                    value: lower_value,
                },
                upper,
            ) => {
                self.constrain_subtype(*lower_value, upper)?;
                self.constrain_subtype(*lower_effect, Type::pure_effect())
            }
            (
                Type::Con {
                    path: lower_path,
                    args: lower_args,
                },
                Type::Con {
                    path: upper_path,
                    args: upper_args,
                },
            ) if lower_path == upper_path && lower_args.len() == upper_args.len() => {
                for (lower, upper) in lower_args.into_iter().zip(upper_args) {
                    self.constrain_subtype(lower.clone(), upper.clone())?;
                    self.constrain_subtype(upper, lower)?;
                }
                Ok(())
            }
            (
                Type::Con {
                    path: lower_path,
                    args: lower_args,
                },
                Type::Con {
                    path: upper_path,
                    args: upper_args,
                },
            ) => {
                let lower = Type::Con {
                    path: lower_path.clone(),
                    args: lower_args,
                };
                let upper = Type::Con {
                    path: upper_path.clone(),
                    args: upper_args,
                };
                self.constrain_direct_cast(&lower_path, &upper_path, lower, upper)
            }
            (Type::Tuple(lower_items), Type::Tuple(upper_items))
                if lower_items.len() == upper_items.len() =>
            {
                for (lower, upper) in lower_items.into_iter().zip(upper_items) {
                    self.constrain_subtype(lower, upper)?;
                }
                Ok(())
            }
            (Type::Record(lower_fields), Type::Record(upper_fields)) => {
                for upper_field in upper_fields {
                    let Some(lower_field) = record_field_type(&lower_fields, &upper_field.name)
                    else {
                        continue;
                    };
                    self.constrain_subtype(lower_field.value.clone(), upper_field.value)?;
                }
                Ok(())
            }
            (Type::PolyVariant(lower_variants), Type::PolyVariant(upper_variants)) => {
                for lower_variant in lower_variants {
                    let Some(upper_variant) = upper_variants.iter().find(|variant| {
                        variant.name == lower_variant.name
                            && variant.payloads.len() == lower_variant.payloads.len()
                    }) else {
                        continue;
                    };
                    for (lower, upper) in lower_variant
                        .payloads
                        .into_iter()
                        .zip(upper_variant.payloads.iter().cloned())
                    {
                        self.constrain_subtype(lower, upper)?;
                    }
                }
                Ok(())
            }
            (Type::EffectRow(lower_items), Type::EffectRow(upper_items)) => {
                self.constrain_effect_rows(lower_items, upper_items)
            }
            (Type::Stack { inner: lower, .. }, Type::Stack { inner: upper, .. }) => {
                self.constrain_subtype(*lower, *upper)
            }
            (Type::Stack { inner, weight }, upper) => {
                let Some(lower) = self.stack_constraint_projection(*inner, weight) else {
                    return Ok(());
                };
                self.constrain_subtype(lower, upper)
            }
            (lower, Type::Stack { inner, weight }) => {
                let Some(upper) = self.stack_constraint_projection(*inner, weight) else {
                    return Ok(());
                };
                self.constrain_subtype(lower, upper)
            }
            (Type::Union(left, right), upper) => {
                self.constrain_subtype(*left, upper.clone())?;
                self.constrain_subtype(*right, upper)
            }
            (lower, Type::Intersection(left, right)) => {
                self.constrain_subtype(lower.clone(), *left)?;
                self.constrain_subtype(lower, *right)
            }
            _ => Ok(()),
        }
    }

    pub(super) fn constrain_direct_cast(
        &mut self,
        source: &[String],
        target: &[String],
        lower: Type,
        upper: Type,
    ) -> Result<(), SpecializeError> {
        let candidates = self
            .arena
            .cast_rules
            .iter()
            .filter(|rule| rule.source == source && rule.target == target)
            .cloned()
            .collect::<Vec<_>>();
        for candidate in candidates {
            let predicate = self.instantiate_cast_scheme(candidate.def, &candidate.scheme)?;
            self.constrain_subtype(
                predicate,
                types::pure_function_type(lower.clone(), upper.clone()),
            )?;
        }
        Ok(())
    }

    pub(super) fn stack_constraint_projection(
        &self,
        inner: Type,
        weight: mono::StackWeight,
    ) -> Option<Type> {
        match types::simplify_stack_type(inner, weight) {
            Type::Stack { inner, .. } if self.stack_constraint_can_use_inner(&inner) => {
                Some(*inner)
            }
            Type::Stack { .. } => None,
            ty => Some(ty),
        }
    }

    pub(super) fn stack_constraint_can_use_inner(&self, inner: &Type) -> bool {
        !matches!(
            inner,
            Type::OpenVar(slot)
                if self
                    .slots
                    .get(*slot as usize)
                    .is_some_and(|slot| slot.kind == TypeSlotKind::Effect)
        )
    }

    pub(super) fn instantiate_cast_scheme(
        &mut self,
        def: poly_expr::DefId,
        scheme: &poly::types::Scheme,
    ) -> Result<Type, SpecializeError> {
        let arena = self.arena;
        let instantiated = types::instantiate_scheme_with_fresh_and_roles(
            arena,
            def,
            scheme,
            |kind| match kind {
                types::SchemeQuantifierKind::Value => self.fresh_slot(TypeSlotKind::Value),
                types::SchemeQuantifierKind::Effect => self.fresh_slot(TypeSlotKind::Effect),
            },
        )?;
        self.add_role_demands(instantiated.role_predicates);
        self.constrain_recursive_bounds(instantiated.recursive_bounds)?;
        Ok(instantiated.ty)
    }

    pub(super) fn direct_closed_cast_subtype(&self, lower: &Type, upper: &Type) -> bool {
        let Some(source) = con_path_without_args(lower) else {
            return false;
        };
        let Some(target) = con_path_without_args(upper) else {
            return false;
        };
        self.arena.cast_rules.iter().any(|rule| {
            rule.source == source
                && rule.target == target
                && rule.scheme.quantifiers.is_empty()
                && rule.scheme.role_predicates.is_empty()
                && rule.scheme.recursive_bounds.is_empty()
                && rule.scheme.stack_quantifiers.is_empty()
        })
    }

    pub(super) fn constrain_effect_rows(
        &mut self,
        lower_items: Vec<Type>,
        upper_items: Vec<Type>,
    ) -> Result<(), SpecializeError> {
        let (lower_items, lower_tail) = self.split_effect_row_tail(lower_items);
        let (upper_items, upper_tail) = self.split_effect_row_tail(upper_items);
        let mut matched_upper = vec![false; upper_items.len()];
        let mut lower_extra = Vec::new();

        for lower in lower_items {
            let Some(upper_index) = upper_items.iter().enumerate().find_map(|(index, upper)| {
                (!matched_upper[index] && same_effect_row_family(&lower, upper)).then_some(index)
            }) else {
                lower_extra.push(lower);
                continue;
            };
            matched_upper[upper_index] = true;
            self.constrain_subtype(lower, upper_items[upper_index].clone())?;
        }

        let upper_extra = upper_items
            .into_iter()
            .enumerate()
            .filter_map(|(index, upper)| (!matched_upper[index]).then_some(upper))
            .collect::<Vec<_>>();
        if !lower_extra.is_empty() {
            if let Some(upper_tail) = upper_tail.clone() {
                self.constrain_subtype(Type::EffectRow(lower_extra), upper_tail)?;
            }
        }
        if !upper_extra.is_empty() {
            if let Some(lower_tail) = lower_tail.clone() {
                self.constrain_subtype(lower_tail, Type::EffectRow(upper_extra))?;
            }
        }

        match (lower_tail, upper_tail) {
            (Some(lower_tail), Some(upper_tail)) => self.constrain_subtype(lower_tail, upper_tail),
            _ => Ok(()),
        }
    }

    pub(super) fn split_effect_row_tail(&self, mut items: Vec<Type>) -> (Vec<Type>, Option<Type>) {
        let Some(Type::OpenVar(slot)) = items.last().cloned() else {
            return (items, None);
        };
        if self
            .slots
            .get(slot as usize)
            .is_some_and(|slot| slot.kind == TypeSlotKind::Effect)
        {
            items.pop();
            return (items, Some(Type::OpenVar(slot)));
        }
        (items, None)
    }

    pub(super) fn add_edge(&mut self, lower: u32, upper: u32) -> Result<(), SpecializeError> {
        self.ensure_slot(lower)?;
        self.ensure_slot(upper)?;
        if lower == upper {
            return Ok(());
        }
        let lower_index = lower as usize;
        let upper_index = upper as usize;
        if !self.slots[lower_index].successors.contains(&upper) {
            self.slots[lower_index].successors.push(upper);
        }
        if !self.slots[upper_index].predecessors.contains(&lower) {
            self.slots[upper_index].predecessors.push(lower);
        }
        let lowers = self.slots[lower_index].lower.clone();
        for bound in lowers {
            self.add_lower(upper, bound)?;
        }
        let uppers = self.slots[upper_index].upper.clone();
        for bound in uppers {
            self.add_upper(lower, bound)?;
        }
        Ok(())
    }

    pub(super) fn add_lower(&mut self, slot: u32, lower: Type) -> Result<(), SpecializeError> {
        self.ensure_slot(slot)?;
        let slot_index = slot as usize;
        if self.slots[slot_index].lower.contains(&lower) {
            return Ok(());
        }
        self.slots[slot_index].lower.push(lower.clone());
        let uppers = self.slots[slot_index].upper.clone();
        for upper in uppers {
            self.constrain_subtype(lower.clone(), upper)?;
        }
        let successors = self.slots[slot_index].successors.clone();
        for successor in successors {
            self.add_lower(successor, lower.clone())?;
        }
        Ok(())
    }

    pub(super) fn add_upper(&mut self, slot: u32, upper: Type) -> Result<(), SpecializeError> {
        self.ensure_slot(slot)?;
        let slot_index = slot as usize;
        if self.slots[slot_index].upper.contains(&upper) {
            return Ok(());
        }
        self.slots[slot_index].upper.push(upper.clone());
        let lowers = self.slots[slot_index].lower.clone();
        for lower in lowers {
            self.constrain_subtype(lower, upper.clone())?;
        }
        let predecessors = self.slots[slot_index].predecessors.clone();
        for predecessor in predecessors {
            self.add_upper(predecessor, upper.clone())?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct SubtypeConstraint {
    lower: Type,
    upper: Type,
}

#[derive(Debug, Clone)]
pub(super) struct TypeSlot {
    pub(super) kind: TypeSlotKind,
    pub(super) lower: Vec<Type>,
    pub(super) upper: Vec<Type>,
    pub(super) successors: Vec<u32>,
    pub(super) predecessors: Vec<u32>,
}

impl TypeSlot {
    pub(super) fn new(kind: TypeSlotKind) -> Self {
        Self {
            kind,
            lower: Vec::new(),
            upper: Vec::new(),
            successors: Vec::new(),
            predecessors: Vec::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub(super) struct GraphSolution {
    pub(super) slots: Vec<Option<Type>>,
}

impl GraphSolution {
    pub(super) fn new(slot_count: usize) -> Self {
        Self {
            slots: vec![None; slot_count],
        }
    }

    pub(super) fn get(&self, slot: u32) -> Result<Option<&Type>, SpecializeError> {
        self.slots
            .get(slot as usize)
            .map(Option::as_ref)
            .ok_or(SpecializeError::InvalidTypeSlot { slot })
    }
}
