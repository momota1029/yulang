use super::*;

impl<'a> TypeGraph<'a> {
    pub(in crate::specialize2) fn add_weighted_edge(
        &mut self,
        lower: u32,
        upper: u32,
        lower_weight: StackWeight,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        self.ensure_slot(lower)?;
        self.ensure_slot(upper)?;
        if lower == upper && lower_weight == upper_weight {
            return Ok(());
        }
        if stack_weight_is_empty(&lower_weight) && stack_weight_is_empty(&upper_weight) {
            return self.add_edge(lower, upper);
        }
        let forward = WeightedSlotEdge {
            slot: upper,
            lower_weight: lower_weight.clone(),
            upper_weight: upper_weight.clone(),
        };
        let backward = WeightedSlotEdge {
            slot: lower,
            lower_weight,
            upper_weight,
        };
        let lower_index = lower as usize;
        let upper_index = upper as usize;
        if !self.slots[lower_index]
            .weighted_successors
            .contains(&forward)
        {
            self.slots[lower_index].weighted_successors.push(forward);
        }
        if !self.slots[upper_index]
            .weighted_predecessors
            .contains(&backward)
        {
            self.slots[upper_index].weighted_predecessors.push(backward);
        }
        let lower_bounds = self.slots[lower_index].lower.clone();
        let successors = self.slots[lower_index].weighted_successors.clone();
        for bound in lower_bounds {
            for successor in &successors {
                self.constrain_weighted_subtype(
                    bound.clone(),
                    successor.lower_weight.clone(),
                    Type::OpenVar(successor.slot),
                    successor.upper_weight.clone(),
                )?;
            }
        }
        let weighted_lower_bounds = self.slots[lower_index].weighted_lower.clone();
        let successors = self.slots[lower_index].weighted_successors.clone();
        for bound in weighted_lower_bounds {
            for successor in &successors {
                self.constrain_weighted_subtype(
                    bound.ty.clone(),
                    compose_replay_stack_weights(
                        bound.lower_weight.clone(),
                        successor.lower_weight.clone(),
                    ),
                    Type::OpenVar(successor.slot),
                    compose_replay_stack_weights(
                        bound.upper_weight.clone(),
                        successor.upper_weight.clone(),
                    ),
                )?;
            }
        }
        let upper_bounds = self.slots[upper_index].upper.clone();
        let predecessors = self.slots[upper_index].weighted_predecessors.clone();
        for bound in upper_bounds {
            for predecessor in &predecessors {
                self.constrain_weighted_subtype(
                    Type::OpenVar(predecessor.slot),
                    predecessor.lower_weight.clone(),
                    bound.clone(),
                    predecessor.upper_weight.clone(),
                )?;
            }
        }
        let weighted_upper_bounds = self.slots[upper_index].weighted_upper.clone();
        let predecessors = self.slots[upper_index].weighted_predecessors.clone();
        for bound in weighted_upper_bounds {
            for predecessor in &predecessors {
                self.constrain_weighted_subtype(
                    Type::OpenVar(predecessor.slot),
                    compose_replay_stack_weights(
                        predecessor.lower_weight.clone(),
                        bound.lower_weight.clone(),
                    ),
                    bound.ty.clone(),
                    compose_replay_stack_weights(
                        predecessor.upper_weight.clone(),
                        bound.upper_weight.clone(),
                    ),
                )?;
            }
        }
        Ok(())
    }

    pub(in crate::specialize2) fn add_edge(
        &mut self,
        lower: u32,
        upper: u32,
    ) -> Result<(), SpecializeError> {
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

    pub(in crate::specialize2) fn add_lower(
        &mut self,
        slot: u32,
        lower: Type,
    ) -> Result<(), SpecializeError> {
        self.add_lower_weighted(slot, lower, empty_stack_weight(), empty_stack_weight())
    }

    pub(in crate::specialize2) fn add_lower_weighted(
        &mut self,
        slot: u32,
        lower: Type,
        lower_weight: StackWeight,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        if stack_weight_is_empty(&lower_weight) && stack_weight_is_empty(&upper_weight) {
            return self.add_lower_unweighted(slot, lower);
        }
        if let Type::OpenVar(lower_slot) = lower {
            return self.add_weighted_edge(lower_slot, slot, lower_weight, upper_weight);
        }
        self.add_lower_bound_weighted(slot, lower, lower_weight, upper_weight)
    }

    pub(in crate::specialize2) fn add_lower_unweighted(
        &mut self,
        slot: u32,
        lower: Type,
    ) -> Result<(), SpecializeError> {
        self.ensure_slot(slot)?;
        let index = slot as usize;
        let lower = effect_slot_candidate(self.slots[index].kind, lower);
        if self.slots[index].lower.contains(&lower) {
            return Ok(());
        }
        for existing in self.slots[index].lower.clone() {
            self.constrain_same_path_invariant(existing, lower.clone())?;
        }
        self.slots[index].lower.push(lower.clone());
        let effect_consumers = self.slots[index].effect_subtraction_consumers.clone();
        for demand in effect_consumers {
            let Some((items, tail)) = self.effect_row_parts(lower.clone()) else {
                continue;
            };
            self.constrain_effect_lower_against_subtraction_demand(items, tail, &demand, false)?;
        }
        let uppers = self.slots[index].upper.clone();
        for upper in uppers {
            self.constrain_subtype(lower.clone(), upper)?;
        }
        let successors = self.slots[index].successors.clone();
        for successor in successors {
            self.add_lower_unweighted(successor, lower.clone())?;
        }
        let weighted_uppers = self.slots[index].weighted_upper.clone();
        for upper in weighted_uppers {
            self.constrain_weighted_subtype(
                lower.clone(),
                upper.lower_weight,
                upper.ty,
                upper.upper_weight,
            )?;
        }
        let weighted_successors = self.slots[index].weighted_successors.clone();
        for successor in weighted_successors {
            self.constrain_weighted_subtype(
                lower.clone(),
                successor.lower_weight,
                Type::OpenVar(successor.slot),
                successor.upper_weight,
            )?;
        }
        Ok(())
    }

    pub(in crate::specialize2) fn add_lower_bound_weighted(
        &mut self,
        slot: u32,
        lower: Type,
        lower_weight: StackWeight,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        self.ensure_slot(slot)?;
        let index = slot as usize;
        let lower = effect_slot_candidate(self.slots[index].kind, lower);
        let bound = WeightedTypeBound {
            ty: lower.clone(),
            lower_weight,
            upper_weight,
        };
        if self.slots[index].weighted_lower.contains(&bound) {
            return Ok(());
        }
        self.slots[index].weighted_lower.push(bound.clone());

        let uppers = self.slots[index].upper.clone();
        for upper in uppers {
            self.constrain_weighted_subtype(
                lower.clone(),
                bound.lower_weight.clone(),
                upper,
                bound.upper_weight.clone(),
            )?;
        }
        let weighted_uppers = self.slots[index].weighted_upper.clone();
        for upper in weighted_uppers {
            self.constrain_weighted_subtype(
                lower.clone(),
                compose_replay_stack_weights(bound.lower_weight.clone(), upper.lower_weight),
                upper.ty,
                compose_replay_stack_weights(bound.upper_weight.clone(), upper.upper_weight),
            )?;
        }
        let successors = self.slots[index].successors.clone();
        for successor in successors {
            self.constrain_weighted_subtype(
                lower.clone(),
                bound.lower_weight.clone(),
                Type::OpenVar(successor),
                bound.upper_weight.clone(),
            )?;
        }
        let weighted_successors = self.slots[index].weighted_successors.clone();
        for successor in weighted_successors {
            self.constrain_weighted_subtype(
                lower.clone(),
                compose_replay_stack_weights(bound.lower_weight.clone(), successor.lower_weight),
                Type::OpenVar(successor.slot),
                compose_replay_stack_weights(bound.upper_weight.clone(), successor.upper_weight),
            )?;
        }
        Ok(())
    }

    pub(in crate::specialize2) fn add_upper(
        &mut self,
        slot: u32,
        upper: Type,
    ) -> Result<(), SpecializeError> {
        self.add_upper_weighted(slot, empty_stack_weight(), upper, empty_stack_weight())
    }

    pub(in crate::specialize2) fn add_upper_weighted(
        &mut self,
        slot: u32,
        lower_weight: StackWeight,
        upper: Type,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        if stack_weight_is_empty(&lower_weight) && stack_weight_is_empty(&upper_weight) {
            return self.add_upper_unweighted(slot, upper);
        }
        if let Type::OpenVar(upper_slot) = upper {
            return self.add_weighted_edge(slot, upper_slot, lower_weight, upper_weight);
        }
        if self
            .slots
            .get(slot as usize)
            .is_some_and(|slot| slot.kind == TypeSlotKind::Effect)
        {
            return self.add_effect_upper_weighted(slot, lower_weight, upper, upper_weight);
        }
        self.add_upper_bound_weighted(slot, lower_weight, upper, upper_weight)
    }

    pub(in crate::specialize2) fn add_effect_upper_weighted(
        &mut self,
        slot: u32,
        lower_weight: StackWeight,
        upper: Type,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        if stack_weight_is_empty(&lower_weight) && stack_weight_is_empty(&upper_weight) {
            return self.add_upper_unweighted(slot, upper);
        }
        let upper_row = match upper {
            Type::EffectRow(items) => items,
            item if item.is_pure_effect() => Vec::new(),
            item => vec![item],
        };
        let (items, tail) = self.split_effect_row_tail(upper_row);
        if matches!(tail, Some(Type::OpenVar(tail)) if tail == slot) {
            return Ok(());
        }
        if items.is_empty() && tail.is_none() {
            return self.add_upper_bound_weighted(
                slot,
                lower_weight,
                Type::pure_effect(),
                upper_weight,
            );
        }
        let combined_weight = compose_stack_weights(lower_weight, upper_weight);
        let retained = items
            .iter()
            .filter(|item| stack_weight_allows_effect_item(&combined_weight, item))
            .cloned()
            .collect::<Vec<_>>();
        let tail = tail.unwrap_or_else(Type::pure_effect);
        if retained.is_empty() {
            return self.constrain_weighted_subtype(
                Type::OpenVar(slot),
                combined_weight,
                tail,
                empty_stack_weight(),
            );
        }
        let retained_families = sorted_effect_families(effect_families_from_items(&retained));
        let residual_weight = subtract_stack_weight(combined_weight, &retained_families);
        let key = RowResidualKey {
            source: slot,
            retained_families,
            weight: residual_weight.clone(),
        };
        let residual = if let Some(residual) = self.row_residuals.get(&key).copied() {
            Type::OpenVar(residual)
        } else {
            let residual = self.fresh_effect();
            let Type::OpenVar(residual_slot) = residual else {
                unreachable!("fresh_effect returns an open slot");
            };
            self.row_residuals.insert(key, residual_slot);
            residual
        };
        let mut upper_items = retained;
        upper_items.push(residual.clone());
        self.constrain_subtype(Type::OpenVar(slot), Type::EffectRow(upper_items))?;
        self.constrain_weighted_subtype(residual, residual_weight, tail, empty_stack_weight())
    }

    pub(in crate::specialize2) fn add_upper_bound_weighted(
        &mut self,
        slot: u32,
        lower_weight: StackWeight,
        upper: Type,
        upper_weight: StackWeight,
    ) -> Result<(), SpecializeError> {
        self.ensure_slot(slot)?;
        let index = slot as usize;
        let upper = effect_slot_candidate(self.slots[index].kind, upper);
        let bound = WeightedTypeBound {
            ty: upper.clone(),
            lower_weight,
            upper_weight,
        };
        if self.slots[index].weighted_upper.contains(&bound) {
            return Ok(());
        }
        self.slots[index].weighted_upper.push(bound.clone());

        let lowers = self.slots[index].lower.clone();
        for lower in lowers {
            self.constrain_weighted_subtype(
                lower,
                bound.lower_weight.clone(),
                upper.clone(),
                bound.upper_weight.clone(),
            )?;
        }
        let weighted_lowers = self.slots[index].weighted_lower.clone();
        for lower in weighted_lowers {
            self.constrain_weighted_subtype(
                lower.ty,
                compose_replay_stack_weights(lower.lower_weight, bound.lower_weight.clone()),
                upper.clone(),
                compose_replay_stack_weights(lower.upper_weight, bound.upper_weight.clone()),
            )?;
        }
        let predecessors = self.slots[index].predecessors.clone();
        for predecessor in predecessors {
            self.constrain_weighted_subtype(
                Type::OpenVar(predecessor),
                bound.lower_weight.clone(),
                upper.clone(),
                bound.upper_weight.clone(),
            )?;
        }
        let weighted_predecessors = self.slots[index].weighted_predecessors.clone();
        for predecessor in weighted_predecessors {
            self.constrain_weighted_subtype(
                Type::OpenVar(predecessor.slot),
                compose_replay_stack_weights(predecessor.lower_weight, bound.lower_weight.clone()),
                upper.clone(),
                compose_replay_stack_weights(predecessor.upper_weight, bound.upper_weight.clone()),
            )?;
        }
        Ok(())
    }

    pub(in crate::specialize2) fn add_upper_unweighted(
        &mut self,
        slot: u32,
        upper: Type,
    ) -> Result<(), SpecializeError> {
        self.ensure_slot(slot)?;
        let index = slot as usize;
        let upper = effect_slot_candidate(self.slots[index].kind, upper);
        if self.slots[index].upper.contains(&upper) {
            return Ok(());
        }
        for existing in self.slots[index].upper.clone() {
            self.constrain_same_path_invariant(existing, upper.clone())?;
        }
        self.slots[index].upper.push(upper.clone());
        let lowers = self.slots[index].lower.clone();
        for lower in lowers {
            self.constrain_subtype(lower, upper.clone())?;
        }
        let weighted_lowers = self.slots[index].weighted_lower.clone();
        for lower in weighted_lowers {
            self.constrain_weighted_subtype(
                lower.ty,
                lower.lower_weight,
                upper.clone(),
                lower.upper_weight,
            )?;
        }
        let predecessors = self.slots[index].predecessors.clone();
        for predecessor in predecessors {
            self.add_upper_unweighted(predecessor, upper.clone())?;
        }
        let weighted_predecessors = self.slots[index].weighted_predecessors.clone();
        for predecessor in weighted_predecessors {
            self.constrain_weighted_subtype(
                Type::OpenVar(predecessor.slot),
                predecessor.lower_weight,
                upper.clone(),
                predecessor.upper_weight,
            )?;
        }
        Ok(())
    }

    pub(in crate::specialize2) fn ensure_slot(&self, slot: u32) -> Result<(), SpecializeError> {
        if (slot as usize) < self.slots.len() {
            Ok(())
        } else {
            Err(SpecializeError::InvalidTypeSlot { slot })
        }
    }

    pub(in crate::specialize2) fn constrain_same_path_invariant(
        &mut self,
        left: Type,
        right: Type,
    ) -> Result<(), SpecializeError> {
        if matches!((&left, &right), (Type::EffectRow(_), Type::EffectRow(_))) {
            return Ok(());
        }
        if let (
            Type::Stack {
                inner: left_inner,
                weight: left_weight,
            },
            Type::Stack {
                inner: right_inner,
                weight: right_weight,
            },
        ) = (&left, &right)
            && left_weight == right_weight
        {
            self.constrain_subtype(left_inner.as_ref().clone(), right_inner.as_ref().clone())?;
            self.constrain_subtype(right_inner.as_ref().clone(), left_inner.as_ref().clone())?;
            return Ok(());
        }
        let (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) = (left, right)
        else {
            return Ok(());
        };
        if left_path != right_path || left_args.len() != right_args.len() {
            return Ok(());
        }
        for (left, right) in left_args.into_iter().zip(right_args) {
            self.constrain_subtype(left.clone(), right.clone())?;
            self.constrain_subtype(right, left)?;
        }
        Ok(())
    }

    pub(in crate::specialize2) fn solve_slots(&self) -> Result<Solution, SpecializeError> {
        let mut solution = Solution {
            slots: vec![None; self.slots.len()],
        };
        loop {
            let mut progressed = false;
            for slot in 0..self.slots.len() {
                if solution.slots[slot].is_some() {
                    continue;
                }
                let mut resolver = TypeResolver::new(self, &solution);
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
}
