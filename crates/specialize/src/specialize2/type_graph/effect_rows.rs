use super::*;

impl<'a> TypeGraph<'a> {
    pub(in crate::specialize2) fn constrain_effect_rows_weighted(
        &mut self,
        lower_items: Vec<Type>,
        lower_weight: StackWeight,
        upper_items: Vec<Type>,
        upper_weight: StackWeight,
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
            self.constrain_weighted_subtype(
                lower,
                lower_weight.clone(),
                upper_items[upper_index].clone(),
                upper_weight.clone(),
            )?;
        }

        let upper_extra = upper_items
            .into_iter()
            .enumerate()
            .filter_map(|(index, upper)| (!matched_upper[index]).then_some(upper))
            .collect::<Vec<_>>();
        if !lower_extra.is_empty() {
            if let Some(upper_tail) = upper_tail.clone() {
                self.constrain_weighted_subtype(
                    Type::EffectRow(lower_extra),
                    lower_weight.clone(),
                    upper_tail,
                    upper_weight.clone(),
                )?;
            }
        }
        let upper_extra_is_empty = upper_extra.is_empty();
        if !upper_extra_is_empty && let Some(lower_tail) = lower_tail.clone() {
            self.constrain_weighted_subtype(
                lower_tail,
                lower_weight.clone(),
                effect_row_from_parts(upper_extra, upper_tail.clone()),
                upper_weight.clone(),
            )?;
        }

        match (lower_tail, upper_tail) {
            (Some(lower_tail), Some(upper_tail)) if upper_extra_is_empty => {
                self.constrain_weighted_subtype(lower_tail, lower_weight, upper_tail, upper_weight)
            }
            _ => Ok(()),
        }
    }

    pub(in crate::specialize2) fn constrain_consumed_computation_effect(
        &mut self,
        actual_effect: Type,
        expected_effect: Type,
    ) -> Result<Type, SpecializeError> {
        if let Some(runtime_effect) =
            self.constrain_subtractable_computation_effect(actual_effect.clone(), &expected_effect)?
        {
            return Ok(runtime_effect);
        }
        self.constrain_subtype(actual_effect, expected_effect.clone())?;
        Ok(expected_effect)
    }

    pub(in crate::specialize2) fn constrain_subtractable_computation_effect(
        &mut self,
        actual_effect: Type,
        expected_effect: &Type,
    ) -> Result<Option<Type>, SpecializeError> {
        let Some(demand) = effect_consumption_demand(expected_effect) else {
            return Ok(None);
        };
        if let Type::OpenVar(slot) = actual_effect {
            if self
                .slots
                .get(slot as usize)
                .is_some_and(|slot| slot.kind == TypeSlotKind::Effect)
            {
                self.add_effect_subtraction_consumer(slot, demand.clone())?;
                let runtime_effect = demand.runtime_effect;
                self.constrain_subtype(Type::OpenVar(slot), runtime_effect.clone())?;
                return Ok(Some(runtime_effect));
            }
            return Ok(None);
        }
        let Some((actual_items, actual_tail)) = self.effect_row_parts(actual_effect.clone()) else {
            return Ok(None);
        };
        self.constrain_effect_lower_against_subtraction_demand(
            actual_items,
            actual_tail,
            &demand,
            true,
        )?;
        self.constrain_subtype(actual_effect, demand.runtime_effect.clone())?;
        Ok(Some(demand.runtime_effect))
    }

    pub(in crate::specialize2) fn add_effect_subtraction_consumer(
        &mut self,
        slot: u32,
        demand: EffectSubtractionDemand,
    ) -> Result<(), SpecializeError> {
        self.ensure_slot(slot)?;
        let index = slot as usize;
        if self.slots[index]
            .effect_subtraction_consumers
            .contains(&demand)
        {
            return Ok(());
        }
        self.slots[index]
            .effect_subtraction_consumers
            .push(demand.clone());
        let lowers = self.slots[index].lower.clone();
        for lower in lowers {
            let Some((items, tail)) = self.effect_row_parts(lower) else {
                continue;
            };
            self.constrain_effect_lower_against_subtraction_demand(items, tail, &demand, false)?;
        }
        Ok(())
    }

    pub(in crate::specialize2) fn constrain_effect_lower_against_subtraction_demand(
        &mut self,
        actual_items: Vec<Type>,
        actual_tail: Option<Type>,
        demand: &EffectSubtractionDemand,
        close_pure_tail: bool,
    ) -> Result<(), SpecializeError> {
        let residual = self.residual_effect_after_consuming_handled(
            actual_items,
            actual_tail,
            &demand.handled_items,
        )?;
        if close_pure_tail && residual.is_pure_effect() {
            return self.constrain_exact(demand.tail.clone(), residual);
        }
        if !residual.is_pure_effect() {
            self.constrain_subtype(residual, demand.tail.clone())?;
        }
        Ok(())
    }

    pub(in crate::specialize2) fn close_pure_effect_subtraction_tails(
        &mut self,
    ) -> Result<bool, SpecializeError> {
        let mut closed = false;
        for slot in 0..self.slots.len() {
            let demands = self.slots[slot].effect_subtraction_consumers.clone();
            for demand in demands {
                let key = (slot as u32, demand.clone());
                if self.closed_effect_subtraction_consumers.contains(&key) {
                    continue;
                }
                if !self.effect_subtraction_tail_is_pure(slot as u32, &demand) {
                    continue;
                }
                self.closed_effect_subtraction_consumers.insert(key);
                self.constrain_exact(demand.tail.clone(), Type::pure_effect())?;
                closed = true;
            }
        }
        Ok(closed)
    }

    pub(in crate::specialize2) fn effect_subtraction_tail_is_pure(
        &self,
        slot_id: u32,
        demand: &EffectSubtractionDemand,
    ) -> bool {
        let Some(slot) = self.slots.get(slot_id as usize) else {
            return false;
        };
        let mut saw_concrete_lower = false;
        for lower in &slot.lower {
            let Some((items, tail)) = self.effect_row_parts(lower.clone()) else {
                return false;
            };
            if items.is_empty() && matches!(tail, Some(Type::OpenVar(tail)) if tail == slot_id) {
                continue;
            }
            // A lower already present on the residual tail is escaping evidence,
            // not proof that the handled part consumed the whole source effect.
            if self.effect_lower_may_come_from_tail(lower, &demand.tail) {
                return false;
            }
            saw_concrete_lower = true;
            if !residual_effect_after_consuming_handled_candidate(
                items,
                tail,
                &demand.handled_items,
            )
            .is_pure_effect()
            {
                return false;
            }
        }
        saw_concrete_lower
    }

    pub(in crate::specialize2) fn effect_lower_may_come_from_tail(
        &self,
        lower: &Type,
        tail: &Type,
    ) -> bool {
        let Type::OpenVar(tail) = tail else {
            return false;
        };
        let Some(slot) = self.slots.get(*tail as usize) else {
            return false;
        };
        slot.lower
            .iter()
            .any(|tail_lower| effect_lower_candidates_overlap(lower, tail_lower))
    }

    pub(in crate::specialize2) fn residual_effect_after_consuming_handled(
        &mut self,
        actual_items: Vec<Type>,
        actual_tail: Option<Type>,
        handled_items: &[Type],
    ) -> Result<Type, SpecializeError> {
        let mut matched_handled = vec![false; handled_items.len()];
        let mut residual_items = Vec::new();
        for actual in actual_items {
            let Some(index) = handled_items
                .iter()
                .enumerate()
                .find_map(|(index, handled)| {
                    (!matched_handled[index] && same_effect_row_family(&actual, handled))
                        .then_some(index)
                })
            else {
                residual_items.push(actual);
                continue;
            };
            matched_handled[index] = true;
            self.constrain_exact(actual, handled_items[index].clone())?;
        }
        Ok(effect_row_from_parts(residual_items, actual_tail))
    }

    pub(in crate::specialize2) fn effect_row_parts(
        &self,
        effect: Type,
    ) -> Option<(Vec<Type>, Option<Type>)> {
        if effect.is_pure_effect() {
            return Some((Vec::new(), None));
        }
        let Type::EffectRow(items) = effect else {
            return None;
        };
        Some(self.split_effect_row_tail(items))
    }

    pub(in crate::specialize2) fn split_effect_row_tail(
        &self,
        mut items: Vec<Type>,
    ) -> (Vec<Type>, Option<Type>) {
        let Some(tail) = items.last().cloned() else {
            return (items, None);
        };
        if self.type_is_effect_tail(&tail) {
            items.pop();
            return (items, Some(tail));
        }
        (items, None)
    }

    pub(in crate::specialize2) fn type_is_effect_tail(&self, ty: &Type) -> bool {
        match ty {
            Type::OpenVar(slot) => self
                .slots
                .get(*slot as usize)
                .is_some_and(|slot| slot.kind == TypeSlotKind::Effect),
            Type::EffectRow(items) => items
                .last()
                .is_some_and(|tail| self.type_is_effect_tail(tail)),
            Type::Intersection(left, right) => {
                self.type_is_effect_tail(left) && self.type_is_effect_tail(right)
            }
            Type::Stack { inner, .. } => self.type_is_effect_tail(inner),
            _ => false,
        }
    }

    pub(in crate::specialize2) fn effect_family_item_blocked_by_weight(
        &self,
        path: &[String],
        args: &[Type],
        lower_weight: &StackWeight,
        upper_weight: &StackWeight,
    ) -> bool {
        if !self.is_effect_family_path(path) {
            return false;
        }
        let combined_weight = compose_stack_weights(lower_weight.clone(), upper_weight.clone());
        let item = Type::Con {
            path: path.to_vec(),
            args: args.to_vec(),
        };
        !stack_weight_allows_effect_item(&combined_weight, &item)
    }
}
