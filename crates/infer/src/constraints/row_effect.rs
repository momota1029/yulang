//! Weighted effect-row upper bounds and row-subtraction residuals.

use super::*;

impl ConstraintMachine {
    pub(super) fn add_effect_row_upper_bound(
        &mut self,
        source: TypeVar,
        items: Vec<NegId>,
        tail: NegId,
        weights: ConstraintWeights,
    ) {
        if weights.is_empty() {
            if self.add_unweighted_effect_row_upper_bound_from_existing_lowers(
                source,
                items.clone(),
                tail,
            ) {
                return;
            }
            let row = self.alloc_neg(Neg::Row(items, tail));
            self.add_upper_bound(source, row, weights);
            return;
        }

        if matches!(self.types.neg(tail), Neg::Var(tail_var) if *tail_var == source) {
            return;
        }

        let combined = weights.left.compose(&weights.right);
        if combined.is_empty() {
            let row = self.alloc_neg(Neg::Row(items, tail));
            self.add_upper_bound(source, row, ConstraintWeights::empty());
            return;
        }

        let retained_items = self.intersect_row_items_with_stack(items, &combined);
        let retained_items = self.collect_neg_effect_items(retained_items);
        if retained_items.is_empty() {
            let source_pos = self.alloc_pos(Pos::Var(source));
            self.enqueue_subtype(
                source_pos,
                ConstraintWeights {
                    left: combined,
                    right: StackWeight::empty(),
                },
                tail,
            );
            return;
        }

        let retained_families = self.neg_effect_families(&retained_items);
        let residual_weight =
            self.subtract_row_items_from_stack_weight(&combined, retained_families.clone());
        let key = RowResidualKey {
            source,
            retained_families: sorted_effect_families(retained_families),
            weight: residual_weight.clone(),
        };
        let gamma = if let Some(gamma) = self.row_residuals.get(&key) {
            *gamma
        } else {
            let gamma = self.fresh_internal_type_var_at(self.level_of(source));
            self.row_residuals.insert(key, gamma);
            gamma
        };

        let gamma_neg = self.alloc_neg(Neg::Var(gamma));
        let upper = self.alloc_neg(Neg::Row(retained_items, gamma_neg));
        // Feed the residual row back through the normal subtype path so future
        // upper bounds on gamma can replay into source through the same machinery.
        let source_pos = self.alloc_pos(Pos::Var(source));
        self.enqueue_subtype(source_pos, ConstraintWeights::empty(), upper);

        let gamma_pos = self.alloc_pos(Pos::Var(gamma));
        self.enqueue_subtype(
            gamma_pos,
            ConstraintWeights {
                left: residual_weight,
                right: StackWeight::empty(),
            },
            tail,
        );
    }

    fn add_unweighted_effect_row_upper_bound_from_existing_lowers(
        &mut self,
        source: TypeVar,
        items: Vec<NegId>,
        tail: NegId,
    ) -> bool {
        if items.is_empty() {
            return false;
        }
        let lowers = self
            .bounds
            .of(source)
            .map(|bounds| bounds.lowers.clone())
            .unwrap_or_default();
        if lowers.is_empty() {
            return false;
        }

        let mut remaining = items.clone();
        let mut matched_lowers = vec![false; lowers.len()];
        for (index, lower) in lowers.iter().enumerate() {
            if !Self::constraint_weights_are_alias_neutral(&lower.weights) {
                continue;
            }
            let mut seen = FxHashSet::default();
            let mut local_remaining = items.clone();
            if self.consume_row_items_from_lower_bound(lower.pos, &mut local_remaining, &mut seen) {
                for consumed in consumed_row_items(&items, &local_remaining) {
                    remove_first_row_item(&mut remaining, consumed);
                }
                matched_lowers[index] = true;
            }
        }
        if matched_lowers.iter().all(|matched| !matched) {
            return false;
        }

        let original_upper = self.effect_row_upper(items, tail);
        let reduced_upper = self.effect_row_upper(remaining, tail);
        self.store_upper_bound_without_replay(source, reduced_upper, ConstraintWeights::empty());

        for (index, lower) in lowers.into_iter().enumerate() {
            let upper = if matched_lowers[index] {
                original_upper
            } else {
                reduced_upper
            };
            self.enqueue_subtype(lower.pos, lower.weights, upper);
        }
        true
    }

    fn consume_row_items_from_lower_bound(
        &mut self,
        pos: PosId,
        remaining: &mut Vec<NegId>,
        seen: &mut FxHashSet<TypeVar>,
    ) -> bool {
        match self.types.pos(pos).clone() {
            Pos::Con(_, _) => self.consume_matching_row_item(pos, remaining),
            Pos::Row(items) => {
                let mut consumed = false;
                for item in items {
                    consumed |= self.consume_row_items_from_lower_bound(item, remaining, seen);
                }
                consumed
            }
            Pos::Var(var) => {
                if !seen.insert(var) {
                    return false;
                }
                let lowers = self
                    .bounds
                    .of(var)
                    .map(|bounds| bounds.lowers.clone())
                    .unwrap_or_default();
                let mut consumed = false;
                for lower in lowers {
                    if !Self::constraint_weights_are_alias_neutral(&lower.weights) {
                        continue;
                    }
                    consumed |= self.consume_row_items_from_lower_bound(lower.pos, remaining, seen);
                }
                consumed
            }
            _ => false,
        }
    }

    fn consume_matching_row_item(&mut self, lower: PosId, remaining: &mut Vec<NegId>) -> bool {
        let Some(index) = remaining
            .iter()
            .position(|upper| self.row_items_can_match(lower, *upper))
        else {
            return false;
        };
        let upper = remaining.remove(index);
        self.enqueue_row_item_match(lower, upper, ConstraintWeights::empty());
        true
    }

    fn effect_row_upper(&mut self, items: Vec<NegId>, tail: NegId) -> NegId {
        if items.is_empty() {
            tail
        } else {
            self.alloc_neg(Neg::Row(items, tail))
        }
    }

    fn constraint_weights_are_alias_neutral(weights: &ConstraintWeights) -> bool {
        Self::stack_weight_is_alias_neutral(&weights.left)
            && Self::stack_weight_is_alias_neutral(&weights.right)
    }

    fn stack_weight_is_alias_neutral(weight: &StackWeight) -> bool {
        weight
            .entries()
            .iter()
            .all(|entry| entry.floor.is_empty() && entry.stack.is_empty())
    }

    fn store_upper_bound_without_replay(
        &mut self,
        source: TypeVar,
        neg: NegId,
        weights: ConstraintWeights,
    ) -> bool {
        let neg = self.extrude_neg(neg, self.level_of(source));
        if self.upper_bound_subsumed_by_existing(source, neg, &weights) {
            return false;
        }
        if weights.is_empty() {
            self.prune_upper_rows_subsumed_by_reduced_upper(source, neg);
        } else {
            self.prune_upper_rows_subsumed_by(source, neg, &weights);
        }
        if !self.bounds.add_upper(source, neg, weights.clone()) {
            return false;
        }
        self.record_neg_bound_var_neighbors(source, neg);
        self.events.push(ConstraintEvent::UpperBoundAdded {
            var: source,
            bound: neg,
            weights: weights.clone(),
        });
        trace_var_bounds(
            "after row-match upper",
            source,
            self.bounds.of(source),
            &self.types,
        );
        true
    }

    fn intersect_row_items_with_stack(
        &mut self,
        items: Vec<NegId>,
        weight: &StackWeight,
    ) -> Vec<NegId> {
        self.collect_stack_effect_families(weight);
        let subtractability = common_stack_subtractability(weight.stack_items());
        self.intersect_row_items_with_subtractability(items, &subtractability)
    }

    fn intersect_row_items_with_subtractability(
        &mut self,
        items: Vec<NegId>,
        subtractability: &Subtractability,
    ) -> Vec<NegId> {
        match subtractability {
            Subtractability::All => items,
            Subtractability::Empty => Vec::new(),
            Subtractability::Set(path, args) => items
                .into_iter()
                .filter(|item| self.constrain_neg_effect_family_args(*item, path, args))
                .collect(),
            Subtractability::SetMany(families) => items
                .into_iter()
                .filter(|item| {
                    families.iter().any(|(path, args)| {
                        self.constrain_neg_effect_family_args(*item, path, args)
                    })
                })
                .collect(),
            Subtractability::AllExcept(path, args) => items
                .into_iter()
                .filter(|item| !self.constrain_neg_effect_family_args(*item, path, args))
                .collect(),
            Subtractability::AllExceptMany(families) => items
                .into_iter()
                .filter(|item| {
                    !families.iter().any(|(path, args)| {
                        self.constrain_neg_effect_family_args(*item, path, args)
                    })
                })
                .collect(),
        }
    }

    fn constrain_neg_effect_family_args(
        &mut self,
        item: NegId,
        path: &[String],
        args: &[NeuId],
    ) -> bool {
        let Neg::Con(item_path, item_args) = self.types.neg(item).clone() else {
            return false;
        };
        if item_path != path {
            return false;
        }
        self.enqueue_invariant_neu_args(item_args, args.to_vec(), ConstraintWeights::empty());
        true
    }

    fn collect_stack_effect_families(&mut self, weight: &StackWeight) {
        let mut families = EffectFamilyMap::default();
        for family in weight.stack_items().flat_map(subtractability_families) {
            self.insert_effect_family(&mut families, family);
        }
    }

    fn collect_neg_effect_items(&mut self, items: Vec<NegId>) -> Vec<NegId> {
        let mut by_path = FxHashMap::<Vec<String>, (usize, Vec<NeuId>)>::default();
        let mut out = Vec::new();
        for item in items {
            let Neg::Con(path, args) = self.types.neg(item).clone() else {
                out.push(item);
                continue;
            };
            if let Some((_, existing_args)) = by_path.get(&path) {
                self.enqueue_invariant_neu_args(
                    existing_args.clone(),
                    args,
                    ConstraintWeights::empty(),
                );
                continue;
            }
            by_path.insert(path, (out.len(), args));
            out.push(item);
        }
        out
    }

    fn neg_effect_families(&self, items: &[NegId]) -> Vec<EffectFamily> {
        let mut families = EffectFamilyMap::default();
        for item in items {
            if let Neg::Con(path, args) = self.types.neg(*item) {
                families.insert_first(EffectFamily {
                    path: path.clone(),
                    args: args.clone(),
                });
            }
        }
        families.into_entries()
    }

    fn insert_effect_family(&mut self, families: &mut EffectFamilyMap, family: EffectFamily) {
        if let EffectFamilyInsert::Duplicate {
            existing_args,
            duplicate_args,
        } = families.insert(family)
        {
            self.enqueue_invariant_neu_args(
                existing_args,
                duplicate_args,
                ConstraintWeights::empty(),
            );
        }
    }

    fn collect_effect_families(
        &mut self,
        families: impl IntoIterator<Item = EffectFamily>,
    ) -> Vec<EffectFamily> {
        let mut out = EffectFamilyMap::default();
        for family in families {
            self.insert_effect_family(&mut out, family);
        }
        out.into_entries()
    }

    fn set_effect_families(
        &mut self,
        families: impl IntoIterator<Item = EffectFamily>,
    ) -> Subtractability {
        match self.collect_effect_families(families).as_slice() {
            [] => Subtractability::Empty,
            [family] => Subtractability::Set(family.path.clone(), family.args.clone()),
            families => Subtractability::SetMany(
                families
                    .iter()
                    .cloned()
                    .map(|family| (family.path, family.args))
                    .collect(),
            ),
        }
    }

    fn all_except_effect_families(
        &mut self,
        families: impl IntoIterator<Item = EffectFamily>,
    ) -> Subtractability {
        match self.collect_effect_families(families).as_slice() {
            [] => Subtractability::All,
            [family] => Subtractability::AllExcept(family.path.clone(), family.args.clone()),
            families => Subtractability::AllExceptMany(
                families
                    .iter()
                    .cloned()
                    .map(|family| (family.path, family.args))
                    .collect(),
            ),
        }
    }

    fn subtract_row_items_from_stack_weight(
        &mut self,
        weight: &StackWeight,
        removed: impl IntoIterator<Item = EffectFamily>,
    ) -> StackWeight {
        let removed = self.collect_effect_families(removed);
        if removed.is_empty() {
            return weight.clone();
        }

        let mut out = StackWeight::empty();
        for entry in weight.entries() {
            let mut residual_parts = Vec::new();
            if entry.floor.is_empty() && entry.stack.is_empty() {
                residual_parts.push(self.subtract_effect_families(Subtractability::All, &removed));
            } else {
                for subtractability in &entry.floor {
                    residual_parts
                        .push(self.subtract_effect_families(subtractability.clone(), &removed));
                }
                for subtractability in &entry.stack {
                    residual_parts
                        .push(self.subtract_effect_families(subtractability.clone(), &removed));
                }
            }
            if let Some(floor) = residual_parts.into_iter().reduce(intersect_subtractability) {
                out = out.compose(&StackWeight::floor(entry.id, floor));
            }
            out = out.compose(&StackWeight::pops(entry.id, entry.pops));
            for subtractability in &entry.stack {
                out = out.compose(&StackWeight::push(
                    entry.id,
                    self.subtract_effect_families(subtractability.clone(), &removed),
                ));
            }
        }
        out
    }

    fn subtract_effect_families(
        &mut self,
        subtractability: Subtractability,
        removed: &[EffectFamily],
    ) -> Subtractability {
        use Subtractability::*;
        match subtractability {
            Empty => Empty,
            All => self.all_except_effect_families(removed.iter().cloned()),
            Set(path, args) => {
                let family = EffectFamily { path, args };
                if let Some(removed) = find_removed_family(&family, removed) {
                    self.enqueue_invariant_neu_args(
                        family.args,
                        removed.args.clone(),
                        ConstraintWeights::empty(),
                    );
                    Empty
                } else {
                    self.set_effect_families([family])
                }
            }
            SetMany(families) => {
                let mut remaining = Vec::new();
                for family in families_from_pairs(families) {
                    if let Some(removed) = find_removed_family(&family, removed) {
                        self.enqueue_invariant_neu_args(
                            family.args,
                            removed.args.clone(),
                            ConstraintWeights::empty(),
                        );
                    } else {
                        remaining.push(family);
                    }
                }
                self.set_effect_families(remaining)
            }
            AllExcept(path, args) => self.all_except_effect_families(
                [EffectFamily { path, args }]
                    .into_iter()
                    .chain(removed.iter().cloned()),
            ),
            AllExceptMany(families) => self.all_except_effect_families(
                families_from_pairs(families)
                    .into_iter()
                    .chain(removed.iter().cloned()),
            ),
        }
    }
}

fn consumed_row_items(original: &[NegId], remaining: &[NegId]) -> Vec<NegId> {
    let mut unmatched_remaining = remaining.to_vec();
    let mut consumed = Vec::new();
    for item in original {
        if let Some(index) = unmatched_remaining
            .iter()
            .position(|remaining| remaining == item)
        {
            unmatched_remaining.remove(index);
        } else {
            consumed.push(*item);
        }
    }
    consumed
}

fn remove_first_row_item(items: &mut Vec<NegId>, item: NegId) {
    if let Some(index) = items.iter().position(|existing| *existing == item) {
        items.remove(index);
    }
}
