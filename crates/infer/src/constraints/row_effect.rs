//! Weighted effect-row upper bounds and row-subtraction residuals.

use super::*;

impl ConstraintMachine {
    pub(in crate::constraints) fn row_derivation_parents(
        &mut self,
        producer: Option<ConstraintRecordId>,
        weights: &ConstraintWeights,
        use_rule: SubtractFactUseRule,
    ) -> Vec<RowDerivationParent> {
        let mut parents = producer
            .map(RowDerivationParent::Constraint)
            .into_iter()
            .collect::<Vec<_>>();
        let mut subtract_ids = weights
            .left
            .entries()
            .iter()
            .map(|entry| entry.id)
            .chain(weights.right.entries().iter().map(|entry| entry.id))
            .collect::<Vec<_>>();
        subtract_ids.sort_by_key(|id| id.0);
        subtract_ids.dedup();
        let fact_ids = subtract_ids
            .into_iter()
            .flat_map(|id| {
                self.subtracts
                    .record_ids_by_subtract
                    .get(&id)
                    .into_iter()
                    .flatten()
                    .copied()
            })
            .collect::<Vec<_>>();
        let fact_use = SubtractFactUse {
            rule: use_rule,
            consumer: producer,
        };
        let mut provenance_changed = false;
        for id in fact_ids {
            let record = &mut self.subtracts.records[id.0 as usize];
            if !record.uses.contains(&fact_use) {
                record.uses.push(fact_use);
                provenance_changed = true;
            }
            parents.push(RowDerivationParent::SubtractFact(id));
        }
        if provenance_changed {
            self.bump_provenance_epoch();
        }
        parents
    }

    pub(in crate::constraints) fn row_derivation_parents_from_bound(
        derivation: &BoundDerivation,
    ) -> Vec<RowDerivationParent> {
        match derivation {
            BoundDerivation::Constraint(parent) => vec![RowDerivationParent::Constraint(*parent)],
            BoundDerivation::Origin(origin) => vec![RowDerivationParent::Origin(*origin)],
            BoundDerivation::ReplayEvidence(replay) => vec![
                RowDerivationParent::Bound(replay.lower),
                RowDerivationParent::Bound(replay.upper),
            ],
            BoundDerivation::Row(parent) => vec![RowDerivationParent::RowDerivation(*parent)],
            BoundDerivation::SchemeInstantiation(_) => Vec::new(),
            BoundDerivation::IncompleteReplay => Vec::new(),
        }
    }

    fn enqueue_row_invariant_args(
        &mut self,
        rule: RowDerivationRule,
        parents: Vec<RowDerivationParent>,
        lower: Vec<NeuId>,
        upper: Vec<NeuId>,
        weights: ConstraintWeights,
    ) {
        let derivation = self.intern_row_derivation(rule, parents, Vec::new());
        for (lower, upper) in lower.into_iter().zip(upper) {
            let (lower_pos, lower_neg) = self.neu_bounds(lower);
            let (upper_pos, upper_neg) = self.neu_bounds(upper);
            self.enqueue_row_derived_subtype(lower_pos, weights.clone(), upper_neg, derivation);
            self.enqueue_row_derived_subtype(upper_pos, weights.swapped(), lower_neg, derivation);
        }
    }

    pub(super) fn add_effect_row_upper_bound(
        &mut self,
        source: TypeVar,
        items: Vec<NegId>,
        tail: NegId,
        weights: ConstraintWeights,
        producer: Option<ConstraintRecordId>,
    ) {
        if weights.is_empty() {
            if self.add_unweighted_effect_row_upper_bound_from_existing_lowers(
                source,
                items.clone(),
                tail,
                producer,
            ) {
                // Preserve CPROV-D's historical characterization while CPROV-G separately records
                // that this path now owns an exact multi-parent hyperedge.
                self.timing.record_structural_deferred_multi_parent();
                return;
            }
            let row = self.alloc_neg(Neg::Row(items, tail));
            self.add_upper_bound(
                source,
                row,
                weights,
                producer
                    .map(BoundDerivation::Constraint)
                    .unwrap_or(BoundDerivation::Origin(OriginId::unknown_internal())),
            );
            return;
        }

        let filter_parents =
            self.row_derivation_parents(producer, &weights, SubtractFactUseRule::Filter);
        self.constrain_neg_effect_items_by_filter(
            &items,
            weights.left.filter_set(),
            &filter_parents,
        );

        let weights = ConstraintWeights {
            left: weights.left.with_filter(Subtractability::All),
            right: weights.right,
        };
        if weights.is_empty() {
            let row = self.alloc_neg(Neg::Row(items, tail));
            self.add_upper_bound(
                source,
                row,
                ConstraintWeights::empty(),
                producer
                    .map(BoundDerivation::Constraint)
                    .unwrap_or(BoundDerivation::Origin(OriginId::unknown_internal())),
            );
            return;
        }

        if matches!(self.types.neg(tail), Neg::Var(tail_var) if *tail_var == source)
            && weights.right.is_empty()
        {
            return;
        }

        let row_parents =
            self.row_derivation_parents(producer, &weights, SubtractFactUseRule::RowReduction);
        let retained_items =
            self.intersect_row_items_with_left_stack(items, &weights.left, &row_parents);
        let retained_items = self.collect_neg_effect_items(retained_items, &row_parents);
        if retained_items.is_empty() {
            let source_pos = self.alloc_pos(Pos::Var(source));
            let parents =
                self.row_derivation_parents(producer, &weights, SubtractFactUseRule::RowReduction);
            let derivation = self.intern_row_derivation(
                RowDerivationRule::WeightedResidual,
                parents,
                Vec::new(),
            );
            self.enqueue_row_derived_subtype(
                source_pos,
                weights.normalize_directed_mix(),
                tail,
                derivation,
            );
            return;
        }

        let retained_families = self.neg_effect_families(&retained_items);
        let residual_weight = self.subtract_row_items_from_left_stack_weight(
            &weights.left,
            retained_families.clone(),
            &row_parents,
        );
        let key = RowResidualKey {
            source,
            retained_families: sorted_effect_families(retained_families),
            weight: residual_weight.clone(),
        };
        let (gamma, residual, reused) = if let Some(gamma) = self.row_residuals.get(&key) {
            let gamma = *gamma;
            let residual = self.row_residual_record_ids[&key];
            self.timing.record_row_residual_reused();
            (gamma, residual, true)
        } else {
            let gamma = self.fresh_internal_type_var_at(self.level_of(source));
            let residual = RowResidualRecordId(self.row_residual_records.len() as u32);
            self.row_residuals.insert(key.clone(), gamma);
            self.row_residual_record_ids.insert(key.clone(), residual);
            self.row_residual_records.push(RowResidualRecord {
                key,
                gamma,
                derivations: Vec::new(),
            });
            self.timing.record_row_residual_created();
            (gamma, residual, false)
        };
        let parents =
            self.row_derivation_parents(producer, &weights, SubtractFactUseRule::RowReduction);
        let derivation = self.intern_row_derivation(
            RowDerivationRule::WeightedResidual,
            parents,
            retained_items.clone(),
        );
        let residual_record = &mut self.row_residual_records[residual.0 as usize];
        if !residual_record.derivations.contains(&derivation) {
            residual_record.derivations.push(derivation);
        }
        self.timing.record_row_residual_derivation(reused);

        let gamma_neg = self.alloc_neg(Neg::Var(gamma));
        let upper = self.alloc_neg(Neg::Row(retained_items, gamma_neg));
        // Feed the residual row back through the normal subtype path so future
        // upper bounds on gamma can replay into source through the same machinery.
        let source_pos = self.alloc_pos(Pos::Var(source));
        self.enqueue_row_derived_subtype(source_pos, ConstraintWeights::empty(), upper, derivation);

        let gamma_pos = self.alloc_pos(Pos::Var(gamma));
        self.enqueue_row_derived_subtype(
            gamma_pos,
            ConstraintWeights {
                left: residual_weight,
                right: weights.right,
            }
            .normalize_directed_mix(),
            tail,
            derivation,
        );
    }

    fn add_unweighted_effect_row_upper_bound_from_existing_lowers(
        &mut self,
        source: TypeVar,
        items: Vec<NegId>,
        tail: NegId,
        producer: Option<ConstraintRecordId>,
    ) -> bool {
        if items.is_empty() {
            return false;
        }
        let lowers = self.bounds.of(source).map_or_else(Vec::new, |bounds| {
            bounds
                .lower_record_ids()
                .iter()
                .copied()
                .zip(bounds.lowers().iter().cloned())
                .collect::<Vec<_>>()
        });
        if lowers.is_empty() {
            return false;
        }

        let mut remaining = items.clone();
        let mut matched_lowers = vec![false; lowers.len()];
        let mut matching_parents = Vec::new();
        let mut item_matches = Vec::new();
        for (index, (record, lower)) in lowers.iter().enumerate() {
            if !Self::constraint_weights_are_alias_neutral(&lower.weights) {
                continue;
            }
            let mut seen = FxHashSet::default();
            let mut local_remaining = items.clone();
            if self.consume_row_items_from_lower_bound(
                lower.pos,
                &mut local_remaining,
                &mut seen,
                &mut item_matches,
            ) {
                for consumed in consumed_row_items(&items, &local_remaining) {
                    remove_first_row_item(&mut remaining, consumed);
                }
                matched_lowers[index] = true;
                if !matching_parents.contains(record) {
                    matching_parents.push(*record);
                }
            }
        }
        if matched_lowers.iter().all(|matched| !matched) {
            return false;
        }

        let original_upper = self.effect_row_upper(items, tail);
        let reduced_upper = self.effect_row_upper(remaining, tail);
        let mut parents = producer
            .map(RowDerivationParent::Constraint)
            .into_iter()
            .collect::<Vec<_>>();
        parents.extend(matching_parents.into_iter().map(RowDerivationParent::Bound));
        let aggregate =
            self.intern_row_derivation(RowDerivationRule::UnweightedReduction, parents, Vec::new());
        for (lower, upper) in item_matches {
            let derivation = self.intern_row_derivation(
                RowDerivationRule::RowItemMatch,
                vec![RowDerivationParent::RowDerivation(aggregate)],
                vec![upper],
            );
            self.enqueue_row_item_match_from_row(
                lower,
                upper,
                ConstraintWeights::empty(),
                derivation,
            );
        }
        self.store_upper_bound_without_replay(
            source,
            reduced_upper,
            ConstraintWeights::empty(),
            BoundDerivation::Row(aggregate),
        );

        for (index, (_, lower)) in lowers.into_iter().enumerate() {
            let upper = if matched_lowers[index] {
                original_upper
            } else {
                reduced_upper
            };
            self.enqueue_row_derived_subtype(lower.pos, lower.weights, upper, aggregate);
        }
        true
    }

    fn consume_row_items_from_lower_bound(
        &mut self,
        pos: PosId,
        remaining: &mut Vec<NegId>,
        seen: &mut FxHashSet<TypeVar>,
        item_matches: &mut Vec<(PosId, NegId)>,
    ) -> bool {
        match self.types.pos(pos).clone() {
            Pos::Con(_, _) => self.consume_matching_row_item(pos, remaining, item_matches),
            Pos::Row(items) => {
                let mut consumed = false;
                for item in items {
                    consumed |= self.consume_row_items_from_lower_bound(
                        item,
                        remaining,
                        seen,
                        item_matches,
                    );
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
                    consumed |= self.consume_row_items_from_lower_bound(
                        lower.pos,
                        remaining,
                        seen,
                        item_matches,
                    );
                }
                consumed
            }
            _ => false,
        }
    }

    fn consume_matching_row_item(
        &mut self,
        lower: PosId,
        remaining: &mut Vec<NegId>,
        item_matches: &mut Vec<(PosId, NegId)>,
    ) -> bool {
        let Some(index) = remaining
            .iter()
            .position(|upper| self.row_items_can_match(lower, *upper))
        else {
            return false;
        };
        let upper = remaining.remove(index);
        item_matches.push((lower, upper));
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
    }

    fn stack_weight_is_alias_neutral(weight: &LeftConstraintWeight) -> bool {
        !weight.has_filter() && weight.entries().iter().all(|entry| entry.pushes == 0)
    }

    fn store_upper_bound_without_replay(
        &mut self,
        source: TypeVar,
        neg: NegId,
        weights: ConstraintWeights,
        derivation: BoundDerivation,
    ) -> bool {
        let neg = self.extrude_neg(neg, self.level_of(source));
        if let Some(survivor) = self.upper_bound_subsumed_by_existing(source, neg, &weights) {
            self.record_bound_disposition(
                BoundDirection::Upper,
                source,
                BoundEndpoint::Upper(neg),
                weights,
                Some(derivation),
                BoundDisposition::SubsumedBy(survivor),
                None,
            );
            return false;
        }
        let pruned = if weights.is_empty() {
            self.prune_upper_rows_subsumed_by_reduced_upper(source, neg)
        } else {
            self.prune_upper_rows_subsumed_by(source, neg, &weights)
        };
        let insertion = self
            .bounds
            .add_upper(source, neg, weights.clone(), derivation.clone());
        self.record_bound_provenance(insertion, BoundDirection::Upper, false);
        self.record_bound_disposition(
            BoundDirection::Upper,
            source,
            BoundEndpoint::Upper(neg),
            weights.clone(),
            Some(derivation),
            if insertion.semantic_changed {
                BoundDisposition::Inserted(insertion.id)
            } else {
                BoundDisposition::EquivalentTo(insertion.id)
            },
            None,
        );
        self.record_pruned_bound_dispositions(pruned, insertion.id);
        if !insertion.semantic_changed {
            return false;
        }
        self.timing.record_row_upper_bound_added_without_replay();
        // Keep this mutation outside the legacy replay/lifecycle epoch: changing that epoch can
        // alter existing production audit paths. The supplemental role-solve witness is inert.
        self.bump_role_solve_supplemental_epoch();
        if self.method_role_mutations.is_active() {
            self.method_role_mutations
                .record(DependencyKey::ConstraintBounds(source));
        }
        self.record_neg_bound_var_neighbors(source, neg);
        self.events.push(ConstraintEvent::UpperBoundAdded {
            record: insertion.id,
            producer: None,
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

    fn intersect_row_items_with_left_stack(
        &mut self,
        items: Vec<NegId>,
        weight: &LeftConstraintWeight,
        parents: &[RowDerivationParent],
    ) -> Vec<NegId> {
        let subtractability =
            self.common_stack_subtractability(left_active_stack_items(weight), parents);
        self.intersect_row_items_with_subtractability(items, &subtractability, parents)
    }

    pub(in crate::constraints) fn common_stack_subtractability<'a>(
        &mut self,
        items: impl Iterator<Item = &'a Subtractability>,
        parents: &[RowDerivationParent],
    ) -> Subtractability {
        let items = items.cloned().collect::<Vec<_>>();
        self.constrain_duplicate_subtractability_families(&items, parents);
        items
            .into_iter()
            .reduce(intersect_subtractability)
            .unwrap_or(Subtractability::All)
    }

    fn constrain_duplicate_subtractability_families(
        &mut self,
        items: &[Subtractability],
        parents: &[RowDerivationParent],
    ) {
        let mut families = EffectFamilyMap::default();
        for family in items.iter().flat_map(subtractability_families) {
            self.insert_effect_family(
                &mut families,
                family,
                RowDerivationRule::SubtractFactTransformation,
                parents,
            );
        }
    }

    pub(in crate::constraints) fn constrain_stack_by_filter(
        &mut self,
        weight: &StackWeight,
        filter: &Subtractability,
        parents: &[RowDerivationParent],
    ) {
        if matches!(filter, Subtractability::All) {
            return;
        }
        for entry in weight.entries() {
            for subtractability in &entry.stack {
                self.constrain_subtractability_by_filter(subtractability, filter, parents);
            }
        }
    }

    fn constrain_neg_effect_items_by_filter(
        &mut self,
        items: &[NegId],
        filter: &Subtractability,
        parents: &[RowDerivationParent],
    ) {
        if matches!(filter, Subtractability::All) {
            return;
        }
        for item in items {
            self.constrain_neg_effect_item_by_filter(*item, filter, parents);
        }
    }

    fn constrain_subtractability_by_filter(
        &mut self,
        subtractability: &Subtractability,
        filter: &Subtractability,
        parents: &[RowDerivationParent],
    ) {
        match subtractability {
            Subtractability::Empty => {}
            Subtractability::All => {
                self.record_effect_filter_violation(None, filter.clone());
            }
            Subtractability::AllExcept(_, _) | Subtractability::AllExceptMany(_) => {
                if !matches!(filter, Subtractability::All) {
                    self.record_effect_filter_violation(None, filter.clone());
                }
            }
            Subtractability::Set(path, args) => {
                self.constrain_effect_family_by_filter(path, args, filter, parents);
            }
            Subtractability::SetMany(families) => {
                for (path, args) in families {
                    self.constrain_effect_family_by_filter(path, args, filter, parents);
                }
            }
        }
    }

    fn constrain_neg_effect_item_by_filter(
        &mut self,
        item: NegId,
        filter: &Subtractability,
        parents: &[RowDerivationParent],
    ) {
        let Neg::Con(path, args) = self.types.neg(item).clone() else {
            return;
        };
        self.constrain_effect_family_by_filter(&path, &args, filter, parents);
    }

    pub(in crate::constraints) fn constrain_effect_family_by_filter(
        &mut self,
        path: &[String],
        args: &[NeuId],
        filter: &Subtractability,
        parents: &[RowDerivationParent],
    ) {
        if !self.effect_family_passes_filter(path, args, filter, parents) {
            self.record_effect_filter_violation(Some(path.to_vec()), filter.clone());
        }
    }

    fn effect_family_passes_filter(
        &mut self,
        path: &[String],
        args: &[NeuId],
        filter: &Subtractability,
        parents: &[RowDerivationParent],
    ) -> bool {
        match filter {
            Subtractability::All => true,
            Subtractability::Empty => false,
            Subtractability::Set(filter_path, filter_args) => {
                if filter_path == path {
                    self.enqueue_row_invariant_args(
                        RowDerivationRule::FilterInvariant,
                        parents.to_vec(),
                        args.to_vec(),
                        filter_args.clone(),
                        ConstraintWeights::empty(),
                    );
                    true
                } else {
                    false
                }
            }
            Subtractability::SetMany(families) => {
                let mut matched = false;
                for (filter_path, filter_args) in families {
                    if filter_path == path {
                        self.enqueue_row_invariant_args(
                            RowDerivationRule::FilterInvariant,
                            parents.to_vec(),
                            args.to_vec(),
                            filter_args.clone(),
                            ConstraintWeights::empty(),
                        );
                        matched = true;
                    }
                }
                matched
            }
            Subtractability::AllExcept(filter_path, filter_args) => {
                if filter_path == path {
                    self.enqueue_row_invariant_args(
                        RowDerivationRule::FilterInvariant,
                        parents.to_vec(),
                        args.to_vec(),
                        filter_args.clone(),
                        ConstraintWeights::empty(),
                    );
                    false
                } else {
                    true
                }
            }
            Subtractability::AllExceptMany(families) => {
                let mut excluded = false;
                for (filter_path, filter_args) in families {
                    if filter_path == path {
                        self.enqueue_row_invariant_args(
                            RowDerivationRule::FilterInvariant,
                            parents.to_vec(),
                            args.to_vec(),
                            filter_args.clone(),
                            ConstraintWeights::empty(),
                        );
                        excluded = true;
                    }
                }
                !excluded
            }
        }
    }

    fn record_effect_filter_violation(
        &mut self,
        effect: Option<Vec<String>>,
        filter: Subtractability,
    ) {
        if matches!(filter, Subtractability::All) {
            return;
        }
        let key = EffectFilterViolationKey { effect, filter };
        if self.effect_filter_violations.insert(key.clone()) {
            self.events.push(ConstraintEvent::EffectFilterViolation {
                effect: key.effect,
                filter: key.filter,
            });
        }
    }

    fn intersect_row_items_with_subtractability(
        &mut self,
        items: Vec<NegId>,
        subtractability: &Subtractability,
        parents: &[RowDerivationParent],
    ) -> Vec<NegId> {
        match subtractability {
            Subtractability::All => items,
            Subtractability::Empty => Vec::new(),
            Subtractability::Set(path, args) => items
                .into_iter()
                .filter(|item| self.constrain_neg_effect_family_args(*item, path, args, parents))
                .collect(),
            Subtractability::SetMany(families) => items
                .into_iter()
                .filter(|item| {
                    families.iter().any(|(path, args)| {
                        self.constrain_neg_effect_family_args(*item, path, args, parents)
                    })
                })
                .collect(),
            Subtractability::AllExcept(path, args) => items
                .into_iter()
                .filter(|item| !self.constrain_neg_effect_family_args(*item, path, args, parents))
                .collect(),
            Subtractability::AllExceptMany(families) => items
                .into_iter()
                .filter(|item| {
                    !families.iter().any(|(path, args)| {
                        self.constrain_neg_effect_family_args(*item, path, args, parents)
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
        parents: &[RowDerivationParent],
    ) -> bool {
        let Neg::Con(item_path, item_args) = self.types.neg(item).clone() else {
            return false;
        };
        if item_path != path {
            return false;
        }
        self.enqueue_row_invariant_args(
            RowDerivationRule::PayloadInvariant,
            parents.to_vec(),
            item_args,
            args.to_vec(),
            ConstraintWeights::empty(),
        );
        true
    }

    fn collect_neg_effect_items(
        &mut self,
        items: Vec<NegId>,
        parents: &[RowDerivationParent],
    ) -> Vec<NegId> {
        let mut by_path = FxHashMap::<Vec<String>, (usize, Vec<NeuId>)>::default();
        let mut out = Vec::new();
        for item in items {
            let Neg::Con(path, args) = self.types.neg(item).clone() else {
                out.push(item);
                continue;
            };
            if let Some((_, existing_args)) = by_path.get(&path) {
                self.enqueue_row_invariant_args(
                    RowDerivationRule::PayloadInvariant,
                    parents.to_vec(),
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

    fn insert_effect_family(
        &mut self,
        families: &mut EffectFamilyMap,
        family: EffectFamily,
        rule: RowDerivationRule,
        parents: &[RowDerivationParent],
    ) {
        if let EffectFamilyInsert::Duplicate {
            existing_args,
            duplicate_args,
        } = families.insert(family)
        {
            self.enqueue_row_invariant_args(
                rule,
                parents.to_vec(),
                existing_args,
                duplicate_args,
                ConstraintWeights::empty(),
            );
        }
    }

    fn collect_effect_families(
        &mut self,
        families: impl IntoIterator<Item = EffectFamily>,
        rule: RowDerivationRule,
        parents: &[RowDerivationParent],
    ) -> Vec<EffectFamily> {
        let mut out = EffectFamilyMap::default();
        for family in families {
            self.insert_effect_family(&mut out, family, rule, parents);
        }
        out.into_entries()
    }

    fn set_effect_families(
        &mut self,
        families: impl IntoIterator<Item = EffectFamily>,
        parents: &[RowDerivationParent],
    ) -> Subtractability {
        match self
            .collect_effect_families(
                families,
                RowDerivationRule::SubtractFactTransformation,
                parents,
            )
            .as_slice()
        {
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
        parents: &[RowDerivationParent],
    ) -> Subtractability {
        match self
            .collect_effect_families(
                families,
                RowDerivationRule::SubtractFactTransformation,
                parents,
            )
            .as_slice()
        {
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

    fn subtract_row_items_from_left_stack_weight(
        &mut self,
        weight: &LeftConstraintWeight,
        removed: impl IntoIterator<Item = EffectFamily>,
        parents: &[RowDerivationParent],
    ) -> LeftConstraintWeight {
        let removed = self.collect_effect_families(
            removed,
            RowDerivationRule::SubtractFactTransformation,
            parents,
        );
        if removed.is_empty() {
            return weight.with_filter(Subtractability::All);
        }

        let mut out = LeftConstraintWeight::empty();
        for entry in weight.entries() {
            out = out.compose(&LeftConstraintWeight::pops(entry.id, entry.leading_pops));
            if entry.pushes > 0 {
                let family = entry.family.clone().unwrap_or(Subtractability::All);
                let family = self.subtract_effect_families(family, &removed, parents);
                for _ in 0..entry.pushes {
                    out = out.compose(&LeftConstraintWeight::push(entry.id, family.clone()));
                }
            }
        }
        out
    }

    fn subtract_effect_families(
        &mut self,
        subtractability: Subtractability,
        removed: &[EffectFamily],
        parents: &[RowDerivationParent],
    ) -> Subtractability {
        use Subtractability::*;
        match subtractability {
            Empty => Empty,
            All => self.all_except_effect_families(removed.iter().cloned(), parents),
            Set(path, args) => {
                let family = EffectFamily { path, args };
                if let Some(removed) = find_removed_family(&family, removed) {
                    self.enqueue_row_invariant_args(
                        RowDerivationRule::SubtractFactTransformation,
                        parents.to_vec(),
                        family.args,
                        removed.args.clone(),
                        ConstraintWeights::empty(),
                    );
                    Empty
                } else {
                    self.set_effect_families([family], parents)
                }
            }
            SetMany(families) => {
                let mut remaining = Vec::new();
                for family in families_from_pairs(families) {
                    if let Some(removed) = find_removed_family(&family, removed) {
                        self.enqueue_row_invariant_args(
                            RowDerivationRule::SubtractFactTransformation,
                            parents.to_vec(),
                            family.args,
                            removed.args.clone(),
                            ConstraintWeights::empty(),
                        );
                    } else {
                        remaining.push(family);
                    }
                }
                self.set_effect_families(remaining, parents)
            }
            AllExcept(path, args) => self.all_except_effect_families(
                [EffectFamily { path, args }]
                    .into_iter()
                    .chain(removed.iter().cloned()),
                parents,
            ),
            AllExceptMany(families) => self.all_except_effect_families(
                families_from_pairs(families)
                    .into_iter()
                    .chain(removed.iter().cloned()),
                parents,
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

fn left_active_stack_items(
    weight: &LeftConstraintWeight,
) -> impl Iterator<Item = &Subtractability> + '_ {
    weight.active_stack_items()
}
