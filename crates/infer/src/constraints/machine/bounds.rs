use super::*;

use smallvec::SmallVec;

type BoundReplayActions = SmallVec<[BoundReplayAction; 4]>;

impl ConstraintMachine {
    pub(in crate::constraints) fn add_lower_bound(
        &mut self,
        target: TypeVar,
        pos: PosId,
        weights: ConstraintWeights,
    ) {
        let pos = self.extrude_pos(pos, self.level_of(target));
        let weights = self.check_and_erase_lower_left_filter(pos, weights);
        if !self.bounds.add_lower(target, pos, weights.clone()) {
            return;
        }
        let empty_alias_source = if weights.is_empty() {
            match self.types.pos(pos) {
                Pos::Var(source) => Some(*source),
                _ => None,
            }
        } else {
            None
        };
        if let Some(source) = empty_alias_source {
            self.propagate_var_var_replay_pop_sentinels_across_alias(source, target);
        }
        self.constrain_lower_bound_by_registered_filters(target, pos, &weights);
        self.record_pos_bound_var_neighbors(target, pos);
        self.events.push(ConstraintEvent::LowerBoundAdded {
            var: target,
            bound: pos,
            weights: weights.clone(),
        });
        trace_selected_bound("lower", target, &weights);
        trace_pop_gt1_bound("lower", target, &weights);
        trace_var_bounds("after lower", target, self.bounds.of(target), &self.types);

        let (replay_input_count, replay_enqueued, replay_var_var, actions) =
            self.lower_bound_replay_actions(target, pos, &weights);
        self.apply_bound_replay_actions(actions);
        self.timing
            .record_lower_bound_added(replay_input_count, replay_enqueued, replay_var_var);
    }

    pub(in crate::constraints) fn add_upper_bound(
        &mut self,
        source: TypeVar,
        neg: NegId,
        weights: ConstraintWeights,
    ) {
        let neg = self.extrude_neg(neg, self.level_of(source));
        let weights = self.check_and_erase_upper_left_filter(source, weights);
        if self.upper_bound_subsumed_by_existing(source, neg, &weights) {
            return;
        }
        self.prune_upper_rows_subsumed_by(source, neg, &weights);
        if !self.bounds.add_upper(source, neg, weights.clone()) {
            return;
        }
        let empty_alias_target = if weights.is_empty() {
            match self.types.neg(neg) {
                Neg::Var(target) => Some(*target),
                _ => None,
            }
        } else {
            None
        };
        if let Some(target) = empty_alias_target {
            self.propagate_var_var_replay_pop_sentinels_across_alias(source, target);
        }
        self.record_neg_bound_var_neighbors(source, neg);
        self.events.push(ConstraintEvent::UpperBoundAdded {
            var: source,
            bound: neg,
            weights: weights.clone(),
        });
        trace_selected_bound("upper", source, &weights);
        trace_pop_gt1_bound("upper", source, &weights);
        trace_var_bounds("after upper", source, self.bounds.of(source), &self.types);

        let (replay_input_count, replay_enqueued, replay_var_var, actions) =
            self.upper_bound_replay_actions(source, neg, &weights);
        self.apply_bound_replay_actions(actions);
        self.timing
            .record_upper_bound_added(replay_input_count, replay_enqueued, replay_var_var);
    }

    fn add_var_var_bound_collecting(
        &mut self,
        lower: PosId,
        upper: NegId,
        weights: ConstraintWeights,
        pending: &mut Vec<BoundReplayAction>,
    ) {
        let (Pos::Var(lower_var), Neg::Var(upper_var)) =
            (self.types.pos(lower).clone(), self.types.neg(upper).clone())
        else {
            return;
        };
        let weights = weights.normalize_for_var_var_replay();
        if lower_var == upper_var {
            return;
        }
        let weights = self.check_and_erase_var_var_left_filter(lower_var, weights);
        // Var-var replay is alias closure, not a new source edge. A left pop-only
        // alias cycle can only grow counters by rewalking the same pair, so the
        // replay key drops those counts while preserving the pop ids and right side.
        if let Some((ids, right)) = Self::nonempty_left_pop_only_replay_key(&weights) {
            if self.pop_only_var_var_replay_subsumed_by_upper(
                lower_var,
                upper_var,
                &ids,
                &right,
            ) {
                return;
            }
            if !self.record_var_var_pop_replay_pair(lower_var, upper_var, ids, right) {
                return;
            }
        }
        if !self.record_var_var_pair(lower_var, upper_var, &weights) {
            return;
        }
        if weights.is_empty() {
            self.propagate_var_var_replay_pop_sentinels_across_alias(lower_var, upper_var);
        }
        trace_selected_var_var_bound(lower_var, upper_var, &weights);
        let upper = self.extrude_neg(upper, self.level_of(lower_var));
        self.prune_upper_rows_subsumed_by(lower_var, upper, &weights);
        if self.bounds.add_upper(lower_var, upper, weights.clone()) {
            self.record_neg_bound_var_neighbors(lower_var, upper);
            self.events.push(ConstraintEvent::UpperBoundAdded {
                var: lower_var,
                bound: upper,
                weights: weights.clone(),
            });
            trace_selected_bound("var-var upper", lower_var, &weights);
            trace_pop_gt1_bound("var-var upper", lower_var, &weights);
            trace_var_bounds(
                "after var-var upper",
                lower_var,
                self.bounds.of(lower_var),
                &self.types,
            );
            let (replay_input_count, replay_enqueued, empty_replay_skipped, actions) =
                self.var_var_upper_replay_actions(lower_var, upper, &weights);
            push_bound_replay_actions(pending, actions);
            self.timing.record_var_var_direct_upper_bound(
                replay_input_count,
                replay_enqueued,
                empty_replay_skipped,
            );
        }

        let lower = self.extrude_pos(lower, self.level_of(upper_var));
        if self.bounds.add_lower(upper_var, lower, weights.clone()) {
            self.constrain_lower_bound_by_registered_filters(upper_var, lower, &weights);
            self.record_pos_bound_var_neighbors(upper_var, lower);
            self.events.push(ConstraintEvent::LowerBoundAdded {
                var: upper_var,
                bound: lower,
                weights: weights.clone(),
            });
            trace_selected_bound("var-var lower", upper_var, &weights);
            trace_pop_gt1_bound("var-var lower", upper_var, &weights);
            trace_var_bounds(
                "after var-var lower",
                upper_var,
                self.bounds.of(upper_var),
                &self.types,
            );
            let (replay_input_count, replay_enqueued, empty_replay_skipped, actions) =
                self.var_var_lower_replay_actions(upper_var, lower, &weights);
            push_bound_replay_actions(pending, actions);
            self.timing.record_var_var_direct_lower_bound(
                replay_input_count,
                replay_enqueued,
                empty_replay_skipped,
            );
        }
    }

    fn check_and_erase_lower_left_filter(
        &mut self,
        pos: PosId,
        weights: ConstraintWeights,
    ) -> ConstraintWeights {
        let filter = weights.left_filter_set().clone();
        if !matches!(filter, Subtractability::All) {
            self.constrain_weighted_pos_lower_by_filter(pos, &weights, &filter);
        }
        weights.without_left_filter()
    }

    fn check_and_erase_upper_left_filter(
        &mut self,
        source: TypeVar,
        weights: ConstraintWeights,
    ) -> ConstraintWeights {
        let filter = weights.left_filter_set().clone();
        if !matches!(filter, Subtractability::All) {
            self.constrain_stack_by_filter(&weights.left.to_stack_weight(), &filter);
            self.constrain_type_var_lowers_by_filter(source, filter);
        }
        weights.without_left_filter()
    }

    fn check_and_erase_var_var_left_filter(
        &mut self,
        lower: TypeVar,
        weights: ConstraintWeights,
    ) -> ConstraintWeights {
        let filter = weights.left_filter_set().clone();
        if !matches!(filter, Subtractability::All) {
            self.constrain_stack_by_filter(&weights.left.to_stack_weight(), &filter);
            self.constrain_type_var_lowers_by_filter(lower, filter);
        }
        weights.without_left_filter()
    }

    pub(crate) fn constrain_type_var_lowers_by_filter(
        &mut self,
        var: TypeVar,
        filter: Subtractability,
    ) {
        if matches!(filter, Subtractability::All) {
            return;
        }
        if !self
            .lower_filters
            .entry(var)
            .or_default()
            .insert(filter.clone())
        {
            return;
        }
        let lowers = self
            .bounds
            .of(var)
            .map(|bounds| bounds.lowers.clone())
            .unwrap_or_default();
        for lower in lowers {
            self.constrain_weighted_pos_lower_by_filter(lower.pos, &lower.weights, &filter);
        }
    }

    fn constrain_lower_bound_by_registered_filters(
        &mut self,
        target: TypeVar,
        pos: PosId,
        weights: &ConstraintWeights,
    ) {
        let filters = self.lower_filters.get(&target).cloned().unwrap_or_default();
        for filter in filters {
            self.constrain_weighted_pos_lower_by_filter(pos, weights, &filter);
        }
    }

    fn constrain_weighted_pos_lower_by_filter(
        &mut self,
        pos: PosId,
        weights: &ConstraintWeights,
        filter: &Subtractability,
    ) {
        if matches!(filter, Subtractability::All) {
            return;
        }
        self.constrain_stack_by_filter(&weights.left.to_stack_weight(), filter);
        let filter = weights.left.filter_set().clone().intersect(filter.clone());
        self.constrain_pos_lower_by_filter(pos, &filter);
    }

    pub(in crate::constraints) fn constrain_pos_lower_by_filter(
        &mut self,
        pos: PosId,
        filter: &Subtractability,
    ) {
        if matches!(filter, Subtractability::All) {
            return;
        }
        match self.types.pos(pos).clone() {
            Pos::Con(path, args) => {
                if self.effect_family_paths.contains(&path) {
                    self.constrain_effect_family_by_filter(&path, &args, filter);
                }
            }
            Pos::Row(items) => {
                for item in items {
                    self.constrain_pos_lower_by_filter(item, filter);
                }
            }
            Pos::Stack { inner, weight } => {
                self.constrain_stack_by_filter(&weight, filter);
                self.constrain_pos_lower_by_filter(inner, filter);
            }
            Pos::NonSubtract(inner, weight) => {
                self.constrain_stack_by_filter(&weight, filter);
                self.constrain_pos_lower_by_filter(inner, filter);
            }
            Pos::Union(left, right) => {
                self.constrain_pos_lower_by_filter(left, filter);
                self.constrain_pos_lower_by_filter(right, filter);
            }
            Pos::Var(var) => self.constrain_type_var_lowers_by_filter(var, filter.clone()),
            Pos::Bot
            | Pos::Fun { .. }
            | Pos::Record(_)
            | Pos::RecordTailSpread { .. }
            | Pos::RecordHeadSpread { .. }
            | Pos::PolyVariant(_)
            | Pos::Tuple(_) => {}
        }
    }

    fn lower_bound_replay_actions(
        &self,
        target: TypeVar,
        pos: PosId,
        weights: &ConstraintWeights,
    ) -> (usize, usize, usize, BoundReplayActions) {
        let Some(bounds) = self.bounds.of(target) else {
            return (0, 0, 0, SmallVec::new());
        };
        let replay_input_count = bounds.uppers.len();
        let mut replay_enqueued = 0usize;
        let mut replay_var_var = 0usize;
        let mut actions = SmallVec::with_capacity(replay_input_count);
        trace_bound_replay_start("lower", target, replay_input_count);
        for (index, upper) in bounds.uppers.iter().enumerate() {
            trace_bound_replay_progress("lower", target, index);
            if self.is_var_var_replay(pos, upper.neg) {
                let replay_weights =
                    self.compose_for_var_var_replay_through_upper(
                        target,
                        weights,
                        upper.neg,
                        &upper.weights,
                    );
                trace_pop_gt1_replay(
                    "lower var-var",
                    target,
                    weights,
                    &upper.weights,
                    &replay_weights,
                );
                replay_var_var += 1;
                actions.push(BoundReplayAction::VarVar {
                    lower: pos,
                    upper: upper.neg,
                    weights: replay_weights,
                });
            } else {
                let replay_weights = weights.compose_for_replay(&upper.weights);
                trace_pop_gt1_replay("lower", target, weights, &upper.weights, &replay_weights);
                replay_enqueued += 1;
                actions.push(BoundReplayAction::Subtype {
                    lower: pos,
                    upper: upper.neg,
                    weights: replay_weights,
                });
            }
        }
        (replay_input_count, replay_enqueued, replay_var_var, actions)
    }

    fn upper_bound_replay_actions(
        &self,
        source: TypeVar,
        neg: NegId,
        weights: &ConstraintWeights,
    ) -> (usize, usize, usize, BoundReplayActions) {
        let Some(bounds) = self.bounds.of(source) else {
            return (0, 0, 0, SmallVec::new());
        };
        let replay_input_count = bounds.lowers.len();
        let mut replay_enqueued = 0usize;
        let mut replay_var_var = 0usize;
        let mut actions = SmallVec::with_capacity(replay_input_count);
        trace_bound_replay_start("upper", source, replay_input_count);
        for (index, lower) in bounds.lowers.iter().enumerate() {
            trace_bound_replay_progress("upper", source, index);
            if self.is_var_var_replay(lower.pos, neg) {
                let replay_weights =
                    self.compose_for_var_var_replay_through_upper(source, &lower.weights, neg, weights);
                trace_pop_gt1_replay(
                    "upper var-var",
                    source,
                    &lower.weights,
                    weights,
                    &replay_weights,
                );
                replay_var_var += 1;
                actions.push(BoundReplayAction::VarVar {
                    lower: lower.pos,
                    upper: neg,
                    weights: replay_weights,
                });
            } else {
                let replay_weights = lower.weights.compose_for_replay(weights);
                trace_pop_gt1_replay("upper", source, &lower.weights, weights, &replay_weights);
                replay_enqueued += 1;
                actions.push(BoundReplayAction::Subtype {
                    lower: lower.pos,
                    upper: neg,
                    weights: replay_weights,
                });
            }
        }
        (replay_input_count, replay_enqueued, replay_var_var, actions)
    }

    fn var_var_upper_replay_actions(
        &self,
        lower_var: TypeVar,
        upper: NegId,
        weights: &ConstraintWeights,
    ) -> (usize, usize, usize, BoundReplayActions) {
        let Some(bounds) = self.bounds.of(lower_var) else {
            return (0, 0, 0, SmallVec::new());
        };
        let mut skipped = 0usize;
        let mut replay_enqueued = 0usize;
        let mut actions = SmallVec::with_capacity(bounds.lowers.len());
        for lower in &bounds.lowers {
            if weights.is_empty()
                && lower.weights.is_empty()
                && self.is_var_var_replay(lower.pos, upper)
            {
                skipped += 1;
                continue;
            }
            if self.is_var_var_replay(lower.pos, upper) {
                let replay_weights =
                    self.compose_for_var_var_replay_through_upper(lower_var, &lower.weights, upper, weights);
                if Self::weights_are_pop_only(&replay_weights) {
                    actions.push(BoundReplayAction::VarVar {
                        lower: lower.pos,
                        upper,
                        weights: replay_weights,
                    });
                }
            } else {
                let replay_weights = lower.weights.compose_for_replay(weights);
                replay_enqueued += 1;
                actions.push(BoundReplayAction::Subtype {
                    lower: lower.pos,
                    upper,
                    weights: replay_weights,
                });
            }
        }
        (bounds.lowers.len(), replay_enqueued, skipped, actions)
    }

    fn var_var_lower_replay_actions(
        &self,
        upper_var: TypeVar,
        lower: PosId,
        weights: &ConstraintWeights,
    ) -> (usize, usize, usize, BoundReplayActions) {
        let Some(bounds) = self.bounds.of(upper_var) else {
            return (0, 0, 0, SmallVec::new());
        };
        let mut skipped = 0usize;
        let mut replay_enqueued = 0usize;
        let mut actions = SmallVec::with_capacity(bounds.uppers.len());
        for upper in &bounds.uppers {
            if weights.is_empty()
                && upper.weights.is_empty()
                && self.is_var_var_replay(lower, upper.neg)
            {
                skipped += 1;
                continue;
            }
            let replay_weights =
                self.compose_for_var_var_replay_through_upper(upper_var, weights, upper.neg, &upper.weights);
            if self.is_var_var_replay(lower, upper.neg) {
                if Self::weights_are_pop_only(&replay_weights) {
                    actions.push(BoundReplayAction::VarVar {
                        lower,
                        upper: upper.neg,
                        weights: replay_weights,
                    });
                }
            } else {
                replay_enqueued += 1;
                actions.push(BoundReplayAction::Subtype {
                    lower,
                    upper: upper.neg,
                    weights: replay_weights,
                });
            }
        }
        (bounds.uppers.len(), replay_enqueued, skipped, actions)
    }

    fn compose_for_var_var_replay_through_upper(
        &self,
        middle: TypeVar,
        earlier: &ConstraintWeights,
        later_neg: NegId,
        later_weights: &ConstraintWeights,
    ) -> ConstraintWeights {
        let sentinels = match self.types.neg(later_neg) {
            Neg::Var(upper) => self.var_var_replay_pop_sentinels.get(&(middle, *upper)),
            _ => None,
        };
        earlier.compose_for_var_var_replay_with_pop_sentinels(later_weights, sentinels)
    }

    fn apply_bound_replay_actions(&mut self, actions: BoundReplayActions) {
        let mut pending = Vec::new();
        push_bound_replay_actions(&mut pending, actions);
        self.apply_pending_bound_replay_actions(pending);
    }

    fn apply_pending_bound_replay_actions(&mut self, mut pending: Vec<BoundReplayAction>) {
        // Var-to-var replay can discover more var-to-var replay. Keep that chain
        // on an explicit stack so recursive definitions cannot overflow Rust's stack.
        while let Some(action) = pending.pop() {
            self.apply_bound_replay_action(action, &mut pending);
        }
    }

    fn apply_bound_replay_action(
        &mut self,
        action: BoundReplayAction,
        pending: &mut Vec<BoundReplayAction>,
    ) {
        match action {
            BoundReplayAction::Subtype {
                lower,
                upper,
                weights,
            } => {
                self.enqueue_subtype(lower, weights, upper);
            }
            BoundReplayAction::VarVar {
                lower,
                upper,
                weights,
            } => self.add_var_var_bound_collecting(lower, upper, weights, pending),
        }
    }

    pub(in crate::constraints) fn is_var_var_replay(&self, lower: PosId, upper: NegId) -> bool {
        matches!(self.types.pos(lower), Pos::Var(_)) && matches!(self.types.neg(upper), Neg::Var(_))
    }

    pub(in crate::constraints) fn upper_bound_subsumed_by_existing(
        &self,
        source: TypeVar,
        neg: NegId,
        weights: &ConstraintWeights,
    ) -> bool {
        if !weights.is_empty() {
            return false;
        }
        let Some(bounds) = self.bounds.of(source) else {
            return false;
        };
        if self.source_has_row_tail_boundary(source) {
            return bounds
                .uppers()
                .iter()
                .any(|upper| upper.weights.is_empty() && upper.neg == neg);
        }
        let Neg::Row(_, tail) = self.types.neg(neg) else {
            return bounds
                .uppers()
                .iter()
                .any(|upper| upper.weights.is_empty() && upper.neg == neg);
        };
        bounds.uppers().iter().any(|upper| {
            upper.weights.is_empty() && self.neg_ids_match_for_row_tail(upper.neg, *tail)
        })
    }

    pub(in crate::constraints) fn prune_upper_rows_subsumed_by(
        &mut self,
        source: TypeVar,
        neg: NegId,
        weights: &ConstraintWeights,
    ) {
        if !weights.is_empty() {
            return;
        }
        if self.source_has_row_tail_boundary(source) {
            return;
        }
        self.prune_upper_rows_subsumed_by_reduced_upper(source, neg);
    }

    pub(in crate::constraints) fn prune_upper_rows_subsumed_by_reduced_upper(
        &mut self,
        source: TypeVar,
        neg: NegId,
    ) {
        let Some(bounds) = self
            .bounds
            .vars
            .get_mut(source.0 as usize)
            .and_then(|bounds| bounds.as_mut())
        else {
            return;
        };
        let mut removed = Vec::new();
        bounds.uppers.retain(|upper| {
            let keep = !upper.weights.is_empty() || !row_tail_matches(&self.types, upper.neg, neg);
            if !keep {
                removed.push(upper.neg);
            }
            keep
        });
        for upper in removed {
            self.unrecord_neg_bound_var_neighbors(source, upper);
        }
    }

    pub(in crate::constraints) fn record_pos_bound_var_neighbors(
        &mut self,
        source: TypeVar,
        pos: PosId,
    ) {
        match self.types.pos(pos) {
            Pos::Bot => return,
            Pos::Var(var) => {
                self.record_var_neighbor(source, *var);
                return;
            }
            Pos::Con(_, args) if args.is_empty() => return,
            _ => {}
        }
        let mut vars = FxHashSet::default();
        collect_pos_id_vars(&self.types, pos, &mut vars);
        self.record_bound_var_neighbors(source, vars);
    }

    pub(in crate::constraints) fn record_neg_bound_var_neighbors(
        &mut self,
        source: TypeVar,
        neg: NegId,
    ) {
        match self.types.neg(neg) {
            Neg::Top | Neg::Bot => return,
            Neg::Var(var) => {
                self.record_var_neighbor(source, *var);
                return;
            }
            Neg::Con(_, args) if args.is_empty() => return,
            _ => {}
        }
        let mut vars = FxHashSet::default();
        collect_neg_id_vars(&self.types, neg, &mut vars);
        self.record_bound_var_neighbors(source, vars);
    }

    pub(in crate::constraints) fn unrecord_neg_bound_var_neighbors(
        &mut self,
        source: TypeVar,
        neg: NegId,
    ) {
        match self.types.neg(neg) {
            Neg::Top | Neg::Bot => return,
            Neg::Var(var) => {
                self.unrecord_var_neighbor(source, *var);
                return;
            }
            Neg::Con(_, args) if args.is_empty() => return,
            _ => {}
        }
        let mut vars = FxHashSet::default();
        collect_neg_id_vars(&self.types, neg, &mut vars);
        self.unrecord_bound_var_neighbors(source, vars);
    }

    fn record_bound_var_neighbors(
        &mut self,
        source: TypeVar,
        vars: impl IntoIterator<Item = TypeVar>,
    ) {
        for var in vars {
            self.record_var_neighbor(source, var);
        }
    }

    fn unrecord_bound_var_neighbors(
        &mut self,
        source: TypeVar,
        vars: impl IntoIterator<Item = TypeVar>,
    ) {
        for var in vars {
            self.unrecord_var_neighbor(source, var);
        }
    }

    fn record_var_neighbor(&mut self, left: TypeVar, right: TypeVar) {
        if left == right {
            return;
        }
        *self
            .var_adjacency
            .entry(left)
            .or_default()
            .entry(right)
            .or_default() += 1;
        *self
            .var_adjacency
            .entry(right)
            .or_default()
            .entry(left)
            .or_default() += 1;
    }

    fn unrecord_var_neighbor(&mut self, left: TypeVar, right: TypeVar) {
        if left == right {
            return;
        }
        decrement_var_neighbor(&mut self.var_adjacency, left, right);
        decrement_var_neighbor(&mut self.var_adjacency, right, left);
    }

    fn neg_ids_match_for_row_tail(&self, lhs: NegId, rhs: NegId) -> bool {
        neg_ids_match_for_row_tail(&self.types, lhs, rhs)
    }

    fn source_has_row_tail_boundary(&self, source: TypeVar) -> bool {
        !self.pre_pop_effect_families(source).is_empty()
            || self.bounds.of(source).is_some_and(|bounds| {
                bounds
                    .lowers()
                    .iter()
                    .any(|lower| constraint_weights_have_row_tail_boundary(&lower.weights))
            })
    }

    fn weights_are_pop_only(weights: &ConstraintWeights) -> bool {
        Self::left_weight_is_pop_only(&weights.left)
    }

    fn nonempty_left_pop_only_replay_key(
        weights: &ConstraintWeights,
    ) -> Option<(Vec<SubtractId>, RightConstraintWeight)> {
        if !weights.left.is_empty() && Self::left_weight_is_pop_only(&weights.left) {
            let ids = weights
                .left
                .entries()
                .iter()
                .map(|entry| entry.id)
                .collect();
            return Some((ids, weights.right.clone()));
        }
        None
    }

    fn pop_only_var_var_replay_subsumed_by_upper(
        &self,
        lower_var: TypeVar,
        upper_var: TypeVar,
        ids: &[SubtractId],
        right: &RightConstraintWeight,
    ) -> bool {
        let upper_seen = self.bounds.of(lower_var).is_some_and(|bounds| {
            bounds.uppers().iter().any(|bound| {
                matches!(self.types.neg(bound.neg), Neg::Var(var) if *var == upper_var)
                    && Self::nonempty_left_pop_only_replay_key(&bound.weights)
                        .is_some_and(|(existing_ids, existing_right)| {
                            existing_ids == ids && &existing_right == right
                        })
            })
        });
        let lower_seen = self.bounds.of(upper_var).is_some_and(|bounds| {
            bounds.lowers().iter().any(|bound| {
                matches!(self.types.pos(bound.pos), Pos::Var(var) if *var == lower_var)
                    && Self::nonempty_left_pop_only_replay_key(&bound.weights)
                        .is_some_and(|(existing_ids, existing_right)| {
                            existing_ids == ids && &existing_right == right
                        })
            })
        });
        upper_seen || lower_seen
    }

    fn propagate_var_var_replay_pop_sentinels_across_alias(
        &mut self,
        lower_var: TypeVar,
        upper_var: TypeVar,
    ) {
        let additions = self
            .var_var_replay_pop_sentinels
            .iter()
            .filter_map(|(&(source, target), ids)| {
                if target == lower_var {
                    Some(((source, upper_var), ids.clone()))
                } else if source == upper_var {
                    Some(((lower_var, target), ids.clone()))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        for (key, ids) in additions {
            self.var_var_replay_pop_sentinels
                .entry(key)
                .or_default()
                .extend(ids);
        }
    }

    fn left_weight_is_pop_only(weight: &LeftConstraintWeight) -> bool {
        !weight.has_filter() && weight.entries().iter().all(|entry| entry.pushes == 0)
    }

    pub(in crate::constraints) fn extrude_pos(&mut self, pos: PosId, target: TypeLevel) -> PosId {
        match self.types.pos(pos) {
            Pos::Bot => return pos,
            Pos::Var(var) if self.level_of(*var) <= target => return pos,
            Pos::Con(_, args) if args.is_empty() => return pos,
            _ => {}
        }
        let mut ctx = ExtrudeCtx::new(target);
        self.extrude_pos_id(pos, &mut ctx);
        pos
    }

    pub(in crate::constraints) fn extrude_neg(&mut self, neg: NegId, target: TypeLevel) -> NegId {
        match self.types.neg(neg) {
            Neg::Top | Neg::Bot => return neg,
            Neg::Var(var) if self.level_of(*var) <= target => return neg,
            Neg::Con(_, args) if args.is_empty() => return neg,
            _ => {}
        }
        let mut ctx = ExtrudeCtx::new(target);
        self.extrude_neg_id(neg, &mut ctx);
        neg
    }

    pub(in crate::constraints) fn extrude_pos_id(&mut self, id: PosId, ctx: &mut ExtrudeCtx) {
        if !ctx.visited_pos.insert(id) {
            return;
        }
        match self.types.pos(id).clone() {
            Pos::Bot => {}
            Pos::Var(var) => self.extrude_type_var(var, ctx),
            Pos::Con(_, args) => self.extrude_neu_ids(args, ctx),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.extrude_neg_id(arg, ctx);
                self.extrude_neg_id(arg_eff, ctx);
                self.extrude_pos_id(ret_eff, ctx);
                self.extrude_pos_id(ret, ctx);
            }
            Pos::Record(fields) => {
                for field in fields {
                    self.extrude_pos_id(field.value, ctx);
                }
            }
            Pos::RecordTailSpread { fields, tail } => {
                for field in fields {
                    self.extrude_pos_id(field.value, ctx);
                }
                self.extrude_pos_id(tail, ctx);
            }
            Pos::RecordHeadSpread { tail, fields } => {
                self.extrude_pos_id(tail, ctx);
                for field in fields {
                    self.extrude_pos_id(field.value, ctx);
                }
            }
            Pos::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.extrude_pos_id(payload, ctx);
                    }
                }
            }
            Pos::Tuple(items) | Pos::Row(items) => {
                for item in items {
                    self.extrude_pos_id(item, ctx);
                }
            }
            Pos::Stack { inner, .. } => self.extrude_pos_id(inner, ctx),
            Pos::NonSubtract(pos, _) => self.extrude_pos_id(pos, ctx),
            Pos::Union(left, right) => {
                self.extrude_pos_id(left, ctx);
                self.extrude_pos_id(right, ctx);
            }
        }
    }

    pub(in crate::constraints) fn extrude_neg_id(&mut self, id: NegId, ctx: &mut ExtrudeCtx) {
        if !ctx.visited_neg.insert(id) {
            return;
        }
        match self.types.neg(id).clone() {
            Neg::Top | Neg::Bot => {}
            Neg::Var(var) => self.extrude_type_var(var, ctx),
            Neg::Con(_, args) => self.extrude_neu_ids(args, ctx),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.extrude_pos_id(arg, ctx);
                self.extrude_pos_id(arg_eff, ctx);
                self.extrude_neg_id(ret_eff, ctx);
                self.extrude_neg_id(ret, ctx);
            }
            Neg::Record(fields) => {
                for field in fields {
                    self.extrude_neg_id(field.value, ctx);
                }
            }
            Neg::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.extrude_neg_id(payload, ctx);
                    }
                }
            }
            Neg::Tuple(items) => {
                for item in items {
                    self.extrude_neg_id(item, ctx);
                }
            }
            Neg::Row(items, tail) => {
                for item in items {
                    self.extrude_neg_id(item, ctx);
                }
                self.extrude_neg_id(tail, ctx);
            }
            Neg::Stack { inner, .. } => self.extrude_neg_id(inner, ctx),
            Neg::Intersection(left, right) => {
                self.extrude_neg_id(left, ctx);
                self.extrude_neg_id(right, ctx);
            }
        }
    }

    pub(in crate::constraints) fn extrude_neu_ids(
        &mut self,
        ids: Vec<NeuId>,
        ctx: &mut ExtrudeCtx,
    ) {
        for id in ids {
            self.extrude_neu_id(id, ctx);
        }
    }

    pub(in crate::constraints) fn extrude_neu_id(&mut self, id: NeuId, ctx: &mut ExtrudeCtx) {
        if !ctx.visited_neu.insert(id) {
            return;
        }
        match self.types.neu(id).clone() {
            Neu::Bounds(lower, upper) => {
                self.extrude_pos_id(lower, ctx);
                self.extrude_neg_id(upper, ctx);
            }
            Neu::Con(_, args) => self.extrude_neu_ids(args, ctx),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.extrude_neu_id(arg, ctx);
                self.extrude_neu_id(arg_eff, ctx);
                self.extrude_neu_id(ret_eff, ctx);
                self.extrude_neu_id(ret, ctx);
            }
            Neu::Record(fields) => {
                for field in fields {
                    self.extrude_neu_id(field.value, ctx);
                }
            }
            Neu::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.extrude_neu_id(payload, ctx);
                    }
                }
            }
            Neu::Tuple(items) => self.extrude_neu_ids(items, ctx),
        }
    }

    pub(in crate::constraints) fn extrude_type_var(&mut self, var: TypeVar, ctx: &mut ExtrudeCtx) {
        if self.level_of(var) <= ctx.target {
            return;
        }
        if !ctx.visited.insert(var) {
            return;
        }
        self.levels.lower_to(var, ctx.target);
        let bounds = self
            .bounds
            .of(var)
            .map(|bounds| (bounds.lowers.clone(), bounds.uppers.clone()));
        if let Some((lowers, uppers)) = bounds {
            for lower in lowers {
                self.extrude_pos_id(lower.pos, ctx);
            }
            for upper in uppers {
                self.extrude_neg_id(upper.neg, ctx);
            }
        }
    }
}

/// Snapshot of replay work. Applying a replay action can mutate the same
/// bounds table, so replay construction must not keep borrowed bound rows.
enum BoundReplayAction {
    Subtype {
        lower: PosId,
        upper: NegId,
        weights: ConstraintWeights,
    },
    VarVar {
        lower: PosId,
        upper: NegId,
        weights: ConstraintWeights,
    },
}

fn push_bound_replay_actions(pending: &mut Vec<BoundReplayAction>, actions: BoundReplayActions) {
    pending.extend(actions.into_iter().rev());
}

fn decrement_var_neighbor(
    adjacency: &mut FxHashMap<TypeVar, FxHashMap<TypeVar, usize>>,
    left: TypeVar,
    right: TypeVar,
) {
    let Some(neighbors) = adjacency.get_mut(&left) else {
        return;
    };
    let Some(count) = neighbors.get_mut(&right) else {
        return;
    };
    *count = count.saturating_sub(1);
    if *count == 0 {
        neighbors.remove(&right);
    }
    if neighbors.is_empty() {
        adjacency.remove(&left);
    }
}

fn collect_pos_id_vars(types: &TypeArena, id: PosId, out: &mut FxHashSet<TypeVar>) {
    match types.pos(id) {
        Pos::Bot => {}
        Pos::Var(var) => {
            out.insert(*var);
        }
        Pos::Con(_, args) => collect_neu_id_vars(types, args.iter().copied(), out),
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_neg_id_vars(types, *arg, out);
            collect_neg_id_vars(types, *arg_eff, out);
            collect_pos_id_vars(types, *ret_eff, out);
            collect_pos_id_vars(types, *ret, out);
        }
        Pos::Record(fields) => {
            for field in fields {
                collect_pos_id_vars(types, field.value, out);
            }
        }
        Pos::RecordTailSpread { fields, tail } => {
            for field in fields {
                collect_pos_id_vars(types, field.value, out);
            }
            collect_pos_id_vars(types, *tail, out);
        }
        Pos::RecordHeadSpread { tail, fields } => {
            collect_pos_id_vars(types, *tail, out);
            for field in fields {
                collect_pos_id_vars(types, field.value, out);
            }
        }
        Pos::PolyVariant(items) => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_pos_id_vars(types, *payload, out);
                }
            }
        }
        Pos::Tuple(items) | Pos::Row(items) => {
            for item in items {
                collect_pos_id_vars(types, *item, out);
            }
        }
        Pos::Stack { inner, .. } | Pos::NonSubtract(inner, _) => {
            collect_pos_id_vars(types, *inner, out);
        }
        Pos::Union(left, right) => {
            collect_pos_id_vars(types, *left, out);
            collect_pos_id_vars(types, *right, out);
        }
    }
}

fn collect_neg_id_vars(types: &TypeArena, id: NegId, out: &mut FxHashSet<TypeVar>) {
    match types.neg(id) {
        Neg::Top | Neg::Bot => {}
        Neg::Var(var) => {
            out.insert(*var);
        }
        Neg::Con(_, args) => collect_neu_id_vars(types, args.iter().copied(), out),
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_pos_id_vars(types, *arg, out);
            collect_pos_id_vars(types, *arg_eff, out);
            collect_neg_id_vars(types, *ret_eff, out);
            collect_neg_id_vars(types, *ret, out);
        }
        Neg::Record(fields) => {
            for field in fields {
                collect_neg_id_vars(types, field.value, out);
            }
        }
        Neg::PolyVariant(items) => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_neg_id_vars(types, *payload, out);
                }
            }
        }
        Neg::Tuple(items) => {
            for item in items {
                collect_neg_id_vars(types, *item, out);
            }
        }
        Neg::Row(items, tail) => {
            for item in items {
                collect_neg_id_vars(types, *item, out);
            }
            collect_neg_id_vars(types, *tail, out);
        }
        Neg::Stack { inner, .. } => collect_neg_id_vars(types, *inner, out),
        Neg::Intersection(left, right) => {
            collect_neg_id_vars(types, *left, out);
            collect_neg_id_vars(types, *right, out);
        }
    }
}

fn collect_neu_id_vars(
    types: &TypeArena,
    ids: impl IntoIterator<Item = NeuId>,
    out: &mut FxHashSet<TypeVar>,
) {
    for id in ids {
        match types.neu(id) {
            Neu::Bounds(lower, upper) => {
                collect_pos_id_vars(types, *lower, out);
                collect_neg_id_vars(types, *upper, out);
            }
            Neu::Con(_, args) => collect_neu_id_vars(types, args.iter().copied(), out),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                collect_neu_id_vars(types, [*arg, *arg_eff, *ret_eff, *ret], out);
            }
            Neu::Record(fields) => {
                for field in fields {
                    collect_neu_id_vars(types, [field.value], out);
                }
            }
            Neu::PolyVariant(items) => {
                for (_, payloads) in items {
                    collect_neu_id_vars(types, payloads.iter().copied(), out);
                }
            }
            Neu::Tuple(items) => collect_neu_id_vars(types, items.iter().copied(), out),
        }
    }
}

fn row_tail_matches(types: &TypeArena, row_upper: NegId, tail_upper: NegId) -> bool {
    let Neg::Row(_, tail) = types.neg(row_upper) else {
        return false;
    };
    neg_ids_match_for_row_tail(types, *tail, tail_upper)
}

fn neg_ids_match_for_row_tail(types: &TypeArena, lhs: NegId, rhs: NegId) -> bool {
    if lhs == rhs {
        return true;
    }
    match (types.neg(lhs), types.neg(rhs)) {
        (Neg::Var(left), Neg::Var(right)) => left == right,
        (Neg::Top, Neg::Top) | (Neg::Bot, Neg::Bot) => true,
        _ => false,
    }
}

fn constraint_weights_have_row_tail_boundary(weights: &ConstraintWeights) -> bool {
    left_constraint_weight_has_row_tail_boundary(&weights.left)
}

fn left_constraint_weight_has_row_tail_boundary(weight: &LeftConstraintWeight) -> bool {
    weight.has_filter() || weight.entries().iter().any(|entry| entry.pushes > 0)
}

fn trace_pop_gt1_bound(kind: &str, var: TypeVar, weights: &ConstraintWeights) {
    if std::env::var("YULANG_TRACE_POP_GT1_BOUNDS").is_err() {
        return;
    }
    let left = weights.left.to_stack_weight();
    let right = weights.right.to_stack_weight();
    let has_large_pop = left
        .entries()
        .iter()
        .chain(right.entries())
        .any(|entry| entry.pops > 1);
    if has_large_pop {
        eprintln!("[constraints] {kind} var={var:?} weights={weights:?}");
    }
}

fn trace_selected_bound(kind: &str, var: TypeVar, weights: &ConstraintWeights) {
    let Ok(value) = std::env::var("YULANG_TRACE_BOUNDS_FOR") else {
        return;
    };
    if !value.split(',').any(|part| {
        part.trim()
            .parse::<u32>()
            .is_ok_and(|expected| expected == var.0)
    }) {
        return;
    }
    eprintln!("[constraints] selected {kind} var={var:?} weights={weights:?}");
}

fn trace_selected_var_var_bound(lower: TypeVar, upper: TypeVar, weights: &ConstraintWeights) {
    let Ok(value) = std::env::var("YULANG_TRACE_VAR_VAR_FOR") else {
        return;
    };
    if !value.split(',').any(|part| {
        let mut sides = part.trim().split("->");
        match (sides.next(), sides.next(), sides.next()) {
            (Some(left), Some(right), None) => {
                trace_type_var_side_matches(left, lower) && trace_type_var_side_matches(right, upper)
            }
            _ => false,
        }
    }) {
        return;
    }
    eprintln!("[constraints] selected var-var lower={lower:?} upper={upper:?} weights={weights:?}");
}

fn trace_type_var_side_matches(pattern: &str, var: TypeVar) -> bool {
    let pattern = pattern.trim();
    pattern == "*" || pattern.parse::<u32>().is_ok_and(|expected| expected == var.0)
}

fn trace_pop_gt1_replay(
    kind: &str,
    var: TypeVar,
    earlier: &ConstraintWeights,
    later: &ConstraintWeights,
    replay: &ConstraintWeights,
) {
    if std::env::var("YULANG_TRACE_POP_GT1_REPLAY").is_err() {
        return;
    }
    let left = replay.left.to_stack_weight();
    let right = replay.right.to_stack_weight();
    let has_large_pop = left
        .entries()
        .iter()
        .chain(right.entries())
        .any(|entry| entry.pops > 1);
    if has_large_pop {
        eprintln!(
            "[constraints] replay {kind} var={var:?} earlier={earlier:?} later={later:?} replay={replay:?}"
        );
    }
}
