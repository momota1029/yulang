use super::*;

use smallvec::SmallVec;

/// Snapshot of canonical replay work. Applying a replay constraint can mutate
/// the same bounds table, so replay construction must not keep borrowed bound
/// rows. Existing duplicate/trivial constraints are filtered before this
/// snapshot to avoid materializing replay actions that `seen` would drop.
type BoundReplayActions = SmallVec<[SubtypeConstraint; 4]>;

#[derive(Debug, Default, PartialEq, Eq)]
struct BoundReplayPlan {
    input_count: usize,
    generated: usize,
    var_var: usize,
    prefiltered: usize,
    prefilter_duplicate: ReplayDuplicateProfile,
    stats: BoundReplayApplyStats,
    actions: BoundReplayActions,
    evidence_actions: BoundReplayActions,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct BoundReplayApplyStats {
    accepted: usize,
    duplicate: usize,
    trivial: usize,
}

impl BoundReplayApplyStats {
    fn absorb(&mut self, other: Self) {
        self.accepted += other.accepted;
        self.duplicate += other.duplicate;
        self.trivial += other.trivial;
    }
}

impl ConstraintMachine {
    pub(in crate::constraints) fn add_lower_bound(
        &mut self,
        target: TypeVar,
        pos: PosId,
        weights: ConstraintWeights,
    ) {
        let pos = self.extrude_pos(pos, self.level_of(target));
        let weights = self.check_and_erase_lower_left_filter(pos, weights);
        if self.lower_var_alias_replay_cycle_subsumed(target, pos, &weights) {
            return;
        }
        if !self.bounds.add_lower(target, pos, weights.clone()) {
            return;
        }
        self.record_effective_bounds_mutation(target);
        let frontier_shadow = self.observe_lower_replay_frontier_shadow(target, pos, &weights);
        self.constrain_lower_bound_by_registered_filters(target, pos, &weights);
        self.record_pos_bound_var_neighbors(target, pos);
        self.events.push(ConstraintEvent::LowerBoundAdded {
            var: target,
            bound: pos,
            weights: weights.clone(),
        });
        trace_var_bounds("after lower", target, self.bounds.of(target), &self.types);

        let mut replay = self.lower_bound_replay_actions(target, pos, &weights);
        let apply = self.apply_bound_replay_actions(replay.actions);
        replay.stats.absorb(apply);
        let evidence_count = replay.evidence_actions.len();
        self.apply_bound_replay_evidence_actions(replay.evidence_actions);
        self.record_lower_replay_frontier_shadow(frontier_shadow, replay.stats.accepted);
        self.timing.record_lower_bound_added(
            replay.input_count,
            replay.generated,
            replay.var_var,
            replay.stats.accepted,
            evidence_count,
            replay.stats.duplicate,
            replay.stats.trivial,
            replay.prefiltered,
            replay.prefilter_duplicate,
        );
    }

    pub(in crate::constraints) fn add_upper_bound(
        &mut self,
        source: TypeVar,
        neg: NegId,
        weights: ConstraintWeights,
    ) {
        let neg = self.extrude_neg(neg, self.level_of(source));
        let weights = self.check_and_erase_upper_left_filter(source, weights);
        if self.upper_var_alias_replay_cycle_subsumed(source, neg, &weights) {
            return;
        }
        if self.upper_bound_subsumed_by_existing(source, neg, &weights) {
            return;
        }
        self.prune_upper_rows_subsumed_by(source, neg, &weights);
        if !self.bounds.add_upper(source, neg, weights.clone()) {
            return;
        }
        self.record_effective_bounds_mutation(source);
        let frontier_shadow = self.observe_upper_replay_frontier_shadow(source, neg, &weights);
        self.record_neg_bound_var_neighbors(source, neg);
        self.events.push(ConstraintEvent::UpperBoundAdded {
            var: source,
            bound: neg,
            weights: weights.clone(),
        });
        trace_var_bounds("after upper", source, self.bounds.of(source), &self.types);

        let mut replay = self.upper_bound_replay_actions(source, neg, &weights);
        let apply = self.apply_bound_replay_actions(replay.actions);
        replay.stats.absorb(apply);
        let evidence_count = replay.evidence_actions.len();
        self.apply_bound_replay_evidence_actions(replay.evidence_actions);
        self.record_upper_replay_frontier_shadow(frontier_shadow, replay.stats.accepted);
        self.timing.record_upper_bound_added(
            replay.input_count,
            replay.generated,
            replay.var_var,
            replay.stats.accepted,
            evidence_count,
            replay.stats.duplicate,
            replay.stats.trivial,
            replay.prefiltered,
            replay.prefilter_duplicate,
        );
    }

    /// Publish one effective mutation of the exact projected bound vectors.
    ///
    /// This is deliberately independent of replay. Callers are the ordinary and evidence bound
    /// insertions already represented by the legacy global and per-variable epochs.
    pub(in crate::constraints) fn record_effective_bounds_mutation(&mut self, var: TypeVar) {
        if self.method_role_mutations.is_active() {
            self.method_role_mutations
                .record(DependencyKey::ConstraintBounds(var));
        }
        let epoch = self.bump_epoch();
        self.bounds.record_var_epoch(var, epoch);
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
    ) -> BoundReplayPlan {
        let Some(bounds) = self.bounds.of(target) else {
            return BoundReplayPlan::default();
        };
        let replay_input_count = bounds.projection_uppers().count();
        let mut replay = BoundReplayPlan {
            input_count: replay_input_count,
            ..BoundReplayPlan::default()
        };
        trace_bound_replay_start("lower", target, replay_input_count);
        for (index, upper) in bounds.projection_uppers().enumerate() {
            trace_bound_replay_progress("lower", target, index);
            let replay_weights = weights.compose_for_replay(&upper.weights);
            if self.is_var_var_replay(pos, upper.neg) {
                replay.var_var += 1;
            }
            replay.generated += 1;
            self.push_replay_constraint_or_prefilter(pos, replay_weights, upper.neg, &mut replay);
        }
        replay
    }

    fn upper_bound_replay_actions(
        &self,
        source: TypeVar,
        neg: NegId,
        weights: &ConstraintWeights,
    ) -> BoundReplayPlan {
        let Some(bounds) = self.bounds.of(source) else {
            return BoundReplayPlan::default();
        };
        let replay_input_count = bounds.projection_lowers().count();
        let mut replay = BoundReplayPlan {
            input_count: replay_input_count,
            ..BoundReplayPlan::default()
        };
        trace_bound_replay_start("upper", source, replay_input_count);
        for (index, lower) in bounds.projection_lowers().enumerate() {
            trace_bound_replay_progress("upper", source, index);
            let replay_weights = lower.weights.compose_for_replay(weights);
            if self.is_var_var_replay(lower.pos, neg) {
                replay.var_var += 1;
            }
            replay.generated += 1;
            self.push_replay_constraint_or_prefilter(lower.pos, replay_weights, neg, &mut replay);
        }
        replay
    }

    fn push_replay_constraint_or_prefilter(
        &self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
        replay: &mut BoundReplayPlan,
    ) {
        let duplicate_profile = self.replay_duplicate_profile(lower, &weights, upper);
        let Some(constraint) = self.canonical_subtype_constraint(lower, weights, upper) else {
            replay.prefiltered += 1;
            replay.stats.trivial += 1;
            return;
        };
        let seen_before = self.seen.contains(&constraint);
        self.observe_weighted_routing_consequence_shadow(&constraint, seen_before);
        if seen_before {
            replay.prefiltered += 1;
            replay.stats.duplicate += 1;
            replay.prefilter_duplicate.absorb(duplicate_profile);
            return;
        }
        if self.should_store_replay_as_evidence_only(&constraint) {
            replay.prefiltered += 1;
            replay.evidence_actions.push(constraint);
            return;
        }
        replay.actions.push(constraint);
    }

    fn replay_duplicate_profile(
        &self,
        lower: PosId,
        weights: &ConstraintWeights,
        upper: NegId,
    ) -> ReplayDuplicateProfile {
        let var_var_key = self.is_var_var_replay(lower, upper);
        let terminal_weight_erased =
            !weights.is_empty() && self.has_terminal_subtype_endpoint(lower, upper);
        ReplayDuplicateProfile {
            exact_key: usize::from(!var_var_key && !terminal_weight_erased),
            var_var_key: usize::from(var_var_key),
            terminal_weight_erased: usize::from(terminal_weight_erased),
            row_tail: usize::from(self.is_row_tail_replay_candidate(upper)),
        }
    }

    fn is_row_tail_replay_candidate(&self, upper: NegId) -> bool {
        matches!(
            self.types.neg(upper),
            Neg::Row(_, tail) if matches!(self.types.neg(*tail), Neg::Var(_))
        )
    }

    fn observe_lower_replay_frontier_shadow(
        &mut self,
        pivot: TypeVar,
        pos: PosId,
        weights: &ConstraintWeights,
    ) -> ReplayFrontierShadowObservation {
        if self.replay_frontier_shadow.is_none() {
            return ReplayFrontierShadowObservation::NotCandidate;
        }
        let Pos::Var(endpoint) = self.types.pos(pos) else {
            return ReplayFrontierShadowObservation::NotCandidate;
        };
        let Some(shadow) = self.replay_frontier_shadow.as_mut() else {
            return ReplayFrontierShadowObservation::NotCandidate;
        };
        shadow.observe_lower_var_var(pivot, *endpoint, weights)
    }

    fn observe_upper_replay_frontier_shadow(
        &mut self,
        pivot: TypeVar,
        neg: NegId,
        weights: &ConstraintWeights,
    ) -> ReplayFrontierShadowObservation {
        if self.replay_frontier_shadow.is_none() {
            return ReplayFrontierShadowObservation::NotCandidate;
        }
        let Neg::Var(endpoint) = self.types.neg(neg) else {
            return ReplayFrontierShadowObservation::NotCandidate;
        };
        let Some(shadow) = self.replay_frontier_shadow.as_mut() else {
            return ReplayFrontierShadowObservation::NotCandidate;
        };
        shadow.observe_upper_var_var(pivot, *endpoint, weights)
    }

    fn record_lower_replay_frontier_shadow(
        &mut self,
        observation: ReplayFrontierShadowObservation,
        accepted: usize,
    ) {
        if let Some(shadow) = &mut self.replay_frontier_shadow {
            shadow.record_lower_result(observation, accepted);
        }
    }

    fn record_upper_replay_frontier_shadow(
        &mut self,
        observation: ReplayFrontierShadowObservation,
        accepted: usize,
    ) {
        if let Some(shadow) = &mut self.replay_frontier_shadow {
            shadow.record_upper_result(observation, accepted);
        }
    }

    fn observe_weighted_routing_consequence_shadow(
        &self,
        constraint: &SubtypeConstraint,
        seen_before: bool,
    ) {
        let Some(shadow) = &self.replay_routing_shadow else {
            return;
        };
        let (Pos::Var(source), Neg::Var(target)) = (
            self.types.pos(constraint.lower),
            self.types.neg(constraint.upper),
        ) else {
            return;
        };
        shadow.borrow_mut().observe_var_var_consequence(
            *source,
            *target,
            &constraint.weights,
            seen_before,
        );
    }

    fn should_store_replay_as_evidence_only(&self, constraint: &SubtypeConstraint) -> bool {
        if !evidence_only_replay_skip_enabled() {
            return false;
        }
        let Some(shadow) = &self.replay_routing_shadow else {
            return false;
        };
        let (Pos::Var(source), Neg::Var(target)) = (
            self.types.pos(constraint.lower),
            self.types.neg(constraint.upper),
        ) else {
            return false;
        };
        shadow
            .borrow_mut()
            .has_weighted_frontier_path(*source, *target, &constraint.weights)
    }

    fn apply_bound_replay_actions(&mut self, actions: BoundReplayActions) -> BoundReplayApplyStats {
        let mut stats = BoundReplayApplyStats::default();
        for constraint in actions {
            if self.enqueue_canonical_subtype(constraint) {
                stats.accepted += 1;
            } else {
                stats.duplicate += 1;
            }
        }
        stats
    }

    fn apply_bound_replay_evidence_actions(&mut self, actions: BoundReplayActions) {
        for constraint in actions {
            let (source, target) = match (
                self.types.pos(constraint.lower),
                self.types.neg(constraint.upper),
            ) {
                (Pos::Var(source), Neg::Var(target)) => (*source, *target),
                _ => continue,
            };
            if self
                .bounds
                .add_evidence_lower(target, constraint.lower, constraint.weights.clone())
            {
                self.timing.record_evidence_lower_bound_added();
                self.record_effective_bounds_mutation(target);
            }
            if self
                .bounds
                .add_evidence_upper(source, constraint.upper, constraint.weights)
            {
                self.timing.record_evidence_upper_bound_added();
                self.record_effective_bounds_mutation(source);
            }
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

    fn lower_var_alias_replay_cycle_subsumed(
        &self,
        target: TypeVar,
        pos: PosId,
        weights: &ConstraintWeights,
    ) -> bool {
        if !matches!(self.types.pos(pos), Pos::Var(_))
            || alias_replay_cycle_weight_key(weights).is_none()
        {
            return false;
        }
        self.bounds.of(target).is_some_and(|bounds| {
            bounds.lowers().iter().any(|lower| {
                lower.pos == pos && alias_replay_cycle_weights_match(&lower.weights, weights)
            })
        })
    }

    fn upper_var_alias_replay_cycle_subsumed(
        &self,
        source: TypeVar,
        neg: NegId,
        weights: &ConstraintWeights,
    ) -> bool {
        if !matches!(self.types.neg(neg), Neg::Var(_))
            || alias_replay_cycle_weight_key(weights).is_none()
        {
            return false;
        }
        self.bounds.of(source).is_some_and(|bounds| {
            bounds.uppers().iter().any(|upper| {
                upper.neg == neg && alias_replay_cycle_weights_match(&upper.weights, weights)
            })
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
        let bounds_changed = !removed.is_empty();
        for upper in removed {
            self.unrecord_neg_bound_var_neighbors(source, upper);
        }
        if bounds_changed {
            self.bump_role_solve_supplemental_epoch();
            if self.method_role_mutations.is_active() {
                self.method_role_mutations
                    .record(DependencyKey::ConstraintBounds(source));
            }
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
        if !self.method_role_mutations.is_active() {
            increment_var_neighbor(&mut self.var_adjacency, left, right);
            increment_var_neighbor(&mut self.var_adjacency, right, left);
            return;
        }
        let left_transition =
            increment_var_neighbor_recording_transition(&mut self.var_adjacency, left, right);
        let right_transition =
            increment_var_neighbor_recording_transition(&mut self.var_adjacency, right, left);
        if left_transition != right_transition {
            self.method_role_mutations.invalidate_all(
                InvalidateAllReason::AuditFenceDisagreement {
                    site: "record_var_neighbor symmetry",
                },
            );
            return;
        }
        if left_transition {
            self.method_role_mutations.record_many([
                DependencyKey::ConstraintNeighbors(left),
                DependencyKey::ConstraintNeighbors(right),
            ]);
        }
    }

    fn unrecord_var_neighbor(&mut self, left: TypeVar, right: TypeVar) {
        if left == right {
            return;
        }
        let left_transition = decrement_var_neighbor(&mut self.var_adjacency, left, right);
        let right_transition = decrement_var_neighbor(&mut self.var_adjacency, right, left);
        if !self.method_role_mutations.is_active() {
            return;
        }
        if left_transition != right_transition {
            self.method_role_mutations.invalidate_all(
                InvalidateAllReason::AuditFenceDisagreement {
                    site: "unrecord_var_neighbor symmetry",
                },
            );
            return;
        }
        if left_transition {
            self.method_role_mutations.record_many([
                DependencyKey::ConstraintNeighbors(left),
                DependencyKey::ConstraintNeighbors(right),
            ]);
        }
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
        let level_lowered = self.levels.lower_to(var, ctx.target);
        if level_lowered {
            self.bump_role_solve_supplemental_epoch();
            if self.method_role_mutations.is_active() {
                self.method_role_mutations
                    .record(DependencyKey::ConstraintLevel(var));
            }
        }
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

#[cfg(test)]
mod mutation_tests {
    use super::*;

    #[test]
    fn evidence_add_and_promotion_emit_bounds_only_while_active() {
        let mut machine = ConstraintMachine::new();
        let source = TypeVar(0);
        let target = TypeVar(1);
        machine.register_type_var(source, TypeLevel::root());
        machine.register_type_var(target, TypeLevel::root());
        assert!(machine.take_method_role_mutations().is_empty());

        let journal = machine.activate_method_role_mutations();
        let lower = machine.alloc_pos(Pos::Var(source));
        let upper = machine.alloc_neg(Neg::Var(target));
        let mut actions = BoundReplayActions::new();
        actions.push(SubtypeConstraint {
            lower,
            upper,
            weights: ConstraintWeights::empty(),
        });
        machine.apply_bound_replay_evidence_actions(actions);
        assert_eq!(
            changed_keys(machine.take_method_role_mutations()),
            [
                DependencyKey::ConstraintBounds(target),
                DependencyKey::ConstraintBounds(source),
            ]
        );
        assert_eq!(
            machine.bounds().of(target).unwrap().evidence_lower_count(),
            1
        );
        assert_eq!(
            machine.bounds().of(source).unwrap().evidence_upper_count(),
            1
        );

        machine.add_lower_bound(target, lower, ConstraintWeights::empty());
        assert!(
            changed_keys(machine.take_method_role_mutations())
                .contains(&DependencyKey::ConstraintBounds(target))
        );
        assert_eq!(
            machine.bounds().of(target).unwrap().evidence_lower_count(),
            0
        );

        machine.add_upper_bound(source, upper, ConstraintWeights::empty());
        assert!(
            changed_keys(machine.take_method_role_mutations())
                .contains(&DependencyKey::ConstraintBounds(source))
        );
        assert_eq!(
            machine.bounds().of(source).unwrap().evidence_upper_count(),
            0
        );
        journal.finish();

        machine.register_type_var(TypeVar(2), TypeLevel::root());
        assert!(machine.take_method_role_mutations().is_empty());
    }

    #[test]
    fn neighbor_symmetry_audit_fences_fail_closed_when_active() {
        let left = TypeVar(3);
        let right = TypeVar(4);

        let mut add = ConstraintMachine::new();
        add.var_adjacency.entry(left).or_default().insert(right, 1);
        let add_journal = add.activate_method_role_mutations();
        add.record_var_neighbor(left, right);
        assert!(matches!(
            add.method_role_mutations(),
            [MethodRoleMutation::InvalidateAll {
                reason: InvalidateAllReason::AuditFenceDisagreement {
                    site: "record_var_neighbor symmetry",
                },
                ..
            }]
        ));
        add_journal.finish();

        let mut remove = ConstraintMachine::new();
        remove
            .var_adjacency
            .entry(left)
            .or_default()
            .insert(right, 1);
        let remove_journal = remove.activate_method_role_mutations();
        remove.unrecord_var_neighbor(left, right);
        assert!(matches!(
            remove.method_role_mutations(),
            [MethodRoleMutation::InvalidateAll {
                reason: InvalidateAllReason::AuditFenceDisagreement {
                    site: "unrecord_var_neighbor symmetry",
                },
                ..
            }]
        ));
        remove_journal.finish();
    }

    fn changed_keys(mutations: Vec<MethodRoleMutation>) -> Vec<DependencyKey> {
        mutations
            .into_iter()
            .filter_map(|mutation| match mutation {
                MethodRoleMutation::Changed { key, .. } => Some(key),
                MethodRoleMutation::InvalidateAll { reason, .. } => {
                    panic!("unexpected InvalidateAll: {reason:?}")
                }
            })
            .collect()
    }
}

fn increment_var_neighbor(
    adjacency: &mut FxHashMap<TypeVar, FxHashMap<TypeVar, usize>>,
    left: TypeVar,
    right: TypeVar,
) {
    *adjacency.entry(left).or_default().entry(right).or_default() += 1;
}

fn increment_var_neighbor_recording_transition(
    adjacency: &mut FxHashMap<TypeVar, FxHashMap<TypeVar, usize>>,
    left: TypeVar,
    right: TypeVar,
) -> bool {
    let count = adjacency.entry(left).or_default().entry(right).or_default();
    let absent = *count == 0;
    *count += 1;
    absent
}

fn decrement_var_neighbor(
    adjacency: &mut FxHashMap<TypeVar, FxHashMap<TypeVar, usize>>,
    left: TypeVar,
    right: TypeVar,
) -> bool {
    let Some(neighbors) = adjacency.get_mut(&left) else {
        return false;
    };
    let Some(count) = neighbors.get_mut(&right) else {
        return false;
    };
    *count = count.saturating_sub(1);
    let removed = *count == 0;
    if *count == 0 {
        neighbors.remove(&right);
    }
    if neighbors.is_empty() {
        adjacency.remove(&left);
    }
    removed
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct AliasReplayCycleLeftEntry {
    id: SubtractId,
    leading_pop: bool,
    family: Option<Subtractability>,
    push: bool,
}

fn alias_replay_cycle_weights_match(lhs: &ConstraintWeights, rhs: &ConstraintWeights) -> bool {
    let Some(lhs) = alias_replay_cycle_weight_key(lhs) else {
        return false;
    };
    let Some(rhs) = alias_replay_cycle_weight_key(rhs) else {
        return false;
    };
    lhs == rhs
}

fn alias_replay_cycle_weight_key(
    weights: &ConstraintWeights,
) -> Option<(Vec<AliasReplayCycleLeftEntry>, Vec<SubtractId>)> {
    if weights.left.has_filter() {
        return None;
    }
    let left = weights
        .left
        .entries()
        .iter()
        .filter(|entry| entry.leading_pops > 0 || entry.pushes > 0)
        .map(|entry| AliasReplayCycleLeftEntry {
            id: entry.id,
            leading_pop: entry.leading_pops > 0,
            family: entry.family.clone(),
            push: entry.pushes > 0,
        })
        .collect::<Vec<_>>();
    let right = weights
        .right
        .entries()
        .iter()
        .filter(|entry| entry.pops > 0)
        .map(|entry| entry.id)
        .collect::<Vec<_>>();
    if left.is_empty() && right.is_empty() {
        None
    } else {
        Some((left, right))
    }
}
