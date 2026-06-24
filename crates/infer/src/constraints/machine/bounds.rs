use super::*;

use smallvec::SmallVec;

type BoundReplayActions = SmallVec<[BoundReplayAction; 4]>;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct BoundReplayApplyStats {
    accepted: usize,
    duplicate: usize,
    trivial: usize,
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
        self.constrain_lower_bound_by_registered_filters(target, pos, &weights);
        self.record_pos_bound_var_neighbors(target, pos);
        self.events.push(ConstraintEvent::LowerBoundAdded {
            var: target,
            bound: pos,
            weights: weights.clone(),
        });
        trace_var_bounds("after lower", target, self.bounds.of(target), &self.types);

        let (replay_input_count, replay_enqueued, replay_var_var, actions) =
            self.lower_bound_replay_actions(target, pos, &weights);
        let apply = self.apply_bound_replay_actions(actions);
        self.timing.record_lower_bound_added(
            replay_input_count,
            replay_enqueued,
            replay_var_var,
            apply.accepted,
            apply.duplicate,
            apply.trivial,
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
        self.record_neg_bound_var_neighbors(source, neg);
        self.events.push(ConstraintEvent::UpperBoundAdded {
            var: source,
            bound: neg,
            weights: weights.clone(),
        });
        trace_var_bounds("after upper", source, self.bounds.of(source), &self.types);

        let (replay_input_count, replay_enqueued, replay_var_var, actions) =
            self.upper_bound_replay_actions(source, neg, &weights);
        let apply = self.apply_bound_replay_actions(actions);
        self.timing.record_upper_bound_added(
            replay_input_count,
            replay_enqueued,
            replay_var_var,
            apply.accepted,
            apply.duplicate,
            apply.trivial,
        );
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
            let replay_weights = weights.compose_for_replay(&upper.weights);
            if self.is_var_var_replay(pos, upper.neg) {
                replay_var_var += 1;
            }
            replay_enqueued += 1;
            actions.push(BoundReplayAction::Subtype {
                lower: pos,
                upper: upper.neg,
                weights: replay_weights,
            });
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
            let replay_weights = lower.weights.compose_for_replay(weights);
            if self.is_var_var_replay(lower.pos, neg) {
                replay_var_var += 1;
            }
            replay_enqueued += 1;
            actions.push(BoundReplayAction::Subtype {
                lower: lower.pos,
                upper: neg,
                weights: replay_weights,
            });
        }
        (replay_input_count, replay_enqueued, replay_var_var, actions)
    }

    fn apply_bound_replay_actions(&mut self, actions: BoundReplayActions) -> BoundReplayApplyStats {
        let mut stats = BoundReplayApplyStats::default();
        for action in actions {
            let BoundReplayAction::Subtype {
                lower,
                upper,
                weights,
            } = action;
            match self.enqueue_subtype_classified(lower, weights, upper) {
                EnqueueSubtypeResult::Enqueued => stats.accepted += 1,
                EnqueueSubtypeResult::Duplicate => stats.duplicate += 1,
                EnqueueSubtypeResult::Trivial => stats.trivial += 1,
            }
        }
        stats
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
