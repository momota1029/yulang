use super::*;

use crate::time::Instant;

impl ConstraintMachine {
    pub fn new() -> Self {
        Self {
            types: TypeArena::new(),
            queue: VecDeque::new(),
            bounds: TypeBounds::new(),
            var_adjacency: FxHashMap::default(),
            subtracts: SubtractTable::new(),
            levels: TypeLevels::new(),
            next_internal_type_var: 0,
            row_residuals: FxHashMap::default(),
            declared_subtracts: FxHashSet::default(),
            effect_family_paths: FxHashSet::default(),
            row_tail_vars: FxHashSet::default(),
            pre_pop_effect_families: FxHashMap::default(),
            lower_filters: FxHashMap::default(),
            effect_filter_violations: FxHashSet::default(),
            seen: FxHashSet::default(),
            events: Vec::new(),
            method_role_mutations: MethodRoleMutationOutbox::new(),
            timing: ConstraintTiming::default(),
            epoch: ConstraintEpoch::default(),
            replay_frontier_shadow: ReplayFrontierShadow::from_env(),
            replay_routing_shadow: ReplayRoutingShadow::from_env().map(RefCell::new),
        }
    }

    pub fn alloc_pos(&mut self, pos: Pos) -> PosId {
        self.observe_pos(&pos);
        self.types.alloc_pos(pos)
    }

    pub fn alloc_neg(&mut self, neg: Neg) -> NegId {
        self.observe_neg(&neg);
        self.types.alloc_neg(neg)
    }

    pub fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        self.observe_neu(&neu);
        self.types.alloc_neu(neu)
    }

    pub fn types(&self) -> &TypeArena {
        &self.types
    }

    pub fn bounds(&self) -> &TypeBounds {
        &self.bounds
    }

    pub(crate) fn var_neighbors(&self, var: TypeVar) -> impl Iterator<Item = TypeVar> + '_ {
        #[cfg(test)]
        crate::analysis::record_owner_neighbor_read(var);
        self.var_adjacency
            .get(&var)
            .into_iter()
            .flat_map(|neighbors| neighbors.keys().copied())
    }

    pub fn subtracts(&self) -> &SubtractTable {
        &self.subtracts
    }

    pub fn register_type_var(&mut self, var: TypeVar, level: TypeLevel) {
        if self.method_role_mutations.is_active() {
            if self.levels.register_recording_change(var, level) {
                self.method_role_mutations.record_many([
                    DependencyKey::ConstraintLevel(var),
                    DependencyKey::ConstraintBirthLevel(var),
                ]);
            }
        } else {
            self.levels.register(var, level);
        }
        self.next_internal_type_var = self.next_internal_type_var.max(var.0.saturating_add(1));
    }

    pub fn level_of(&self, var: TypeVar) -> TypeLevel {
        #[cfg(test)]
        crate::analysis::record_owner_level_read(var);
        self.levels.level_of(var)
    }

    pub fn birth_level_of(&self, var: TypeVar) -> TypeLevel {
        #[cfg(test)]
        crate::analysis::record_owner_birth_level_read(var);
        self.levels.birth_level_of(var)
    }

    pub fn next_type_var(&self) -> u32 {
        self.next_internal_type_var
    }

    pub fn events(&self) -> &[ConstraintEvent] {
        &self.events
    }

    pub fn timing(&self) -> ConstraintTiming {
        let mut timing = self.timing;
        timing.epoch = self.epoch.as_u64();
        timing.type_var_count = self.next_internal_type_var as usize;
        timing.row_tail_var_count = self.row_tail_vars.len();
        timing.pos_node_count = self.types.pos_len();
        timing.neg_node_count = self.types.neg_len();
        timing.neu_node_count = self.types.neu_len();
        timing.type_node_count = self.types.node_len();
        if let Some(shadow) = &self.replay_frontier_shadow {
            timing.replay_frontier_shadow_lower_var_var = shadow.lower_var_var;
            timing.replay_frontier_shadow_upper_var_var = shadow.upper_var_var;
        }
        if let Some(shadow) = &self.replay_routing_shadow {
            let shadow = shadow.borrow();
            timing.replay_routing_shadow_var_var = shadow.metrics;
            if let Some(weighted) = &shadow.weighted {
                timing.replay_weighted_routing_shadow_var_var = weighted.metrics;
            }
        }
        timing
    }

    pub fn epoch(&self) -> ConstraintEpoch {
        self.epoch
    }

    pub fn take_events(&mut self) -> Vec<ConstraintEvent> {
        std::mem::take(&mut self.events)
    }

    pub(crate) fn activate_method_role_mutations(&self) -> MethodRoleMutationActivation {
        self.method_role_mutations.activate()
    }

    pub(crate) fn method_role_mutation_generation(&self) -> MutationGeneration {
        self.method_role_mutations.generation()
    }

    pub(crate) fn drain_method_role_mutations_into(
        &mut self,
        target: &mut MethodRoleMutationOutbox,
    ) -> bool {
        self.method_role_mutations.drain_into(target)
    }

    #[cfg(test)]
    pub(crate) fn method_role_mutation_journal_active(&self) -> bool {
        self.method_role_mutations.is_active()
    }

    #[cfg(test)]
    pub(crate) fn method_role_mutations(&self) -> &[MethodRoleMutation] {
        self.method_role_mutations.mutations()
    }

    #[cfg(test)]
    pub(crate) fn method_role_owner_eligibility(&self) -> bool {
        self.method_role_mutations.owner_eligibility()
    }

    #[cfg(test)]
    pub(crate) fn take_method_role_mutations(&mut self) -> Vec<MethodRoleMutation> {
        self.method_role_mutations.take()
    }

    #[cfg(test)]
    pub(crate) fn invalidate_method_role_mutations_for_test(
        &mut self,
        reason: InvalidateAllReason,
    ) {
        self.method_role_mutations.invalidate_all(reason);
    }

    pub fn subtype(&mut self, lower: PosId, upper: NegId) {
        self.timing.record_subtype_call();
        if self.enqueue_subtype(lower, ConstraintWeights::empty(), upper) || !self.queue.is_empty()
        {
            self.drain();
        }
    }

    pub(crate) fn subtype_many(&mut self, constraints: impl IntoIterator<Item = (PosId, NegId)>) {
        let mut item_count = 0usize;
        let mut queued = false;
        for (lower, upper) in constraints {
            item_count += 1;
            queued |= self.enqueue_subtype(lower, ConstraintWeights::empty(), upper);
        }
        self.timing.record_subtype_many_call(item_count);
        if queued || !self.queue.is_empty() {
            self.drain();
        }
    }

    pub fn weighted_subtype(&mut self, lower: PosId, weights: ConstraintWeights, upper: NegId) {
        self.timing.record_weighted_subtype_call();
        if self.enqueue_subtype(lower, weights, upper) || !self.queue.is_empty() {
            self.drain();
        }
    }

    pub(crate) fn constrain_subtype(&mut self, lower: PosId, upper: NegId) -> bool {
        self.timing.record_constrain_subtype_call();
        let seen_len = self.seen.len();
        if self.enqueue_subtype(lower, ConstraintWeights::empty(), upper) || !self.queue.is_empty()
        {
            self.drain();
        }
        self.seen.len() != seen_len
    }

    pub(crate) fn constrain_invariant_neu(&mut self, lower: NeuId, upper: NeuId) -> bool {
        self.constrain_invariant_neus([(lower, upper)])
    }

    pub(crate) fn constrain_invariant_neus(
        &mut self,
        pairs: impl IntoIterator<Item = (NeuId, NeuId)>,
    ) -> bool {
        let seen_len = self.seen.len();
        for (lower, upper) in pairs {
            self.timing.record_constrain_invariant_neu_call();
            self.enqueue_invariant_neu(lower, upper, ConstraintWeights::empty());
        }
        if !self.queue.is_empty() {
            self.drain();
        }
        self.seen.len() != seen_len
    }

    pub(crate) fn constrain_var_var_pairs_direct(
        &mut self,
        pairs: impl IntoIterator<Item = (TypeVar, TypeVar)>,
    ) -> bool {
        let mut pair_count = 0usize;
        let seen_len = self.seen.len();
        let mut queued = false;
        for (lower, upper) in pairs {
            pair_count += 1;
            if lower == upper {
                continue;
            }
            let lower_pos = self.alloc_pos(Pos::Var(lower));
            let upper_neg = self.alloc_neg(Neg::Var(upper));
            queued |= self.enqueue_subtype(lower_pos, ConstraintWeights::empty(), upper_neg);
        }
        self.timing.record_constrain_var_var_direct_call(pair_count);
        if queued || !self.queue.is_empty() {
            self.drain();
        }
        self.seen.len() != seen_len
    }

    pub(crate) fn constrain_pos_to_var_direct_many(
        &mut self,
        bounds: impl IntoIterator<Item = (PosId, TypeVar)>,
    ) {
        for (lower, target) in bounds {
            self.timing.record_constrain_pos_var_direct_call();
            self.add_lower_bound(target, lower, ConstraintWeights::empty());
        }
        if !self.queue.is_empty() {
            self.drain();
        }
    }

    pub fn subtract_fact(
        &mut self,
        effect: TypeVar,
        id: SubtractId,
        subtractability: Subtractability,
    ) {
        self.timing.record_subtract_fact_call();
        self.observe_type_var(effect);
        self.queue
            .push_back(ConstraintWork::SubtractFact(QueuedSubtractFact {
                effect,
                fact: SubtractFact {
                    id,
                    subtractability,
                },
            }));
        self.drain();
    }

    /// 注釈・データ宣言が直接導入した subtract fact。scheme 量化はこの宣言由来 id
    /// だけを保持対象とし、instantiate の clone で再登録される fact（推論残差）は
    /// 量化境界で表示から消える。
    pub fn declared_subtract_fact(
        &mut self,
        effect: TypeVar,
        id: SubtractId,
        subtractability: Subtractability,
    ) {
        if self.declared_subtracts.insert(id) {
            self.bump_epoch();
        }
        self.subtract_fact(effect, id, subtractability);
    }

    pub fn subtract_declared(&self, id: SubtractId) -> bool {
        self.declared_subtracts.contains(&id)
    }

    pub fn register_effect_family_path(&mut self, path: Vec<String>) {
        self.effect_family_paths.insert(path);
    }

    pub(crate) fn pre_pop_effect_families(&self, var: TypeVar) -> &[ConstraintEffectFamily] {
        #[cfg(test)]
        crate::analysis::record_owner_pre_pop_read(var);
        self.pre_pop_effect_families
            .get(&var)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub fn drain(&mut self) {
        let start = Instant::now();
        let initial_queue = self.queue.len();
        let mut work_items = 0usize;
        let mut subtype_work_items = 0usize;
        let mut subtract_work_items = 0usize;
        let mut trace = ConstraintDrainTrace::from_env(self);
        while let Some(work) = self.queue.pop_front() {
            trace.work(&work, self);
            work_items += 1;
            match &work {
                ConstraintWork::Subtype(_) => subtype_work_items += 1,
                ConstraintWork::SubtractFact(_) => subtract_work_items += 1,
            }
            self.step(work);
        }
        trace.finish(self);
        self.timing.record_drain(
            start.elapsed(),
            initial_queue,
            work_items,
            subtype_work_items,
            subtract_work_items,
        );
    }

    pub(in crate::constraints) fn enqueue_subtype(
        &mut self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
    ) -> bool {
        matches!(
            self.enqueue_subtype_classified(lower, weights, upper),
            EnqueueSubtypeResult::Enqueued
        )
    }

    pub(in crate::constraints) fn enqueue_subtype_classified(
        &mut self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
    ) -> EnqueueSubtypeResult {
        let Some(constraint) = self.canonical_subtype_constraint(lower, weights, upper) else {
            return EnqueueSubtypeResult::Trivial;
        };
        if self.enqueue_canonical_subtype(constraint) {
            EnqueueSubtypeResult::Enqueued
        } else {
            EnqueueSubtypeResult::Duplicate
        }
    }

    pub(in crate::constraints) fn canonical_subtype_constraint(
        &self,
        lower: PosId,
        weights: ConstraintWeights,
        upper: NegId,
    ) -> Option<SubtypeConstraint> {
        if matches!(self.types.pos(lower), Pos::Bot) || matches!(self.types.neg(upper), Neg::Top) {
            return None;
        }
        if matches!(
            (self.types.pos(lower), self.types.neg(upper)),
            (Pos::Var(lower), Neg::Var(upper)) if lower == upper
        ) {
            return None;
        }
        let weights = self.terminal_subtype_weights(lower, upper, weights);
        let weights = if self.is_var_var_replay(lower, upper) {
            weights.normalize_for_var_var_replay_key()
        } else {
            weights
        };
        Some(SubtypeConstraint {
            lower,
            upper,
            weights,
        })
    }

    pub(in crate::constraints) fn enqueue_canonical_subtype(
        &mut self,
        constraint: SubtypeConstraint,
    ) -> bool {
        if self.seen.insert(constraint.clone()) {
            self.observe_routing_shadow(&constraint);
            self.queue.push_back(ConstraintWork::Subtype(constraint));
            true
        } else {
            false
        }
    }

    fn observe_routing_shadow(&mut self, constraint: &SubtypeConstraint) {
        let Some(shadow) = &self.replay_routing_shadow else {
            return;
        };
        let (Pos::Var(source), Neg::Var(target)) = (
            self.types.pos(constraint.lower),
            self.types.neg(constraint.upper),
        ) else {
            return;
        };
        shadow
            .borrow_mut()
            .observe_var_var_edge(*source, *target, &constraint.weights);
    }

    pub(in crate::constraints) fn terminal_subtype_weights(
        &self,
        lower: PosId,
        upper: NegId,
        weights: ConstraintWeights,
    ) -> ConstraintWeights {
        // Terminal subtype checks do not forward weights into child constraints.
        // Canonicalizing them here keeps the queue/seen set finite without
        // changing bounds or row-subtraction state.
        if self.has_terminal_subtype_endpoint(lower, upper) {
            ConstraintWeights::empty()
        } else {
            weights
        }
    }

    pub(in crate::constraints) fn has_terminal_subtype_endpoint(
        &self,
        lower: PosId,
        upper: NegId,
    ) -> bool {
        match (self.types.pos(lower), self.types.neg(upper)) {
            (Pos::Bot, _) | (_, Neg::Top) => true,
            (Pos::Con(path, args), _) if self.is_non_effect_terminal_con(path, args) => true,
            (_, Neg::Con(path, args)) if self.is_non_effect_terminal_con(path, args) => true,
            _ => false,
        }
    }

    pub(in crate::constraints) fn is_non_effect_terminal_con(
        &self,
        path: &[String],
        args: &[NeuId],
    ) -> bool {
        args.is_empty() && !self.effect_family_paths.contains(path)
    }

    pub(in crate::constraints) fn step(&mut self, work: ConstraintWork) {
        match work {
            ConstraintWork::Subtype(constraint) => self.step_subtype(constraint),
            ConstraintWork::SubtractFact(fact) => {
                self.record_subtract_fact(fact.effect, fact.fact);
            }
        }
    }

    pub(in crate::constraints) fn record_subtract_fact(
        &mut self,
        effect: TypeVar,
        fact: SubtractFact,
    ) {
        let id = fact.id;
        if self.subtracts.record(effect, fact) {
            self.bump_epoch();
            if self.method_role_mutations.is_active() {
                self.method_role_mutations
                    .record(DependencyKey::ConstraintSubtractFacts(effect));
            }
            self.events
                .push(ConstraintEvent::SubtractFactAdded { effect, id });
        }
    }

    pub(in crate::constraints) fn record_pre_pop_effect_families(
        &mut self,
        target: TypeVar,
        weight: &StackWeight,
    ) {
        let families = self.pre_pop_effect_families.entry(target).or_default();
        let mut changed = false;
        for family in weight
            .active_stack_items()
            .flat_map(subtractability_families)
        {
            let family = ConstraintEffectFamily {
                path: family.path,
                args: family.args,
            };
            if !families.contains(&family) {
                families.push(family);
                changed = true;
            }
        }
        if changed {
            self.bump_epoch();
            if self.method_role_mutations.is_active() {
                self.method_role_mutations
                    .record(DependencyKey::ConstraintPrePopFamilies(target));
            }
        }
    }

    pub(in crate::constraints) fn bump_epoch(&mut self) -> ConstraintEpoch {
        self.epoch.bump();
        self.epoch
    }

    pub(in crate::constraints) fn fresh_internal_type_var_at(
        &mut self,
        level: TypeLevel,
    ) -> TypeVar {
        let var = TypeVar(self.next_internal_type_var);
        self.next_internal_type_var = self.next_internal_type_var.saturating_add(1);
        self.register_type_var(var, level);
        var
    }

    pub(in crate::constraints) fn observe_type_var(&mut self, var: TypeVar) {
        self.next_internal_type_var = self.next_internal_type_var.max(var.0.saturating_add(1));
    }

    pub(in crate::constraints) fn observe_pos(&mut self, pos: &Pos) {
        match pos {
            Pos::Bot => {}
            Pos::Var(var) => self.observe_type_var(*var),
            Pos::Con(_, args) => {
                for arg in args {
                    self.observe_neu_id(*arg);
                }
            }
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.observe_neg_id(*arg);
                self.observe_neg_id(*arg_eff);
                self.observe_pos_id(*ret_eff);
                self.observe_pos_id(*ret);
            }
            Pos::Record(fields) => {
                for field in fields {
                    self.observe_pos_id(field.value);
                }
            }
            Pos::RecordTailSpread { fields, tail } => {
                for field in fields {
                    self.observe_pos_id(field.value);
                }
                self.observe_pos_id(*tail);
            }
            Pos::RecordHeadSpread { tail, fields } => {
                self.observe_pos_id(*tail);
                for field in fields {
                    self.observe_pos_id(field.value);
                }
            }
            Pos::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.observe_pos_id(*payload);
                    }
                }
            }
            Pos::Tuple(items) | Pos::Row(items) => {
                for item in items {
                    self.observe_pos_id(*item);
                }
            }
            Pos::Stack { inner, .. } | Pos::NonSubtract(inner, _) => {
                self.observe_pos_id(*inner);
            }
            Pos::Union(left, right) => {
                self.observe_pos_id(*left);
                self.observe_pos_id(*right);
            }
        }
    }

    pub(in crate::constraints) fn observe_neg(&mut self, neg: &Neg) {
        match neg {
            Neg::Top | Neg::Bot => {}
            Neg::Var(var) => self.observe_type_var(*var),
            Neg::Con(_, args) => {
                for arg in args {
                    self.observe_neu_id(*arg);
                }
            }
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.observe_pos_id(*arg);
                self.observe_pos_id(*arg_eff);
                self.observe_neg_id(*ret_eff);
                self.observe_neg_id(*ret);
            }
            Neg::Record(fields) => {
                for field in fields {
                    self.observe_neg_id(field.value);
                }
            }
            Neg::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.observe_neg_id(*payload);
                    }
                }
            }
            Neg::Tuple(items) => {
                for item in items {
                    self.observe_neg_id(*item);
                }
            }
            Neg::Row(items, tail) => {
                for item in items {
                    self.observe_neg_id(*item);
                }
                self.observe_row_tail(*tail);
            }
            Neg::Stack { inner, .. } => self.observe_neg_id(*inner),
            Neg::Intersection(left, right) => {
                self.observe_neg_id(*left);
                self.observe_neg_id(*right);
            }
        }
    }

    pub(in crate::constraints) fn observe_neu(&mut self, neu: &Neu) {
        match neu {
            Neu::Bounds(lower, upper) => {
                self.observe_pos_id(*lower);
                self.observe_neg_id(*upper);
            }
            Neu::Con(_, args) => {
                for arg in args {
                    self.observe_neu_id(*arg);
                }
            }
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.observe_neu_id(*arg);
                self.observe_neu_id(*arg_eff);
                self.observe_neu_id(*ret_eff);
                self.observe_neu_id(*ret);
            }
            Neu::Record(fields) => {
                for field in fields {
                    self.observe_neu_id(field.value);
                }
            }
            Neu::PolyVariant(items) => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.observe_neu_id(*payload);
                    }
                }
            }
            Neu::Tuple(items) => {
                for item in items {
                    self.observe_neu_id(*item);
                }
            }
        }
    }

    pub(in crate::constraints) fn observe_pos_id(&mut self, id: PosId) {
        let pos = self.types.pos(id).clone();
        self.observe_pos(&pos);
    }

    pub(in crate::constraints) fn observe_neg_id(&mut self, id: NegId) {
        let neg = self.types.neg(id).clone();
        self.observe_neg(&neg);
    }

    pub(in crate::constraints) fn observe_neu_id(&mut self, id: NeuId) {
        let neu = self.types.neu(id).clone();
        self.observe_neu(&neu);
    }

    fn observe_row_tail(&mut self, tail: NegId) {
        let neg = self.types.neg(tail).clone();
        if let Neg::Var(var) = &neg {
            self.row_tail_vars.insert(*var);
        }
        self.observe_neg(&neg);
    }
}
