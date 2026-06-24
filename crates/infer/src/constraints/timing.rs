//! Aggregate timing counters for the subtype constraint machine.
//!
//! The machine owns propagation semantics; this module only records how work
//! enters and drains through that machine so performance probes do not obscure
//! the main constraint data structures.

use crate::time::Duration;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ConstraintTiming {
    pub drain: Duration,
    pub type_var_count: usize,
    pub row_tail_var_count: usize,
    pub pos_node_count: usize,
    pub neg_node_count: usize,
    pub neu_node_count: usize,
    pub type_node_count: usize,
    pub drains: usize,
    pub empty_drains: usize,
    pub initial_queue_items: usize,
    pub work_items: usize,
    pub subtype_work_items: usize,
    pub subtract_work_items: usize,
    pub max_initial_queue: usize,
    pub max_work_items: usize,
    pub subtype_calls: usize,
    pub subtype_many_calls: usize,
    pub subtype_many_items: usize,
    pub weighted_subtype_calls: usize,
    pub constrain_subtype_calls: usize,
    pub constrain_invariant_neu_calls: usize,
    pub constrain_var_var_direct_calls: usize,
    pub constrain_var_var_direct_pairs: usize,
    pub constrain_pos_var_direct_calls: usize,
    pub subtract_fact_calls: usize,
    pub lower_bounds_added: usize,
    pub upper_bounds_added: usize,
    pub lower_replay_inputs: usize,
    pub upper_replay_inputs: usize,
    pub lower_replay_enqueued: usize,
    pub upper_replay_enqueued: usize,
    pub lower_replay_var_var: usize,
    pub upper_replay_var_var: usize,
    pub lower_replay_accepted: usize,
    pub upper_replay_accepted: usize,
    pub lower_replay_duplicate: usize,
    pub upper_replay_duplicate: usize,
    pub lower_replay_trivial: usize,
    pub upper_replay_trivial: usize,
    pub max_lower_replay_inputs: usize,
    pub max_upper_replay_inputs: usize,
    pub max_lower_replay_enqueued: usize,
    pub max_upper_replay_enqueued: usize,
    pub max_lower_replay_var_var: usize,
    pub max_upper_replay_var_var: usize,
    pub max_lower_replay_accepted: usize,
    pub max_upper_replay_accepted: usize,
    pub max_lower_replay_duplicate: usize,
    pub max_upper_replay_duplicate: usize,
    pub max_lower_replay_trivial: usize,
    pub max_upper_replay_trivial: usize,
}

impl ConstraintTiming {
    pub(super) fn record_subtype_call(&mut self) {
        self.subtype_calls += 1;
    }

    pub(super) fn record_subtype_many_call(&mut self, item_count: usize) {
        self.subtype_many_calls += 1;
        self.subtype_many_items += item_count;
    }

    pub(super) fn record_weighted_subtype_call(&mut self) {
        self.weighted_subtype_calls += 1;
    }

    pub(super) fn record_constrain_subtype_call(&mut self) {
        self.constrain_subtype_calls += 1;
    }

    pub(super) fn record_constrain_invariant_neu_call(&mut self) {
        self.constrain_invariant_neu_calls += 1;
    }

    pub(super) fn record_constrain_var_var_direct_call(&mut self, pair_count: usize) {
        self.constrain_var_var_direct_calls += 1;
        self.constrain_var_var_direct_pairs += pair_count;
    }

    pub(super) fn record_constrain_pos_var_direct_call(&mut self) {
        self.constrain_pos_var_direct_calls += 1;
    }

    pub(super) fn record_subtract_fact_call(&mut self) {
        self.subtract_fact_calls += 1;
    }

    pub(super) fn record_lower_bound_added(
        &mut self,
        replay_inputs: usize,
        replay_enqueued: usize,
        replay_var_var: usize,
        replay_accepted: usize,
        replay_duplicate: usize,
        replay_trivial: usize,
    ) {
        self.lower_bounds_added += 1;
        self.lower_replay_inputs += replay_inputs;
        self.lower_replay_enqueued += replay_enqueued;
        self.lower_replay_var_var += replay_var_var;
        self.lower_replay_accepted += replay_accepted;
        self.lower_replay_duplicate += replay_duplicate;
        self.lower_replay_trivial += replay_trivial;
        self.max_lower_replay_inputs = self.max_lower_replay_inputs.max(replay_inputs);
        self.max_lower_replay_enqueued = self.max_lower_replay_enqueued.max(replay_enqueued);
        self.max_lower_replay_var_var = self.max_lower_replay_var_var.max(replay_var_var);
        self.max_lower_replay_accepted = self.max_lower_replay_accepted.max(replay_accepted);
        self.max_lower_replay_duplicate = self.max_lower_replay_duplicate.max(replay_duplicate);
        self.max_lower_replay_trivial = self.max_lower_replay_trivial.max(replay_trivial);
    }

    pub(super) fn record_upper_bound_added(
        &mut self,
        replay_inputs: usize,
        replay_enqueued: usize,
        replay_var_var: usize,
        replay_accepted: usize,
        replay_duplicate: usize,
        replay_trivial: usize,
    ) {
        self.upper_bounds_added += 1;
        self.upper_replay_inputs += replay_inputs;
        self.upper_replay_enqueued += replay_enqueued;
        self.upper_replay_var_var += replay_var_var;
        self.upper_replay_accepted += replay_accepted;
        self.upper_replay_duplicate += replay_duplicate;
        self.upper_replay_trivial += replay_trivial;
        self.max_upper_replay_inputs = self.max_upper_replay_inputs.max(replay_inputs);
        self.max_upper_replay_enqueued = self.max_upper_replay_enqueued.max(replay_enqueued);
        self.max_upper_replay_var_var = self.max_upper_replay_var_var.max(replay_var_var);
        self.max_upper_replay_accepted = self.max_upper_replay_accepted.max(replay_accepted);
        self.max_upper_replay_duplicate = self.max_upper_replay_duplicate.max(replay_duplicate);
        self.max_upper_replay_trivial = self.max_upper_replay_trivial.max(replay_trivial);
    }

    pub(super) fn record_drain(
        &mut self,
        elapsed: Duration,
        initial_queue: usize,
        work_items: usize,
        subtype_work_items: usize,
        subtract_work_items: usize,
    ) {
        self.drain += elapsed;
        self.drains += 1;
        if work_items == 0 {
            self.empty_drains += 1;
        }
        self.initial_queue_items += initial_queue;
        self.work_items += work_items;
        self.subtype_work_items += subtype_work_items;
        self.subtract_work_items += subtract_work_items;
        self.max_initial_queue = self.max_initial_queue.max(initial_queue);
        self.max_work_items = self.max_work_items.max(work_items);
    }
}
