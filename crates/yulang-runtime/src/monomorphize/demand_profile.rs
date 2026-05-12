use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct DemandEvidenceProfile {
    pub apply_arg_signature_calls: usize,
    pub expected_arg_hint_disabled: usize,
    pub expected_arg_hint_present: usize,
    pub expected_arg_hint_converted: usize,
    pub expected_arg_hint_used: usize,
    pub expected_arg_hint_changed_signature: usize,
    pub expected_arg_hint_same_signature: usize,
    pub expected_arg_hint_rejected_open: usize,
    pub apply_callee_signature_calls: usize,
    pub expected_callee_hint_disabled: usize,
    pub expected_callee_hint_present: usize,
    pub expected_callee_hint_converted: usize,
    pub expected_callee_hint_used: usize,
    pub expected_callee_hint_changed_param_signature: usize,
    pub expected_callee_hint_same_param_signature: usize,
    pub expected_callee_hint_rejected_open: usize,
    pub expected_callee_hint_rejected_non_function: usize,
}

pub(crate) fn reset_demand_evidence_profile() {
    DEMAND_EVIDENCE_PROFILE.reset();
}

pub(crate) fn snapshot_demand_evidence_profile() -> DemandEvidenceProfile {
    DEMAND_EVIDENCE_PROFILE.snapshot()
}

pub(super) struct DemandEvidenceProfileCounters {
    apply_arg_signature_calls: AtomicUsize,
    expected_arg_hint_disabled: AtomicUsize,
    expected_arg_hint_present: AtomicUsize,
    expected_arg_hint_converted: AtomicUsize,
    expected_arg_hint_used: AtomicUsize,
    expected_arg_hint_changed_signature: AtomicUsize,
    expected_arg_hint_same_signature: AtomicUsize,
    expected_arg_hint_rejected_open: AtomicUsize,
    apply_callee_signature_calls: AtomicUsize,
    expected_callee_hint_disabled: AtomicUsize,
    expected_callee_hint_present: AtomicUsize,
    expected_callee_hint_converted: AtomicUsize,
    expected_callee_hint_used: AtomicUsize,
    expected_callee_hint_changed_param_signature: AtomicUsize,
    expected_callee_hint_same_param_signature: AtomicUsize,
    expected_callee_hint_rejected_open: AtomicUsize,
    expected_callee_hint_rejected_non_function: AtomicUsize,
}

impl DemandEvidenceProfileCounters {
    pub(super) const fn new() -> Self {
        Self {
            apply_arg_signature_calls: AtomicUsize::new(0),
            expected_arg_hint_disabled: AtomicUsize::new(0),
            expected_arg_hint_present: AtomicUsize::new(0),
            expected_arg_hint_converted: AtomicUsize::new(0),
            expected_arg_hint_used: AtomicUsize::new(0),
            expected_arg_hint_changed_signature: AtomicUsize::new(0),
            expected_arg_hint_same_signature: AtomicUsize::new(0),
            expected_arg_hint_rejected_open: AtomicUsize::new(0),
            apply_callee_signature_calls: AtomicUsize::new(0),
            expected_callee_hint_disabled: AtomicUsize::new(0),
            expected_callee_hint_present: AtomicUsize::new(0),
            expected_callee_hint_converted: AtomicUsize::new(0),
            expected_callee_hint_used: AtomicUsize::new(0),
            expected_callee_hint_changed_param_signature: AtomicUsize::new(0),
            expected_callee_hint_same_param_signature: AtomicUsize::new(0),
            expected_callee_hint_rejected_open: AtomicUsize::new(0),
            expected_callee_hint_rejected_non_function: AtomicUsize::new(0),
        }
    }

    pub(super) fn reset(&self) {
        self.apply_arg_signature_calls.store(0, Ordering::Relaxed);
        self.expected_arg_hint_disabled.store(0, Ordering::Relaxed);
        self.expected_arg_hint_present.store(0, Ordering::Relaxed);
        self.expected_arg_hint_converted.store(0, Ordering::Relaxed);
        self.expected_arg_hint_used.store(0, Ordering::Relaxed);
        self.expected_arg_hint_changed_signature
            .store(0, Ordering::Relaxed);
        self.expected_arg_hint_same_signature
            .store(0, Ordering::Relaxed);
        self.expected_arg_hint_rejected_open
            .store(0, Ordering::Relaxed);
        self.apply_callee_signature_calls
            .store(0, Ordering::Relaxed);
        self.expected_callee_hint_disabled
            .store(0, Ordering::Relaxed);
        self.expected_callee_hint_present
            .store(0, Ordering::Relaxed);
        self.expected_callee_hint_converted
            .store(0, Ordering::Relaxed);
        self.expected_callee_hint_used.store(0, Ordering::Relaxed);
        self.expected_callee_hint_changed_param_signature
            .store(0, Ordering::Relaxed);
        self.expected_callee_hint_same_param_signature
            .store(0, Ordering::Relaxed);
        self.expected_callee_hint_rejected_open
            .store(0, Ordering::Relaxed);
        self.expected_callee_hint_rejected_non_function
            .store(0, Ordering::Relaxed);
    }

    pub(super) fn snapshot(&self) -> DemandEvidenceProfile {
        DemandEvidenceProfile {
            apply_arg_signature_calls: self.apply_arg_signature_calls.load(Ordering::Relaxed),
            expected_arg_hint_disabled: self.expected_arg_hint_disabled.load(Ordering::Relaxed),
            expected_arg_hint_present: self.expected_arg_hint_present.load(Ordering::Relaxed),
            expected_arg_hint_converted: self.expected_arg_hint_converted.load(Ordering::Relaxed),
            expected_arg_hint_used: self.expected_arg_hint_used.load(Ordering::Relaxed),
            expected_arg_hint_changed_signature: self
                .expected_arg_hint_changed_signature
                .load(Ordering::Relaxed),
            expected_arg_hint_same_signature: self
                .expected_arg_hint_same_signature
                .load(Ordering::Relaxed),
            expected_arg_hint_rejected_open: self
                .expected_arg_hint_rejected_open
                .load(Ordering::Relaxed),
            apply_callee_signature_calls: self.apply_callee_signature_calls.load(Ordering::Relaxed),
            expected_callee_hint_disabled: self
                .expected_callee_hint_disabled
                .load(Ordering::Relaxed),
            expected_callee_hint_present: self.expected_callee_hint_present.load(Ordering::Relaxed),
            expected_callee_hint_converted: self
                .expected_callee_hint_converted
                .load(Ordering::Relaxed),
            expected_callee_hint_used: self.expected_callee_hint_used.load(Ordering::Relaxed),
            expected_callee_hint_changed_param_signature: self
                .expected_callee_hint_changed_param_signature
                .load(Ordering::Relaxed),
            expected_callee_hint_same_param_signature: self
                .expected_callee_hint_same_param_signature
                .load(Ordering::Relaxed),
            expected_callee_hint_rejected_open: self
                .expected_callee_hint_rejected_open
                .load(Ordering::Relaxed),
            expected_callee_hint_rejected_non_function: self
                .expected_callee_hint_rejected_non_function
                .load(Ordering::Relaxed),
        }
    }

    pub(super) fn fetch_add_apply_arg_signature_calls(&self) {
        self.apply_arg_signature_calls
            .fetch_add(1, Ordering::Relaxed);
    }
    pub(super) fn fetch_add_expected_arg_hint_disabled(&self) {
        self.expected_arg_hint_disabled
            .fetch_add(1, Ordering::Relaxed);
    }
    pub(super) fn fetch_add_expected_arg_hint_present(&self) {
        self.expected_arg_hint_present
            .fetch_add(1, Ordering::Relaxed);
    }
    pub(super) fn fetch_add_expected_arg_hint_converted(&self) {
        self.expected_arg_hint_converted
            .fetch_add(1, Ordering::Relaxed);
    }
    pub(super) fn fetch_add_expected_arg_hint_used(&self) {
        self.expected_arg_hint_used.fetch_add(1, Ordering::Relaxed);
    }
    pub(super) fn fetch_add_expected_arg_hint_changed_signature(&self) {
        self.expected_arg_hint_changed_signature
            .fetch_add(1, Ordering::Relaxed);
    }
    pub(super) fn fetch_add_expected_arg_hint_same_signature(&self) {
        self.expected_arg_hint_same_signature
            .fetch_add(1, Ordering::Relaxed);
    }
    pub(super) fn fetch_add_expected_arg_hint_rejected_open(&self) {
        self.expected_arg_hint_rejected_open
            .fetch_add(1, Ordering::Relaxed);
    }
    pub(super) fn fetch_add_apply_callee_signature_calls(&self) {
        self.apply_callee_signature_calls
            .fetch_add(1, Ordering::Relaxed);
    }
    pub(super) fn fetch_add_expected_callee_hint_disabled(&self) {
        self.expected_callee_hint_disabled
            .fetch_add(1, Ordering::Relaxed);
    }
    pub(super) fn fetch_add_expected_callee_hint_present(&self) {
        self.expected_callee_hint_present
            .fetch_add(1, Ordering::Relaxed);
    }
    pub(super) fn fetch_add_expected_callee_hint_converted(&self) {
        self.expected_callee_hint_converted
            .fetch_add(1, Ordering::Relaxed);
    }
    pub(super) fn fetch_add_expected_callee_hint_used(&self) {
        self.expected_callee_hint_used
            .fetch_add(1, Ordering::Relaxed);
    }
    pub(super) fn fetch_add_expected_callee_hint_changed_param_signature(&self) {
        self.expected_callee_hint_changed_param_signature
            .fetch_add(1, Ordering::Relaxed);
    }
    pub(super) fn fetch_add_expected_callee_hint_same_param_signature(&self) {
        self.expected_callee_hint_same_param_signature
            .fetch_add(1, Ordering::Relaxed);
    }
    pub(super) fn fetch_add_expected_callee_hint_rejected_open(&self) {
        self.expected_callee_hint_rejected_open
            .fetch_add(1, Ordering::Relaxed);
    }
    pub(super) fn fetch_add_expected_callee_hint_rejected_non_function(&self) {
        self.expected_callee_hint_rejected_non_function
            .fetch_add(1, Ordering::Relaxed);
    }
}

pub(super) static DEMAND_EVIDENCE_PROFILE: DemandEvidenceProfileCounters =
    DemandEvidenceProfileCounters::new();
