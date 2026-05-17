//! Diagnostic counters for runtime type projection fallbacks.
//!
//! A projection fallback means a monomorphize refresh/rewrite pass could
//! not derive an expression's runtime type from its rewritten children and
//! kept the pre-existing `Expr.ty` instead.  Keeping the old type is
//! sometimes harmless for leaves, but at structured nodes it can hide stale
//! `Unknown` / fallback slots.  Enable reporting with
//! `YULANG_REPORT_TYPE_PROJECTION_FALLBACKS=1`.

use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum TypeProjectionFallbackReason {
    IfBranchMismatch,
    MatchNoArms,
    ApplyCalleeNotFunction,
    ApplyProjectedUnknown,
    BindHereNotThunk,
    BindHereProjectedUnknown,
    LambdaProjectedUnknown,
    LambdaProjectedUnit,
}

static IF_BRANCH_MISMATCH: AtomicU64 = AtomicU64::new(0);
static MATCH_NO_ARMS: AtomicU64 = AtomicU64::new(0);
static APPLY_CALLEE_NOT_FUNCTION: AtomicU64 = AtomicU64::new(0);
static APPLY_PROJECTED_UNKNOWN: AtomicU64 = AtomicU64::new(0);
static BIND_HERE_NOT_THUNK: AtomicU64 = AtomicU64::new(0);
static BIND_HERE_PROJECTED_UNKNOWN: AtomicU64 = AtomicU64::new(0);
static LAMBDA_PROJECTED_UNKNOWN: AtomicU64 = AtomicU64::new(0);
static LAMBDA_PROJECTED_UNIT: AtomicU64 = AtomicU64::new(0);
static ENABLED: OnceLock<bool> = OnceLock::new();

pub(super) fn record(reason: TypeProjectionFallbackReason) {
    if !enabled() {
        return;
    }
    counter(reason).fetch_add(1, Ordering::Relaxed);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypeProjectionFallbackCounts {
    pub if_branch_mismatch: u64,
    pub match_no_arms: u64,
    pub apply_callee_not_function: u64,
    pub apply_projected_unknown: u64,
    pub bind_here_not_thunk: u64,
    pub bind_here_projected_unknown: u64,
    pub lambda_projected_unknown: u64,
    pub lambda_projected_unit: u64,
}

impl TypeProjectionFallbackCounts {
    pub fn total(self) -> u64 {
        self.if_branch_mismatch
            + self.match_no_arms
            + self.apply_callee_not_function
            + self.apply_projected_unknown
            + self.bind_here_not_thunk
            + self.bind_here_projected_unknown
            + self.lambda_projected_unknown
            + self.lambda_projected_unit
    }
}

pub fn snapshot() -> TypeProjectionFallbackCounts {
    TypeProjectionFallbackCounts {
        if_branch_mismatch: IF_BRANCH_MISMATCH.load(Ordering::Relaxed),
        match_no_arms: MATCH_NO_ARMS.load(Ordering::Relaxed),
        apply_callee_not_function: APPLY_CALLEE_NOT_FUNCTION.load(Ordering::Relaxed),
        apply_projected_unknown: APPLY_PROJECTED_UNKNOWN.load(Ordering::Relaxed),
        bind_here_not_thunk: BIND_HERE_NOT_THUNK.load(Ordering::Relaxed),
        bind_here_projected_unknown: BIND_HERE_PROJECTED_UNKNOWN.load(Ordering::Relaxed),
        lambda_projected_unknown: LAMBDA_PROJECTED_UNKNOWN.load(Ordering::Relaxed),
        lambda_projected_unit: LAMBDA_PROJECTED_UNIT.load(Ordering::Relaxed),
    }
}

pub fn reset() {
    IF_BRANCH_MISMATCH.store(0, Ordering::Relaxed);
    MATCH_NO_ARMS.store(0, Ordering::Relaxed);
    APPLY_CALLEE_NOT_FUNCTION.store(0, Ordering::Relaxed);
    APPLY_PROJECTED_UNKNOWN.store(0, Ordering::Relaxed);
    BIND_HERE_NOT_THUNK.store(0, Ordering::Relaxed);
    BIND_HERE_PROJECTED_UNKNOWN.store(0, Ordering::Relaxed);
    LAMBDA_PROJECTED_UNKNOWN.store(0, Ordering::Relaxed);
    LAMBDA_PROJECTED_UNIT.store(0, Ordering::Relaxed);
}

pub fn report_if_requested(label: &str) {
    if !enabled() {
        return;
    }
    let counts = snapshot();
    eprintln!(
        "[type-projection-fallback] {label}: total={} if_branch_mismatch={} match_no_arms={} apply_callee_not_function={} apply_projected_unknown={} bind_here_not_thunk={} bind_here_projected_unknown={} lambda_projected_unknown={} lambda_projected_unit={}",
        counts.total(),
        counts.if_branch_mismatch,
        counts.match_no_arms,
        counts.apply_callee_not_function,
        counts.apply_projected_unknown,
        counts.bind_here_not_thunk,
        counts.bind_here_projected_unknown,
        counts.lambda_projected_unknown,
        counts.lambda_projected_unit,
    );
}

fn enabled() -> bool {
    *ENABLED.get_or_init(|| std::env::var_os("YULANG_REPORT_TYPE_PROJECTION_FALLBACKS").is_some())
}

fn counter(reason: TypeProjectionFallbackReason) -> &'static AtomicU64 {
    match reason {
        TypeProjectionFallbackReason::IfBranchMismatch => &IF_BRANCH_MISMATCH,
        TypeProjectionFallbackReason::MatchNoArms => &MATCH_NO_ARMS,
        TypeProjectionFallbackReason::ApplyCalleeNotFunction => &APPLY_CALLEE_NOT_FUNCTION,
        TypeProjectionFallbackReason::ApplyProjectedUnknown => &APPLY_PROJECTED_UNKNOWN,
        TypeProjectionFallbackReason::BindHereNotThunk => &BIND_HERE_NOT_THUNK,
        TypeProjectionFallbackReason::BindHereProjectedUnknown => &BIND_HERE_PROJECTED_UNKNOWN,
        TypeProjectionFallbackReason::LambdaProjectedUnknown => &LAMBDA_PROJECTED_UNKNOWN,
        TypeProjectionFallbackReason::LambdaProjectedUnit => &LAMBDA_PROJECTED_UNIT,
    }
}
