//! Diagnostic counters for `DemandEffect::Hole(_) -> DemandEffect::Empty`
//! collapses. Three sites can fire today:
//!
//! - `close_default_effect` in associated.rs (final post-monomorphize
//!   sweep that closes any unresolved hole as `Empty`).
//! - `DemandUnifier::row` in solve.rs, two branches: leftover expected
//!   holes after row matching, and leftover actual holes.
//!
//! Counters are process-global `AtomicU64` and `Relaxed` (the diagnostic
//! does not need ordering guarantees). Enable runtime reporting with
//! `YULANG_REPORT_EFFECT_HOLE_COLLAPSES=1`; the snapshot is printed via
//! [`report_if_requested`]. Reset between runs with [`reset`].

use std::sync::atomic::{AtomicU64, Ordering};

static CLOSE_DEFAULT: AtomicU64 = AtomicU64::new(0);
static UNIFIER_EXPECTED: AtomicU64 = AtomicU64::new(0);
static UNIFIER_ACTUAL: AtomicU64 = AtomicU64::new(0);

pub(crate) fn record_close_default_collapse() {
    CLOSE_DEFAULT.fetch_add(1, Ordering::Relaxed);
}

pub(crate) fn record_unifier_expected_collapse() {
    UNIFIER_EXPECTED.fetch_add(1, Ordering::Relaxed);
}

pub(crate) fn record_unifier_actual_collapse() {
    UNIFIER_ACTUAL.fetch_add(1, Ordering::Relaxed);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EffectHoleCollapseCounts {
    pub close_default: u64,
    pub unifier_expected: u64,
    pub unifier_actual: u64,
}

impl EffectHoleCollapseCounts {
    pub fn total(self) -> u64 {
        self.close_default + self.unifier_expected + self.unifier_actual
    }
}

pub fn snapshot() -> EffectHoleCollapseCounts {
    EffectHoleCollapseCounts {
        close_default: CLOSE_DEFAULT.load(Ordering::Relaxed),
        unifier_expected: UNIFIER_EXPECTED.load(Ordering::Relaxed),
        unifier_actual: UNIFIER_ACTUAL.load(Ordering::Relaxed),
    }
}

pub fn reset() {
    CLOSE_DEFAULT.store(0, Ordering::Relaxed);
    UNIFIER_EXPECTED.store(0, Ordering::Relaxed);
    UNIFIER_ACTUAL.store(0, Ordering::Relaxed);
}

pub fn report_if_requested(label: &str) {
    if std::env::var_os("YULANG_REPORT_EFFECT_HOLE_COLLAPSES").is_none() {
        return;
    }
    let counts = snapshot();
    eprintln!(
        "[effect-hole] {label}: total={} close_default={} unifier_expected={} unifier_actual={}",
        counts.total(),
        counts.close_default,
        counts.unifier_expected,
        counts.unifier_actual,
    );
}

/// Returns true when the user has opted in to treating any
/// `DemandEffect::Hole(_) -> DemandEffect::Empty` collapse as a hard
/// failure (set `YULANG_STRICT_EFFECT_HOLE_COLLAPSE=1`). Default off so
/// existing programs are unaffected; tests can flip the flag to
/// surface unresolved effect holes.
pub fn strict_collapse_enabled() -> bool {
    use std::sync::atomic::{AtomicU8, Ordering};
    static STATE: AtomicU8 = AtomicU8::new(0); // 0 = uninit, 1 = off, 2 = on
    match STATE.load(Ordering::Relaxed) {
        2 => true,
        1 => false,
        _ => {
            let on = std::env::var_os("YULANG_STRICT_EFFECT_HOLE_COLLAPSE").is_some();
            STATE.store(if on { 2 } else { 1 }, Ordering::Relaxed);
            on
        }
    }
}
