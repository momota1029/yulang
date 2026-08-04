//! Test census for the M1 synthetic-act template boundary.
//!
//! M1-0 records the legacy route before typed templates exist. Later slices can record template
//! eligibility and fallback in the same matrix without changing the measurement contract.

pub(super) use crate::module_table::typed_act_catalog::SyntheticActCopyKind;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ActTemplateCatalogSource {
    Prefix,
    Embedded,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(
    dead_code,
    reason = "M1-0 fixes the outcome matrix before M1-1 can produce template outcomes"
)]
pub(super) enum ActTemplateAttemptOutcome {
    NotAttempted,
    Eligible,
    Miss,
    Fallback,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct SyntheticActCopyCensusCell {
    pub not_attempted: usize,
    pub eligible: usize,
    pub miss: usize,
    pub fallback: usize,
    pub legacy_cst_lowerings: usize,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct SyntheticActCopyCensusSnapshot {
    cells: [[SyntheticActCopyCensusCell; 2]; 2],
}

#[cfg(test)]
impl SyntheticActCopyCensusSnapshot {
    pub fn cell(
        self,
        kind: SyntheticActCopyKind,
        source: ActTemplateCatalogSource,
    ) -> SyntheticActCopyCensusCell {
        self.cells[kind_index(kind)][source_index(source)]
    }
}

#[cfg(test)]
std::thread_local! {
    static TEST_CAPTURE: std::cell::RefCell<Option<SyntheticActCopyCensusSnapshot>> =
        const { std::cell::RefCell::new(None) };
}

#[inline]
pub(super) fn record_act_template_attempt(
    kind: SyntheticActCopyKind,
    source: ActTemplateCatalogSource,
    outcome: ActTemplateAttemptOutcome,
) {
    #[cfg(test)]
    update_capture(|snapshot| {
        let cell = &mut snapshot.cells[kind_index(kind)][source_index(source)];
        match outcome {
            ActTemplateAttemptOutcome::NotAttempted => cell.not_attempted += 1,
            ActTemplateAttemptOutcome::Eligible => cell.eligible += 1,
            ActTemplateAttemptOutcome::Miss => cell.miss += 1,
            ActTemplateAttemptOutcome::Fallback => cell.fallback += 1,
        }
    });
    #[cfg(not(test))]
    let _ = (kind, source, outcome);
}

#[inline]
pub(super) fn record_legacy_act_copy_lowering(
    kind: SyntheticActCopyKind,
    source: ActTemplateCatalogSource,
) {
    #[cfg(test)]
    update_capture(|snapshot| {
        snapshot.cells[kind_index(kind)][source_index(source)].legacy_cst_lowerings += 1;
    });
    #[cfg(not(test))]
    let _ = (kind, source);
}

#[cfg(test)]
pub(super) fn capture_synthetic_act_copy_census<T>(
    run: impl FnOnce() -> T,
) -> (T, SyntheticActCopyCensusSnapshot) {
    TEST_CAPTURE.with(|capture| {
        assert!(
            capture.borrow().is_none(),
            "nested synthetic-act-copy census capture"
        );
        *capture.borrow_mut() = Some(SyntheticActCopyCensusSnapshot::default());
    });
    let output = run();
    let snapshot = TEST_CAPTURE.with(|capture| {
        capture
            .borrow_mut()
            .take()
            .expect("synthetic-act-copy census capture must remain installed")
    });
    (output, snapshot)
}

#[cfg(test)]
fn update_capture(update: impl FnOnce(&mut SyntheticActCopyCensusSnapshot)) {
    TEST_CAPTURE.with(|capture| {
        if let Some(snapshot) = capture.borrow_mut().as_mut() {
            update(snapshot);
        }
    });
}

#[cfg(test)]
const fn kind_index(kind: SyntheticActCopyKind) -> usize {
    match kind {
        SyntheticActCopyKind::Var => 0,
        SyntheticActCopyKind::LabelSub => 1,
    }
}

#[cfg(test)]
const fn source_index(source: ActTemplateCatalogSource) -> usize {
    match source {
        ActTemplateCatalogSource::Prefix => 0,
        ActTemplateCatalogSource::Embedded => 1,
    }
}
