use rustc_hash::FxHashMap;

use crate::constraints::SourceBoundaryId;
use crate::SourceSpan;

/// Source-only locations for constraint boundaries whose semantic identity lives in `infer`.
///
/// This table is deliberately separate from constraint records: locations neither affect
/// semantic equality nor participate in derivation traversal.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct SourceBoundaryProvenanceTable {
    entries: FxHashMap<SourceBoundaryId, SourceBoundaryProvenance>,
}

impl SourceBoundaryProvenanceTable {
    pub(crate) fn insert_application_argument(
        &mut self,
        boundary: SourceBoundaryId,
        provenance: ApplicationArgumentBoundaryProvenance,
    ) -> bool {
        self.entries
            .insert(
                boundary,
                SourceBoundaryProvenance::ApplicationArgument(provenance),
            )
            .is_none()
    }

    pub(crate) fn application_argument(
        &self,
        boundary: SourceBoundaryId,
    ) -> Option<&ApplicationArgumentBoundaryProvenance> {
        match self.entries.get(&boundary)? {
            SourceBoundaryProvenance::ApplicationArgument(provenance) => Some(provenance),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SourceBoundaryProvenance {
    ApplicationArgument(ApplicationArgumentBoundaryProvenance),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ApplicationArgumentBoundaryProvenance {
    pub(crate) application_span: SourceSpan,
    pub(crate) callee_span: SourceSpan,
    pub(crate) argument_span: SourceSpan,
}
