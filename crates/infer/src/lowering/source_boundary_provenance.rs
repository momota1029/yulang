use rustc_hash::FxHashMap;

use crate::SourceSpan;
use crate::constraints::SourceBoundaryId;

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
            SourceBoundaryProvenance::BodyRequirement(_) => None,
        }
    }

    pub(crate) fn insert_body_requirement(
        &mut self,
        boundary: SourceBoundaryId,
        provenance: BodyRequirementBoundaryProvenance,
    ) -> bool {
        self.entries
            .insert(
                boundary,
                SourceBoundaryProvenance::BodyRequirement(provenance),
            )
            .is_none()
    }

    #[allow(dead_code)] // Queried by characterization now; the first production consumer is PUSP-F.
    pub(crate) fn body_requirement(
        &self,
        boundary: SourceBoundaryId,
    ) -> Option<&BodyRequirementBoundaryProvenance> {
        match self.entries.get(&boundary)? {
            SourceBoundaryProvenance::ApplicationArgument(_) => None,
            SourceBoundaryProvenance::BodyRequirement(provenance) => Some(provenance),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SourceBoundaryProvenance {
    ApplicationArgument(ApplicationArgumentBoundaryProvenance),
    BodyRequirement(BodyRequirementBoundaryProvenance),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ApplicationArgumentBoundaryProvenance {
    pub(crate) application_span: SourceSpan,
    pub(crate) callee_span: SourceSpan,
    pub(crate) argument_span: SourceSpan,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BodyRequirementBoundaryProvenance {
    pub(crate) use_span: SourceSpan,
    pub(crate) context_span: Option<SourceSpan>,
}
