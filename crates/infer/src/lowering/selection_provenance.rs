use poly::expr::{DefId, SelectId};
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};

use crate::SourceSpan;

/// Sparse source identity needed to diagnose role-method selections after inference.
///
/// Selection spans identify the source field token. Definition spans identify matching impl
/// method candidates for ambiguous selections. Both maps contain only identities captured while
/// source ownership is still available; imported or synthetic identities are intentionally absent.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SelectionProvenanceTable {
    selections: FxHashMap<SelectId, SourceSpan>,
    definitions: FxHashMap<DefId, SourceSpan>,
}

impl SelectionProvenanceTable {
    pub fn from_source_spans(
        selections: impl IntoIterator<Item = (SelectId, SourceSpan)>,
        definitions: impl IntoIterator<Item = (DefId, SourceSpan)>,
    ) -> Self {
        Self {
            selections: selections.into_iter().collect(),
            definitions: definitions.into_iter().collect(),
        }
    }

    pub fn selection_span(&self, select: SelectId) -> Option<&SourceSpan> {
        self.selections.get(&select)
    }

    pub fn definition_span(&self, def: DefId) -> Option<&SourceSpan> {
        self.definitions.get(&def)
    }

    pub fn selection_spans(&self) -> impl Iterator<Item = (SelectId, &SourceSpan)> {
        self.selections.iter().map(|(select, span)| (*select, span))
    }

    pub fn definition_spans(&self) -> impl Iterator<Item = (DefId, &SourceSpan)> {
        self.definitions.iter().map(|(def, span)| (*def, span))
    }

    pub fn is_empty(&self) -> bool {
        self.selections.is_empty() && self.definitions.is_empty()
    }
}
