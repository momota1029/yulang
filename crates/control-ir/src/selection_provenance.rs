use std::collections::HashMap;

use mono::SelectionProvenanceTag;
use serde::{Deserialize, Serialize};

use crate::ExprId;

/// Sparse bridge from final control-IR selection sites to their specialization origin.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SelectionProvenanceTable {
    entries: HashMap<ExprId, SelectionProvenanceTag>,
}

impl SelectionProvenanceTable {
    pub fn get(&self, site: ExprId) -> Option<SelectionProvenanceTag> {
        self.entries.get(&site).copied()
    }

    pub fn iter(&self) -> impl Iterator<Item = (ExprId, SelectionProvenanceTag)> + '_ {
        self.entries.iter().map(|(site, tag)| (*site, *tag))
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub(crate) fn insert(
        &mut self,
        site: ExprId,
        tag: SelectionProvenanceTag,
    ) -> Option<SelectionProvenanceTag> {
        self.entries.insert(site, tag)
    }
}
