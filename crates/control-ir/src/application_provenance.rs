use std::collections::HashMap;

use mono::ApplicationProvenanceTag;
use serde::{Deserialize, Serialize};

use crate::ExprId;

/// Sparse bridge from final control-IR apply sites to their specialization origin.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ApplicationProvenanceTable {
    entries: HashMap<ExprId, ApplicationProvenanceTag>,
}

impl ApplicationProvenanceTable {
    pub fn get(&self, site: ExprId) -> Option<ApplicationProvenanceTag> {
        self.entries.get(&site).copied()
    }

    pub fn iter(&self) -> impl Iterator<Item = (ExprId, ApplicationProvenanceTag)> + '_ {
        self.entries.iter().map(|(site, tag)| (*site, *tag))
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub(crate) fn insert(
        &mut self,
        site: ExprId,
        tag: ApplicationProvenanceTag,
    ) -> Option<ApplicationProvenanceTag> {
        self.entries.insert(site, tag)
    }
}
