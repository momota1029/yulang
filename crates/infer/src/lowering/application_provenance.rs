use poly::expr::ExprId;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};

use crate::{ModuleId, SourceSpan};

/// Sparse source ownership for arena-local application expressions.
///
/// An absent entry is an explicitly unowned application produced by lowering/desugaring rather
/// than by surface application syntax. Source ownership is assigned only while the matching CST
/// nodes are still available; it is never reconstructed from the finished expression tree.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ApplicationProvenanceTable {
    entries: FxHashMap<ExprId, ApplicationProvenance>,
}

impl ApplicationProvenanceTable {
    pub(crate) fn insert(
        &mut self,
        expr: ExprId,
        provenance: ApplicationProvenance,
    ) -> Option<ApplicationProvenance> {
        self.entries.insert(expr, provenance)
    }

    pub fn get(&self, expr: ExprId) -> Option<&ApplicationProvenance> {
        self.entries.get(&expr)
    }

    pub fn iter(&self) -> impl Iterator<Item = (ExprId, &ApplicationProvenance)> {
        self.entries
            .iter()
            .map(|(expr, provenance)| (*expr, provenance))
    }

    pub fn expr_ids(&self) -> impl Iterator<Item = ExprId> + '_ {
        self.entries.keys().copied()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ApplicationProvenance {
    pub origin: ApplicationOrigin,
    pub module: ModuleId,
    pub application_span: SourceSpan,
    pub callee_span: SourceSpan,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ApplicationOrigin {
    Source,
}
