use poly::expr::ExprId;
use rustc_hash::FxHashMap;

use crate::{ModuleId, SourceSpan};

/// Sparse source ownership for arena-local application expressions.
///
/// An absent entry is an explicitly unowned application produced by lowering/desugaring rather
/// than by surface application syntax. Source ownership is assigned only while the matching CST
/// nodes are still available; it is never reconstructed from the finished expression tree.
#[derive(Debug, Default)]
pub(crate) struct ApplicationProvenanceTable {
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

    #[cfg(test)]
    pub(crate) fn get(&self, expr: ExprId) -> Option<&ApplicationProvenance> {
        self.entries.get(&expr)
    }

    #[cfg(test)]
    pub(crate) fn iter(&self) -> impl Iterator<Item = (ExprId, &ApplicationProvenance)> {
        self.entries
            .iter()
            .map(|(expr, provenance)| (*expr, provenance))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ApplicationProvenance {
    pub(crate) origin: ApplicationOrigin,
    pub(crate) module: ModuleId,
    pub(crate) application_span: SourceSpan,
    pub(crate) callee_span: SourceSpan,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ApplicationOrigin {
    Source,
}
