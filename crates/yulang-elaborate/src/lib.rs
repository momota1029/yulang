//! Elaborate erased principal inference output into runtime-ready demands.
//!
//! This crate is the new post-inference boundary. It intentionally accepts
//! `yulang_erased_ir::InferExport` instead of typed IR or infer internals, so
//! later implementation cannot read expression-node types, apply evidence, or
//! annotation evidence through the public entrypoint.

#![forbid(unsafe_code)]

use yulang_erased_ir::{InferExport, PrincipalRoot, RefExportTable};

#[derive(Debug, Clone, Copy)]
pub struct Elaborator<'a> {
    export: &'a InferExport,
}

impl<'a> Elaborator<'a> {
    pub fn new(export: &'a InferExport) -> Self {
        Self { export }
    }

    pub fn export(&self) -> &'a InferExport {
        self.export
    }

    pub fn ref_table(&self) -> &'a RefExportTable {
        &self.export.erased.refs
    }

    pub fn roots(&self) -> &'a [PrincipalRoot] {
        &self.export.erased.module.roots
    }

    pub fn input_summary(&self) -> ElaborateInputSummary {
        ElaborateInputSummary {
            bindings: self.export.erased.module.bindings.len(),
            root_exprs: self.export.erased.module.root_exprs.len(),
            roots: self.export.erased.module.roots.len(),
            direct_refs: self.export.erased.refs.direct.len(),
            resolved_typeclass_refs: self.export.erased.refs.resolved_typeclass.len(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElaborateInputSummary {
    pub bindings: usize,
    pub root_exprs: usize,
    pub roots: usize,
    pub direct_refs: usize,
    pub resolved_typeclass_refs: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn elaborator_accepts_erased_infer_export_boundary() {
        let mut export = InferExport::default();
        export.erased.module.roots.push(PrincipalRoot::Expr(0));
        export
            .erased
            .refs
            .direct
            .insert(yulang_erased_ir::RefId(1), yulang_erased_ir::DefId(2));

        let elaborator = Elaborator::new(&export);

        assert_eq!(elaborator.roots(), &[PrincipalRoot::Expr(0)]);
        assert_eq!(
            elaborator.input_summary(),
            ElaborateInputSummary {
                bindings: 0,
                root_exprs: 0,
                roots: 1,
                direct_refs: 1,
                resolved_typeclass_refs: 0,
            }
        );
    }
}
