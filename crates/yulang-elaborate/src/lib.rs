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
        let quantified_refs = self
            .export
            .erased
            .module
            .bindings
            .iter()
            .map(|binding| binding.scheme.quantified_refs.len())
            .sum();
        let typeclass_obligations = self
            .export
            .erased
            .module
            .bindings
            .iter()
            .map(|binding| binding.scheme.typeclass_obligations.len())
            .sum();
        ElaborateInputSummary {
            bindings: self.export.erased.module.bindings.len(),
            root_exprs: self.export.erased.module.root_exprs.len(),
            roots: self.export.erased.module.roots.len(),
            direct_refs: self.export.erased.refs.direct.len(),
            resolved_typeclass_refs: self.export.erased.refs.resolved_typeclass.len(),
            quantified_refs,
            typeclass_obligations,
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
    pub quantified_refs: usize,
    pub typeclass_obligations: usize,
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
                quantified_refs: 0,
                typeclass_obligations: 0,
            }
        );
    }

    #[test]
    fn elaborator_counts_erased_typeclass_obligation_inputs() {
        let mut export = InferExport::default();
        export
            .erased
            .module
            .bindings
            .push(yulang_erased_ir::InferredBinding {
                name: yulang_erased_ir::Path::from_name(yulang_erased_ir::Name("show".to_string())),
                scheme: yulang_erased_ir::Scheme {
                    body: yulang_erased_ir::Type::Unknown,
                    quantified_types: Vec::new(),
                    quantified_effects: Vec::new(),
                    quantified_refs: vec![yulang_erased_ir::RefId(7)],
                    typeclass_obligations: vec![yulang_erased_ir::TypeClassObligation {
                        ref_id: yulang_erased_ir::RefId(7),
                        class: yulang_erased_ir::Path::from_name(yulang_erased_ir::Name(
                            "Display".to_string(),
                        )),
                        member: yulang_erased_ir::DefId(3),
                        args: vec![yulang_erased_ir::Type::Var(yulang_erased_ir::TypeVar(
                            "t0".to_string(),
                        ))],
                        associated: Vec::new(),
                    }],
                    requirements: Vec::new(),
                },
                body: yulang_erased_ir::InferredExpr {
                    typ: yulang_erased_ir::TypeBounds::default(),
                    eff: yulang_erased_ir::TypeBounds::default(),
                    ir: yulang_erased_ir::ErasedExpr::Ref(yulang_erased_ir::RefId(7)),
                },
            });

        assert_eq!(
            Elaborator::new(&export).input_summary(),
            ElaborateInputSummary {
                bindings: 1,
                root_exprs: 0,
                roots: 0,
                direct_refs: 0,
                resolved_typeclass_refs: 0,
                quantified_refs: 1,
                typeclass_obligations: 1,
            }
        );
    }
}
