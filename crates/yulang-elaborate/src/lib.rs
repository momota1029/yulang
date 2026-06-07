//! Elaborate erased principal inference output into runtime-ready demands.
//!
//! This crate is the new post-inference boundary. It intentionally accepts
//! `yulang_erased_ir::InferExport` instead of typed IR or infer internals, so
//! later implementation cannot read expression-node types, apply evidence, or
//! annotation evidence through the public entrypoint.

#![forbid(unsafe_code)]

use yulang_erased_ir::{
    DefId, InferExport, PrincipalRoot, RefCoverageReport, RefExportTable, RefId,
    ResolvedTypeClassRef, TypeClassObligation,
};

#[derive(Debug, Clone, Copy)]
pub struct Elaborator<'a> {
    export: &'a InferExport,
}

impl<'a> Elaborator<'a> {
    pub fn new(export: &'a InferExport) -> Self {
        Self { export }
    }

    pub fn try_new(export: &'a InferExport) -> Result<Self, ElaborateInputError> {
        let elaborator = Self::new(export);
        elaborator.validate_input()?;
        Ok(elaborator)
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

    pub fn validate_input(&self) -> Result<(), ElaborateInputError> {
        let ref_coverage = self.export.erased.ref_coverage();
        if ref_coverage.is_clean() {
            Ok(())
        } else {
            Err(ElaborateInputError::RefCoverage(ref_coverage))
        }
    }

    pub fn build_plan(&self) -> Result<ElaboratePlan, ElaborateInputError> {
        self.validate_input()?;
        let mut refs = Vec::new();
        for (&ref_id, &def) in &self.export.erased.refs.direct {
            refs.push(RefDemand::Direct { ref_id, def });
        }
        for (&ref_id, resolved) in &self.export.erased.refs.resolved_typeclass {
            refs.push(RefDemand::ResolvedTypeclass {
                ref_id,
                resolved: resolved.clone(),
            });
        }
        for obligation in self.export.erased.typeclass_obligations() {
            refs.push(RefDemand::TypeclassObligation {
                ref_id: obligation.ref_id,
                obligation: obligation.clone(),
            });
        }
        refs.sort_by_key(RefDemand::ref_id);
        Ok(ElaboratePlan {
            roots: self.export.erased.module.roots.clone(),
            refs,
        })
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ElaborateInputError {
    RefCoverage(RefCoverageReport),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElaboratePlan {
    pub roots: Vec<PrincipalRoot>,
    pub refs: Vec<RefDemand>,
}

impl ElaboratePlan {
    pub fn impl_member_demands(&self) -> Vec<DefId> {
        self.refs
            .iter()
            .filter_map(|demand| match demand {
                RefDemand::ResolvedTypeclass { resolved, .. } => Some(resolved.impl_member),
                RefDemand::Direct { .. } | RefDemand::TypeclassObligation { .. } => None,
            })
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RefDemand {
    Direct {
        ref_id: RefId,
        def: DefId,
    },
    ResolvedTypeclass {
        ref_id: RefId,
        resolved: ResolvedTypeClassRef,
    },
    TypeclassObligation {
        ref_id: RefId,
        obligation: TypeClassObligation,
    },
}

impl RefDemand {
    pub fn ref_id(&self) -> RefId {
        match self {
            Self::Direct { ref_id, .. }
            | Self::ResolvedTypeclass { ref_id, .. }
            | Self::TypeclassObligation { ref_id, .. } => *ref_id,
        }
    }
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
        assert_eq!(elaborator.validate_input(), Ok(()));
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
        assert_eq!(Elaborator::new(&export).validate_input(), Ok(()));
    }

    #[test]
    fn elaborator_rejects_uncovered_erased_refs_at_boundary() {
        let mut export = InferExport::default();
        export
            .erased
            .module
            .root_exprs
            .push(yulang_erased_ir::InferredExpr {
                typ: yulang_erased_ir::TypeBounds::default(),
                eff: yulang_erased_ir::TypeBounds::default(),
                ir: yulang_erased_ir::ErasedExpr::Ref(yulang_erased_ir::RefId(99)),
            });

        let Err(ElaborateInputError::RefCoverage(report)) =
            Elaborator::new(&export).validate_input()
        else {
            panic!("uncovered RefId should be rejected");
        };
        assert_eq!(report.uncovered, vec![yulang_erased_ir::RefId(99)]);
        assert!(report.conflicting.is_empty());
        assert!(Elaborator::try_new(&export).is_err());
    }

    #[test]
    fn elaborator_builds_ref_demand_plan_from_erased_export() {
        let mut export = InferExport::default();
        export.erased.module.roots.push(PrincipalRoot::Expr(0));
        export
            .erased
            .module
            .root_exprs
            .push(yulang_erased_ir::InferredExpr {
                typ: yulang_erased_ir::TypeBounds::default(),
                eff: yulang_erased_ir::TypeBounds::default(),
                ir: yulang_erased_ir::ErasedExpr::Tuple(vec![
                    yulang_erased_ir::ErasedExpr::Ref(yulang_erased_ir::RefId(1)),
                    yulang_erased_ir::ErasedExpr::Ref(yulang_erased_ir::RefId(2)),
                    yulang_erased_ir::ErasedExpr::Ref(yulang_erased_ir::RefId(3)),
                ]),
            });
        export
            .erased
            .refs
            .direct
            .insert(yulang_erased_ir::RefId(1), yulang_erased_ir::DefId(11));
        export.erased.refs.resolved_typeclass.insert(
            yulang_erased_ir::RefId(2),
            yulang_erased_ir::ResolvedTypeClassRef {
                class: yulang_erased_ir::Path::from_name(yulang_erased_ir::Name(
                    "Display".to_string(),
                )),
                member: yulang_erased_ir::DefId(20),
                impl_def: Some(yulang_erased_ir::DefId(21)),
                impl_member: yulang_erased_ir::DefId(22),
            },
        );
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
                    quantified_refs: vec![yulang_erased_ir::RefId(3)],
                    typeclass_obligations: vec![yulang_erased_ir::TypeClassObligation {
                        ref_id: yulang_erased_ir::RefId(3),
                        class: yulang_erased_ir::Path::from_name(yulang_erased_ir::Name(
                            "Show".to_string(),
                        )),
                        member: yulang_erased_ir::DefId(30),
                        args: Vec::new(),
                        associated: Vec::new(),
                    }],
                    requirements: Vec::new(),
                },
                body: yulang_erased_ir::InferredExpr {
                    typ: yulang_erased_ir::TypeBounds::default(),
                    eff: yulang_erased_ir::TypeBounds::default(),
                    ir: yulang_erased_ir::ErasedExpr::Ref(yulang_erased_ir::RefId(3)),
                },
            });

        let plan = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_plan()
            .expect("demand plan");

        assert_eq!(plan.roots, vec![PrincipalRoot::Expr(0)]);
        assert!(matches!(
            &plan.refs[0],
            RefDemand::Direct {
                ref_id: yulang_erased_ir::RefId(1),
                def: yulang_erased_ir::DefId(11),
            }
        ));
        assert!(matches!(
            &plan.refs[1],
            RefDemand::ResolvedTypeclass {
                ref_id: yulang_erased_ir::RefId(2),
                resolved,
            } if resolved.impl_member == yulang_erased_ir::DefId(22)
        ));
        assert!(matches!(
            &plan.refs[2],
            RefDemand::TypeclassObligation {
                ref_id: yulang_erased_ir::RefId(3),
                obligation,
            } if obligation.member == yulang_erased_ir::DefId(30)
        ));
        assert_eq!(
            plan.impl_member_demands(),
            vec![yulang_erased_ir::DefId(22)]
        );
    }

    #[test]
    fn elaborate_plan_accepts_actual_erased_infer_export() {
        let mut lowered = yulang_infer::lower_virtual_source_with_options(
            "role Display 'a:\n  our a.display: string\n\n\
impl Display int:\n  our x.display = \"int\"\n\n\
my id x = x\n\
my show x = x.display\n\
my used = id (1.display)\n",
            None,
            yulang_infer::SourceOptions::default(),
        )
        .expect("lower virtual source");
        let export = yulang_infer::export_erased_program(&mut lowered.state);
        let plan = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_plan()
            .expect("demand plan");

        assert!(
            plan.refs
                .iter()
                .any(|demand| matches!(demand, RefDemand::Direct { .. })),
            "direct global refs should become elaborate ref demands: {:?}",
            plan.refs,
        );
        assert!(
            plan.refs.iter().any(|demand| matches!(
                demand,
                RefDemand::ResolvedTypeclass { resolved, .. }
                    if resolved
                        .class
                        .segments
                        .last()
                        .is_some_and(|name| name.0 == "Display")
            )),
            "infer-resolved role method refs should become elaborate demands: {:?}",
            plan.refs,
        );
        assert!(
            plan.refs.iter().any(|demand| matches!(
                demand,
                RefDemand::TypeclassObligation { obligation, .. }
                    if obligation
                        .class
                        .segments
                        .last()
                        .is_some_and(|name| name.0 == "Display")
            )),
            "unresolved role method refs should become elaborate obligation demands: {:?}",
            plan.refs,
        );
    }
}
