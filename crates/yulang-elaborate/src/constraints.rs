use crate::draft::{DraftComputationId, DraftExprId, ElaborationDraft};

use yulang_elaborated_ir::MonoComputation;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConstraintSet {
    pub(crate) root: DraftComputationId,
    pub(crate) computation_seeds: Vec<ComputationSeed>,
    pub(crate) force_thunk_boundaries: Vec<ForceThunkBoundaryConstraint>,
}

impl ConstraintSet {
    pub(crate) fn seed_root(draft: &ElaborationDraft, root: MonoComputation) -> Self {
        let root_slot = draft.expr(draft.root).computation;
        Self {
            root: root_slot,
            computation_seeds: vec![ComputationSeed {
                slot: root_slot,
                computation: root,
            }],
            force_thunk_boundaries: draft
                .force_thunk_boundaries
                .iter()
                .map(|boundary| ForceThunkBoundaryConstraint {
                    site: boundary.site,
                    thunk: boundary.thunk,
                })
                .collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ComputationSeed {
    pub(crate) slot: DraftComputationId,
    pub(crate) computation: MonoComputation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ForceThunkBoundaryConstraint {
    pub(crate) site: DraftExprId,
    pub(crate) thunk: DraftExprId,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::draft::{DraftComputationId, DraftExprId};
    use yulang_elaborated_ir::{ConcreteType, MonoEffect, MonoType};
    use yulang_erased_ir::{ErasedExpr, Lit, Name, Path, Type};

    #[test]
    fn seed_root_records_root_computation_slot() {
        let draft =
            ElaborationDraft::from_root_expr(0, &ErasedExpr::Lit(Lit::Int("1".to_string())));
        let computation = int_computation();

        let constraints = ConstraintSet::seed_root(&draft, computation.clone());

        assert_eq!(constraints.root, DraftComputationId(0));
        assert_eq!(
            constraints.computation_seeds,
            vec![ComputationSeed {
                slot: DraftComputationId(0),
                computation,
            }]
        );
        assert!(constraints.force_thunk_boundaries.is_empty());
    }

    #[test]
    fn seed_root_keeps_force_thunk_boundaries_from_draft() {
        let draft = ElaborationDraft::from_root_expr(
            0,
            &ErasedExpr::BindHere {
                expr: Box::new(ErasedExpr::Ref(yulang_erased_ir::RefId(7))),
            },
        );

        let constraints = ConstraintSet::seed_root(&draft, int_computation());

        assert_eq!(
            constraints.force_thunk_boundaries,
            vec![ForceThunkBoundaryConstraint {
                site: DraftExprId(0),
                thunk: DraftExprId(1),
            }]
        );
    }

    fn int_computation() -> MonoComputation {
        MonoComputation {
            value: MonoType::Value(concrete_named("int")),
            effect: MonoEffect::new(
                ConcreteType::try_from_type(Type::Never).expect("Never is concrete"),
            ),
        }
    }

    fn concrete_named(name: &str) -> ConcreteType {
        ConcreteType::try_from_type(Type::Named {
            path: Path::from_name(Name(name.to_string())),
            args: Vec::new(),
        })
        .expect("named type is concrete")
    }
}
