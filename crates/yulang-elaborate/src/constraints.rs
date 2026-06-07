use std::collections::BTreeMap;

use crate::ErasedExprKind;
use crate::draft::{DraftComputationId, DraftExprId, ElaborationDraft};

use yulang_elaborated_ir::{
    ConcreteType, ConcreteTypeError, MonoComputation, MonoEffect, MonoType,
};
use yulang_erased_ir::{ErasedExpr, Type};

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

    pub(crate) fn solve(
        self,
        draft: &ElaborationDraft,
        root_expr: &ErasedExpr,
    ) -> Result<ComputationSolution, ConstraintError> {
        let mut solver = ConstraintSolver::from_set(self)?;
        solver.solve_expr(draft, draft.root, root_expr)?;
        Ok(solver.into_solution())
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ComputationSolution {
    computations: BTreeMap<DraftComputationId, MonoComputation>,
}

impl ComputationSolution {
    pub(crate) fn computation_for_expr(
        &self,
        draft: &ElaborationDraft,
        expr: DraftExprId,
    ) -> Result<&MonoComputation, ConstraintError> {
        let slot = draft.expr(expr).computation;
        self.computations
            .get(&slot)
            .ok_or(ConstraintError::MissingComputation { slot: slot.into() })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ConstraintComputationSlot(pub u32);

impl From<DraftComputationId> for ConstraintComputationSlot {
    fn from(slot: DraftComputationId) -> Self {
        Self(slot.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintError {
    ConflictingComputation {
        slot: ConstraintComputationSlot,
        existing: MonoComputation,
        incoming: MonoComputation,
    },
    MissingComputation {
        slot: ConstraintComputationSlot,
    },
    ExpectedTuple {
        slot: ConstraintComputationSlot,
        found: MonoType,
    },
    TupleArityMismatch {
        slot: ConstraintComputationSlot,
        expected: usize,
        actual: usize,
    },
    NonConcreteTupleItem {
        slot: ConstraintComputationSlot,
        error: ConcreteTypeError,
    },
    NonPureCompoundEffect {
        slot: ConstraintComputationSlot,
        kind: ErasedExprKind,
        effect: MonoEffect,
    },
}

struct ConstraintSolver {
    computations: BTreeMap<DraftComputationId, MonoComputation>,
}

impl ConstraintSolver {
    fn from_set(set: ConstraintSet) -> Result<Self, ConstraintError> {
        let mut solver = Self {
            computations: BTreeMap::new(),
        };
        for seed in set.computation_seeds {
            solver.assign(seed.slot, seed.computation)?;
        }
        Ok(solver)
    }

    fn into_solution(self) -> ComputationSolution {
        ComputationSolution {
            computations: self.computations,
        }
    }

    fn solve_expr(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        expr: &ErasedExpr,
    ) -> Result<(), ConstraintError> {
        match expr {
            ErasedExpr::Tuple(items) => self.solve_tuple(draft, id, items),
            ErasedExpr::Def(_)
            | ErasedExpr::Ref(_)
            | ErasedExpr::PrimitiveOp(_)
            | ErasedExpr::Lit(_) => self
                .require_assigned(draft.expr(id).computation)
                .map(|_| ()),
            _ => Ok(()),
        }
    }

    fn solve_tuple(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        items: &[ErasedExpr],
    ) -> Result<(), ConstraintError> {
        let slot = draft.expr(id).computation;
        let computation = self.require_assigned(slot)?.clone();
        if !effect_is_pure(&computation.effect) {
            return Err(ConstraintError::NonPureCompoundEffect {
                slot: slot.into(),
                kind: ErasedExprKind::Tuple,
                effect: computation.effect,
            });
        }
        let MonoType::Value(value) = computation.value else {
            return Err(ConstraintError::ExpectedTuple {
                slot: slot.into(),
                found: computation.value,
            });
        };
        let item_types = match value.as_type() {
            Type::Tuple(item_types) => item_types,
            _ => {
                return Err(ConstraintError::ExpectedTuple {
                    slot: slot.into(),
                    found: MonoType::Value(value),
                });
            }
        };
        if item_types.len() != items.len() {
            return Err(ConstraintError::TupleArityMismatch {
                slot: slot.into(),
                expected: item_types.len(),
                actual: items.len(),
            });
        }

        let children = draft.expr(id).children.clone();
        for ((child_id, item), item_type) in children.into_iter().zip(items).zip(item_types) {
            let child_slot = draft.expr(child_id).computation;
            let child_computation = MonoComputation {
                value: MonoType::Value(ConcreteType::try_from_type(item_type.clone()).map_err(
                    |error| ConstraintError::NonConcreteTupleItem {
                        slot: child_slot.into(),
                        error,
                    },
                )?),
                effect: pure_effect(),
            };
            self.assign(child_slot, child_computation)?;
            self.solve_expr(draft, child_id, item)?;
        }
        Ok(())
    }

    fn assign(
        &mut self,
        slot: DraftComputationId,
        computation: MonoComputation,
    ) -> Result<(), ConstraintError> {
        if let Some(existing) = self.computations.get(&slot) {
            if existing != &computation {
                return Err(ConstraintError::ConflictingComputation {
                    slot: slot.into(),
                    existing: existing.clone(),
                    incoming: computation,
                });
            }
            return Ok(());
        }
        self.computations.insert(slot, computation);
        Ok(())
    }

    fn require_assigned(
        &self,
        slot: DraftComputationId,
    ) -> Result<&MonoComputation, ConstraintError> {
        self.computations
            .get(&slot)
            .ok_or(ConstraintError::MissingComputation { slot: slot.into() })
    }
}

fn effect_is_pure(effect: &MonoEffect) -> bool {
    matches!(effect.row().as_type(), Type::Never)
}

fn pure_effect() -> MonoEffect {
    MonoEffect::new(ConcreteType::try_from_type(Type::Never).expect("Never is concrete"))
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
