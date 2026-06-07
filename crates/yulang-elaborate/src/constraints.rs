use std::collections::BTreeMap;

use crate::ErasedExprKind;
use crate::draft::{DraftComputationId, DraftExprId, ElaborationDraft};

use yulang_elaborated_ir::{
    ConcreteType, ConcreteTypeError, MonoComputation, MonoEffect, MonoType,
};
use yulang_erased_ir::{ErasedExpr, Lit, Name, Path, Type};

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
    NonConcreteType {
        slot: ConstraintComputationSlot,
        source: ConstraintTypeSource,
        error: ConcreteTypeError,
    },
    NonPureCompoundEffect {
        slot: ConstraintComputationSlot,
        kind: ErasedExprKind,
        effect: MonoEffect,
    },
    ExpectedFunction {
        slot: ConstraintComputationSlot,
        found: MonoType,
    },
    ExpectedValue {
        slot: ConstraintComputationSlot,
        found: MonoType,
    },
    UnsupportedApplyArg {
        slot: ConstraintComputationSlot,
        kind: ErasedExprKind,
    },
    UnsupportedApplyCallee {
        slot: ConstraintComputationSlot,
        kind: ErasedExprKind,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintTypeSource {
    TupleItem,
    FunctionParam,
    FunctionParamEffect,
    FunctionReturn,
    FunctionReturnEffect,
    Literal,
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
            ErasedExpr::Apply { callee, arg } => self.solve_apply(draft, id, callee, arg),
            ErasedExpr::Lambda { body, .. } => self.solve_lambda(draft, id, body),
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

    fn solve_apply(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        callee: &ErasedExpr,
        arg: &ErasedExpr,
    ) -> Result<(), ConstraintError> {
        let slot = draft.expr(id).computation;
        let computation = self.require_assigned(slot)?.clone();
        if !matches!(callee, ErasedExpr::Lambda { .. }) {
            return Err(ConstraintError::UnsupportedApplyCallee {
                slot: slot.into(),
                kind: ErasedExprKind::from_expr(callee),
            });
        }
        let ret_type = value_type(slot, &computation.value)?;
        let ret_effect = computation.effect.row().as_type().clone();
        let arg_computation = literal_computation(slot, arg)?.ok_or_else(|| {
            ConstraintError::UnsupportedApplyArg {
                slot: slot.into(),
                kind: ErasedExprKind::from_expr(arg),
            }
        })?;
        let arg_type = value_type(slot, &arg_computation.value)?;
        let callee_computation = MonoComputation {
            value: MonoType::Value(concrete_type(
                slot,
                ConstraintTypeSource::FunctionParam,
                Type::Fun {
                    param: Box::new(arg_type),
                    param_effect: Box::new(Type::Never),
                    ret_effect: Box::new(ret_effect),
                    ret: Box::new(ret_type),
                },
            )?),
            effect: pure_effect(),
        };

        let children = draft.expr(id).children.clone();
        let [callee_id, arg_id] = children.as_slice() else {
            return Ok(());
        };
        self.assign(draft.expr(*callee_id).computation, callee_computation)?;
        self.assign(draft.expr(*arg_id).computation, arg_computation)?;
        self.solve_expr(draft, *callee_id, callee)?;
        self.solve_expr(draft, *arg_id, arg)
    }

    fn solve_lambda(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        body: &ErasedExpr,
    ) -> Result<(), ConstraintError> {
        let slot = draft.expr(id).computation;
        let computation = self.require_assigned(slot)?.clone();
        if !effect_is_pure(&computation.effect) {
            return Err(ConstraintError::NonPureCompoundEffect {
                slot: slot.into(),
                kind: ErasedExprKind::Lambda,
                effect: computation.effect,
            });
        }
        let MonoType::Value(value) = computation.value else {
            return Err(ConstraintError::ExpectedFunction {
                slot: slot.into(),
                found: computation.value,
            });
        };
        let Type::Fun {
            ret_effect, ret, ..
        } = value.as_type()
        else {
            return Err(ConstraintError::ExpectedFunction {
                slot: slot.into(),
                found: MonoType::Value(value),
            });
        };
        let body_computation = MonoComputation {
            value: MonoType::Value(concrete_type(
                slot,
                ConstraintTypeSource::FunctionReturn,
                (**ret).clone(),
            )?),
            effect: MonoEffect::new(concrete_type(
                slot,
                ConstraintTypeSource::FunctionReturnEffect,
                (**ret_effect).clone(),
            )?),
        };

        let children = draft.expr(id).children.clone();
        let [body_id] = children.as_slice() else {
            return Ok(());
        };
        self.assign(draft.expr(*body_id).computation, body_computation)?;
        self.solve_expr(draft, *body_id, body)
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
                value: MonoType::Value(concrete_type(
                    child_slot,
                    ConstraintTypeSource::TupleItem,
                    item_type.clone(),
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

fn value_type(slot: DraftComputationId, typ: &MonoType) -> Result<Type, ConstraintError> {
    match typ {
        MonoType::Value(value) => Ok(value.as_type().clone()),
        MonoType::EffectiveThunk(_) => Err(ConstraintError::ExpectedValue {
            slot: slot.into(),
            found: typ.clone(),
        }),
    }
}

fn literal_computation(
    slot: DraftComputationId,
    expr: &ErasedExpr,
) -> Result<Option<MonoComputation>, ConstraintError> {
    let ErasedExpr::Lit(lit) = expr else {
        return Ok(None);
    };
    Ok(Some(MonoComputation {
        value: MonoType::Value(concrete_type(
            slot,
            ConstraintTypeSource::Literal,
            literal_type(lit),
        )?),
        effect: pure_effect(),
    }))
}

fn literal_type(lit: &Lit) -> Type {
    Type::Named {
        path: match lit {
            Lit::Int(_) => Path::from_name(Name("int".to_string())),
            Lit::Float(_) => Path::from_name(Name("float".to_string())),
            Lit::String(_) => Path::new(vec![
                Name("std".to_string()),
                Name("str".to_string()),
                Name("str".to_string()),
            ]),
            Lit::Bool(_) => Path::from_name(Name("bool".to_string())),
            Lit::Unit => Path::from_name(Name("unit".to_string())),
        },
        args: Vec::new(),
    }
}

fn concrete_type(
    slot: DraftComputationId,
    source: ConstraintTypeSource,
    ty: Type,
) -> Result<ConcreteType, ConstraintError> {
    ConcreteType::try_from_type(ty).map_err(|error| ConstraintError::NonConcreteType {
        slot: slot.into(),
        source,
        error,
    })
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
