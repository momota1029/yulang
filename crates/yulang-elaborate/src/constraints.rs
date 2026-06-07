use std::collections::{BTreeMap, BTreeSet};

use crate::ErasedExprKind;
use crate::draft::{DraftComputationId, DraftExprId, ElaborationDraft};

use yulang_elaborated_ir::{
    ConcreteType, ConcreteTypeError, MonoComputation, MonoEffect, MonoType,
};
use yulang_erased_ir::{
    DefId, ErasedExpr, InferredBinding, Lit, Name, Path, RefExportTable, RefId,
    ResolvedTypeClassRef, Scheme, Type, TypeVar,
};

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
        env: &ConstraintEnvironment<'_>,
    ) -> Result<ComputationSolution, ConstraintError> {
        let mut solver = ConstraintSolver::from_set(self)?;
        solver.solve_expr(draft, draft.root, root_expr, env)?;
        solver.into_solution()
    }
}

#[derive(Debug, Clone)]
pub(crate) struct ConstraintEnvironment<'a> {
    refs: &'a RefExportTable,
    schemes: BTreeMap<DefId, &'a Scheme>,
}

impl<'a> ConstraintEnvironment<'a> {
    pub(crate) fn new(refs: &'a RefExportTable, bindings: &'a [InferredBinding]) -> Self {
        Self {
            refs,
            schemes: bindings
                .iter()
                .map(|binding| (binding.def, &binding.scheme))
                .collect(),
        }
    }

    pub(crate) fn direct_scheme(&self, ref_id: RefId) -> Option<(DefId, &'a Scheme)> {
        let def = *self.refs.direct.get(&ref_id)?;
        let scheme = *self.schemes.get(&def)?;
        Some((def, scheme))
    }

    pub(crate) fn resolved_typeclass_scheme(
        &self,
        ref_id: RefId,
    ) -> Option<(&'a ResolvedTypeClassRef, &'a Scheme)> {
        let resolved = self.refs.resolved_typeclass.get(&ref_id)?;
        let scheme = *self.schemes.get(&resolved.impl_member)?;
        Some((resolved, scheme))
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
    direct_ref_instances: BTreeMap<RefId, DirectRefInstanceDemand>,
    resolved_typeclass_instances: BTreeMap<RefId, ResolvedTypeclassInstanceDemand>,
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

    pub(crate) fn direct_ref_instances(&self) -> &BTreeMap<RefId, DirectRefInstanceDemand> {
        &self.direct_ref_instances
    }

    pub(crate) fn resolved_typeclass_instances(
        &self,
    ) -> &BTreeMap<RefId, ResolvedTypeclassInstanceDemand> {
        &self.resolved_typeclass_instances
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DirectRefInstanceDemand {
    pub(crate) def: DefId,
    pub(crate) signature: MonoComputation,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResolvedTypeclassInstanceDemand {
    pub(crate) resolved: ResolvedTypeClassRef,
    pub(crate) signature: MonoComputation,
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
    MissingDirectRefScheme {
        ref_id: RefId,
    },
    GenericDirectRefScheme {
        def: DefId,
    },
    FunctionResultMismatch {
        slot: ConstraintComputationSlot,
        expected: MonoComputation,
        actual: MonoComputation,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintTypeSource {
    BoundsSelection,
    TupleItem,
    FunctionParam,
    FunctionParamEffect,
    FunctionReturn,
    FunctionReturnEffect,
    Literal,
}

struct ConstraintSolver {
    bounds: BTreeMap<TypeNode, TypeBoundsGraph>,
    pending_bounds: Vec<PendingBound>,
    subtype_edges: BTreeSet<(TypeNode, TypeNode)>,
    next_type_var: u32,
    direct_ref_instances: BTreeMap<RefId, DirectRefInstanceDemand>,
    resolved_typeclass_instances: BTreeMap<RefId, ResolvedTypeclassInstanceDemand>,
}

impl ConstraintSolver {
    fn from_set(set: ConstraintSet) -> Result<Self, ConstraintError> {
        let mut solver = Self {
            bounds: BTreeMap::new(),
            pending_bounds: Vec::new(),
            subtype_edges: BTreeSet::new(),
            next_type_var: 0,
            direct_ref_instances: BTreeMap::new(),
            resolved_typeclass_instances: BTreeMap::new(),
        };
        for seed in set.computation_seeds {
            solver.assign(seed.slot, seed.computation)?;
        }
        Ok(solver)
    }

    fn into_solution(self) -> Result<ComputationSolution, ConstraintError> {
        let mut computations = BTreeMap::new();
        let slots = self
            .bounds
            .keys()
            .filter_map(TypeNode::computation_slot)
            .collect::<BTreeSet<_>>();
        for slot in slots {
            computations.insert(slot, self.require_assigned(slot)?);
        }
        Ok(ComputationSolution {
            computations,
            direct_ref_instances: self.direct_ref_instances,
            resolved_typeclass_instances: self.resolved_typeclass_instances,
        })
    }

    fn solve_expr(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        expr: &ErasedExpr,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<(), ConstraintError> {
        match expr {
            ErasedExpr::Apply { callee, arg } => self.solve_apply(draft, id, callee, arg, env),
            ErasedExpr::Lambda { body, .. } => self.solve_lambda(draft, id, body, env),
            ErasedExpr::Tuple(items) => self.solve_tuple(draft, id, items, env),
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
        env: &ConstraintEnvironment<'_>,
    ) -> Result<(), ConstraintError> {
        let slot = draft.expr(id).computation;
        let computation = self.require_assigned(slot)?.clone();
        let apply_computation = match callee {
            ErasedExpr::Lambda { .. } => {
                let ret_type = value_type(slot, &computation.value)?;
                let ret_effect = computation.effect.row().as_type().clone();
                let arg_computation = literal_computation(slot, arg)?.ok_or_else(|| {
                    ConstraintError::UnsupportedApplyArg {
                        slot: slot.into(),
                        kind: ErasedExprKind::from_expr(arg),
                    }
                })?;
                let arg_type = value_type(slot, &arg_computation.value)?;
                ApplyComputation {
                    callee: function_computation(
                        slot,
                        arg_type,
                        Type::Never,
                        ret_effect,
                        ret_type,
                    )?,
                    arg: arg_computation,
                }
            }
            ErasedExpr::Ref(ref_id) => {
                if let Some((def, scheme)) = env.direct_scheme(*ref_id) {
                    let Some(apply) =
                        self.apply_from_scheme(slot, &computation, scheme, arg, env)?
                    else {
                        return Err(ConstraintError::GenericDirectRefScheme { def });
                    };
                    self.direct_ref_instances.insert(
                        *ref_id,
                        DirectRefInstanceDemand {
                            def,
                            signature: apply.callee.clone(),
                        },
                    );
                    apply
                } else if let Some((resolved, scheme)) = env.resolved_typeclass_scheme(*ref_id) {
                    let Some(apply) =
                        self.apply_from_scheme(slot, &computation, scheme, arg, env)?
                    else {
                        return Err(ConstraintError::GenericDirectRefScheme {
                            def: resolved.impl_member,
                        });
                    };
                    self.resolved_typeclass_instances.insert(
                        *ref_id,
                        ResolvedTypeclassInstanceDemand {
                            resolved: resolved.clone(),
                            signature: apply.callee.clone(),
                        },
                    );
                    apply
                } else {
                    return Err(ConstraintError::MissingDirectRefScheme { ref_id: *ref_id });
                }
            }
            _ => {
                return Err(ConstraintError::UnsupportedApplyCallee {
                    slot: slot.into(),
                    kind: ErasedExprKind::from_expr(callee),
                });
            }
        };

        let children = draft.expr(id).children.clone();
        let [callee_id, arg_id] = children.as_slice() else {
            return Ok(());
        };
        self.assign(draft.expr(*callee_id).computation, apply_computation.callee)?;
        self.assign(draft.expr(*arg_id).computation, apply_computation.arg)?;
        self.solve_expr(draft, *callee_id, callee, env)?;
        self.solve_expr(draft, *arg_id, arg, env)
    }

    fn solve_lambda(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        body: &ErasedExpr,
        env: &ConstraintEnvironment<'_>,
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
        self.solve_expr(draft, *body_id, body, env)
    }

    fn solve_tuple(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        items: &[ErasedExpr],
        env: &ConstraintEnvironment<'_>,
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
            self.solve_expr(draft, child_id, item, env)?;
        }
        Ok(())
    }

    fn apply_from_scheme(
        &mut self,
        slot: DraftComputationId,
        expected: &MonoComputation,
        scheme: &Scheme,
        arg: &ErasedExpr,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<Option<ApplyComputation>, ConstraintError> {
        if !scheme_needs_instantiation(scheme) {
            return concrete_apply_from_scheme(slot, expected, scheme).map(Some);
        }
        if !scheme_can_be_instantiated_locally(scheme) {
            return Ok(None);
        }
        let Some(instantiated) = self.instantiate_apply_scheme(slot, expected, scheme, arg, env)?
        else {
            return Ok(None);
        };
        concrete_apply_from_scheme(slot, expected, &instantiated).map(Some)
    }

    fn instantiate_apply_scheme(
        &mut self,
        slot: DraftComputationId,
        expected: &MonoComputation,
        scheme: &Scheme,
        arg: &ErasedExpr,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<Option<Scheme>, ConstraintError> {
        let body = self.freshen_scheme_body(scheme);
        let Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } = &body
        else {
            return Ok(None);
        };

        let Some(arg_computation) = known_computation(slot, arg, env)? else {
            return Ok(None);
        };
        let expected_value = value_type(slot, &expected.value)?;
        let expected_effect = expected.effect.row().as_type().clone();
        let arg_value = value_type(slot, &arg_computation.value)?;
        let arg_effect = arg_computation.effect.row().as_type().clone();

        self.constrain_types(arg_value, (**param).clone())?;
        self.constrain_types(arg_effect, (**param_effect).clone())?;
        self.constrain_types((**ret).clone(), expected_value)?;
        self.constrain_types((**ret_effect).clone(), expected_effect)?;
        self.drain_pending_bounds()?;

        let substitution = self.build_substitution(slot, ConstraintTypeSource::BoundsSelection)?;
        let body = substitution.apply_type(&body);
        if ConcreteType::try_from_type(body.clone()).is_err() {
            return Ok(None);
        }
        Ok(Some(Scheme {
            body,
            quantified_types: Vec::new(),
            quantified_effects: Vec::new(),
            quantified_refs: Vec::new(),
            typeclass_obligations: Vec::new(),
            requirements: Vec::new(),
        }))
    }

    fn freshen_scheme_body(&mut self, scheme: &Scheme) -> Type {
        let instantiation = SchemeFreshening::new(self, scheme);
        instantiation.substitute_type(&scheme.body)
    }

    fn fresh_type_var(&mut self, original: &TypeVar) -> TypeVar {
        let id = self.next_type_var;
        self.next_type_var += 1;
        TypeVar(format!("$elab{id}${}", original.0))
    }

    fn assign(
        &mut self,
        slot: DraftComputationId,
        computation: MonoComputation,
    ) -> Result<(), ConstraintError> {
        self.add_exact_computation(slot, computation)?;
        self.drain_pending_bounds()
    }

    fn add_subtype_edge(
        &mut self,
        lower: TypeNode,
        upper: TypeNode,
    ) -> Result<(), ConstraintError> {
        if !self.subtype_edges.insert((lower.clone(), upper.clone())) {
            return Ok(());
        }

        let lower_bounds = self.type_bounds(&lower).lower.clone();
        let upper_bounds = self.type_bounds(&upper).upper.clone();
        for ty in lower_bounds {
            self.add_lower_bound(upper.clone(), ty)?;
        }
        for ty in upper_bounds {
            self.add_upper_bound(lower.clone(), ty)?;
        }
        self.drain_pending_bounds()
    }

    fn add_exact_computation(
        &mut self,
        slot: DraftComputationId,
        computation: MonoComputation,
    ) -> Result<(), ConstraintError> {
        self.add_exact_type(
            TypeNode::value(slot),
            mono_type_to_type(slot, &computation.value)?,
        )?;
        self.add_exact_type(
            TypeNode::effect(slot),
            computation.effect.row().as_type().clone(),
        )
    }

    fn add_exact_type(&mut self, node: TypeNode, ty: Type) -> Result<(), ConstraintError> {
        self.add_subtype_edge(node.clone(), node.clone())?;
        self.add_lower_bound(node.clone(), ty.clone())?;
        self.add_upper_bound(node, ty)
    }

    fn add_lower_bound(&mut self, node: TypeNode, ty: Type) -> Result<(), ConstraintError> {
        let bounds = self.type_bounds_mut(node.clone());
        if bounds.lower.iter().any(|existing| existing == &ty) {
            return Ok(());
        }
        let uppers = bounds.upper.clone();
        bounds.lower.push(ty.clone());
        for upper in uppers {
            self.constrain_types(ty.clone(), upper)?;
        }
        self.pending_bounds.push(PendingBound {
            node,
            kind: BoundKind::Lower,
            ty,
        });
        Ok(())
    }

    fn add_upper_bound(&mut self, node: TypeNode, ty: Type) -> Result<(), ConstraintError> {
        let bounds = self.type_bounds_mut(node.clone());
        if bounds.upper.iter().any(|existing| existing == &ty) {
            return Ok(());
        }
        let lowers = bounds.lower.clone();
        bounds.upper.push(ty.clone());
        for lower in lowers {
            self.constrain_types(lower, ty.clone())?;
        }
        self.pending_bounds.push(PendingBound {
            node,
            kind: BoundKind::Upper,
            ty,
        });
        Ok(())
    }

    fn drain_pending_bounds(&mut self) -> Result<(), ConstraintError> {
        while let Some(bound) = self.pending_bounds.pop() {
            match bound.kind {
                BoundKind::Lower => {
                    let targets = self
                        .subtype_edges
                        .iter()
                        .filter_map(|(lower, upper)| {
                            (lower == &bound.node).then_some(upper.clone())
                        })
                        .collect::<Vec<_>>();
                    for target in targets {
                        self.add_lower_bound(target, bound.ty.clone())?;
                    }
                }
                BoundKind::Upper => {
                    let sources = self
                        .subtype_edges
                        .iter()
                        .filter_map(|(lower, upper)| {
                            (upper == &bound.node).then_some(lower.clone())
                        })
                        .collect::<Vec<_>>();
                    for source in sources {
                        self.add_upper_bound(source, bound.ty.clone())?;
                    }
                }
            }
        }
        Ok(())
    }

    fn constrain_types(&mut self, lower: Type, upper: Type) -> Result<(), ConstraintError> {
        if lower == upper || matches!(lower, Type::Never) || matches!(upper, Type::Any) {
            return Ok(());
        }
        match (lower, upper) {
            (Type::Var(lower), Type::Var(upper)) => {
                self.add_subtype_edge(TypeNode::var(lower), TypeNode::var(upper))
            }
            (Type::Var(var), upper) => self.add_upper_bound(TypeNode::var(var), upper),
            (lower, Type::Var(var)) => self.add_lower_bound(TypeNode::var(var), lower),
            (Type::Union(items), upper) => {
                for item in items {
                    self.constrain_types(item, upper.clone())?;
                }
                Ok(())
            }
            (lower, Type::Inter(items)) => {
                for item in items {
                    self.constrain_types(lower.clone(), item)?;
                }
                Ok(())
            }
            (
                Type::Fun {
                    param: lower_param,
                    param_effect: lower_param_effect,
                    ret_effect: lower_ret_effect,
                    ret: lower_ret,
                },
                Type::Fun {
                    param: upper_param,
                    param_effect: upper_param_effect,
                    ret_effect: upper_ret_effect,
                    ret: upper_ret,
                },
            ) => {
                self.constrain_types(*upper_param, *lower_param)?;
                self.constrain_types(*upper_param_effect, *lower_param_effect)?;
                self.constrain_types(*lower_ret_effect, *upper_ret_effect)?;
                self.constrain_types(*lower_ret, *upper_ret)
            }
            (Type::Tuple(lower_items), Type::Tuple(upper_items))
                if lower_items.len() == upper_items.len() =>
            {
                for (lower, upper) in lower_items.into_iter().zip(upper_items) {
                    self.constrain_types(lower, upper)?;
                }
                Ok(())
            }
            (
                Type::Named {
                    path: lower_path,
                    args: lower_args,
                },
                Type::Named {
                    path: upper_path,
                    args: upper_args,
                },
            ) if lower_path == upper_path && lower_args.len() == upper_args.len() => {
                for (lower, upper) in lower_args.into_iter().zip(upper_args) {
                    self.constrain_type_args(lower, upper)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn constrain_type_args(
        &mut self,
        lower: yulang_erased_ir::TypeArg,
        upper: yulang_erased_ir::TypeArg,
    ) -> Result<(), ConstraintError> {
        match (lower, upper) {
            (yulang_erased_ir::TypeArg::Type(lower), yulang_erased_ir::TypeArg::Type(upper)) => {
                self.constrain_types(lower, upper)
            }
            (
                yulang_erased_ir::TypeArg::Bounds(lower),
                yulang_erased_ir::TypeArg::Bounds(upper),
            ) => {
                let yulang_erased_ir::TypeBounds {
                    lower: lower_lower,
                    upper: lower_upper,
                } = lower;
                let yulang_erased_ir::TypeBounds {
                    lower: upper_lower,
                    upper: upper_upper,
                } = upper;
                if let (Some(lower), Some(upper)) = (lower_lower, upper_lower) {
                    self.constrain_types(*lower, *upper)?;
                }
                if let (Some(lower), Some(upper)) = (lower_upper, upper_upper) {
                    self.constrain_types(*lower, *upper)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn require_assigned(
        &self,
        slot: DraftComputationId,
    ) -> Result<MonoComputation, ConstraintError> {
        let mut substitution =
            self.build_substitution(slot, ConstraintTypeSource::BoundsSelection)?;
        let value_node = TypeNode::value(slot);
        let effect_node = TypeNode::effect(slot);
        let Some(value_bounds) = self.bounds.get(&value_node) else {
            return Err(ConstraintError::MissingComputation { slot: slot.into() });
        };
        let Some(effect_bounds) = self.bounds.get(&effect_node) else {
            return Err(ConstraintError::MissingComputation { slot: slot.into() });
        };
        Ok(MonoComputation {
            value: MonoType::Value(self.select_concrete_type(
                slot,
                value_bounds,
                ConstraintTypeSource::BoundsSelection,
                &mut substitution,
            )?),
            effect: MonoEffect::new(self.select_concrete_type(
                slot,
                effect_bounds,
                ConstraintTypeSource::BoundsSelection,
                &mut substitution,
            )?),
        })
    }

    fn build_substitution(
        &self,
        slot: DraftComputationId,
        source: ConstraintTypeSource,
    ) -> Result<ElaborationSubstitution, ConstraintError> {
        let mut substitution = ElaborationSubstitution::default();
        let vars = self
            .bounds
            .keys()
            .filter_map(|node| match node {
                TypeNode::Var(var) => Some(var.clone()),
                TypeNode::Computation { .. } => None,
            })
            .collect::<Vec<_>>();
        for var in vars {
            self.solve_type_var(slot, &var, source, &mut substitution, &mut BTreeSet::new())?;
        }
        Ok(substitution)
    }

    fn select_concrete_type(
        &self,
        slot: DraftComputationId,
        bounds: &TypeBoundsGraph,
        source: ConstraintTypeSource,
        substitution: &mut ElaborationSubstitution,
    ) -> Result<ConcreteType, ConstraintError> {
        let Some(ty) = self.select_type_candidate_from_bounds(
            slot,
            bounds,
            source,
            substitution,
            &mut BTreeSet::new(),
            &mut BTreeSet::new(),
        )?
        else {
            return Err(ConstraintError::MissingComputation { slot: slot.into() });
        };
        concrete_type(slot, source, ty)
    }

    fn solve_type_var(
        &self,
        slot: DraftComputationId,
        var: &TypeVar,
        source: ConstraintTypeSource,
        substitution: &mut ElaborationSubstitution,
        visiting: &mut BTreeSet<TypeVar>,
    ) -> Result<Option<Type>, ConstraintError> {
        if let Some(solution) = substitution.get(var) {
            return Ok(Some(solution.clone()));
        }
        if !visiting.insert(var.clone()) {
            return Ok(None);
        }
        let node = TypeNode::var(var.clone());
        let out = if let Some(bounds) = self.bounds.get(&node) {
            self.select_type_candidate_from_bounds(
                slot,
                bounds,
                source,
                substitution,
                visiting,
                &mut BTreeSet::new(),
            )?
        } else {
            None
        };
        if let Some(solution) = &out {
            substitution.insert(var.clone(), solution.clone());
        }
        visiting.remove(var);
        Ok(out)
    }

    fn select_type_candidate_from_bounds(
        &self,
        slot: DraftComputationId,
        bounds: &TypeBoundsGraph,
        source: ConstraintTypeSource,
        substitution: &mut ElaborationSubstitution,
        visiting: &mut BTreeSet<TypeVar>,
        shadowed: &mut BTreeSet<TypeVar>,
    ) -> Result<Option<Type>, ConstraintError> {
        let mut candidates = Vec::new();
        for ty in bounds.lower.iter().chain(bounds.upper.iter()) {
            let ty = self.candidate_type(slot, ty, source, substitution, visiting, shadowed)?;
            collect_concrete_candidates(&ty, &mut candidates);
        }
        match candidates.as_slice() {
            [candidate] => Ok(Some(candidate.clone())),
            [] => Ok(None),
            _ => Err(ConstraintError::ConflictingComputation {
                slot: slot.into(),
                existing: MonoComputation {
                    value: MonoType::Value(
                        concrete_type(slot, source, candidates[0].clone())
                            .expect("candidate was collected as concrete"),
                    ),
                    effect: pure_effect(),
                },
                incoming: MonoComputation {
                    value: MonoType::Value(
                        concrete_type(slot, source, candidates[1].clone())
                            .expect("candidate was collected as concrete"),
                    ),
                    effect: pure_effect(),
                },
            }),
        }
    }

    fn candidate_type(
        &self,
        slot: DraftComputationId,
        ty: &Type,
        source: ConstraintTypeSource,
        substitution: &mut ElaborationSubstitution,
        visiting: &mut BTreeSet<TypeVar>,
        shadowed: &mut BTreeSet<TypeVar>,
    ) -> Result<Type, ConstraintError> {
        match ty {
            Type::Var(var) if !shadowed.contains(var) => Ok(self
                .solve_type_var(slot, var, source, substitution, visiting)?
                .unwrap_or_else(|| ty.clone())),
            Type::Named { path, args } => Ok(Type::Named {
                path: path.clone(),
                args: args
                    .iter()
                    .map(|arg| {
                        self.candidate_type_arg(slot, arg, source, substitution, visiting, shadowed)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => Ok(Type::Fun {
                param: Box::new(self.candidate_type(
                    slot,
                    param,
                    source,
                    substitution,
                    visiting,
                    shadowed,
                )?),
                param_effect: Box::new(self.candidate_type(
                    slot,
                    param_effect,
                    source,
                    substitution,
                    visiting,
                    shadowed,
                )?),
                ret_effect: Box::new(self.candidate_type(
                    slot,
                    ret_effect,
                    source,
                    substitution,
                    visiting,
                    shadowed,
                )?),
                ret: Box::new(self.candidate_type(
                    slot,
                    ret,
                    source,
                    substitution,
                    visiting,
                    shadowed,
                )?),
            }),
            Type::Tuple(items) => Ok(Type::Tuple(
                items
                    .iter()
                    .map(|item| {
                        self.candidate_type(slot, item, source, substitution, visiting, shadowed)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Type::Record(record) => Ok(Type::Record(yulang_erased_ir::RecordType {
                fields: record
                    .fields
                    .iter()
                    .map(|field| {
                        Ok(yulang_erased_ir::RecordField {
                            name: field.name.clone(),
                            value: self.candidate_type(
                                slot,
                                &field.value,
                                source,
                                substitution,
                                visiting,
                                shadowed,
                            )?,
                            optional: field.optional,
                        })
                    })
                    .collect::<Result<Vec<_>, ConstraintError>>()?,
                spread: record
                    .spread
                    .as_ref()
                    .map(|spread| match spread {
                        yulang_erased_ir::RecordSpread::Head(ty) => self
                            .candidate_type(slot, ty, source, substitution, visiting, shadowed)
                            .map(Box::new)
                            .map(yulang_erased_ir::RecordSpread::Head),
                        yulang_erased_ir::RecordSpread::Tail(ty) => self
                            .candidate_type(slot, ty, source, substitution, visiting, shadowed)
                            .map(Box::new)
                            .map(yulang_erased_ir::RecordSpread::Tail),
                    })
                    .transpose()?,
            })),
            Type::Variant(variant) => Ok(Type::Variant(yulang_erased_ir::VariantType {
                cases: variant
                    .cases
                    .iter()
                    .map(|case| {
                        Ok(yulang_erased_ir::VariantCase {
                            name: case.name.clone(),
                            payloads: case
                                .payloads
                                .iter()
                                .map(|payload| {
                                    self.candidate_type(
                                        slot,
                                        payload,
                                        source,
                                        substitution,
                                        visiting,
                                        shadowed,
                                    )
                                })
                                .collect::<Result<Vec<_>, _>>()?,
                        })
                    })
                    .collect::<Result<Vec<_>, ConstraintError>>()?,
                tail: variant
                    .tail
                    .as_ref()
                    .map(|tail| {
                        self.candidate_type(slot, tail, source, substitution, visiting, shadowed)
                            .map(Box::new)
                    })
                    .transpose()?,
            })),
            Type::Row { items, tail } => Ok(Type::Row {
                items: items
                    .iter()
                    .map(|item| {
                        self.candidate_type(slot, item, source, substitution, visiting, shadowed)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                tail: Box::new(self.candidate_type(
                    slot,
                    tail,
                    source,
                    substitution,
                    visiting,
                    shadowed,
                )?),
            }),
            Type::Union(items) => Ok(Type::Union(
                items
                    .iter()
                    .map(|item| {
                        self.candidate_type(slot, item, source, substitution, visiting, shadowed)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Type::Inter(items) => Ok(Type::Inter(
                items
                    .iter()
                    .map(|item| {
                        self.candidate_type(slot, item, source, substitution, visiting, shadowed)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Type::Recursive { var, body } => {
                let inserted = shadowed.insert(var.clone());
                let body =
                    self.candidate_type(slot, body, source, substitution, visiting, shadowed);
                if inserted {
                    shadowed.remove(var);
                }
                Ok(Type::Recursive {
                    var: var.clone(),
                    body: Box::new(body?),
                })
            }
            Type::Var(_) | Type::Unknown | Type::Never | Type::Any => Ok(ty.clone()),
        }
    }

    fn candidate_type_arg(
        &self,
        slot: DraftComputationId,
        arg: &yulang_erased_ir::TypeArg,
        source: ConstraintTypeSource,
        substitution: &mut ElaborationSubstitution,
        visiting: &mut BTreeSet<TypeVar>,
        shadowed: &mut BTreeSet<TypeVar>,
    ) -> Result<yulang_erased_ir::TypeArg, ConstraintError> {
        match arg {
            yulang_erased_ir::TypeArg::Type(ty) => Ok(yulang_erased_ir::TypeArg::Type(
                self.candidate_type(slot, ty, source, substitution, visiting, shadowed)?,
            )),
            yulang_erased_ir::TypeArg::Bounds(bounds) => Ok(yulang_erased_ir::TypeArg::Bounds(
                yulang_erased_ir::TypeBounds {
                    lower: bounds
                        .lower
                        .as_ref()
                        .map(|lower| {
                            self.candidate_type(
                                slot,
                                lower,
                                source,
                                substitution,
                                visiting,
                                shadowed,
                            )
                            .map(Box::new)
                        })
                        .transpose()?,
                    upper: bounds
                        .upper
                        .as_ref()
                        .map(|upper| {
                            self.candidate_type(
                                slot,
                                upper,
                                source,
                                substitution,
                                visiting,
                                shadowed,
                            )
                            .map(Box::new)
                        })
                        .transpose()?,
                },
            )),
        }
    }

    fn type_bounds(&self, node: &TypeNode) -> TypeBoundsGraph {
        self.bounds.get(node).cloned().unwrap_or_default()
    }

    fn type_bounds_mut(&mut self, node: TypeNode) -> &mut TypeBoundsGraph {
        self.bounds.entry(node).or_default()
    }
}

#[derive(Debug, Clone, Default)]
struct TypeBoundsGraph {
    lower: Vec<Type>,
    upper: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum TypeNode {
    Computation {
        slot: DraftComputationId,
        kind: TypeNodeKind,
    },
    Var(TypeVar),
}

impl TypeNode {
    fn value(slot: DraftComputationId) -> Self {
        Self::Computation {
            slot,
            kind: TypeNodeKind::Value,
        }
    }

    fn effect(slot: DraftComputationId) -> Self {
        Self::Computation {
            slot,
            kind: TypeNodeKind::Effect,
        }
    }

    fn var(var: TypeVar) -> Self {
        Self::Var(var)
    }

    fn computation_slot(&self) -> Option<DraftComputationId> {
        match self {
            Self::Computation { slot, .. } => Some(*slot),
            Self::Var(_) => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum TypeNodeKind {
    Value,
    Effect,
}

#[derive(Debug, Clone)]
struct PendingBound {
    node: TypeNode,
    kind: BoundKind,
    ty: Type,
}

#[derive(Debug, Clone, Copy)]
enum BoundKind {
    Lower,
    Upper,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ElaborationSubstitution {
    types: BTreeMap<TypeVar, Type>,
}

impl ElaborationSubstitution {
    fn get(&self, var: &TypeVar) -> Option<&Type> {
        self.types.get(var)
    }

    fn insert(&mut self, var: TypeVar, ty: Type) {
        self.types.insert(var, ty);
    }

    fn apply_type(&self, ty: &Type) -> Type {
        self.apply_type_inner(ty, &mut BTreeSet::new())
    }

    fn apply_type_inner(&self, ty: &Type, shadowed: &mut BTreeSet<TypeVar>) -> Type {
        match ty {
            Type::Var(var) if !shadowed.contains(var) => {
                self.types.get(var).cloned().unwrap_or_else(|| ty.clone())
            }
            Type::Named { path, args } => Type::Named {
                path: path.clone(),
                args: args
                    .iter()
                    .map(|arg| self.apply_type_arg(arg, shadowed))
                    .collect(),
            },
            Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => Type::Fun {
                param: Box::new(self.apply_type_inner(param, shadowed)),
                param_effect: Box::new(self.apply_type_inner(param_effect, shadowed)),
                ret_effect: Box::new(self.apply_type_inner(ret_effect, shadowed)),
                ret: Box::new(self.apply_type_inner(ret, shadowed)),
            },
            Type::Tuple(items) => Type::Tuple(
                items
                    .iter()
                    .map(|item| self.apply_type_inner(item, shadowed))
                    .collect(),
            ),
            Type::Record(record) => Type::Record(yulang_erased_ir::RecordType {
                fields: record
                    .fields
                    .iter()
                    .map(|field| yulang_erased_ir::RecordField {
                        name: field.name.clone(),
                        value: self.apply_type_inner(&field.value, shadowed),
                        optional: field.optional,
                    })
                    .collect(),
                spread: record.spread.as_ref().map(|spread| match spread {
                    yulang_erased_ir::RecordSpread::Head(ty) => {
                        yulang_erased_ir::RecordSpread::Head(Box::new(
                            self.apply_type_inner(ty, shadowed),
                        ))
                    }
                    yulang_erased_ir::RecordSpread::Tail(ty) => {
                        yulang_erased_ir::RecordSpread::Tail(Box::new(
                            self.apply_type_inner(ty, shadowed),
                        ))
                    }
                }),
            }),
            Type::Variant(variant) => Type::Variant(yulang_erased_ir::VariantType {
                cases: variant
                    .cases
                    .iter()
                    .map(|case| yulang_erased_ir::VariantCase {
                        name: case.name.clone(),
                        payloads: case
                            .payloads
                            .iter()
                            .map(|payload| self.apply_type_inner(payload, shadowed))
                            .collect(),
                    })
                    .collect(),
                tail: variant
                    .tail
                    .as_ref()
                    .map(|tail| Box::new(self.apply_type_inner(tail, shadowed))),
            }),
            Type::Row { items, tail } => Type::Row {
                items: items
                    .iter()
                    .map(|item| self.apply_type_inner(item, shadowed))
                    .collect(),
                tail: Box::new(self.apply_type_inner(tail, shadowed)),
            },
            Type::Union(items) => Type::Union(
                items
                    .iter()
                    .map(|item| self.apply_type_inner(item, shadowed))
                    .collect(),
            ),
            Type::Inter(items) => Type::Inter(
                items
                    .iter()
                    .map(|item| self.apply_type_inner(item, shadowed))
                    .collect(),
            ),
            Type::Recursive { var, body } => {
                let inserted = shadowed.insert(var.clone());
                let body = self.apply_type_inner(body, shadowed);
                if inserted {
                    shadowed.remove(var);
                }
                Type::Recursive {
                    var: var.clone(),
                    body: Box::new(body),
                }
            }
            Type::Var(_) | Type::Unknown | Type::Never | Type::Any => ty.clone(),
        }
    }

    fn apply_type_arg(
        &self,
        arg: &yulang_erased_ir::TypeArg,
        shadowed: &mut BTreeSet<TypeVar>,
    ) -> yulang_erased_ir::TypeArg {
        match arg {
            yulang_erased_ir::TypeArg::Type(ty) => {
                yulang_erased_ir::TypeArg::Type(self.apply_type_inner(ty, shadowed))
            }
            yulang_erased_ir::TypeArg::Bounds(bounds) => {
                yulang_erased_ir::TypeArg::Bounds(yulang_erased_ir::TypeBounds {
                    lower: bounds
                        .lower
                        .as_ref()
                        .map(|lower| Box::new(self.apply_type_inner(lower, shadowed))),
                    upper: bounds
                        .upper
                        .as_ref()
                        .map(|upper| Box::new(self.apply_type_inner(upper, shadowed))),
                })
            }
        }
    }
}

struct SchemeFreshening {
    substitution: ElaborationSubstitution,
}

impl SchemeFreshening {
    fn new(solver: &mut ConstraintSolver, scheme: &Scheme) -> Self {
        let mut substitution = ElaborationSubstitution::default();
        for var in &scheme.quantified_types {
            substitution.insert(var.clone(), Type::Var(solver.fresh_type_var(var)));
        }
        for var in &scheme.quantified_effects {
            let var = TypeVar(var.0.clone());
            substitution.insert(var.clone(), Type::Var(solver.fresh_type_var(&var)));
        }
        Self { substitution }
    }

    fn substitute_type(&self, ty: &Type) -> Type {
        self.substitution.apply_type(ty)
    }
}

struct ApplyComputation {
    callee: MonoComputation,
    arg: MonoComputation,
}

fn concrete_apply_from_scheme(
    slot: DraftComputationId,
    expected: &MonoComputation,
    scheme: &Scheme,
) -> Result<ApplyComputation, ConstraintError> {
    let Type::Fun {
        param,
        param_effect,
        ret_effect,
        ret,
    } = &scheme.body
    else {
        return Err(ConstraintError::ExpectedFunction {
            slot: slot.into(),
            found: MonoType::Value(concrete_type(
                slot,
                ConstraintTypeSource::FunctionParam,
                scheme.body.clone(),
            )?),
        });
    };

    let actual_result = MonoComputation {
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
    if &actual_result != expected {
        return Err(ConstraintError::FunctionResultMismatch {
            slot: slot.into(),
            expected: expected.clone(),
            actual: actual_result,
        });
    }

    Ok(ApplyComputation {
        callee: function_computation(
            slot,
            (**param).clone(),
            (**param_effect).clone(),
            (**ret_effect).clone(),
            (**ret).clone(),
        )?,
        arg: MonoComputation {
            value: MonoType::Value(concrete_type(
                slot,
                ConstraintTypeSource::FunctionParam,
                (**param).clone(),
            )?),
            effect: MonoEffect::new(concrete_type(
                slot,
                ConstraintTypeSource::FunctionParamEffect,
                (**param_effect).clone(),
            )?),
        },
    })
}

fn scheme_can_be_instantiated_locally(scheme: &Scheme) -> bool {
    scheme.quantified_refs.is_empty()
        && scheme.typeclass_obligations.is_empty()
        && scheme.requirements.is_empty()
}

fn function_computation(
    slot: DraftComputationId,
    param: Type,
    param_effect: Type,
    ret_effect: Type,
    ret: Type,
) -> Result<MonoComputation, ConstraintError> {
    Ok(MonoComputation {
        value: MonoType::Value(concrete_type(
            slot,
            ConstraintTypeSource::FunctionParam,
            Type::Fun {
                param: Box::new(param),
                param_effect: Box::new(param_effect),
                ret_effect: Box::new(ret_effect),
                ret: Box::new(ret),
            },
        )?),
        effect: pure_effect(),
    })
}

pub(crate) fn scheme_needs_instantiation(scheme: &Scheme) -> bool {
    scheme
        .quantified_types
        .iter()
        .any(|var| type_mentions_type_var(&scheme.body, var))
        || scheme
            .quantified_effects
            .iter()
            .any(|var| type_mentions_var_name(&scheme.body, &var.0))
        || !scheme.quantified_refs.is_empty()
        || !scheme.typeclass_obligations.is_empty()
        || !scheme.requirements.is_empty()
}

pub(crate) fn direct_apply_ret_effect_from_scheme(
    scheme: &Scheme,
    result_value: &Type,
    arg: &ErasedExpr,
    env: &ConstraintEnvironment<'_>,
) -> Option<Type> {
    let Type::Fun {
        param,
        param_effect,
        ret_effect,
        ret,
    } = &scheme.body
    else {
        return None;
    };
    if !scheme_needs_instantiation(scheme) {
        return Some((**ret_effect).clone());
    }
    if !scheme_can_be_instantiated_locally(scheme) {
        return None;
    }
    let arg_value = known_value_type(arg, env)?;
    let mut instantiation = TypeInstantiation::new(scheme);
    if !instantiation.match_type(param, &arg_value)
        || !instantiation.match_type(param_effect, &Type::Never)
        || !instantiation.match_type(ret, result_value)
    {
        return None;
    }
    let ret_effect = instantiation.substitute_type(ret_effect);
    (!scheme_quantified_vars_appear_in_type(scheme, &ret_effect)).then_some(ret_effect)
}

fn type_mentions_type_var(ty: &Type, target: &yulang_erased_ir::TypeVar) -> bool {
    match ty {
        Type::Var(var) => var == target,
        Type::Named { args, .. } => args
            .iter()
            .any(|arg| type_arg_mentions_type_var(arg, target)),
        Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            type_mentions_type_var(param, target)
                || type_mentions_type_var(param_effect, target)
                || type_mentions_type_var(ret_effect, target)
                || type_mentions_type_var(ret, target)
        }
        Type::Tuple(items) | Type::Union(items) | Type::Inter(items) => items
            .iter()
            .any(|item| type_mentions_type_var(item, target)),
        Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| type_mentions_type_var(&field.value, target))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    yulang_erased_ir::RecordSpread::Head(ty)
                    | yulang_erased_ir::RecordSpread::Tail(ty) => {
                        type_mentions_type_var(ty, target)
                    }
                })
        }
        Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .flat_map(|case| &case.payloads)
                .any(|payload| type_mentions_type_var(payload, target))
                || variant
                    .tail
                    .as_ref()
                    .is_some_and(|tail| type_mentions_type_var(tail, target))
        }
        Type::Row { items, tail } => {
            items
                .iter()
                .any(|item| type_mentions_type_var(item, target))
                || type_mentions_type_var(tail, target)
        }
        Type::Recursive { var, body } => var != target && type_mentions_type_var(body, target),
        Type::Unknown | Type::Never | Type::Any => false,
    }
}

fn type_arg_mentions_type_var(
    arg: &yulang_erased_ir::TypeArg,
    target: &yulang_erased_ir::TypeVar,
) -> bool {
    match arg {
        yulang_erased_ir::TypeArg::Type(ty) => type_mentions_type_var(ty, target),
        yulang_erased_ir::TypeArg::Bounds(bounds) => type_bounds_mentions_type_var(bounds, target),
    }
}

fn type_bounds_mentions_type_var(
    bounds: &yulang_erased_ir::TypeBounds,
    target: &yulang_erased_ir::TypeVar,
) -> bool {
    bounds
        .lower
        .as_ref()
        .is_some_and(|lower| type_mentions_type_var(lower, target))
        || bounds
            .upper
            .as_ref()
            .is_some_and(|upper| type_mentions_type_var(upper, target))
}

fn type_mentions_var_name(ty: &Type, target: &str) -> bool {
    type_mentions_type_var(ty, &yulang_erased_ir::TypeVar(target.to_string()))
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

fn known_computation(
    slot: DraftComputationId,
    expr: &ErasedExpr,
    env: &ConstraintEnvironment<'_>,
) -> Result<Option<MonoComputation>, ConstraintError> {
    let Some(ty) = known_value_type(expr, env) else {
        return Ok(None);
    };
    Ok(Some(MonoComputation {
        value: MonoType::Value(concrete_type(slot, ConstraintTypeSource::Literal, ty)?),
        effect: pure_effect(),
    }))
}

fn known_value_type(expr: &ErasedExpr, env: &ConstraintEnvironment<'_>) -> Option<Type> {
    match expr {
        ErasedExpr::Lit(lit) => Some(literal_type(lit)),
        ErasedExpr::Tuple(items) => items
            .iter()
            .map(|item| known_value_type(item, env))
            .collect::<Option<Vec<_>>>()
            .map(Type::Tuple),
        ErasedExpr::Ref(ref_id) => {
            let (_, scheme) = env.direct_scheme(*ref_id)?;
            if scheme_needs_instantiation(scheme)
                || ConcreteType::try_from_type(scheme.body.clone()).is_err()
            {
                return None;
            }
            Some(scheme.body.clone())
        }
        _ => None,
    }
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

fn mono_type_to_type(slot: DraftComputationId, typ: &MonoType) -> Result<Type, ConstraintError> {
    match typ {
        MonoType::Value(value) => Ok(value.as_type().clone()),
        MonoType::EffectiveThunk(_) => Err(ConstraintError::ExpectedValue {
            slot: slot.into(),
            found: typ.clone(),
        }),
    }
}

fn collect_concrete_candidates(ty: &Type, candidates: &mut Vec<Type>) {
    if ConcreteType::try_from_type(ty.clone()).is_ok() {
        push_unique_candidate(candidates, ty.clone());
        return;
    }
    match ty {
        Type::Union(items) | Type::Inter(items) => {
            for item in items {
                collect_concrete_candidates(item, candidates);
            }
        }
        Type::Unknown
        | Type::Never
        | Type::Any
        | Type::Var(_)
        | Type::Named { .. }
        | Type::Fun { .. }
        | Type::Tuple(_)
        | Type::Record(_)
        | Type::Variant(_)
        | Type::Row { .. }
        | Type::Recursive { .. } => {}
    }
}

fn push_unique_candidate(candidates: &mut Vec<Type>, candidate: Type) {
    if !candidates.iter().any(|existing| existing == &candidate) {
        candidates.push(candidate);
    }
}

fn effect_is_pure(effect: &MonoEffect) -> bool {
    matches!(effect.row().as_type(), Type::Never)
}

fn pure_effect() -> MonoEffect {
    MonoEffect::new(ConcreteType::try_from_type(Type::Never).expect("Never is concrete"))
}

#[derive(Default)]
struct TypeInstantiation {
    quantifiable: BTreeSet<yulang_erased_ir::TypeVar>,
    assignments: BTreeMap<yulang_erased_ir::TypeVar, Type>,
}

impl TypeInstantiation {
    fn new(scheme: &Scheme) -> Self {
        let mut quantifiable = scheme
            .quantified_types
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();
        quantifiable.extend(
            scheme
                .quantified_effects
                .iter()
                .map(|var| yulang_erased_ir::TypeVar(var.0.clone())),
        );
        Self {
            quantifiable,
            assignments: BTreeMap::new(),
        }
    }

    fn match_type(&mut self, pattern: &Type, actual: &Type) -> bool {
        match pattern {
            Type::Var(var) if self.quantifiable.contains(var) => {
                self.assign(var.clone(), actual.clone())
            }
            Type::Named { path, args } => {
                let Type::Named {
                    path: actual_path,
                    args: actual_args,
                } = actual
                else {
                    return false;
                };
                path == actual_path
                    && args.len() == actual_args.len()
                    && args
                        .iter()
                        .zip(actual_args)
                        .all(|(pattern, actual)| self.match_type_arg(pattern, actual))
            }
            Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => {
                let Type::Fun {
                    param: actual_param,
                    param_effect: actual_param_effect,
                    ret_effect: actual_ret_effect,
                    ret: actual_ret,
                } = actual
                else {
                    return false;
                };
                self.match_type(param, actual_param)
                    && self.match_type(param_effect, actual_param_effect)
                    && self.match_type(ret_effect, actual_ret_effect)
                    && self.match_type(ret, actual_ret)
            }
            Type::Tuple(items) => {
                let Type::Tuple(actual_items) = actual else {
                    return false;
                };
                items.len() == actual_items.len()
                    && items
                        .iter()
                        .zip(actual_items)
                        .all(|(pattern, actual)| self.match_type(pattern, actual))
            }
            Type::Record(record) => {
                let Type::Record(actual_record) = actual else {
                    return false;
                };
                record.fields.len() == actual_record.fields.len()
                    && record.spread.is_none() == actual_record.spread.is_none()
                    && record
                        .fields
                        .iter()
                        .zip(&actual_record.fields)
                        .all(|(pattern, actual)| {
                            pattern.name == actual.name
                                && pattern.optional == actual.optional
                                && self.match_type(&pattern.value, &actual.value)
                        })
                    && match (&record.spread, &actual_record.spread) {
                        (Some(pattern), Some(actual)) => self.match_record_spread(pattern, actual),
                        (None, None) => true,
                        _ => false,
                    }
            }
            Type::Variant(variant) => {
                let Type::Variant(actual_variant) = actual else {
                    return false;
                };
                variant.cases.len() == actual_variant.cases.len()
                    && variant.tail.is_none() == actual_variant.tail.is_none()
                    && variant
                        .cases
                        .iter()
                        .zip(&actual_variant.cases)
                        .all(|(pattern, actual)| {
                            pattern.name == actual.name
                                && pattern.payloads.len() == actual.payloads.len()
                                && pattern
                                    .payloads
                                    .iter()
                                    .zip(&actual.payloads)
                                    .all(|(pattern, actual)| self.match_type(pattern, actual))
                        })
                    && match (&variant.tail, &actual_variant.tail) {
                        (Some(pattern), Some(actual)) => self.match_type(pattern, actual),
                        (None, None) => true,
                        _ => false,
                    }
            }
            Type::Row { items, tail } => {
                let Type::Row {
                    items: actual_items,
                    tail: actual_tail,
                } = actual
                else {
                    return false;
                };
                items.len() == actual_items.len()
                    && items
                        .iter()
                        .zip(actual_items)
                        .all(|(pattern, actual)| self.match_type(pattern, actual))
                    && self.match_type(tail, actual_tail)
            }
            Type::Union(items) => self.match_variadic_type(items, actual, TypeVariant::Union),
            Type::Inter(items) => self.match_variadic_type(items, actual, TypeVariant::Inter),
            Type::Recursive { var, body } => {
                let Type::Recursive {
                    var: actual_var,
                    body: actual_body,
                } = actual
                else {
                    return false;
                };
                var == actual_var
                    && self.without_var(var, |this| this.match_type(body, actual_body))
            }
            Type::Unknown | Type::Never | Type::Any | Type::Var(_) => pattern == actual,
        }
    }

    fn match_type_arg(
        &mut self,
        pattern: &yulang_erased_ir::TypeArg,
        actual: &yulang_erased_ir::TypeArg,
    ) -> bool {
        match (pattern, actual) {
            (yulang_erased_ir::TypeArg::Type(pattern), yulang_erased_ir::TypeArg::Type(actual)) => {
                self.match_type(pattern, actual)
            }
            (
                yulang_erased_ir::TypeArg::Bounds(pattern),
                yulang_erased_ir::TypeArg::Bounds(actual),
            ) => self.match_type_bounds(pattern, actual),
            _ => false,
        }
    }

    fn match_type_bounds(
        &mut self,
        pattern: &yulang_erased_ir::TypeBounds,
        actual: &yulang_erased_ir::TypeBounds,
    ) -> bool {
        match (&pattern.lower, &actual.lower) {
            (Some(pattern), Some(actual)) if !self.match_type(pattern, actual) => return false,
            (None, None) | (Some(_), Some(_)) => {}
            _ => return false,
        }
        match (&pattern.upper, &actual.upper) {
            (Some(pattern), Some(actual)) if !self.match_type(pattern, actual) => return false,
            (None, None) | (Some(_), Some(_)) => {}
            _ => return false,
        }
        true
    }

    fn match_record_spread(
        &mut self,
        pattern: &yulang_erased_ir::RecordSpread,
        actual: &yulang_erased_ir::RecordSpread,
    ) -> bool {
        match (pattern, actual) {
            (
                yulang_erased_ir::RecordSpread::Head(pattern),
                yulang_erased_ir::RecordSpread::Head(actual),
            )
            | (
                yulang_erased_ir::RecordSpread::Tail(pattern),
                yulang_erased_ir::RecordSpread::Tail(actual),
            ) => self.match_type(pattern, actual),
            _ => false,
        }
    }

    fn match_variadic_type(&mut self, items: &[Type], actual: &Type, variant: TypeVariant) -> bool {
        let actual_items = match (variant, actual) {
            (TypeVariant::Union, Type::Union(items)) | (TypeVariant::Inter, Type::Inter(items)) => {
                items
            }
            _ => return false,
        };
        items.len() == actual_items.len()
            && items
                .iter()
                .zip(actual_items)
                .all(|(pattern, actual)| self.match_type(pattern, actual))
    }

    fn assign(&mut self, var: yulang_erased_ir::TypeVar, actual: Type) -> bool {
        if let Some(existing) = self.assignments.get(&var) {
            return existing == &actual;
        }
        self.assignments.insert(var, actual);
        true
    }

    fn substitute_type(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(var) => self
                .assignments
                .get(var)
                .cloned()
                .unwrap_or_else(|| ty.clone()),
            Type::Named { path, args } => Type::Named {
                path: path.clone(),
                args: args
                    .iter()
                    .map(|arg| self.substitute_type_arg(arg))
                    .collect(),
            },
            Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => Type::Fun {
                param: Box::new(self.substitute_type(param)),
                param_effect: Box::new(self.substitute_type(param_effect)),
                ret_effect: Box::new(self.substitute_type(ret_effect)),
                ret: Box::new(self.substitute_type(ret)),
            },
            Type::Tuple(items) => Type::Tuple(
                items
                    .iter()
                    .map(|item| self.substitute_type(item))
                    .collect(),
            ),
            Type::Record(record) => Type::Record(yulang_erased_ir::RecordType {
                fields: record
                    .fields
                    .iter()
                    .map(|field| yulang_erased_ir::RecordField {
                        name: field.name.clone(),
                        value: self.substitute_type(&field.value),
                        optional: field.optional,
                    })
                    .collect(),
                spread: record.spread.as_ref().map(|spread| match spread {
                    yulang_erased_ir::RecordSpread::Head(ty) => {
                        yulang_erased_ir::RecordSpread::Head(Box::new(self.substitute_type(ty)))
                    }
                    yulang_erased_ir::RecordSpread::Tail(ty) => {
                        yulang_erased_ir::RecordSpread::Tail(Box::new(self.substitute_type(ty)))
                    }
                }),
            }),
            Type::Variant(variant) => Type::Variant(yulang_erased_ir::VariantType {
                cases: variant
                    .cases
                    .iter()
                    .map(|case| yulang_erased_ir::VariantCase {
                        name: case.name.clone(),
                        payloads: case
                            .payloads
                            .iter()
                            .map(|payload| self.substitute_type(payload))
                            .collect(),
                    })
                    .collect(),
                tail: variant
                    .tail
                    .as_ref()
                    .map(|tail| Box::new(self.substitute_type(tail))),
            }),
            Type::Row { items, tail } => Type::Row {
                items: items
                    .iter()
                    .map(|item| self.substitute_type(item))
                    .collect(),
                tail: Box::new(self.substitute_type(tail)),
            },
            Type::Union(items) => Type::Union(
                items
                    .iter()
                    .map(|item| self.substitute_type(item))
                    .collect(),
            ),
            Type::Inter(items) => Type::Inter(
                items
                    .iter()
                    .map(|item| self.substitute_type(item))
                    .collect(),
            ),
            Type::Recursive { var, body } => Type::Recursive {
                var: var.clone(),
                body: Box::new(self.substitute_type_under_binder(var, body)),
            },
            Type::Unknown | Type::Never | Type::Any => ty.clone(),
        }
    }

    fn substitute_type_arg(&self, arg: &yulang_erased_ir::TypeArg) -> yulang_erased_ir::TypeArg {
        match arg {
            yulang_erased_ir::TypeArg::Type(ty) => {
                yulang_erased_ir::TypeArg::Type(self.substitute_type(ty))
            }
            yulang_erased_ir::TypeArg::Bounds(bounds) => {
                yulang_erased_ir::TypeArg::Bounds(yulang_erased_ir::TypeBounds {
                    lower: bounds
                        .lower
                        .as_ref()
                        .map(|lower| Box::new(self.substitute_type(lower))),
                    upper: bounds
                        .upper
                        .as_ref()
                        .map(|upper| Box::new(self.substitute_type(upper))),
                })
            }
        }
    }

    fn substitute_type_under_binder(&self, var: &yulang_erased_ir::TypeVar, body: &Type) -> Type {
        let mut nested = Self {
            quantifiable: self.quantifiable.clone(),
            assignments: self.assignments.clone(),
        };
        nested.quantifiable.remove(var);
        nested.assignments.remove(var);
        nested.substitute_type(body)
    }

    fn without_var<T>(
        &mut self,
        var: &yulang_erased_ir::TypeVar,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let removed_assignment = self.assignments.remove(var);
        let removed_quantifiable = self.quantifiable.remove(var);
        let out = f(self);
        if let Some(assignment) = removed_assignment {
            self.assignments.insert(var.clone(), assignment);
        }
        if removed_quantifiable {
            self.quantifiable.insert(var.clone());
        }
        out
    }
}

#[derive(Clone, Copy)]
enum TypeVariant {
    Union,
    Inter,
}

fn scheme_quantified_vars_appear_in_type(scheme: &Scheme, ty: &Type) -> bool {
    scheme
        .quantified_types
        .iter()
        .any(|var| type_mentions_type_var(ty, var))
        || scheme
            .quantified_effects
            .iter()
            .any(|var| type_mentions_var_name(ty, &var.0))
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

    #[test]
    fn subtype_edges_propagate_lower_and_upper_bounds() {
        let mut solver = empty_solver();
        let alpha = TypeNode::var(TypeVar("alpha".to_string()));
        let beta = TypeNode::var(TypeVar("beta".to_string()));
        let int = named_type("int");

        solver
            .add_subtype_edge(alpha.clone(), beta.clone())
            .expect("add subtype edge");
        solver
            .add_lower_bound(alpha.clone(), int.clone())
            .expect("add lower bound");
        solver
            .add_upper_bound(beta.clone(), int.clone())
            .expect("add upper bound");
        solver.drain_pending_bounds().expect("drain bounds");

        assert_eq!(solver.type_bounds(&beta).lower, vec![int.clone()]);
        assert_eq!(solver.type_bounds(&alpha).upper, vec![int]);
    }

    #[test]
    fn generic_apply_instantiation_solves_type_var_from_bounds() {
        let mut solver = empty_solver();
        let refs = RefExportTable::default();
        let env = ConstraintEnvironment::new(&refs, &[]);
        let var = TypeVar("a".to_string());
        let int = named_type("int");
        let scheme = Scheme {
            body: Type::Fun {
                param: Box::new(Type::Var(var.clone())),
                param_effect: Box::new(Type::Never),
                ret_effect: Box::new(Type::Never),
                ret: Box::new(Type::Var(var)),
            },
            quantified_types: vec![TypeVar("a".to_string())],
            quantified_effects: Vec::new(),
            quantified_refs: Vec::new(),
            typeclass_obligations: Vec::new(),
            requirements: Vec::new(),
        };
        let expected = int_computation();

        let apply = solver
            .apply_from_scheme(
                DraftComputationId(0),
                &expected,
                &scheme,
                &ErasedExpr::Lit(Lit::Int("1".to_string())),
                &env,
            )
            .expect("instantiate scheme")
            .expect("scheme should be concrete enough");

        assert_eq!(
            apply.callee.value,
            MonoType::Value(
                ConcreteType::try_from_type(Type::Fun {
                    param: Box::new(int.clone()),
                    param_effect: Box::new(Type::Never),
                    ret_effect: Box::new(Type::Never),
                    ret: Box::new(int.clone()),
                })
                .expect("function is concrete")
            )
        );
        assert_eq!(apply.arg.value, MonoType::Value(concrete_named("int")));
    }

    #[test]
    fn bounds_solution_builds_explicit_substitution_before_rewriting_type() {
        let mut solver = empty_solver();
        let alpha = TypeVar("alpha".to_string());
        let int = named_type("int");
        solver
            .add_lower_bound(TypeNode::var(alpha.clone()), int.clone())
            .expect("add lower");
        solver
            .add_upper_bound(TypeNode::var(alpha.clone()), int.clone())
            .expect("add upper");

        let substitution = solver
            .build_substitution(DraftComputationId(0), ConstraintTypeSource::BoundsSelection)
            .expect("build substitution");

        assert_eq!(substitution.get(&alpha), Some(&int));
        assert_eq!(
            substitution.apply_type(&Type::Fun {
                param: Box::new(Type::Var(alpha.clone())),
                param_effect: Box::new(Type::Never),
                ret_effect: Box::new(Type::Never),
                ret: Box::new(Type::Var(alpha)),
            }),
            Type::Fun {
                param: Box::new(int.clone()),
                param_effect: Box::new(Type::Never),
                ret_effect: Box::new(Type::Never),
                ret: Box::new(int),
            }
        );
    }

    fn empty_solver() -> ConstraintSolver {
        ConstraintSolver {
            bounds: BTreeMap::new(),
            pending_bounds: Vec::new(),
            subtype_edges: BTreeSet::new(),
            next_type_var: 0,
            direct_ref_instances: BTreeMap::new(),
            resolved_typeclass_instances: BTreeMap::new(),
        }
    }

    fn int_computation() -> MonoComputation {
        MonoComputation {
            value: MonoType::Value(concrete_named("int")),
            effect: MonoEffect::new(
                ConcreteType::try_from_type(Type::Never).expect("Never is concrete"),
            ),
        }
    }

    fn named_type(name: &str) -> Type {
        Type::Named {
            path: Path::from_name(Name(name.to_string())),
            args: Vec::new(),
        }
    }

    fn concrete_named(name: &str) -> ConcreteType {
        ConcreteType::try_from_type(named_type(name)).expect("named type is concrete")
    }
}
