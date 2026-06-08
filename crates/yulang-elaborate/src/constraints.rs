use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::ErasedExprKind;
use crate::draft::{DraftComputationId, DraftExprId, ElaborationDraft};

use yulang_elaborated_ir::{
    ConcreteType, ConcreteTypeError, EffectiveThunkType, MonoComputation, MonoEffect, MonoType,
};
use yulang_erased_ir::{
    DefId, EnumVariantGraphNode, ErasedExpr, InferredBinding, Lit, Name, Path, RefExportTable,
    RefId, ResolvedTypeClassRef, RoleRequirement, RoleRequirementArg, Scheme, Type, TypeArg,
    TypeBounds, TypeClassImplCandidate, TypeClassObligation, TypeVar,
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
    schemes_by_path: Vec<(Path, DefId, &'a Scheme)>,
    effect_operation_schemes: Vec<(Path, &'a Scheme)>,
    enum_variants: HashMap<(Path, Name), &'a EnumVariantGraphNode>,
    typeclass_obligations: BTreeMap<RefId, TypeClassObligation>,
}

impl<'a> ConstraintEnvironment<'a> {
    pub(crate) fn new(
        refs: &'a RefExportTable,
        bindings: &'a [InferredBinding],
        enum_variants: &'a [EnumVariantGraphNode],
        effect_operations: &'a [yulang_erased_ir::EffectOperationDecl],
    ) -> Self {
        let typeclass_obligations = bindings
            .iter()
            .flat_map(|binding| binding.scheme.typeclass_obligations.iter())
            .chain(refs.typeclass_obligations.values())
            .map(|obligation| (obligation.ref_id, obligation.clone()))
            .collect();
        Self {
            refs,
            schemes: bindings
                .iter()
                .map(|binding| (binding.def, &binding.scheme))
                .collect(),
            schemes_by_path: bindings
                .iter()
                .map(|binding| (binding.name.clone(), binding.def, &binding.scheme))
                .collect(),
            effect_operation_schemes: effect_operations
                .iter()
                .map(|operation| (operation.path.clone(), &operation.scheme))
                .collect(),
            enum_variants: enum_variants
                .iter()
                .map(|variant| ((variant.enum_path.clone(), variant.tag.clone()), variant))
                .collect(),
            typeclass_obligations,
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

    pub(crate) fn with_typeclass_obligation_overrides(
        &self,
        obligations: BTreeMap<RefId, TypeClassObligation>,
    ) -> Self {
        let mut next = self.clone();
        next.typeclass_obligations.extend(obligations);
        next
    }

    pub(crate) fn typeclass_obligation(&self, ref_id: RefId) -> Option<&TypeClassObligation> {
        self.typeclass_obligations.get(&ref_id)
    }

    pub(crate) fn typeclass_obligation_scheme(
        &self,
        ref_id: RefId,
    ) -> Option<(TypeClassObligation, ResolvedTypeClassRef, &'a Scheme)> {
        let obligation = self.typeclass_obligation(ref_id)?.clone();
        let resolved = self.resolve_typeclass_obligation(&obligation)?;
        let scheme = *self.schemes.get(&resolved.impl_member)?;
        Some((obligation, resolved, scheme))
    }

    pub(crate) fn scheme_for_path(&self, path: &Path) -> Option<(DefId, &'a Scheme)> {
        self.schemes_by_path
            .iter()
            .find(|(candidate, _, _)| candidate == path)
            .map(|(_, def, scheme)| (*def, *scheme))
    }

    pub(crate) fn effect_operation_scheme(&self, path: &Path) -> Option<&'a Scheme> {
        self.effect_operation_schemes
            .iter()
            .find(|(candidate, _)| candidate == path)
            .map(|(_, scheme)| *scheme)
    }

    fn scheme_for_def(&self, def: DefId) -> Option<&'a Scheme> {
        self.schemes.get(&def).copied()
    }

    pub(crate) fn named_variant_payload_type(
        &self,
        path: &Path,
        args: &[TypeArg],
        tag: &Name,
    ) -> Option<Option<Type>> {
        let node = self.enum_variants.get(&(path.clone(), tag.clone()))?;
        let substitutions = node
            .type_params
            .iter()
            .zip(args.iter())
            .filter_map(|(param, arg)| type_arg_value(arg).map(|ty| (param.clone(), ty)))
            .collect::<BTreeMap<_, _>>();
        Some(
            node.payload
                .as_ref()
                .map(|payload| substitute_candidate_type_with_assignments(payload, &substitutions)),
        )
    }

    fn resolve_typeclass_obligation(
        &self,
        obligation: &TypeClassObligation,
    ) -> Option<ResolvedTypeClassRef> {
        let matches = self
            .refs
            .typeclass_impl_candidates
            .iter()
            .filter(|candidate| candidate.class == obligation.class)
            .filter(|candidate| typeclass_candidate_matches_obligation(candidate, obligation))
            .collect::<Vec<_>>();
        let matches = select_most_specific_typeclass_candidates(matches);
        let [candidate] = matches.as_slice() else {
            return None;
        };
        let member = candidate
            .members
            .iter()
            .find(|member| member.member == obligation.member)?;
        Some(ResolvedTypeClassRef {
            class: obligation.class.clone(),
            member: obligation.member,
            impl_def: None,
            impl_member: member.impl_member,
        })
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
    typeclass_obligation_instances: BTreeMap<RefId, TypeclassObligationInstanceDemand>,
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

    pub(crate) fn typeclass_obligation_instances(
        &self,
    ) -> &BTreeMap<RefId, TypeclassObligationInstanceDemand> {
        &self.typeclass_obligation_instances
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypeclassObligationInstanceDemand {
    pub(crate) obligation: TypeClassObligation,
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
    ExpectedRecord {
        slot: ConstraintComputationSlot,
        found: MonoType,
    },
    MissingRecordField {
        slot: ConstraintComputationSlot,
        field: Name,
    },
    MissingRecordSpread {
        slot: ConstraintComputationSlot,
    },
    ExpectedVariant {
        slot: ConstraintComputationSlot,
        found: MonoType,
    },
    MissingVariantCase {
        slot: ConstraintComputationSlot,
        tag: Name,
    },
    VariantPayloadMismatch {
        slot: ConstraintComputationSlot,
        tag: Name,
        expected: usize,
        actual: usize,
    },
    SelectFieldMismatch {
        slot: ConstraintComputationSlot,
        field: Name,
        expected: Type,
        actual: Type,
    },
    UnsupportedSelectBase {
        slot: ConstraintComputationSlot,
        kind: ErasedExprKind,
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
    RecordField,
    RecordSpread,
    SelectBase,
    VariantPayload,
    TupleItem,
    FunctionParam,
    FunctionParamEffect,
    FunctionReturn,
    FunctionReturnEffect,
    Literal,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UnboundedTypeDefault {
    Value,
    Effect,
}

impl UnboundedTypeDefault {
    fn as_type(self) -> Type {
        match self {
            Self::Value => unit_type(),
            Self::Effect => Type::Never,
        }
    }
}

struct ConstraintSolver {
    explicit_computations: BTreeMap<DraftComputationId, MonoComputation>,
    bounds: BTreeMap<TypeNode, TypeBoundsGraph>,
    pending_bounds: Vec<PendingBound>,
    subtype_edges: BTreeSet<(TypeNode, TypeNode)>,
    type_var_defaults: BTreeMap<TypeVar, UnboundedTypeDefault>,
    next_type_var: u32,
    local_def_computations: Vec<BTreeMap<DefId, MonoComputation>>,
    direct_ref_instances: BTreeMap<RefId, DirectRefInstanceDemand>,
    resolved_typeclass_instances: BTreeMap<RefId, ResolvedTypeclassInstanceDemand>,
    typeclass_obligation_instances: BTreeMap<RefId, TypeclassObligationInstanceDemand>,
}

impl ConstraintSolver {
    fn from_set(set: ConstraintSet) -> Result<Self, ConstraintError> {
        let mut solver = Self {
            explicit_computations: BTreeMap::new(),
            bounds: BTreeMap::new(),
            pending_bounds: Vec::new(),
            subtype_edges: BTreeSet::new(),
            type_var_defaults: BTreeMap::new(),
            next_type_var: 0,
            local_def_computations: Vec::new(),
            direct_ref_instances: BTreeMap::new(),
            resolved_typeclass_instances: BTreeMap::new(),
            typeclass_obligation_instances: BTreeMap::new(),
        };
        for seed in set.computation_seeds {
            solver.assign(seed.slot, seed.computation)?;
        }
        Ok(solver)
    }

    fn into_solution(self) -> Result<ComputationSolution, ConstraintError> {
        let mut computations = BTreeMap::new();
        let mut slots = self
            .bounds
            .keys()
            .filter_map(TypeNode::computation_slot)
            .collect::<BTreeSet<_>>();
        slots.extend(self.explicit_computations.keys().copied());
        for slot in slots {
            computations.insert(slot, self.require_assigned(slot)?);
        }
        Ok(ComputationSolution {
            computations,
            direct_ref_instances: self.direct_ref_instances,
            resolved_typeclass_instances: self.resolved_typeclass_instances,
            typeclass_obligation_instances: self.typeclass_obligation_instances,
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
            ErasedExpr::Lambda { param, body } => self.solve_lambda(draft, id, *param, body, env),
            ErasedExpr::Tuple(items) => self.solve_tuple(draft, id, items, env),
            ErasedExpr::Record { fields, spread } => {
                self.solve_record(draft, id, fields, spread.as_ref(), env)
            }
            ErasedExpr::Variant { tag, value, .. } => {
                self.solve_variant(draft, id, tag, value.as_deref(), env)
            }
            ErasedExpr::Match { scrutinee, arms } => {
                self.solve_match(draft, id, scrutinee, arms, env)
            }
            ErasedExpr::Handle { body, arms } => self.solve_handle(draft, id, body, arms, env),
            ErasedExpr::Block(block) => self.solve_block(draft, id, block, env),
            ErasedExpr::Select { base, field } => self.solve_select(draft, id, base, field, env),
            ErasedExpr::BindHere { expr } => self.solve_bind_here(draft, id, expr, env),
            ErasedExpr::Pack { expr, .. } => self.solve_pack(draft, id, expr, env),
            ErasedExpr::Ref(ref_id) => self.solve_ref(draft, id, *ref_id, env),
            ErasedExpr::Def(def) => self.solve_def(draft, id, *def),
            ErasedExpr::EffectOp(_) | ErasedExpr::PrimitiveOp(_) | ErasedExpr::Lit(_) => self
                .require_assigned(draft.expr(id).computation)
                .map(|_| ()),
            _ => Ok(()),
        }
    }

    fn solve_ref(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        ref_id: RefId,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<(), ConstraintError> {
        let slot = draft.expr(id).computation;
        let computation = self.require_assigned(slot)?.clone();
        if let Some((def, scheme)) = env.direct_scheme(ref_id) {
            if let Some(signature) =
                self.ref_signature_from_scheme(slot, &computation, scheme, env)?
            {
                self.direct_ref_instances
                    .insert(ref_id, DirectRefInstanceDemand { def, signature });
            } else if scheme_needs_instantiation(scheme) {
                return Err(ConstraintError::GenericDirectRefScheme { def });
            }
        } else if let Some((resolved, scheme)) = env.resolved_typeclass_scheme(ref_id) {
            if let Some(signature) =
                self.ref_signature_from_scheme(slot, &computation, scheme, env)?
            {
                self.resolved_typeclass_instances.insert(
                    ref_id,
                    ResolvedTypeclassInstanceDemand {
                        resolved: resolved.clone(),
                        signature,
                    },
                );
            } else if scheme_needs_instantiation(scheme) {
                return Err(ConstraintError::GenericDirectRefScheme {
                    def: resolved.impl_member,
                });
            }
        } else if let Some((obligation, resolved, scheme)) =
            self.typeclass_obligation_scheme_from_current_bounds(slot, ref_id, env)?
        {
            if let Some(signature) =
                self.ref_signature_from_scheme(slot, &computation, scheme, env)?
            {
                self.typeclass_obligation_instances.insert(
                    ref_id,
                    TypeclassObligationInstanceDemand {
                        obligation,
                        resolved,
                        signature,
                    },
                );
            } else if scheme_needs_instantiation(scheme) {
                return Err(ConstraintError::GenericDirectRefScheme {
                    def: resolved.impl_member,
                });
            }
        } else if env.typeclass_obligation(ref_id).is_some() {
            return Err(ConstraintError::MissingDirectRefScheme { ref_id });
        }
        Ok(())
    }

    fn typeclass_obligation_scheme_from_current_bounds<'a>(
        &self,
        slot: DraftComputationId,
        ref_id: RefId,
        env: &'a ConstraintEnvironment<'a>,
    ) -> Result<Option<(TypeClassObligation, ResolvedTypeClassRef, &'a Scheme)>, ConstraintError>
    {
        let Some(raw_obligation) = env.typeclass_obligation(ref_id) else {
            return Ok(None);
        };
        let substitution =
            self.build_substitution_without_defaults(slot, ConstraintTypeSource::BoundsSelection)?;
        let obligation = substitution.apply_typeclass_obligation(raw_obligation);
        let Some(resolved) = env.resolve_typeclass_obligation(&obligation) else {
            return Ok(None);
        };
        let Some(scheme) = env.scheme_for_def(resolved.impl_member) else {
            return Ok(None);
        };
        Ok(Some((obligation, resolved, scheme)))
    }

    fn solve_def(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        def: DefId,
    ) -> Result<(), ConstraintError> {
        let slot = draft.expr(id).computation;
        if self.explicit_computations.contains_key(&slot)
            || self.bounds.contains_key(&TypeNode::value(slot))
            || self.bounds.contains_key(&TypeNode::effect(slot))
        {
            self.require_assigned(slot).map(|_| ())
        } else if let Some(computation) = self.local_def_computation(def) {
            self.assign(slot, computation)
        } else {
            self.require_assigned(slot).map(|_| ())
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
        let mut solve_arg_before_callee = false;
        let apply_computation = match callee {
            ErasedExpr::EffectOp(path) => {
                if let Some(scheme) = env.effect_operation_scheme(path) {
                    let Some(apply) =
                        self.apply_from_scheme(slot, &computation, scheme, arg, env)?
                    else {
                        return Err(ConstraintError::UnsupportedApplyArg {
                            slot: slot.into(),
                            kind: ErasedExprKind::from_expr(arg),
                        });
                    };
                    apply
                } else if let Some((def, scheme)) = env.scheme_for_path(path) {
                    let Some(apply) =
                        self.apply_from_scheme(slot, &computation, scheme, arg, env)?
                    else {
                        return Err(ConstraintError::GenericDirectRefScheme { def });
                    };
                    apply
                } else {
                    self.apply_from_known_callee_or_arg(slot, &computation, callee, arg, env)?
                        .ok_or_else(|| ConstraintError::UnsupportedApplyArg {
                            slot: slot.into(),
                            kind: ErasedExprKind::from_expr(arg),
                        })?
                }
            }
            ErasedExpr::Def(_)
            | ErasedExpr::PrimitiveOp(_)
            | ErasedExpr::Lambda { .. }
            | ErasedExpr::Apply { .. } => self
                .apply_from_known_callee_or_arg(slot, &computation, callee, arg, env)?
                .ok_or_else(|| ConstraintError::UnsupportedApplyArg {
                    slot: slot.into(),
                    kind: ErasedExprKind::from_expr(arg),
                })?,
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
                } else if let Some((obligation, resolved, scheme)) =
                    self.typeclass_obligation_scheme_from_current_bounds(slot, *ref_id, env)?
                {
                    let Some(apply) = self.apply_from_typeclass_obligation_scheme(
                        slot,
                        &computation,
                        &obligation,
                        scheme,
                        arg,
                        env,
                    )?
                    else {
                        return Err(ConstraintError::GenericDirectRefScheme {
                            def: resolved.impl_member,
                        });
                    };
                    self.typeclass_obligation_instances.insert(
                        *ref_id,
                        TypeclassObligationInstanceDemand {
                            obligation,
                            resolved,
                            signature: apply.callee.clone(),
                        },
                    );
                    solve_arg_before_callee = true;
                    apply
                } else if env.typeclass_obligation(*ref_id).is_some() {
                    let Some(apply) = self.apply_from_known_arg(slot, &computation, arg, env)?
                    else {
                        return Err(ConstraintError::UnsupportedApplyArg {
                            slot: slot.into(),
                            kind: ErasedExprKind::from_expr(arg),
                        });
                    };
                    solve_arg_before_callee = true;
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
        if solve_arg_before_callee {
            self.solve_expr(draft, *arg_id, arg, env)?;
            self.solve_expr(draft, *callee_id, callee, env)
        } else {
            self.solve_expr(draft, *callee_id, callee, env)?;
            self.solve_expr(draft, *arg_id, arg, env)
        }
    }

    fn solve_lambda(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        param: DefId,
        body: &ErasedExpr,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<(), ConstraintError> {
        let slot = draft.expr(id).computation;
        let computation = self.require_assigned(slot)?.clone();
        let MonoType::Value(value) = computation.value else {
            return Err(ConstraintError::ExpectedFunction {
                slot: slot.into(),
                found: computation.value,
            });
        };
        let Type::Fun {
            param: param_type,
            param_effect,
            ret_effect,
            ret,
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
            effect: lambda_body_effect(slot, body, (**ret_effect).clone())?,
        };
        let param_computation = pure_value_computation(
            slot,
            ConstraintTypeSource::FunctionParam,
            (**param_type).clone(),
        )?;
        let param_computation = MonoComputation {
            value: param_computation.value,
            effect: MonoEffect::new(concrete_type(
                slot,
                ConstraintTypeSource::FunctionParamEffect,
                (**param_effect).clone(),
            )?),
        };

        let children = draft.expr(id).children.clone();
        let [body_id] = children.as_slice() else {
            return Ok(());
        };
        self.assign(draft.expr(*body_id).computation, body_computation)?;
        self.with_local_def(param, param_computation, |this| {
            this.solve_expr(draft, *body_id, body, env)
        })
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

    fn solve_record(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        fields: &[yulang_erased_ir::RecordExprField],
        spread: Option<&yulang_erased_ir::RecordSpreadExpr>,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<(), ConstraintError> {
        let slot = draft.expr(id).computation;
        let computation = self.require_assigned(slot)?;
        if !effect_is_pure(&computation.effect) {
            return Err(ConstraintError::NonPureCompoundEffect {
                slot: slot.into(),
                kind: ErasedExprKind::Record,
                effect: computation.effect,
            });
        }
        let MonoType::Value(value) = computation.value else {
            return Err(ConstraintError::ExpectedRecord {
                slot: slot.into(),
                found: computation.value,
            });
        };
        let Type::Record(record) = value.as_type() else {
            return Err(ConstraintError::ExpectedRecord {
                slot: slot.into(),
                found: MonoType::Value(value),
            });
        };

        let children = draft.expr(id).children.clone();
        let field_children = children.iter().copied().take(fields.len());
        for (child_id, field) in field_children.zip(fields) {
            let Some(field_type) = record
                .fields
                .iter()
                .find(|record_field| record_field.name == field.name)
                .map(|record_field| record_field.value.clone())
            else {
                return Err(ConstraintError::MissingRecordField {
                    slot: slot.into(),
                    field: field.name.clone(),
                });
            };
            let child_slot = draft.expr(child_id).computation;
            self.assign(
                child_slot,
                pure_value_computation(child_slot, ConstraintTypeSource::RecordField, field_type)?,
            )?;
            self.solve_expr(draft, child_id, &field.value, env)?;
        }

        if let Some(spread) = spread {
            let Some(spread_id) = children.get(fields.len()).copied() else {
                return Ok(());
            };
            let Some(spread_type) = record_spread_type(record.spread.as_ref()) else {
                return Err(ConstraintError::MissingRecordSpread { slot: slot.into() });
            };
            let child_slot = draft.expr(spread_id).computation;
            self.assign(
                child_slot,
                pure_value_computation(
                    child_slot,
                    ConstraintTypeSource::RecordSpread,
                    spread_type,
                )?,
            )?;
            match spread {
                yulang_erased_ir::RecordSpreadExpr::Head(expr)
                | yulang_erased_ir::RecordSpreadExpr::Tail(expr) => {
                    self.solve_expr(draft, spread_id, expr, env)?;
                }
            }
        }
        Ok(())
    }

    fn solve_variant(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        tag: &Name,
        value: Option<&ErasedExpr>,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<(), ConstraintError> {
        let slot = draft.expr(id).computation;
        let computation = self.require_assigned(slot)?;
        if !effect_is_pure(&computation.effect) {
            return Err(ConstraintError::NonPureCompoundEffect {
                slot: slot.into(),
                kind: ErasedExprKind::Variant,
                effect: computation.effect,
            });
        }
        let actual_expr_payloads = usize::from(value.is_some());
        let Some(payload_type) =
            variant_payload_type(slot, &computation, tag, actual_expr_payloads, env)?
        else {
            return Ok(());
        };
        let Some(payload_expr) = value else {
            return Ok(());
        };
        let Some(payload_id) = draft.expr(id).children.first().copied() else {
            return Ok(());
        };
        let payload_slot = draft.expr(payload_id).computation;
        self.assign(
            payload_slot,
            pure_value_computation(
                payload_slot,
                ConstraintTypeSource::VariantPayload,
                payload_type,
            )?,
        )?;
        self.solve_expr(draft, payload_id, payload_expr, env)
    }

    fn solve_select(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        base: &ErasedExpr,
        field: &Name,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<(), ConstraintError> {
        let slot = draft.expr(id).computation;
        let computation = self.require_assigned(slot)?;
        let selected_type = value_type(slot, &computation.value)?;
        let base_type = if let Some(base_type) = known_value_type(base, env) {
            base_type
        } else if let Some(base_type) =
            inline_record_type_from_select(slot, base, field, &selected_type, env)?
        {
            base_type
        } else {
            return Err(ConstraintError::UnsupportedSelectBase {
                slot: slot.into(),
                kind: ErasedExprKind::from_expr(base),
            });
        };
        let actual_field_type = record_field_value_type(slot, &base_type, field)?;
        if actual_field_type != &selected_type {
            return Err(ConstraintError::SelectFieldMismatch {
                slot: slot.into(),
                field: field.clone(),
                expected: selected_type,
                actual: actual_field_type.clone(),
            });
        }

        let Some(base_id) = draft.expr(id).children.first().copied() else {
            return Ok(());
        };
        let base_slot = draft.expr(base_id).computation;
        self.assign(
            base_slot,
            pure_value_computation(base_slot, ConstraintTypeSource::SelectBase, base_type)?,
        )?;
        self.solve_expr(draft, base_id, base, env)
    }

    fn solve_pack(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        expr: &ErasedExpr,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<(), ConstraintError> {
        let [body_id] = draft.expr(id).children.as_slice() else {
            return Ok(());
        };
        let computation = self.require_assigned(draft.expr(id).computation)?;
        self.assign(draft.expr(*body_id).computation, computation)?;
        self.solve_expr(draft, *body_id, expr, env)
    }

    fn solve_bind_here(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        expr: &ErasedExpr,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<(), ConstraintError> {
        let target = self.require_assigned(draft.expr(id).computation)?;
        let [thunk_id] = draft.expr(id).children.as_slice() else {
            return Ok(());
        };
        let source = EffectiveThunkType {
            effect: target.effect.clone(),
            value: Box::new(target.value.clone()),
        };
        let thunk_computation = MonoComputation {
            value: MonoType::EffectiveThunk(source),
            effect: pure_effect(),
        };
        self.assign(draft.expr(*thunk_id).computation, thunk_computation)?;
        self.solve_expr(draft, *thunk_id, expr, env)
    }

    fn solve_match(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        scrutinee: &ErasedExpr,
        arms: &[yulang_erased_ir::MatchArm],
        env: &ConstraintEnvironment<'_>,
    ) -> Result<(), ConstraintError> {
        let slot = draft.expr(id).computation;
        let target = self.require_assigned(slot)?;
        let children = draft.expr(id).children.clone();
        let Some((&scrutinee_id, mut rest)) = children.split_first() else {
            return Ok(());
        };
        let scrutinee_computation = self
            .known_computation(slot, scrutinee, env)?
            .unwrap_or_else(|| pure_unit_computation(slot));
        self.assign(
            draft.expr(scrutinee_id).computation,
            scrutinee_computation.clone(),
        )?;
        self.solve_expr(draft, scrutinee_id, scrutinee, env)?;

        for arm in arms {
            let guard_id = if arm.guard.is_some() {
                let (guard_id, tail) = rest.split_first().expect("draft match guard child");
                rest = tail;
                Some(*guard_id)
            } else {
                None
            };
            let (body_id, tail) = rest.split_first().expect("draft match body child");
            rest = tail;
            self.with_pattern_scope(
                draft.expr(scrutinee_id).computation,
                &arm.pattern,
                &scrutinee_computation,
                env,
                |this| {
                    if let (Some(guard), Some(guard_id)) = (&arm.guard, guard_id) {
                        this.assign(
                            draft.expr(guard_id).computation,
                            pure_value_computation(
                                draft.expr(guard_id).computation,
                                ConstraintTypeSource::Literal,
                                bool_type(),
                            )?,
                        )?;
                        this.solve_expr(draft, guard_id, guard, env)?;
                    }
                    this.assign(draft.expr(*body_id).computation, target.clone())?;
                    this.solve_expr(draft, *body_id, &arm.body, env)
                },
            )?;
        }
        Ok(())
    }

    fn solve_handle(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        body: &ErasedExpr,
        arms: &[yulang_erased_ir::HandleArm],
        env: &ConstraintEnvironment<'_>,
    ) -> Result<(), ConstraintError> {
        let slot = draft.expr(id).computation;
        let target = self.require_assigned(slot)?;
        let children = draft.expr(id).children.clone();
        let Some((&body_id, mut rest)) = children.split_first() else {
            return Ok(());
        };
        let body_computation = self
            .known_computation(slot, body, env)?
            .unwrap_or_else(|| target.clone());
        self.assign(draft.expr(body_id).computation, body_computation.clone())?;
        self.solve_expr(draft, body_id, body, env)?;

        for arm in arms {
            let guard_id = if arm.guard.is_some() {
                let (guard_id, tail) = rest.split_first().expect("draft handle guard child");
                rest = tail;
                Some(*guard_id)
            } else {
                None
            };
            let (arm_body_id, tail) = rest.split_first().expect("draft handle body child");
            rest = tail;

            let payload = handle_payload_computation(slot, arm, &body_computation, env)?;
            let resume = arm
                .resume
                .map(|resume| {
                    handle_resume_computation(slot, arm, &body_computation, env)
                        .map(|computation| (resume, computation))
                })
                .transpose()?;
            self.with_pattern_scope(slot, &arm.payload, &payload, env, |this| {
                if let Some((resume, computation)) = resume.clone() {
                    this.with_local_def(resume, computation, |this| {
                        this.solve_handle_arm_body(
                            draft,
                            guard_id,
                            arm.guard.as_ref(),
                            *arm_body_id,
                            &arm.body,
                            &target,
                            env,
                        )
                    })
                } else {
                    this.solve_handle_arm_body(
                        draft,
                        guard_id,
                        arm.guard.as_ref(),
                        *arm_body_id,
                        &arm.body,
                        &target,
                        env,
                    )
                }
            })?;
        }
        Ok(())
    }

    fn solve_handle_arm_body(
        &mut self,
        draft: &ElaborationDraft,
        guard_id: Option<DraftExprId>,
        guard: Option<&ErasedExpr>,
        body_id: DraftExprId,
        body: &ErasedExpr,
        target: &MonoComputation,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<(), ConstraintError> {
        if let (Some(guard_id), Some(guard)) = (guard_id, guard) {
            self.assign(
                draft.expr(guard_id).computation,
                pure_value_computation(
                    draft.expr(guard_id).computation,
                    ConstraintTypeSource::Literal,
                    bool_type(),
                )?,
            )?;
            self.solve_expr(draft, guard_id, guard, env)?;
        }
        self.assign(draft.expr(body_id).computation, target.clone())?;
        self.solve_expr(draft, body_id, body, env)
    }

    fn solve_block(
        &mut self,
        draft: &ElaborationDraft,
        id: DraftExprId,
        block: &yulang_erased_ir::ErasedBlock,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<(), ConstraintError> {
        let slot = draft.expr(id).computation;
        let target = self.require_assigned(slot)?;
        let mut child_ids = draft.expr(id).children.iter().copied();
        self.local_def_computations.push(BTreeMap::new());
        let out = self.solve_block_inner(draft, block, &mut child_ids, &target, env);
        self.local_def_computations.pop();
        out
    }

    fn solve_block_inner(
        &mut self,
        draft: &ElaborationDraft,
        block: &yulang_erased_ir::ErasedBlock,
        child_ids: &mut impl Iterator<Item = DraftExprId>,
        target: &MonoComputation,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<(), ConstraintError> {
        for stmt in &block.stmts {
            match stmt {
                yulang_erased_ir::ErasedStmt::Let { pattern, value } => {
                    let child_id = child_ids.next().expect("draft block let child");
                    let computation = self
                        .known_computation(draft.expr(child_id).computation, value, env)?
                        .unwrap_or_else(|| pure_unit_computation(draft.expr(child_id).computation));
                    self.assign(draft.expr(child_id).computation, computation.clone())?;
                    self.solve_expr(draft, child_id, value, env)?;
                    let computation = self.require_assigned(draft.expr(child_id).computation)?;
                    self.bind_pattern_locals(
                        draft.expr(child_id).computation,
                        pattern,
                        &computation,
                        env,
                    )?;
                }
                yulang_erased_ir::ErasedStmt::Expr(expr) => {
                    let child_id = child_ids.next().expect("draft block expr child");
                    let computation = self
                        .known_computation(draft.expr(child_id).computation, expr, env)?
                        .unwrap_or_else(|| block_statement_computation(target));
                    self.assign(draft.expr(child_id).computation, computation)?;
                    self.solve_expr(draft, child_id, expr, env)?;
                }
                yulang_erased_ir::ErasedStmt::Module { body, .. } => {
                    self.solve_block_inner(draft, body, child_ids, target, env)?;
                }
            }
        }
        if let Some(tail) = &block.tail {
            let tail_id = child_ids.next().expect("draft block tail child");
            self.assign(draft.expr(tail_id).computation, target.clone())?;
            self.solve_expr(draft, tail_id, tail, env)?;
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
        self.apply_from_scheme_with_arg_hint(slot, expected, scheme, arg, env, None)
    }

    fn apply_from_typeclass_obligation_scheme(
        &mut self,
        slot: DraftComputationId,
        expected: &MonoComputation,
        obligation: &TypeClassObligation,
        scheme: &Scheme,
        arg: &ErasedExpr,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<Option<ApplyComputation>, ConstraintError> {
        let arg_hint = typeclass_obligation_receiver_computation(slot, obligation)?;
        self.apply_from_scheme_with_arg_hint(slot, expected, scheme, arg, env, arg_hint)
    }

    fn apply_from_scheme_with_arg_hint(
        &mut self,
        slot: DraftComputationId,
        expected: &MonoComputation,
        scheme: &Scheme,
        arg: &ErasedExpr,
        env: &ConstraintEnvironment<'_>,
        arg_hint: Option<MonoComputation>,
    ) -> Result<Option<ApplyComputation>, ConstraintError> {
        let known_arg = self.known_computation(slot, arg, env)?;
        let known_arg = known_arg.or(arg_hint);
        if !scheme_needs_instantiation(scheme) {
            return concrete_apply_from_scheme(slot, expected, scheme, known_arg.as_ref())
                .map(Some);
        }
        let Some(instantiated) =
            self.instantiate_apply_scheme(slot, expected, scheme, known_arg.as_ref(), env)?
        else {
            return Ok(None);
        };
        concrete_apply_from_scheme(slot, expected, &instantiated, known_arg.as_ref()).map(Some)
    }

    fn ref_signature_from_scheme(
        &mut self,
        slot: DraftComputationId,
        expected: &MonoComputation,
        scheme: &Scheme,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<Option<MonoComputation>, ConstraintError> {
        if !scheme_needs_instantiation(scheme) {
            return Ok(None);
        }
        let freshened = self.freshen_scheme(scheme);
        let body = freshened.body;
        let expected_value = value_type(slot, &expected.value)?;
        let expected_effect = expected.effect.row().as_type().clone();

        self.constrain_types(body.clone(), expected_value.clone())?;
        self.constrain_types(expected_value, body.clone())?;
        self.constrain_types(Type::Never, expected_effect.clone())?;
        self.constrain_types(expected_effect, Type::Never)?;
        self.drain_pending_bounds()?;
        self.solve_freshened_requirements_to_fixpoint(
            slot,
            &freshened.requirements,
            ConstraintTypeSource::BoundsSelection,
            env,
        )?;

        let substitution =
            self.build_substitution_with_defaults(slot, ConstraintTypeSource::BoundsSelection)?;
        let body = substitution.apply_type(&body);
        let value = concrete_type(slot, ConstraintTypeSource::BoundsSelection, body)?;
        Ok(Some(MonoComputation {
            value: MonoType::Value(value),
            effect: pure_effect(),
        }))
    }

    fn instantiate_apply_scheme(
        &mut self,
        slot: DraftComputationId,
        expected: &MonoComputation,
        scheme: &Scheme,
        arg_computation: Option<&MonoComputation>,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<Option<Scheme>, ConstraintError> {
        let freshened = self.freshen_scheme(scheme);
        let body = freshened.body;
        let Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } = &body
        else {
            return Ok(None);
        };

        let expected_value = value_type(slot, &expected.value)?;
        let expected_effect = expected.effect.row().as_type().clone();
        if let Some(arg_computation) = arg_computation {
            let arg_value = value_type(slot, &arg_computation.value)?;
            let arg_effect = arg_computation.effect.row().as_type().clone();
            self.constrain_types(arg_value, (**param).clone())?;
            self.constrain_types(arg_effect, (**param_effect).clone())?;
        }
        self.constrain_types((**ret).clone(), expected_value)?;
        self.constrain_types((**ret_effect).clone(), expected_effect)?;
        self.drain_pending_bounds()?;
        self.solve_freshened_requirements_to_fixpoint(
            slot,
            &freshened.requirements,
            ConstraintTypeSource::BoundsSelection,
            env,
        )?;

        let substitution =
            self.build_substitution_with_defaults(slot, ConstraintTypeSource::BoundsSelection)?;
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

    fn apply_from_known_arg(
        &self,
        slot: DraftComputationId,
        expected: &MonoComputation,
        arg: &ErasedExpr,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<Option<ApplyComputation>, ConstraintError> {
        let Some(arg_computation) = self.known_computation(slot, arg, env)? else {
            return Ok(None);
        };
        let ret_type = value_type(slot, &expected.value)?;
        let ret_effect = expected.effect.row().as_type().clone();
        let arg_type = value_type(slot, &arg_computation.value)?;
        let arg_effect = arg_computation.effect.row().as_type().clone();
        Ok(Some(ApplyComputation {
            callee: function_computation(slot, arg_type, arg_effect, ret_effect, ret_type)?,
            arg: arg_computation,
        }))
    }

    fn apply_from_known_callee_or_arg(
        &self,
        slot: DraftComputationId,
        expected: &MonoComputation,
        callee: &ErasedExpr,
        arg: &ErasedExpr,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<Option<ApplyComputation>, ConstraintError> {
        if let Some(apply) = self.apply_from_ref_scheme_spine(slot, expected, callee, arg, env)? {
            return Ok(Some(apply));
        }
        if let Some(callee_computation) = self.known_computation(slot, callee, env)?
            && let Some(apply) = apply_from_callee_computation(slot, expected, &callee_computation)?
        {
            return Ok(Some(apply));
        }
        self.apply_from_known_arg(slot, expected, arg, env)
    }

    fn apply_from_ref_scheme_spine(
        &self,
        slot: DraftComputationId,
        expected: &MonoComputation,
        callee: &ErasedExpr,
        arg: &ErasedExpr,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<Option<ApplyComputation>, ConstraintError> {
        let (head, args) = collect_apply_spine_with_final(callee, arg);
        let ErasedExpr::Ref(ref_id) = head else {
            return Ok(None);
        };
        let scheme = env
            .direct_scheme(*ref_id)
            .map(|(_, scheme)| scheme)
            .or_else(|| {
                env.resolved_typeclass_scheme(*ref_id)
                    .map(|(_, scheme)| scheme)
            })
            .or_else(|| {
                env.typeclass_obligation_scheme(*ref_id)
                    .map(|(_, _, scheme)| scheme)
            });
        let Some(scheme) = scheme else {
            return Ok(None);
        };
        self.apply_from_scheme_spine(slot, expected, scheme, &args, env)
    }

    fn apply_from_scheme_spine(
        &self,
        slot: DraftComputationId,
        expected: &MonoComputation,
        scheme: &Scheme,
        args: &[&ErasedExpr],
        env: &ConstraintEnvironment<'_>,
    ) -> Result<Option<ApplyComputation>, ConstraintError> {
        let mut instantiation = TypeInstantiation::new(scheme);
        let expected_value = value_type(slot, &expected.value)?;
        let expected_effect = expected.effect.row().as_type().clone();
        let mut current = scheme.body.clone();
        let mut extra_arg_effect = Type::Never;

        for (index, arg_expr) in args.iter().enumerate() {
            let Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } = current
            else {
                return Ok(None);
            };

            let arg_computation = self.known_computation(slot, arg_expr, env)?;
            if let Some(arg_computation) = &arg_computation {
                let arg_value = value_type(slot, &arg_computation.value)?;
                let arg_effect = arg_computation.effect.row().as_type();
                if !match_apply_arg_type(&mut instantiation, &param, &arg_value) {
                    return Ok(None);
                }
                if !match_apply_arg_effect(&mut instantiation, &param_effect, arg_effect) {
                    extra_arg_effect = join_effect_rows(&extra_arg_effect, arg_effect);
                }
            }

            solve_scheme_requirements_to_fixpoint(&mut instantiation, scheme, env);
            if index + 1 != args.len() {
                current = instantiation.substitute_type(&ret);
                continue;
            }

            let mut trial = instantiation.clone();
            if !match_apply_arg_type(&mut trial, &ret, &expected_value)
                && !type_fits_expected(&trial.substitute_type(&ret), &expected_value)
            {
                return Ok(None);
            }
            if !match_apply_arg_effect(&mut trial, &ret_effect, &expected_effect) {
                let ret_effect =
                    join_effect_rows(&extra_arg_effect, &trial.substitute_type(&ret_effect));
                if !effect_row_fits_expected(&ret_effect, &expected_effect) {
                    return Ok(None);
                }
            }
            solve_scheme_requirements_to_fixpoint(&mut trial, scheme, env);

            let param = trial.substitute_type_with_defaults(&param);
            let param_effect = trial.substitute_type_with_defaults(&param_effect);
            let scheme_arg = MonoComputation {
                value: MonoType::Value(concrete_type(
                    slot,
                    ConstraintTypeSource::FunctionParam,
                    param,
                )?),
                effect: MonoEffect::new(concrete_type(
                    slot,
                    ConstraintTypeSource::FunctionParamEffect,
                    param_effect,
                )?),
            };
            let arg = known_arg_computation_for_apply(slot, &scheme_arg, arg_computation.as_ref())?
                .unwrap_or(scheme_arg);
            let arg_type = value_type(slot, &arg.value)?;
            let arg_effect = arg.effect.row().as_type().clone();
            return Ok(Some(ApplyComputation {
                callee: function_computation(
                    slot,
                    arg_type,
                    arg_effect,
                    expected_effect,
                    expected_value,
                )?,
                arg,
            }));
        }

        Ok(None)
    }

    fn known_computation(
        &self,
        slot: DraftComputationId,
        expr: &ErasedExpr,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<Option<MonoComputation>, ConstraintError> {
        if let ErasedExpr::Def(def) = expr
            && let Some(computation) = self.local_def_computation(*def)
        {
            return Ok(Some(computation));
        }
        if let ErasedExpr::Apply { callee, arg } = expr {
            return self.known_apply_computation(slot, callee, arg, env);
        }
        let Some(ty) = known_value_type(expr, env) else {
            return Ok(None);
        };
        Ok(Some(MonoComputation {
            value: MonoType::Value(concrete_type(slot, ConstraintTypeSource::Literal, ty)?),
            effect: pure_effect(),
        }))
    }

    fn known_apply_computation(
        &self,
        slot: DraftComputationId,
        callee: &ErasedExpr,
        arg: &ErasedExpr,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<Option<MonoComputation>, ConstraintError> {
        if let ErasedExpr::Ref(ref_id) = callee {
            if let Some((_, scheme)) = env.direct_scheme(*ref_id) {
                return self.known_apply_from_scheme(slot, scheme, arg, env);
            }
            if let Some((_, scheme)) = env.resolved_typeclass_scheme(*ref_id) {
                return self.known_apply_from_scheme(slot, scheme, arg, env);
            }
            if let Some((_, _, scheme)) = env.typeclass_obligation_scheme(*ref_id) {
                return self.known_apply_from_scheme(slot, scheme, arg, env);
            }
        }
        if let ErasedExpr::EffectOp(path) = callee
            && let Some(scheme) = env
                .effect_operation_scheme(path)
                .or_else(|| env.scheme_for_path(path).map(|(_, scheme)| scheme))
        {
            return self.known_apply_from_scheme(slot, scheme, arg, env);
        }

        let Some(callee_computation) = self.known_computation(slot, callee, env)? else {
            return Ok(None);
        };
        self.known_apply_from_callee_computation(slot, &callee_computation, arg, env)
    }

    fn known_apply_from_scheme(
        &self,
        slot: DraftComputationId,
        scheme: &Scheme,
        arg: &ErasedExpr,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<Option<MonoComputation>, ConstraintError> {
        let Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } = &scheme.body
        else {
            return Ok(None);
        };

        let mut instantiation = TypeInstantiation::new(scheme);
        let mut extra_arg_effect = Type::Never;
        if let Some(arg_computation) = self.known_computation(slot, arg, env)? {
            let arg_value = value_type(slot, &arg_computation.value)?;
            let arg_effect = arg_computation.effect.row().as_type();
            if !match_apply_arg_type(&mut instantiation, param, &arg_value) {
                return Ok(None);
            }
            if !match_apply_arg_effect(&mut instantiation, param_effect, arg_effect) {
                extra_arg_effect = arg_effect.clone();
            }
        } else if scheme_needs_instantiation(scheme)
            && (scheme_quantified_vars_appear_in_type(scheme, ret)
                || scheme_quantified_vars_appear_in_type(scheme, ret_effect))
        {
            return Ok(None);
        }

        solve_scheme_requirements_to_fixpoint(&mut instantiation, scheme, env);
        let ret = instantiation.substitute_type_with_defaults(ret);
        let ret_effect = join_effect_rows(
            &extra_arg_effect,
            &instantiation.substitute_type_with_defaults(ret_effect),
        );
        known_apply_result_computation(slot, ret, ret_effect)
    }

    fn known_apply_from_callee_computation(
        &self,
        slot: DraftComputationId,
        callee: &MonoComputation,
        arg: &ErasedExpr,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<Option<MonoComputation>, ConstraintError> {
        let MonoType::Value(function) = &callee.value else {
            return Ok(None);
        };
        let Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } = function.as_type()
        else {
            return Ok(None);
        };
        let Some(arg_computation) = self.known_computation(slot, arg, env)? else {
            return Ok(None);
        };
        let arg_value = value_type(slot, &arg_computation.value)?;
        let arg_effect = arg_computation.effect.row().as_type();
        if !type_fits_expected(&arg_value, param) {
            return Ok(None);
        }
        let ret_effect = if effect_row_fits_expected(arg_effect, param_effect) {
            (**ret_effect).clone()
        } else {
            join_effect_rows(arg_effect, ret_effect)
        };
        known_apply_result_computation(slot, (**ret).clone(), ret_effect)
    }

    fn freshen_scheme(&mut self, scheme: &Scheme) -> FreshenedScheme {
        let instantiation = SchemeFreshening::new(self, scheme);
        FreshenedScheme {
            body: instantiation.substitute_type(&scheme.body),
            requirements: scheme
                .requirements
                .iter()
                .map(|requirement| instantiation.substitute_role_requirement(requirement))
                .collect(),
        }
    }

    fn fresh_type_var(&mut self, original: &TypeVar, default: UnboundedTypeDefault) -> TypeVar {
        let id = self.next_type_var;
        self.next_type_var += 1;
        let var = TypeVar(format!("$elab{id}${}", original.0));
        self.type_var_defaults.insert(var.clone(), default);
        var
    }

    fn local_def_computation(&self, def: DefId) -> Option<MonoComputation> {
        self.local_def_computations
            .iter()
            .rev()
            .find_map(|scope| scope.get(&def).cloned())
    }

    fn with_local_def<T>(
        &mut self,
        def: DefId,
        computation: MonoComputation,
        f: impl FnOnce(&mut Self) -> Result<T, ConstraintError>,
    ) -> Result<T, ConstraintError> {
        let mut scope = BTreeMap::new();
        scope.insert(def, computation);
        self.local_def_computations.push(scope);
        let out = f(self);
        self.local_def_computations.pop();
        out
    }

    fn with_pattern_scope<T>(
        &mut self,
        slot: DraftComputationId,
        pattern: &yulang_erased_ir::Pattern,
        computation: &MonoComputation,
        env: &ConstraintEnvironment<'_>,
        f: impl FnOnce(&mut Self) -> Result<T, ConstraintError>,
    ) -> Result<T, ConstraintError> {
        self.local_def_computations.push(BTreeMap::new());
        let bind_result = self.bind_pattern_locals(slot, pattern, computation, env);
        let out = bind_result.and_then(|()| f(self));
        self.local_def_computations.pop();
        out
    }

    fn bind_pattern_locals(
        &mut self,
        slot: DraftComputationId,
        pattern: &yulang_erased_ir::Pattern,
        computation: &MonoComputation,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<(), ConstraintError> {
        match pattern {
            yulang_erased_ir::Pattern::Bind(def) => {
                self.bind_local_def(*def, pure_pattern_value_computation(computation));
                Ok(())
            }
            yulang_erased_ir::Pattern::As { pattern, def } => {
                self.bind_local_def(*def, pure_pattern_value_computation(computation));
                self.bind_pattern_locals(slot, pattern, computation, env)
            }
            yulang_erased_ir::Pattern::Tuple(items) => {
                let value = value_type(slot, &computation.value)?;
                let Type::Tuple(item_types) = value else {
                    return Ok(());
                };
                for (item, item_type) in items.iter().zip(item_types) {
                    let item_computation =
                        pure_value_computation(slot, ConstraintTypeSource::TupleItem, item_type)?;
                    self.bind_pattern_locals(slot, item, &item_computation, env)?;
                }
                Ok(())
            }
            yulang_erased_ir::Pattern::Variant { tag, value } => {
                if let Some(value) = value {
                    let payload =
                        variant_pattern_payload_computation(slot, computation, tag, 1, env)?;
                    self.bind_pattern_locals(slot, value, &payload, env)?;
                }
                Ok(())
            }
            yulang_erased_ir::Pattern::Or { left, right } => {
                self.bind_pattern_locals(slot, left, computation, env)?;
                self.bind_pattern_locals(slot, right, computation, env)
            }
            yulang_erased_ir::Pattern::Record { fields, spread } => {
                let value = value_type(slot, &computation.value)?;
                if let Type::Record(record) = value {
                    for field in fields {
                        if let Some(field_type) = record
                            .fields
                            .iter()
                            .find(|candidate| candidate.name == field.name)
                            .map(|field| field.value.clone())
                        {
                            let field_computation = pure_value_computation(
                                slot,
                                ConstraintTypeSource::RecordField,
                                field_type,
                            )?;
                            self.bind_pattern_locals(
                                slot,
                                &field.pattern,
                                &field_computation,
                                env,
                            )?;
                        }
                        if let Some(default) = &field.default {
                            let _ = default;
                        }
                    }
                    if let Some(spread) = spread
                        && let Some(spread_type) = record_spread_type(record.spread.as_ref())
                    {
                        let spread_computation = pure_value_computation(
                            slot,
                            ConstraintTypeSource::RecordSpread,
                            spread_type,
                        )?;
                        match spread {
                            yulang_erased_ir::RecordSpreadPattern::Head(pattern)
                            | yulang_erased_ir::RecordSpreadPattern::Tail(pattern) => {
                                self.bind_pattern_locals(slot, pattern, &spread_computation, env)?;
                            }
                        }
                    }
                }
                Ok(())
            }
            yulang_erased_ir::Pattern::List { spread, .. } => {
                if let Some(spread) = spread {
                    self.bind_pattern_locals(slot, spread, computation, env)?;
                }
                Ok(())
            }
            yulang_erased_ir::Pattern::Wildcard
            | yulang_erased_ir::Pattern::Lit(_)
            | yulang_erased_ir::Pattern::Constructor { .. }
            | yulang_erased_ir::Pattern::UnresolvedName(_) => Ok(()),
        }
    }

    fn bind_local_def(&mut self, def: DefId, computation: MonoComputation) {
        if let Some(scope) = self.local_def_computations.last_mut() {
            scope.insert(def, computation);
        }
    }

    fn assign(
        &mut self,
        slot: DraftComputationId,
        computation: MonoComputation,
    ) -> Result<(), ConstraintError> {
        if matches!(
            computation.value,
            MonoType::Function(_) | MonoType::EffectiveThunk(_)
        ) {
            return self.add_explicit_computation(slot, computation);
        }
        self.add_exact_computation(slot, computation)?;
        self.drain_pending_bounds()
    }

    fn add_explicit_computation(
        &mut self,
        slot: DraftComputationId,
        computation: MonoComputation,
    ) -> Result<(), ConstraintError> {
        if let Some(existing) = self.explicit_computations.get(&slot) {
            if existing != &computation {
                return Err(ConstraintError::ConflictingComputation {
                    slot: slot.into(),
                    existing: existing.clone(),
                    incoming: computation,
                });
            }
            return Ok(());
        }
        self.explicit_computations.insert(slot, computation);
        Ok(())
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

    fn solve_freshened_requirements_to_fixpoint(
        &mut self,
        slot: DraftComputationId,
        requirements: &[RoleRequirement],
        source: ConstraintTypeSource,
        env: &ConstraintEnvironment<'_>,
    ) -> Result<(), ConstraintError> {
        let mut pending_requirements = requirements.to_vec();
        loop {
            let blockers = AssociatedTypeBlockers::from_requirements(&pending_requirements);
            let substitution =
                self.build_substitution_without_defaults_with_blockers(slot, source, &blockers)?;
            let substituted = pending_requirements
                .iter()
                .map(|requirement| substitution.apply_role_requirement(requirement))
                .collect::<Vec<_>>();
            let mut progressed = false;
            for (index, requirement) in substituted.iter().enumerate() {
                let Some(resolution) = GraphRoleCandidateResolution::select(requirement, env)
                else {
                    continue;
                };
                pending_requirements.remove(index);
                self.constrain_role_associated_outputs(requirement, &resolution)?;
                for prerequisite in resolution.prerequisites() {
                    if !pending_requirements.contains(&prerequisite) {
                        pending_requirements.push(prerequisite);
                    }
                }
                self.drain_pending_bounds()?;
                progressed = true;
                break;
            }
            if !progressed {
                break;
            }
        }
        Ok(())
    }

    fn constrain_role_associated_outputs(
        &mut self,
        requirement: &RoleRequirement,
        resolution: &GraphRoleCandidateResolution<'_>,
    ) -> Result<(), ConstraintError> {
        for arg in &resolution.candidate.args {
            let RoleRequirementArg::Associated {
                name,
                bounds: candidate_bounds,
            } = arg
            else {
                continue;
            };
            let Some(requirement_bounds) = role_requirement_associated_bounds(requirement, name)
            else {
                continue;
            };
            let candidate_bounds = resolution.substitute_candidate_bounds(candidate_bounds);
            self.constrain_associated_bounds(requirement_bounds, &candidate_bounds)?;
        }
        Ok(())
    }

    fn constrain_associated_bounds(
        &mut self,
        requirement: &TypeBounds,
        candidate: &TypeBounds,
    ) -> Result<(), ConstraintError> {
        if let (Some(requirement), Some(candidate)) = (
            exact_type_from_bounds(requirement),
            exact_type_from_bounds(candidate),
        ) {
            self.constrain_types(requirement.clone(), candidate.clone())?;
            self.constrain_types(candidate.clone(), requirement.clone())?;
            return Ok(());
        }
        if let (Some(requirement), Some(candidate)) = (&requirement.lower, &candidate.lower) {
            self.constrain_types((**requirement).clone(), (**candidate).clone())?;
            self.constrain_types((**candidate).clone(), (**requirement).clone())?;
        }
        if let (Some(requirement), Some(candidate)) = (&requirement.upper, &candidate.upper) {
            self.constrain_types((**requirement).clone(), (**candidate).clone())?;
            self.constrain_types((**candidate).clone(), (**requirement).clone())?;
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
        if let Some(computation) = self.explicit_computations.get(&slot) {
            return Ok(computation.clone());
        }
        let mut substitution =
            self.build_substitution_with_defaults(slot, ConstraintTypeSource::BoundsSelection)?;
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
                UnboundedTypeDefault::Value,
                &mut substitution,
            )?),
            effect: MonoEffect::new(self.select_concrete_type(
                slot,
                effect_bounds,
                ConstraintTypeSource::BoundsSelection,
                UnboundedTypeDefault::Effect,
                &mut substitution,
            )?),
        })
    }

    fn build_substitution_with_defaults(
        &self,
        slot: DraftComputationId,
        source: ConstraintTypeSource,
    ) -> Result<ElaborationSubstitution, ConstraintError> {
        self.build_substitution(slot, source, true, &AssociatedTypeBlockers::default())
    }

    fn build_substitution_without_defaults(
        &self,
        slot: DraftComputationId,
        source: ConstraintTypeSource,
    ) -> Result<ElaborationSubstitution, ConstraintError> {
        self.build_substitution(slot, source, false, &AssociatedTypeBlockers::default())
    }

    fn build_substitution_without_defaults_with_blockers(
        &self,
        slot: DraftComputationId,
        source: ConstraintTypeSource,
        blockers: &AssociatedTypeBlockers,
    ) -> Result<ElaborationSubstitution, ConstraintError> {
        self.build_substitution(slot, source, false, blockers)
    }

    fn build_substitution(
        &self,
        slot: DraftComputationId,
        source: ConstraintTypeSource,
        use_defaults: bool,
        blockers: &AssociatedTypeBlockers,
    ) -> Result<ElaborationSubstitution, ConstraintError> {
        let mut substitution = ElaborationSubstitution::default();
        let mut vars = self
            .bounds
            .keys()
            .filter_map(|node| match node {
                TypeNode::Var(var) => Some(var.clone()),
                TypeNode::Computation { .. } => None,
            })
            .collect::<BTreeSet<_>>();
        vars.extend(self.type_var_defaults.keys().cloned());
        for var in vars {
            self.solve_type_var(
                slot,
                &var,
                source,
                &mut substitution,
                &mut BTreeSet::new(),
                use_defaults,
                blockers,
            )?;
        }
        Ok(substitution)
    }

    fn select_concrete_type(
        &self,
        slot: DraftComputationId,
        bounds: &TypeBoundsGraph,
        source: ConstraintTypeSource,
        default: UnboundedTypeDefault,
        substitution: &mut ElaborationSubstitution,
    ) -> Result<ConcreteType, ConstraintError> {
        let ty = self
            .select_type_candidate_from_bounds(
                slot,
                bounds,
                source,
                substitution,
                &mut BTreeSet::new(),
                &mut BTreeSet::new(),
                true,
                &AssociatedTypeBlockers::default(),
                None,
            )?
            .unwrap_or_else(|| default.as_type());
        concrete_type(slot, source, ty)
    }

    fn solve_type_var(
        &self,
        slot: DraftComputationId,
        var: &TypeVar,
        source: ConstraintTypeSource,
        substitution: &mut ElaborationSubstitution,
        visiting: &mut BTreeSet<TypeVar>,
        use_defaults: bool,
        blockers: &AssociatedTypeBlockers,
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
                use_defaults,
                blockers,
                Some(var),
            )?
        } else {
            None
        }
        .or_else(|| {
            use_defaults
                .then(|| {
                    self.type_var_defaults
                        .get(var)
                        .map(|default| default.as_type())
                })
                .flatten()
        });
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
        use_defaults: bool,
        blockers: &AssociatedTypeBlockers,
        target_var: Option<&TypeVar>,
    ) -> Result<Option<Type>, ConstraintError> {
        let mut candidates = Vec::new();
        for ty in &bounds.lower {
            if target_var.is_some_and(|var| blockers.blocks_var(var, BoundKind::Lower)) {
                continue;
            }
            let ty = self.candidate_type(
                slot,
                ty,
                source,
                substitution,
                visiting,
                shadowed,
                use_defaults,
                blockers,
            )?;
            if blockers.type_is_blocked(&ty, BoundKind::Lower) {
                continue;
            }
            collect_concrete_candidates(&ty, &mut candidates);
        }
        for ty in &bounds.upper {
            if target_var.is_some_and(|var| blockers.blocks_var(var, BoundKind::Upper)) {
                continue;
            }
            let ty = self.candidate_type(
                slot,
                ty,
                source,
                substitution,
                visiting,
                shadowed,
                use_defaults,
                blockers,
            )?;
            if blockers.type_is_blocked(&ty, BoundKind::Upper) {
                continue;
            }
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
        use_defaults: bool,
        blockers: &AssociatedTypeBlockers,
    ) -> Result<Type, ConstraintError> {
        match ty {
            Type::Var(var) if !shadowed.contains(var) => Ok(self
                .solve_type_var(
                    slot,
                    var,
                    source,
                    substitution,
                    visiting,
                    use_defaults,
                    blockers,
                )?
                .unwrap_or_else(|| ty.clone())),
            Type::Named { path, args } => Ok(Type::Named {
                path: path.clone(),
                args: args
                    .iter()
                    .map(|arg| {
                        self.candidate_type_arg(
                            slot,
                            arg,
                            source,
                            substitution,
                            visiting,
                            shadowed,
                            use_defaults,
                            blockers,
                        )
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
                    use_defaults,
                    blockers,
                )?),
                param_effect: Box::new(self.candidate_type(
                    slot,
                    param_effect,
                    source,
                    substitution,
                    visiting,
                    shadowed,
                    use_defaults,
                    blockers,
                )?),
                ret_effect: Box::new(self.candidate_type(
                    slot,
                    ret_effect,
                    source,
                    substitution,
                    visiting,
                    shadowed,
                    use_defaults,
                    blockers,
                )?),
                ret: Box::new(self.candidate_type(
                    slot,
                    ret,
                    source,
                    substitution,
                    visiting,
                    shadowed,
                    use_defaults,
                    blockers,
                )?),
            }),
            Type::Tuple(items) => Ok(Type::Tuple(
                items
                    .iter()
                    .map(|item| {
                        self.candidate_type(
                            slot,
                            item,
                            source,
                            substitution,
                            visiting,
                            shadowed,
                            use_defaults,
                            blockers,
                        )
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
                                use_defaults,
                                blockers,
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
                            .candidate_type(
                                slot,
                                ty,
                                source,
                                substitution,
                                visiting,
                                shadowed,
                                use_defaults,
                                blockers,
                            )
                            .map(Box::new)
                            .map(yulang_erased_ir::RecordSpread::Head),
                        yulang_erased_ir::RecordSpread::Tail(ty) => self
                            .candidate_type(
                                slot,
                                ty,
                                source,
                                substitution,
                                visiting,
                                shadowed,
                                use_defaults,
                                blockers,
                            )
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
                                        use_defaults,
                                        blockers,
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
                        self.candidate_type(
                            slot,
                            tail,
                            source,
                            substitution,
                            visiting,
                            shadowed,
                            use_defaults,
                            blockers,
                        )
                        .map(Box::new)
                    })
                    .transpose()?,
            })),
            Type::Row { items, tail } => Ok(Type::Row {
                items: items
                    .iter()
                    .map(|item| {
                        self.candidate_type(
                            slot,
                            item,
                            source,
                            substitution,
                            visiting,
                            shadowed,
                            use_defaults,
                            blockers,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
                tail: Box::new(self.candidate_type(
                    slot,
                    tail,
                    source,
                    substitution,
                    visiting,
                    shadowed,
                    use_defaults,
                    blockers,
                )?),
            }),
            Type::Union(items) => Ok(Type::Union(
                items
                    .iter()
                    .map(|item| {
                        self.candidate_type(
                            slot,
                            item,
                            source,
                            substitution,
                            visiting,
                            shadowed,
                            use_defaults,
                            blockers,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Type::Inter(items) => Ok(Type::Inter(
                items
                    .iter()
                    .map(|item| {
                        self.candidate_type(
                            slot,
                            item,
                            source,
                            substitution,
                            visiting,
                            shadowed,
                            use_defaults,
                            blockers,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            Type::Recursive { var, body } => {
                let inserted = shadowed.insert(var.clone());
                let body = self.candidate_type(
                    slot,
                    body,
                    source,
                    substitution,
                    visiting,
                    shadowed,
                    use_defaults,
                    blockers,
                );
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
        use_defaults: bool,
        blockers: &AssociatedTypeBlockers,
    ) -> Result<yulang_erased_ir::TypeArg, ConstraintError> {
        match arg {
            yulang_erased_ir::TypeArg::Type(ty) => {
                Ok(yulang_erased_ir::TypeArg::Type(self.candidate_type(
                    slot,
                    ty,
                    source,
                    substitution,
                    visiting,
                    shadowed,
                    use_defaults,
                    blockers,
                )?))
            }
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
                                use_defaults,
                                blockers,
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
                                use_defaults,
                                blockers,
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

#[derive(Debug, Clone, Default, PartialEq, Eq)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BoundKind {
    Lower,
    Upper,
}

#[derive(Debug, Clone, Default)]
struct AssociatedTypeBlockers {
    lower: BTreeSet<TypeVar>,
    upper: BTreeSet<TypeVar>,
}

impl AssociatedTypeBlockers {
    fn from_requirements(requirements: &[RoleRequirement]) -> Self {
        let mut blockers = Self::default();
        for requirement in requirements {
            for arg in &requirement.args {
                let RoleRequirementArg::Associated { bounds, .. } = arg else {
                    continue;
                };
                if let Some(lower) = &bounds.lower {
                    collect_type_vars_for_blocker(lower, &mut blockers.lower);
                }
                if let Some(upper) = &bounds.upper {
                    collect_type_vars_for_blocker(upper, &mut blockers.upper);
                }
            }
        }
        blockers
    }

    fn blocks_var(&self, var: &TypeVar, direction: BoundKind) -> bool {
        match direction {
            BoundKind::Lower => self.lower.contains(var),
            BoundKind::Upper => self.upper.contains(var),
        }
    }

    fn type_is_blocked(&self, ty: &Type, direction: BoundKind) -> bool {
        match ty {
            Type::Var(var) => self.blocks_var(var, direction),
            Type::Named { args, .. } => args
                .iter()
                .any(|arg| self.type_arg_is_blocked(arg, direction)),
            Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => {
                self.type_is_blocked(param, direction)
                    || self.type_is_blocked(param_effect, direction)
                    || self.type_is_blocked(ret_effect, direction)
                    || self.type_is_blocked(ret, direction)
            }
            Type::Tuple(items) | Type::Union(items) | Type::Inter(items) => items
                .iter()
                .any(|item| self.type_is_blocked(item, direction)),
            Type::Record(record) => {
                record
                    .fields
                    .iter()
                    .any(|field| self.type_is_blocked(&field.value, direction))
                    || record.spread.as_ref().is_some_and(|spread| match spread {
                        yulang_erased_ir::RecordSpread::Head(ty)
                        | yulang_erased_ir::RecordSpread::Tail(ty) => {
                            self.type_is_blocked(ty, direction)
                        }
                    })
            }
            Type::Variant(variant) => {
                variant
                    .cases
                    .iter()
                    .flat_map(|case| &case.payloads)
                    .any(|payload| self.type_is_blocked(payload, direction))
                    || variant
                        .tail
                        .as_ref()
                        .is_some_and(|tail| self.type_is_blocked(tail, direction))
            }
            Type::Row { items, tail } => {
                items
                    .iter()
                    .any(|item| self.type_is_blocked(item, direction))
                    || self.type_is_blocked(tail, direction)
            }
            Type::Recursive { var, body } => {
                let mut nested = self.clone();
                nested.lower.remove(var);
                nested.upper.remove(var);
                nested.type_is_blocked(body, direction)
            }
            Type::Unknown | Type::Never | Type::Any => false,
        }
    }

    fn type_arg_is_blocked(&self, arg: &yulang_erased_ir::TypeArg, direction: BoundKind) -> bool {
        match arg {
            yulang_erased_ir::TypeArg::Type(ty) => self.type_is_blocked(ty, direction),
            yulang_erased_ir::TypeArg::Bounds(bounds) => {
                bounds
                    .lower
                    .as_ref()
                    .is_some_and(|ty| self.type_is_blocked(ty, direction))
                    || bounds
                        .upper
                        .as_ref()
                        .is_some_and(|ty| self.type_is_blocked(ty, direction))
            }
        }
    }
}

fn collect_type_vars_for_blocker(ty: &Type, out: &mut BTreeSet<TypeVar>) {
    match ty {
        Type::Var(var) => {
            out.insert(var.clone());
        }
        Type::Named { args, .. } => {
            for arg in args {
                collect_type_arg_vars_for_blocker(arg, out);
            }
        }
        Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_type_vars_for_blocker(param, out);
            collect_type_vars_for_blocker(param_effect, out);
            collect_type_vars_for_blocker(ret_effect, out);
            collect_type_vars_for_blocker(ret, out);
        }
        Type::Tuple(items) | Type::Union(items) | Type::Inter(items) => {
            for item in items {
                collect_type_vars_for_blocker(item, out);
            }
        }
        Type::Record(record) => {
            for field in &record.fields {
                collect_type_vars_for_blocker(&field.value, out);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    yulang_erased_ir::RecordSpread::Head(ty)
                    | yulang_erased_ir::RecordSpread::Tail(ty) => {
                        collect_type_vars_for_blocker(ty, out);
                    }
                }
            }
        }
        Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_type_vars_for_blocker(payload, out);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_type_vars_for_blocker(tail, out);
            }
        }
        Type::Row { items, tail } => {
            for item in items {
                collect_type_vars_for_blocker(item, out);
            }
            collect_type_vars_for_blocker(tail, out);
        }
        Type::Recursive { var, body } => {
            let inserted = out.remove(var);
            collect_type_vars_for_blocker(body, out);
            out.remove(var);
            if inserted {
                out.insert(var.clone());
            }
        }
        Type::Unknown | Type::Never | Type::Any => {}
    }
}

fn collect_type_arg_vars_for_blocker(arg: &yulang_erased_ir::TypeArg, out: &mut BTreeSet<TypeVar>) {
    match arg {
        yulang_erased_ir::TypeArg::Type(ty) => collect_type_vars_for_blocker(ty, out),
        yulang_erased_ir::TypeArg::Bounds(bounds) => {
            if let Some(lower) = &bounds.lower {
                collect_type_vars_for_blocker(lower, out);
            }
            if let Some(upper) = &bounds.upper {
                collect_type_vars_for_blocker(upper, out);
            }
        }
    }
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

    fn apply_type_bounds(&self, bounds: &TypeBounds) -> TypeBounds {
        TypeBounds {
            lower: bounds
                .lower
                .as_ref()
                .map(|lower| Box::new(self.apply_type(lower))),
            upper: bounds
                .upper
                .as_ref()
                .map(|upper| Box::new(self.apply_type(upper))),
        }
    }

    fn apply_role_requirement(&self, requirement: &RoleRequirement) -> RoleRequirement {
        RoleRequirement {
            role: requirement.role.clone(),
            args: requirement
                .args
                .iter()
                .map(|arg| match arg {
                    RoleRequirementArg::Input(bounds) => {
                        RoleRequirementArg::Input(self.apply_type_bounds(bounds))
                    }
                    RoleRequirementArg::Associated { name, bounds } => {
                        RoleRequirementArg::Associated {
                            name: name.clone(),
                            bounds: self.apply_type_bounds(bounds),
                        }
                    }
                })
                .collect(),
        }
    }

    fn apply_typeclass_obligation(&self, obligation: &TypeClassObligation) -> TypeClassObligation {
        TypeClassObligation {
            ref_id: obligation.ref_id,
            class: obligation.class.clone(),
            member: obligation.member,
            args: obligation
                .args
                .iter()
                .map(|arg| self.apply_type(arg))
                .collect(),
            associated: obligation
                .associated
                .iter()
                .map(|associated| yulang_erased_ir::AssociatedTypeConstraint {
                    name: associated.name.clone(),
                    bounds: self.apply_type_bounds(&associated.bounds),
                })
                .collect(),
        }
    }
}

struct FreshenedScheme {
    body: Type,
    requirements: Vec<RoleRequirement>,
}

struct SchemeFreshening {
    substitution: ElaborationSubstitution,
}

impl SchemeFreshening {
    fn new(solver: &mut ConstraintSolver, scheme: &Scheme) -> Self {
        let mut substitution = ElaborationSubstitution::default();
        for var in &scheme.quantified_types {
            substitution.insert(
                var.clone(),
                Type::Var(solver.fresh_type_var(var, default_for_quantified_type_var(scheme, var))),
            );
        }
        for var in &scheme.quantified_effects {
            let var = TypeVar(var.0.clone());
            substitution.insert(
                var.clone(),
                Type::Var(solver.fresh_type_var(&var, UnboundedTypeDefault::Effect)),
            );
        }
        Self { substitution }
    }

    fn substitute_type(&self, ty: &Type) -> Type {
        self.substitution.apply_type(ty)
    }

    fn substitute_role_requirement(&self, requirement: &RoleRequirement) -> RoleRequirement {
        self.substitution.apply_role_requirement(requirement)
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
    known_arg: Option<&MonoComputation>,
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
    if !computation_result_matches(expected, &actual_result) {
        return Err(ConstraintError::FunctionResultMismatch {
            slot: slot.into(),
            expected: expected.clone(),
            actual: actual_result,
        });
    }

    let scheme_arg = MonoComputation {
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
    };
    let arg = known_arg_computation_for_apply(slot, &scheme_arg, known_arg)?.unwrap_or(scheme_arg);
    let arg_type = value_type(slot, &arg.value)?;
    let arg_effect = arg.effect.row().as_type().clone();
    let ret_type = value_type(slot, &expected.value)?;
    let ret_effect = expected.effect.row().as_type().clone();

    Ok(ApplyComputation {
        callee: function_computation(slot, arg_type, arg_effect, ret_effect, ret_type)?,
        arg,
    })
}

fn typeclass_obligation_receiver_computation(
    slot: DraftComputationId,
    obligation: &TypeClassObligation,
) -> Result<Option<MonoComputation>, ConstraintError> {
    let Some(receiver) = obligation.args.first() else {
        return Ok(None);
    };
    let receiver = single_concrete_candidate(receiver).unwrap_or_else(|| receiver.clone());
    if ConcreteType::try_from_type(receiver.clone()).is_err() {
        return Ok(None);
    }
    pure_value_computation(slot, ConstraintTypeSource::FunctionParam, receiver).map(Some)
}

fn known_arg_computation_for_apply(
    slot: DraftComputationId,
    scheme_arg: &MonoComputation,
    known_arg: Option<&MonoComputation>,
) -> Result<Option<MonoComputation>, ConstraintError> {
    let Some(known_arg) = known_arg else {
        return Ok(None);
    };
    let known_value = value_type(slot, &known_arg.value)?;
    let scheme_value = value_type(slot, &scheme_arg.value)?;
    if type_fits_expected(&known_value, &scheme_value) {
        Ok(Some(known_arg.clone()))
    } else {
        Ok(None)
    }
}

fn apply_from_callee_computation(
    slot: DraftComputationId,
    expected: &MonoComputation,
    callee: &MonoComputation,
) -> Result<Option<ApplyComputation>, ConstraintError> {
    let MonoType::Value(function) = &callee.value else {
        return Ok(None);
    };
    let Type::Fun {
        param,
        param_effect,
        ret_effect,
        ret,
    } = function.as_type()
    else {
        return Ok(None);
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
    if !computation_result_matches(expected, &actual_result) {
        return Ok(None);
    }
    Ok(Some(ApplyComputation {
        callee: callee.clone(),
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
    }))
}

fn handle_payload_computation(
    slot: DraftComputationId,
    arm: &yulang_erased_ir::HandleArm,
    body: &MonoComputation,
    env: &ConstraintEnvironment<'_>,
) -> Result<MonoComputation, ConstraintError> {
    if arm.effect.segments.is_empty() {
        return Ok(pure_pattern_value_computation(body));
    }
    let payload = env
        .effect_operation_scheme(&arm.effect)
        .and_then(|scheme| operation_payload_type(&scheme.body))
        .unwrap_or_else(unit_type);
    pure_value_computation(slot, ConstraintTypeSource::FunctionParam, payload)
}

fn handle_resume_computation(
    slot: DraftComputationId,
    arm: &yulang_erased_ir::HandleArm,
    body: &MonoComputation,
    env: &ConstraintEnvironment<'_>,
) -> Result<MonoComputation, ConstraintError> {
    let resume_param = env
        .effect_operation_scheme(&arm.effect)
        .and_then(|scheme| operation_resume_type(&scheme.body))
        .unwrap_or_else(unit_type);
    let body_value = value_type(slot, &body.value)?;
    let body_effect = body.effect.row().as_type().clone();
    function_computation(slot, resume_param, Type::Never, body_effect, body_value)
}

fn operation_payload_type(ty: &Type) -> Option<Type> {
    let Type::Fun { param, .. } = ty else {
        return None;
    };
    Some((**param).clone())
}

fn operation_resume_type(ty: &Type) -> Option<Type> {
    let Type::Fun { ret, .. } = ty else {
        return None;
    };
    Some((**ret).clone())
}

fn computation_result_matches(expected: &MonoComputation, actual: &MonoComputation) -> bool {
    mono_type_fits_expected(&actual.value, &expected.value)
        && effect_row_fits_expected(
            actual.effect.row().as_type(),
            expected.effect.row().as_type(),
        )
}

fn mono_type_fits_expected(actual: &MonoType, expected: &MonoType) -> bool {
    match (actual, expected) {
        (MonoType::Value(actual), MonoType::Value(expected)) => {
            type_fits_expected(actual.as_type(), expected.as_type())
        }
        _ => actual == expected,
    }
}

fn type_fits_expected(actual: &Type, expected: &Type) -> bool {
    let actual_candidate = single_concrete_candidate(actual);
    let expected_candidate = single_concrete_candidate(expected);
    if actual_candidate.is_some() || expected_candidate.is_some() {
        let actual = actual_candidate.as_ref().unwrap_or(actual);
        let expected = expected_candidate.as_ref().unwrap_or(expected);
        return actual == expected || type_fits_expected(actual, expected);
    }
    actual == expected
        || matches!(actual, Type::Never)
        || matches!(expected, Type::Any)
        || matches!(
            (actual, expected),
            (
                Type::Fun {
                    param: actual_param,
                    param_effect: actual_param_effect,
                    ret_effect: actual_ret_effect,
                    ret: actual_ret,
                },
                Type::Fun {
                    param: expected_param,
                    param_effect: expected_param_effect,
                    ret_effect: expected_ret_effect,
                    ret: expected_ret,
                },
            ) if type_fits_expected(expected_param, actual_param)
                && effect_row_fits_expected(actual_param_effect, expected_param_effect)
                && effect_row_fits_expected(actual_ret_effect, expected_ret_effect)
                && type_fits_expected(actual_ret, expected_ret)
        )
        || matches!(
            (actual, expected),
            (
                Type::Named {
                    path: actual_path,
                    args: actual_args,
                },
                Type::Named {
                    path: expected_path,
                    args: expected_args,
                },
            ) if actual_path == expected_path && actual_args == expected_args
        )
}

fn effect_row_fits_expected(actual: &Type, expected: &Type) -> bool {
    matches!(actual, Type::Never)
        || matches!(expected, Type::Any)
        || effect_rows_equivalent(actual, expected)
        || effect_row_is_subset(actual, expected)
}

fn effect_rows_equivalent(expected: &Type, actual: &Type) -> bool {
    normalized_effect_row(expected) == normalized_effect_row(actual)
}

fn effect_row_is_subset(actual: &Type, expected: &Type) -> bool {
    if effect_row_allows_any(expected) {
        return true;
    }
    if effect_row_allows_any(actual) {
        return false;
    }
    let actual_atoms = effect_row_atoms(actual);
    let expected_atoms = effect_row_atoms(expected);
    actual_atoms
        .iter()
        .all(|actual| expected_atoms.iter().any(|expected| expected == actual))
}

fn effect_row_allows_any(row: &Type) -> bool {
    match row {
        Type::Any => true,
        Type::Row { items, tail } => {
            items.iter().any(effect_row_allows_any) || effect_row_allows_any(tail)
        }
        Type::Union(items) | Type::Inter(items) => items.iter().any(effect_row_allows_any),
        _ => false,
    }
}

fn effect_row_atoms(row: &Type) -> Vec<Type> {
    match row {
        Type::Never => Vec::new(),
        Type::Row { items, tail } => {
            let mut atoms = Vec::new();
            for item in items {
                atoms.extend(effect_row_atoms(item));
            }
            atoms.extend(effect_row_atoms(tail));
            dedup_normalized_types(atoms)
        }
        Type::Union(items) | Type::Inter(items) => {
            let mut atoms = Vec::new();
            for item in items {
                atoms.extend(effect_row_atoms(item));
            }
            dedup_normalized_types(atoms)
        }
        other => vec![
            concretize_type_candidate(other)
                .unwrap_or_else(|| normalize_concrete_candidate(other.clone())),
        ],
    }
}

fn normalized_effect_row(row: &Type) -> (Vec<Type>, Type) {
    match row {
        Type::Never => (Vec::new(), Type::Never),
        Type::Row { items, tail } => {
            let mut normalized_items = Vec::new();
            for item in items {
                let (mut item_items, item_tail) = normalized_effect_row(item);
                normalized_items.append(&mut item_items);
                if !matches!(item_tail, Type::Never) {
                    normalized_items.push(item_tail);
                }
            }
            let (mut tail_items, tail) = normalized_effect_row_tail(tail);
            normalized_items.append(&mut tail_items);
            (normalized_items, tail)
        }
        other => (vec![other.clone()], Type::Never),
    }
}

fn normalized_effect_row_tail(row: &Type) -> (Vec<Type>, Type) {
    match row {
        Type::Never => (Vec::new(), Type::Never),
        Type::Row { .. } => normalized_effect_row(row),
        other => (Vec::new(), other.clone()),
    }
}

fn single_concrete_candidate(ty: &Type) -> Option<Type> {
    if let Type::Union(items) | Type::Inter(items) = ty {
        let mut candidates = Vec::new();
        for item in items {
            collect_concrete_candidates(item, &mut candidates);
        }
        return (candidates.len() == 1 && candidates[0] != *ty).then(|| candidates.remove(0));
    }
    let mut candidates = Vec::new();
    collect_concrete_candidates(ty, &mut candidates);
    (candidates.len() == 1 && candidates[0] != *ty).then(|| candidates.remove(0))
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

fn known_apply_result_computation(
    _slot: DraftComputationId,
    ret: Type,
    ret_effect: Type,
) -> Result<Option<MonoComputation>, ConstraintError> {
    let Ok(value) = ConcreteType::try_from_type(ret) else {
        return Ok(None);
    };
    let Ok(effect) = ConcreteType::try_from_type(ret_effect) else {
        return Ok(None);
    };
    Ok(Some(MonoComputation {
        value: MonoType::Value(value),
        effect: MonoEffect::new(effect),
    }))
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

pub(crate) fn instantiate_typeclass_obligation_instances(
    scheme: &Scheme,
    signature: &MonoComputation,
    instances: &BTreeMap<RefId, TypeclassObligationInstanceDemand>,
) -> BTreeMap<RefId, TypeclassObligationInstanceDemand> {
    let MonoType::Value(value) = &signature.value else {
        return instances.clone();
    };
    let mut instantiation = TypeInstantiation::new(scheme);
    if !instantiation.match_type(&scheme.body, value.as_type()) {
        return instances.clone();
    }

    instances
        .iter()
        .map(|(ref_id, demand)| {
            let mut demand = demand.clone();
            demand.obligation.args = demand
                .obligation
                .args
                .iter()
                .map(|arg| instantiation.substitute_type_with_defaults(arg))
                .collect();
            demand.obligation.associated = demand
                .obligation
                .associated
                .iter()
                .map(|associated| yulang_erased_ir::AssociatedTypeConstraint {
                    name: associated.name.clone(),
                    bounds: instantiation.substitute_type_bounds_with_defaults(&associated.bounds),
                })
                .collect();
            (*ref_id, demand)
        })
        .collect()
}

pub(crate) fn instantiate_typeclass_obligations_for_signature(
    scheme: &Scheme,
    signature: &MonoComputation,
    env: &ConstraintEnvironment<'_>,
) -> BTreeMap<RefId, TypeClassObligation> {
    let MonoType::Value(value) = &signature.value else {
        return BTreeMap::new();
    };
    let mut instantiation = TypeInstantiation::new(scheme);
    if !instantiation.match_type(&scheme.body, value.as_type()) {
        return BTreeMap::new();
    }
    solve_scheme_requirements_to_fixpoint(&mut instantiation, scheme, env);

    scheme
        .typeclass_obligations
        .iter()
        .map(|obligation| {
            let mut obligation = obligation.clone();
            obligation.args = obligation
                .args
                .iter()
                .map(|arg| instantiation.substitute_type(arg))
                .collect();
            obligation.associated = obligation
                .associated
                .iter()
                .map(|associated| yulang_erased_ir::AssociatedTypeConstraint {
                    name: associated.name.clone(),
                    bounds: instantiation.substitute_type_bounds(&associated.bounds),
                })
                .collect();
            (obligation.ref_id, obligation)
        })
        .collect()
}

fn typeclass_candidate_matches_obligation(
    candidate: &TypeClassImplCandidate,
    obligation: &TypeClassObligation,
) -> bool {
    crate::typeclass_candidate_matches(candidate, obligation)
}

fn select_most_specific_typeclass_candidates<'a>(
    candidates: Vec<&'a TypeClassImplCandidate>,
) -> Vec<&'a TypeClassImplCandidate> {
    crate::select_most_specific_typeclass_candidates(candidates)
}

pub(crate) fn direct_apply_ret_effect_from_scheme_spine(
    scheme: &Scheme,
    result_value: &Type,
    args: &[&ErasedExpr],
    env: &ConstraintEnvironment<'_>,
) -> Option<Type> {
    let needs_instantiation = scheme_needs_instantiation(scheme);
    let mut instantiation = TypeInstantiation::new(scheme);

    let mut current = scheme.body.clone();
    for (index, arg) in args.iter().enumerate() {
        let Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } = current
        else {
            return None;
        };

        if needs_instantiation {
            let arg_value = known_value_type(arg, env)?;
            if !match_apply_arg_type(&mut instantiation, &param, &arg_value)
                || !instantiation.match_type(&param_effect, &Type::Never)
            {
                return None;
            }
        }

        let is_last_arg = index + 1 == args.len();
        if is_last_arg {
            if needs_instantiation {
                if !instantiation.match_type(&ret, result_value) {
                    return None;
                }
                let ret_effect = instantiation.substitute_type_with_defaults(&ret_effect);
                return (!scheme_quantified_vars_appear_in_type(scheme, &ret_effect))
                    .then_some(ret_effect);
            }
            return (ret.as_ref() == result_value).then_some(*ret_effect);
        }

        current = if needs_instantiation {
            instantiation.substitute_type(&ret)
        } else {
            *ret
        };
    }
    None
}

fn collect_apply_spine_with_final<'a>(
    callee: &'a ErasedExpr,
    arg: &'a ErasedExpr,
) -> (&'a ErasedExpr, Vec<&'a ErasedExpr>) {
    let mut head = callee;
    let mut args = vec![arg];
    while let ErasedExpr::Apply { callee, arg } = head {
        args.push(arg);
        head = callee;
    }
    args.reverse();
    (head, args)
}

fn match_apply_arg_type(
    instantiation: &mut TypeInstantiation,
    param: &Type,
    arg_value: &Type,
) -> bool {
    matches!(arg_value, Type::Never)
        || matches!(param, Type::Any)
        || instantiation.match_type(param, arg_value)
}

fn match_apply_arg_effect(
    instantiation: &mut TypeInstantiation,
    param_effect: &Type,
    arg_effect: &Type,
) -> bool {
    if matches!(arg_effect, Type::Never) || matches!(param_effect, Type::Any) {
        return true;
    }
    let mut trial = instantiation.clone();
    if match_effect_row_pattern(&mut trial, param_effect, arg_effect) {
        *instantiation = trial;
        return true;
    }
    false
}

fn solve_scheme_requirements_to_fixpoint(
    instantiation: &mut TypeInstantiation,
    scheme: &Scheme,
    env: &ConstraintEnvironment<'_>,
) {
    loop {
        let before = instantiation.assignments.clone();
        for requirement in &scheme.requirements {
            let mut matches = env
                .refs
                .typeclass_impl_candidates
                .iter()
                .filter(|candidate| candidate.class == requirement.role)
                .filter_map(|candidate| {
                    let mut matcher =
                        RequirementCandidateMatcher::new(instantiation.clone(), requirement);
                    matcher
                        .match_candidate(candidate)
                        .then(|| matcher.into_instantiation())
                })
                .collect::<Vec<_>>();
            if matches.len() == 1 {
                *instantiation = matches.remove(0);
                break;
            }
        }
        if instantiation.assignments == before {
            break;
        }
    }
}

struct GraphRoleCandidateResolution<'a> {
    candidate: &'a TypeClassImplCandidate,
    candidate_assignments: BTreeMap<TypeVar, Type>,
}

impl<'a> GraphRoleCandidateResolution<'a> {
    fn select(requirement: &RoleRequirement, env: &'a ConstraintEnvironment<'_>) -> Option<Self> {
        let matches = env
            .refs
            .typeclass_impl_candidates
            .iter()
            .filter(|candidate| candidate.class == requirement.role)
            .filter(|candidate| GraphRoleCandidateMatcher::matches(candidate, requirement))
            .collect::<Vec<_>>();
        let matches = select_most_specific_typeclass_candidates(matches);
        let [candidate] = matches.as_slice() else {
            return None;
        };
        let mut matcher = GraphRoleCandidateMatcher::default();
        matcher
            .match_candidate_inputs(candidate, requirement)
            .then_some(Self {
                candidate,
                candidate_assignments: matcher.candidate_assignments,
            })
    }

    fn prerequisites(&self) -> Vec<RoleRequirement> {
        self.candidate
            .prerequisites
            .iter()
            .map(|requirement| RoleRequirement {
                role: requirement.role.clone(),
                args: requirement
                    .args
                    .iter()
                    .map(|arg| match arg {
                        RoleRequirementArg::Input(bounds) => {
                            RoleRequirementArg::Input(self.substitute_candidate_bounds(bounds))
                        }
                        RoleRequirementArg::Associated { name, bounds } => {
                            RoleRequirementArg::Associated {
                                name: name.clone(),
                                bounds: self.substitute_candidate_bounds(bounds),
                            }
                        }
                    })
                    .collect(),
            })
            .collect()
    }

    fn substitute_candidate_bounds(&self, bounds: &TypeBounds) -> TypeBounds {
        TypeBounds {
            lower: bounds
                .lower
                .as_ref()
                .map(|lower| Box::new(self.substitute_candidate_type(lower))),
            upper: bounds
                .upper
                .as_ref()
                .map(|upper| Box::new(self.substitute_candidate_type(upper))),
        }
    }

    fn substitute_candidate_type(&self, ty: &Type) -> Type {
        substitute_candidate_type_with_assignments(ty, &self.candidate_assignments)
    }
}

#[derive(Default)]
struct GraphRoleCandidateMatcher {
    candidate_assignments: BTreeMap<TypeVar, Type>,
}

impl GraphRoleCandidateMatcher {
    fn matches(candidate: &TypeClassImplCandidate, requirement: &RoleRequirement) -> bool {
        let mut matcher = Self::default();
        matcher.match_candidate_inputs(candidate, requirement)
    }

    fn match_candidate_inputs(
        &mut self,
        candidate: &TypeClassImplCandidate,
        requirement: &RoleRequirement,
    ) -> bool {
        let mut requirement_inputs = requirement.args.iter().filter_map(|arg| match arg {
            RoleRequirementArg::Input(bounds) => Some(bounds),
            RoleRequirementArg::Associated { .. } => None,
        });
        for arg in &candidate.args {
            let RoleRequirementArg::Input(candidate_bounds) = arg else {
                continue;
            };
            let Some(requirement_bounds) = requirement_inputs.next() else {
                return false;
            };
            if !self.match_candidate_input_bounds(candidate_bounds, requirement_bounds) {
                return false;
            }
        }
        requirement_inputs.next().is_none()
    }

    fn match_candidate_input_bounds(
        &mut self,
        candidate: &TypeBounds,
        requirement: &TypeBounds,
    ) -> bool {
        let Some(candidate) = exact_type_from_bounds(candidate) else {
            return false;
        };
        let Some(requirement) = ready_type_from_bounds(requirement) else {
            return false;
        };
        role_input_type_is_ready(&requirement) && self.match_candidate_type(candidate, &requirement)
    }

    fn match_candidate_type(&mut self, candidate: &Type, actual: &Type) -> bool {
        match candidate {
            Type::Var(var) => self.assign_candidate_var(var.clone(), actual.clone()),
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
                        .all(|(candidate, actual)| self.match_candidate_type_arg(candidate, actual))
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
                self.match_candidate_type(param, actual_param)
                    && self.match_candidate_type(param_effect, actual_param_effect)
                    && self.match_candidate_type(ret_effect, actual_ret_effect)
                    && self.match_candidate_type(ret, actual_ret)
            }
            Type::Tuple(items) => {
                let Type::Tuple(actual_items) = actual else {
                    return false;
                };
                items.len() == actual_items.len()
                    && items
                        .iter()
                        .zip(actual_items)
                        .all(|(candidate, actual)| self.match_candidate_type(candidate, actual))
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
                        .all(|(candidate, actual)| {
                            candidate.name == actual.name
                                && candidate.optional == actual.optional
                                && self.match_candidate_type(&candidate.value, &actual.value)
                        })
                    && match (&record.spread, &actual_record.spread) {
                        (Some(candidate), Some(actual)) => {
                            self.match_candidate_record_spread(candidate, actual)
                        }
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
                        .all(|(candidate, actual)| {
                            candidate.name == actual.name
                                && candidate.payloads.len() == actual.payloads.len()
                                && candidate.payloads.iter().zip(&actual.payloads).all(
                                    |(candidate, actual)| {
                                        self.match_candidate_type(candidate, actual)
                                    },
                                )
                        })
                    && match (&variant.tail, &actual_variant.tail) {
                        (Some(candidate), Some(actual)) => {
                            self.match_candidate_type(candidate, actual)
                        }
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
                        .all(|(candidate, actual)| self.match_candidate_type(candidate, actual))
                    && self.match_candidate_type(tail, actual_tail)
            }
            Type::Union(items) => {
                self.match_candidate_variadic_type(items, actual, TypeVariant::Union)
            }
            Type::Inter(items) => {
                self.match_candidate_variadic_type(items, actual, TypeVariant::Inter)
            }
            Type::Recursive { var, body } => {
                let Type::Recursive {
                    var: actual_var,
                    body: actual_body,
                } = actual
                else {
                    return false;
                };
                var == actual_var && self.match_candidate_type(body, actual_body)
            }
            Type::Unknown | Type::Never | Type::Any => candidate == actual,
        }
    }

    fn match_candidate_type_arg(
        &mut self,
        candidate: &yulang_erased_ir::TypeArg,
        actual: &yulang_erased_ir::TypeArg,
    ) -> bool {
        match (candidate, actual) {
            (
                yulang_erased_ir::TypeArg::Type(candidate),
                yulang_erased_ir::TypeArg::Type(actual),
            ) => self.match_candidate_type(candidate, actual),
            (
                yulang_erased_ir::TypeArg::Bounds(candidate),
                yulang_erased_ir::TypeArg::Bounds(actual),
            ) => {
                let Some(candidate) = exact_type_from_bounds(candidate) else {
                    return false;
                };
                let Some(actual) = ready_type_from_bounds(actual) else {
                    return false;
                };
                role_input_type_is_ready(&actual) && self.match_candidate_type(candidate, &actual)
            }
            _ => false,
        }
    }

    fn match_candidate_record_spread(
        &mut self,
        candidate: &yulang_erased_ir::RecordSpread,
        actual: &yulang_erased_ir::RecordSpread,
    ) -> bool {
        match (candidate, actual) {
            (
                yulang_erased_ir::RecordSpread::Head(candidate),
                yulang_erased_ir::RecordSpread::Head(actual),
            )
            | (
                yulang_erased_ir::RecordSpread::Tail(candidate),
                yulang_erased_ir::RecordSpread::Tail(actual),
            ) => self.match_candidate_type(candidate, actual),
            _ => false,
        }
    }

    fn match_candidate_variadic_type(
        &mut self,
        items: &[Type],
        actual: &Type,
        variant: TypeVariant,
    ) -> bool {
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
                .all(|(candidate, actual)| self.match_candidate_type(candidate, actual))
    }

    fn assign_candidate_var(&mut self, var: TypeVar, actual: Type) -> bool {
        if let Some(existing) = self.candidate_assignments.get(&var) {
            return existing == &actual;
        }
        self.candidate_assignments.insert(var, actual);
        true
    }
}

fn exact_type_from_bounds(bounds: &TypeBounds) -> Option<&Type> {
    let lower = bounds.lower.as_deref()?;
    let upper = bounds.upper.as_deref()?;
    (lower == upper).then_some(lower)
}

fn ready_type_from_bounds(bounds: &TypeBounds) -> Option<Type> {
    type_bounds_concrete_candidate(bounds).or_else(|| exact_type_from_bounds(bounds).cloned())
}

fn type_arg_value(arg: &TypeArg) -> Option<Type> {
    match arg {
        TypeArg::Type(ty) => Some(ty.clone()),
        TypeArg::Bounds(bounds) => ready_type_from_bounds(bounds),
    }
}

fn role_requirement_associated_bounds<'a>(
    requirement: &'a RoleRequirement,
    target: &Name,
) -> Option<&'a TypeBounds> {
    requirement.args.iter().find_map(|arg| match arg {
        RoleRequirementArg::Associated { name, bounds } if name == target => Some(bounds),
        _ => None,
    })
}

fn role_input_type_is_ready(ty: &Type) -> bool {
    match ty {
        Type::Unknown | Type::Var(_) => false,
        Type::Named { args, .. } => args.iter().all(role_input_type_arg_is_ready),
        Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            role_input_type_is_ready(param)
                && role_input_type_is_ready(param_effect)
                && role_input_type_is_ready(ret_effect)
                && role_input_type_is_ready(ret)
        }
        Type::Tuple(items) | Type::Union(items) | Type::Inter(items) => {
            items.iter().all(role_input_type_is_ready)
        }
        Type::Record(record) => {
            record
                .fields
                .iter()
                .all(|field| role_input_type_is_ready(&field.value))
                && record.spread.as_ref().is_none_or(|spread| match spread {
                    yulang_erased_ir::RecordSpread::Head(ty)
                    | yulang_erased_ir::RecordSpread::Tail(ty) => role_input_type_is_ready(ty),
                })
        }
        Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .flat_map(|case| &case.payloads)
                .all(role_input_type_is_ready)
                && variant
                    .tail
                    .as_ref()
                    .is_none_or(|tail| role_input_type_is_ready(tail))
        }
        Type::Row { items, tail } => {
            items.iter().all(role_input_type_is_ready) && role_input_type_is_ready(tail)
        }
        Type::Recursive { var, body } => {
            !type_mentions_type_var(body, var) && role_input_type_is_ready(body)
        }
        Type::Never | Type::Any => true,
    }
}

fn role_input_type_arg_is_ready(arg: &yulang_erased_ir::TypeArg) -> bool {
    match arg {
        yulang_erased_ir::TypeArg::Type(ty) => role_input_type_is_ready(ty),
        yulang_erased_ir::TypeArg::Bounds(bounds) => {
            ready_type_from_bounds(bounds).is_some_and(|ty| role_input_type_is_ready(&ty))
        }
    }
}

fn substitute_candidate_type_with_assignments(
    ty: &Type,
    assignments: &BTreeMap<TypeVar, Type>,
) -> Type {
    match ty {
        Type::Var(var) => assignments.get(var).cloned().unwrap_or_else(|| ty.clone()),
        Type::Named { path, args } => Type::Named {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| substitute_candidate_type_arg_with_assignments(arg, assignments))
                .collect(),
        },
        Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => Type::Fun {
            param: Box::new(substitute_candidate_type_with_assignments(
                param,
                assignments,
            )),
            param_effect: Box::new(substitute_candidate_type_with_assignments(
                param_effect,
                assignments,
            )),
            ret_effect: Box::new(substitute_candidate_type_with_assignments(
                ret_effect,
                assignments,
            )),
            ret: Box::new(substitute_candidate_type_with_assignments(ret, assignments)),
        },
        Type::Tuple(items) => Type::Tuple(
            items
                .iter()
                .map(|item| substitute_candidate_type_with_assignments(item, assignments))
                .collect(),
        ),
        Type::Record(record) => Type::Record(yulang_erased_ir::RecordType {
            fields: record
                .fields
                .iter()
                .map(|field| yulang_erased_ir::RecordField {
                    name: field.name.clone(),
                    value: substitute_candidate_type_with_assignments(&field.value, assignments),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.as_ref().map(|spread| match spread {
                yulang_erased_ir::RecordSpread::Head(ty) => yulang_erased_ir::RecordSpread::Head(
                    Box::new(substitute_candidate_type_with_assignments(ty, assignments)),
                ),
                yulang_erased_ir::RecordSpread::Tail(ty) => yulang_erased_ir::RecordSpread::Tail(
                    Box::new(substitute_candidate_type_with_assignments(ty, assignments)),
                ),
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
                        .map(|payload| {
                            substitute_candidate_type_with_assignments(payload, assignments)
                        })
                        .collect(),
                })
                .collect(),
            tail: variant.tail.as_ref().map(|tail| {
                Box::new(substitute_candidate_type_with_assignments(
                    tail,
                    assignments,
                ))
            }),
        }),
        Type::Row { items, tail } => Type::Row {
            items: items
                .iter()
                .map(|item| substitute_candidate_type_with_assignments(item, assignments))
                .collect(),
            tail: Box::new(substitute_candidate_type_with_assignments(
                tail,
                assignments,
            )),
        },
        Type::Union(items) => Type::Union(
            items
                .iter()
                .map(|item| substitute_candidate_type_with_assignments(item, assignments))
                .collect(),
        ),
        Type::Inter(items) => Type::Inter(
            items
                .iter()
                .map(|item| substitute_candidate_type_with_assignments(item, assignments))
                .collect(),
        ),
        Type::Recursive { var, body } => Type::Recursive {
            var: var.clone(),
            body: Box::new(substitute_candidate_type_with_assignments(
                body,
                assignments,
            )),
        },
        Type::Unknown | Type::Never | Type::Any => ty.clone(),
    }
}

fn substitute_candidate_type_arg_with_assignments(
    arg: &yulang_erased_ir::TypeArg,
    assignments: &BTreeMap<TypeVar, Type>,
) -> yulang_erased_ir::TypeArg {
    match arg {
        yulang_erased_ir::TypeArg::Type(ty) => yulang_erased_ir::TypeArg::Type(
            substitute_candidate_type_with_assignments(ty, assignments),
        ),
        yulang_erased_ir::TypeArg::Bounds(bounds) => {
            yulang_erased_ir::TypeArg::Bounds(TypeBounds {
                lower: bounds.lower.as_ref().map(|lower| {
                    Box::new(substitute_candidate_type_with_assignments(
                        lower,
                        assignments,
                    ))
                }),
                upper: bounds.upper.as_ref().map(|upper| {
                    Box::new(substitute_candidate_type_with_assignments(
                        upper,
                        assignments,
                    ))
                }),
            })
        }
    }
}

struct RequirementCandidateMatcher<'a> {
    instantiation: TypeInstantiation,
    requirement: &'a RoleRequirement,
    candidate_assignments: BTreeMap<TypeVar, Type>,
}

impl<'a> RequirementCandidateMatcher<'a> {
    fn new(instantiation: TypeInstantiation, requirement: &'a RoleRequirement) -> Self {
        Self {
            instantiation,
            requirement,
            candidate_assignments: BTreeMap::new(),
        }
    }

    fn into_instantiation(self) -> TypeInstantiation {
        self.instantiation
    }

    fn match_candidate(&mut self, candidate: &TypeClassImplCandidate) -> bool {
        let mut requirement_inputs = self.requirement.args.iter().filter_map(|arg| match arg {
            RoleRequirementArg::Input(bounds) => Some(bounds),
            RoleRequirementArg::Associated { .. } => None,
        });
        for arg in &candidate.args {
            match arg {
                RoleRequirementArg::Input(candidate_bounds) => {
                    let Some(requirement_bounds) = requirement_inputs.next() else {
                        return false;
                    };
                    if !self.match_candidate_input_bounds(candidate_bounds, requirement_bounds) {
                        return false;
                    }
                }
                RoleRequirementArg::Associated {
                    name,
                    bounds: candidate_bounds,
                } => {
                    let Some(requirement_bounds) =
                        self.requirement.args.iter().find_map(|arg| match arg {
                            RoleRequirementArg::Associated {
                                name: requirement_name,
                                bounds,
                            } if requirement_name == name => Some(bounds),
                            _ => None,
                        })
                    else {
                        continue;
                    };
                    self.match_requirement_associated_bounds(requirement_bounds, candidate_bounds);
                }
            }
        }
        requirement_inputs.next().is_none()
    }

    fn match_candidate_input_bounds(
        &mut self,
        candidate: &TypeBounds,
        requirement: &TypeBounds,
    ) -> bool {
        let requirement = self.instantiation.substitute_type_bounds(requirement);
        let Some(candidate) = exact_type_from_bounds(candidate) else {
            return false;
        };
        let Some(requirement) = ready_type_from_bounds(&requirement) else {
            return false;
        };
        role_input_type_is_ready(&requirement) && self.match_candidate_type(candidate, &requirement)
    }

    fn match_candidate_bounds(
        &mut self,
        candidate: &yulang_erased_ir::TypeBounds,
        actual: &yulang_erased_ir::TypeBounds,
    ) -> bool {
        match (&candidate.lower, &actual.lower) {
            (Some(candidate), Some(actual)) if !self.match_candidate_type(candidate, actual) => {
                return false;
            }
            (None, None) | (Some(_), Some(_)) => {}
            _ => return false,
        }
        match (&candidate.upper, &actual.upper) {
            (Some(candidate), Some(actual)) if !self.match_candidate_type(candidate, actual) => {
                return false;
            }
            (None, None) | (Some(_), Some(_)) => {}
            _ => return false,
        }
        true
    }

    fn match_candidate_type(&mut self, candidate: &Type, actual: &Type) -> bool {
        match candidate {
            Type::Var(var) => self.assign_candidate_var(var.clone(), actual.clone()),
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
                        .all(|(candidate, actual)| self.match_candidate_type_arg(candidate, actual))
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
                self.match_candidate_type(param, actual_param)
                    && self.match_candidate_type(param_effect, actual_param_effect)
                    && self.match_candidate_type(ret_effect, actual_ret_effect)
                    && self.match_candidate_type(ret, actual_ret)
            }
            Type::Tuple(items) => {
                let Type::Tuple(actual_items) = actual else {
                    return false;
                };
                items.len() == actual_items.len()
                    && items
                        .iter()
                        .zip(actual_items)
                        .all(|(candidate, actual)| self.match_candidate_type(candidate, actual))
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
                        .all(|(candidate, actual)| {
                            candidate.name == actual.name
                                && candidate.optional == actual.optional
                                && self.match_candidate_type(&candidate.value, &actual.value)
                        })
                    && match (&record.spread, &actual_record.spread) {
                        (Some(candidate), Some(actual)) => {
                            self.match_candidate_record_spread(candidate, actual)
                        }
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
                        .all(|(candidate, actual)| {
                            candidate.name == actual.name
                                && candidate.payloads.len() == actual.payloads.len()
                                && candidate.payloads.iter().zip(&actual.payloads).all(
                                    |(candidate, actual)| {
                                        self.match_candidate_type(candidate, actual)
                                    },
                                )
                        })
                    && match (&variant.tail, &actual_variant.tail) {
                        (Some(candidate), Some(actual)) => {
                            self.match_candidate_type(candidate, actual)
                        }
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
                        .all(|(candidate, actual)| self.match_candidate_type(candidate, actual))
                    && self.match_candidate_type(tail, actual_tail)
            }
            Type::Union(items) => {
                self.match_candidate_variadic_type(items, actual, TypeVariant::Union)
            }
            Type::Inter(items) => {
                self.match_candidate_variadic_type(items, actual, TypeVariant::Inter)
            }
            Type::Recursive { var, body } => {
                let Type::Recursive {
                    var: actual_var,
                    body: actual_body,
                } = actual
                else {
                    return false;
                };
                var == actual_var && self.match_candidate_type(body, actual_body)
            }
            Type::Unknown | Type::Never | Type::Any => candidate == actual,
        }
    }

    fn match_candidate_type_arg(
        &mut self,
        candidate: &yulang_erased_ir::TypeArg,
        actual: &yulang_erased_ir::TypeArg,
    ) -> bool {
        match (candidate, actual) {
            (
                yulang_erased_ir::TypeArg::Type(candidate),
                yulang_erased_ir::TypeArg::Type(actual),
            ) => self.match_candidate_type(candidate, actual),
            (
                yulang_erased_ir::TypeArg::Bounds(candidate),
                yulang_erased_ir::TypeArg::Bounds(actual),
            ) => self.match_candidate_bounds(candidate, actual),
            _ => false,
        }
    }

    fn match_candidate_record_spread(
        &mut self,
        candidate: &yulang_erased_ir::RecordSpread,
        actual: &yulang_erased_ir::RecordSpread,
    ) -> bool {
        match (candidate, actual) {
            (
                yulang_erased_ir::RecordSpread::Head(candidate),
                yulang_erased_ir::RecordSpread::Head(actual),
            )
            | (
                yulang_erased_ir::RecordSpread::Tail(candidate),
                yulang_erased_ir::RecordSpread::Tail(actual),
            ) => self.match_candidate_type(candidate, actual),
            _ => false,
        }
    }

    fn match_candidate_variadic_type(
        &mut self,
        items: &[Type],
        actual: &Type,
        variant: TypeVariant,
    ) -> bool {
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
                .all(|(candidate, actual)| self.match_candidate_type(candidate, actual))
    }

    fn assign_candidate_var(&mut self, var: TypeVar, actual: Type) -> bool {
        if let Some(existing) = self.candidate_assignments.get(&var) {
            return existing == &actual;
        }
        self.candidate_assignments.insert(var, actual);
        true
    }

    fn match_requirement_associated_bounds(
        &mut self,
        requirement: &yulang_erased_ir::TypeBounds,
        candidate: &yulang_erased_ir::TypeBounds,
    ) {
        if let (Some(requirement), Some(candidate)) = (&requirement.lower, &candidate.lower) {
            let requirement = self.instantiation.substitute_type(requirement);
            let candidate = self.substitute_candidate_type(candidate);
            let mut trial = self.instantiation.clone();
            if trial.match_type(&requirement, &candidate) {
                self.instantiation = trial;
            }
        }
        if let (Some(requirement), Some(candidate)) = (&requirement.upper, &candidate.upper) {
            let requirement = self.instantiation.substitute_type(requirement);
            let candidate = self.substitute_candidate_type(candidate);
            let mut trial = self.instantiation.clone();
            if trial.match_type(&requirement, &candidate) {
                self.instantiation = trial;
            }
        }
    }

    fn substitute_candidate_type(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(var) => self
                .candidate_assignments
                .get(var)
                .cloned()
                .unwrap_or_else(|| ty.clone()),
            Type::Named { path, args } => Type::Named {
                path: path.clone(),
                args: args
                    .iter()
                    .map(|arg| self.substitute_candidate_type_arg(arg))
                    .collect(),
            },
            Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => Type::Fun {
                param: Box::new(self.substitute_candidate_type(param)),
                param_effect: Box::new(self.substitute_candidate_type(param_effect)),
                ret_effect: Box::new(self.substitute_candidate_type(ret_effect)),
                ret: Box::new(self.substitute_candidate_type(ret)),
            },
            Type::Tuple(items) => Type::Tuple(
                items
                    .iter()
                    .map(|item| self.substitute_candidate_type(item))
                    .collect(),
            ),
            Type::Record(record) => Type::Record(yulang_erased_ir::RecordType {
                fields: record
                    .fields
                    .iter()
                    .map(|field| yulang_erased_ir::RecordField {
                        name: field.name.clone(),
                        value: self.substitute_candidate_type(&field.value),
                        optional: field.optional,
                    })
                    .collect(),
                spread: record.spread.as_ref().map(|spread| match spread {
                    yulang_erased_ir::RecordSpread::Head(ty) => {
                        yulang_erased_ir::RecordSpread::Head(Box::new(
                            self.substitute_candidate_type(ty),
                        ))
                    }
                    yulang_erased_ir::RecordSpread::Tail(ty) => {
                        yulang_erased_ir::RecordSpread::Tail(Box::new(
                            self.substitute_candidate_type(ty),
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
                            .map(|payload| self.substitute_candidate_type(payload))
                            .collect(),
                    })
                    .collect(),
                tail: variant
                    .tail
                    .as_ref()
                    .map(|tail| Box::new(self.substitute_candidate_type(tail))),
            }),
            Type::Row { items, tail } => Type::Row {
                items: items
                    .iter()
                    .map(|item| self.substitute_candidate_type(item))
                    .collect(),
                tail: Box::new(self.substitute_candidate_type(tail)),
            },
            Type::Union(items) => Type::Union(
                items
                    .iter()
                    .map(|item| self.substitute_candidate_type(item))
                    .collect(),
            ),
            Type::Inter(items) => Type::Inter(
                items
                    .iter()
                    .map(|item| self.substitute_candidate_type(item))
                    .collect(),
            ),
            Type::Recursive { var, body } => Type::Recursive {
                var: var.clone(),
                body: Box::new(self.substitute_candidate_type(body)),
            },
            Type::Unknown | Type::Never | Type::Any => ty.clone(),
        }
    }

    fn substitute_candidate_type_arg(
        &self,
        arg: &yulang_erased_ir::TypeArg,
    ) -> yulang_erased_ir::TypeArg {
        match arg {
            yulang_erased_ir::TypeArg::Type(ty) => {
                yulang_erased_ir::TypeArg::Type(self.substitute_candidate_type(ty))
            }
            yulang_erased_ir::TypeArg::Bounds(bounds) => {
                yulang_erased_ir::TypeArg::Bounds(yulang_erased_ir::TypeBounds {
                    lower: bounds
                        .lower
                        .as_ref()
                        .map(|lower| Box::new(self.substitute_candidate_type(lower))),
                    upper: bounds
                        .upper
                        .as_ref()
                        .map(|upper| Box::new(self.substitute_candidate_type(upper))),
                })
            }
        }
    }
}

fn match_effect_row_pattern(
    instantiation: &mut TypeInstantiation,
    pattern: &Type,
    actual: &Type,
) -> bool {
    if instantiation.match_type(pattern, actual) || effect_rows_equivalent(pattern, actual) {
        return true;
    }
    let Type::Row { items, tail } = pattern else {
        return false;
    };
    let (actual_items, actual_tail) = normalized_effect_row(actual);
    if actual_items.len() < items.len() {
        return false;
    }
    for (pattern_item, actual_item) in items.iter().zip(&actual_items) {
        if !instantiation.match_type(pattern_item, actual_item) {
            return false;
        }
    }
    let rest = effect_row_from_parts(actual_items[items.len()..].to_vec(), actual_tail);
    match_effect_row_pattern(instantiation, tail, &rest)
}

fn effect_row_from_parts(items: Vec<Type>, tail: Type) -> Type {
    if items.is_empty() {
        tail
    } else {
        Type::Row {
            items,
            tail: Box::new(tail),
        }
    }
}

fn join_effect_rows(lhs: &Type, rhs: &Type) -> Type {
    if matches!(lhs, Type::Never) {
        return rhs.clone();
    }
    if matches!(rhs, Type::Never) {
        return lhs.clone();
    }
    let (mut items, lhs_tail) = normalized_effect_row(lhs);
    let (rhs_items, rhs_tail) = normalized_effect_row(rhs);
    for item in rhs_items {
        if !items.iter().any(|existing| existing == &item) {
            items.push(item);
        }
    }
    effect_row_from_parts(items, join_effect_row_tails(lhs_tail, rhs_tail))
}

fn join_effect_row_tails(lhs: Type, rhs: Type) -> Type {
    match (lhs, rhs) {
        (Type::Never, tail) | (tail, Type::Never) => tail,
        (lhs, rhs) if lhs == rhs => lhs,
        (lhs, rhs) => Type::Row {
            items: vec![rhs],
            tail: Box::new(lhs),
        },
    }
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
        MonoType::Function(_) | MonoType::EffectiveThunk(_) => {
            Err(ConstraintError::ExpectedValue {
                slot: slot.into(),
                found: typ.clone(),
            })
        }
    }
}

fn pure_value_computation(
    slot: DraftComputationId,
    source: ConstraintTypeSource,
    ty: Type,
) -> Result<MonoComputation, ConstraintError> {
    Ok(MonoComputation {
        value: MonoType::Value(concrete_type(slot, source, ty)?),
        effect: pure_effect(),
    })
}

fn variant_pattern_payload_computation(
    slot: DraftComputationId,
    computation: &MonoComputation,
    tag: &Name,
    actual_expr_payloads: usize,
    env: &ConstraintEnvironment<'_>,
) -> Result<MonoComputation, ConstraintError> {
    let payload_type = variant_payload_type(slot, computation, tag, actual_expr_payloads, env)?
        .ok_or_else(|| ConstraintError::VariantPayloadMismatch {
            slot: slot.into(),
            tag: tag.clone(),
            expected: 0,
            actual: actual_expr_payloads,
        })?;
    pure_value_computation(slot, ConstraintTypeSource::VariantPayload, payload_type)
}

fn variant_payload_type(
    slot: DraftComputationId,
    computation: &MonoComputation,
    tag: &Name,
    actual_expr_payloads: usize,
    env: &ConstraintEnvironment<'_>,
) -> Result<Option<Type>, ConstraintError> {
    let MonoType::Value(value_type) = &computation.value else {
        return Err(ConstraintError::ExpectedVariant {
            slot: slot.into(),
            found: computation.value.clone(),
        });
    };
    let payload = match value_type.as_type() {
        Type::Variant(variant) => {
            let Some(case) = variant.cases.iter().find(|case| case.name == *tag) else {
                return Err(ConstraintError::MissingVariantCase {
                    slot: slot.into(),
                    tag: tag.clone(),
                });
            };
            variant_case_payload_type(&case.payloads)
        }
        Type::Named { path, args } => {
            env.named_variant_payload_type(path, args, tag)
                .ok_or_else(|| ConstraintError::MissingVariantCase {
                    slot: slot.into(),
                    tag: tag.clone(),
                })?
        }
        _ => {
            return Err(ConstraintError::ExpectedVariant {
                slot: slot.into(),
                found: computation.value.clone(),
            });
        }
    };
    let expected_expr_payloads = usize::from(payload.is_some());
    if expected_expr_payloads != actual_expr_payloads {
        return Err(ConstraintError::VariantPayloadMismatch {
            slot: slot.into(),
            tag: tag.clone(),
            expected: expected_expr_payloads,
            actual: actual_expr_payloads,
        });
    }
    Ok(payload)
}

fn variant_case_payload_type(payloads: &[Type]) -> Option<Type> {
    match payloads {
        [] => None,
        [payload] => Some(payload.clone()),
        payloads => Some(Type::Tuple(payloads.to_vec())),
    }
}

fn pure_pattern_value_computation(computation: &MonoComputation) -> MonoComputation {
    MonoComputation {
        value: computation.value.clone(),
        effect: pure_effect(),
    }
}

fn pure_unit_computation(_slot: DraftComputationId) -> MonoComputation {
    MonoComputation {
        value: MonoType::Value(ConcreteType::try_from_type(unit_type()).expect("unit is concrete")),
        effect: pure_effect(),
    }
}

fn block_statement_computation(target: &MonoComputation) -> MonoComputation {
    MonoComputation {
        value: MonoType::Value(ConcreteType::try_from_type(unit_type()).expect("unit is concrete")),
        effect: target.effect.clone(),
    }
}

fn lambda_body_effect(
    slot: DraftComputationId,
    body: &ErasedExpr,
    ret_effect: Type,
) -> Result<MonoEffect, ConstraintError> {
    let effect = if erased_expr_is_pure_value(body) {
        Type::Never
    } else {
        ret_effect
    };
    Ok(MonoEffect::new(concrete_type(
        slot,
        ConstraintTypeSource::FunctionReturnEffect,
        effect,
    )?))
}

fn erased_expr_is_pure_value(expr: &ErasedExpr) -> bool {
    match expr {
        ErasedExpr::Def(_)
        | ErasedExpr::Ref(_)
        | ErasedExpr::EffectOp(_)
        | ErasedExpr::PrimitiveOp(_)
        | ErasedExpr::Lit(_)
        | ErasedExpr::Lambda { .. } => true,
        ErasedExpr::Tuple(items) => items.iter().all(erased_expr_is_pure_value),
        ErasedExpr::Record { fields, spread } => {
            fields
                .iter()
                .all(|field| erased_expr_is_pure_value(&field.value))
                && spread.as_ref().is_none_or(|spread| match spread {
                    yulang_erased_ir::RecordSpreadExpr::Head(expr)
                    | yulang_erased_ir::RecordSpreadExpr::Tail(expr) => {
                        erased_expr_is_pure_value(expr)
                    }
                })
        }
        ErasedExpr::Variant { value, .. } => value.as_deref().is_none_or(erased_expr_is_pure_value),
        ErasedExpr::Pack { expr, .. } => erased_expr_is_pure_value(expr),
        ErasedExpr::Apply { .. }
        | ErasedExpr::RefSet { .. }
        | ErasedExpr::Match { .. }
        | ErasedExpr::Handle { .. }
        | ErasedExpr::Block(_)
        | ErasedExpr::BindHere { .. }
        | ErasedExpr::Select { .. } => false,
    }
}

fn known_value_type(expr: &ErasedExpr, env: &ConstraintEnvironment<'_>) -> Option<Type> {
    match expr {
        ErasedExpr::Lit(lit) => Some(literal_type(lit)),
        ErasedExpr::Tuple(items) => items
            .iter()
            .map(|item| known_value_type(item, env))
            .collect::<Option<Vec<_>>>()
            .map(Type::Tuple),
        ErasedExpr::Record { fields, spread } => {
            let fields = fields
                .iter()
                .map(|field| {
                    Some(yulang_erased_ir::RecordField {
                        name: field.name.clone(),
                        value: known_value_type(&field.value, env)?,
                        optional: false,
                    })
                })
                .collect::<Option<Vec<_>>>()?;
            let spread = match spread {
                Some(spread) => Some(record_spread_expr_type(spread, env)?),
                None => None,
            };
            Some(Type::Record(yulang_erased_ir::RecordType {
                fields,
                spread,
            }))
        }
        ErasedExpr::Select { base, field } => {
            let base_type = known_value_type(base, env)?;
            record_field_value_type_opt(&base_type, field).cloned()
        }
        ErasedExpr::Pack { expr, .. } => known_value_type(expr, env),
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

fn inline_record_type_from_select(
    _slot: DraftComputationId,
    base: &ErasedExpr,
    selected_field: &Name,
    selected_type: &Type,
    env: &ConstraintEnvironment<'_>,
) -> Result<Option<Type>, ConstraintError> {
    let ErasedExpr::Record { fields, spread } = base else {
        return Ok(None);
    };
    let mut saw_selected = false;
    let mut record_fields = Vec::new();
    for field in fields {
        let value = if field.name == *selected_field {
            saw_selected = true;
            selected_type.clone()
        } else {
            let Some(value) = known_value_type(&field.value, env) else {
                return Ok(None);
            };
            value
        };
        record_fields.push(yulang_erased_ir::RecordField {
            name: field.name.clone(),
            value,
            optional: false,
        });
    }
    if !saw_selected {
        return Ok(None);
    }
    let spread = match spread {
        Some(spread) => {
            let Some(spread) = record_spread_expr_type(spread, env) else {
                return Ok(None);
            };
            Some(spread)
        }
        None => None,
    };
    Ok(Some(Type::Record(yulang_erased_ir::RecordType {
        fields: record_fields,
        spread,
    })))
}

fn record_spread_expr_type(
    spread: &yulang_erased_ir::RecordSpreadExpr,
    env: &ConstraintEnvironment<'_>,
) -> Option<yulang_erased_ir::RecordSpread> {
    match spread {
        yulang_erased_ir::RecordSpreadExpr::Head(expr) => known_value_type(expr, env)
            .map(Box::new)
            .map(yulang_erased_ir::RecordSpread::Head),
        yulang_erased_ir::RecordSpreadExpr::Tail(expr) => known_value_type(expr, env)
            .map(Box::new)
            .map(yulang_erased_ir::RecordSpread::Tail),
    }
}

fn record_spread_type(spread: Option<&yulang_erased_ir::RecordSpread>) -> Option<Type> {
    match spread {
        Some(yulang_erased_ir::RecordSpread::Head(ty))
        | Some(yulang_erased_ir::RecordSpread::Tail(ty)) => Some((**ty).clone()),
        None => None,
    }
}

fn record_field_value_type<'a>(
    slot: DraftComputationId,
    ty: &'a Type,
    field: &Name,
) -> Result<&'a Type, ConstraintError> {
    if !matches!(ty, Type::Record(_)) {
        return Err(ConstraintError::ExpectedRecord {
            slot: slot.into(),
            found: MonoType::Value(concrete_type(
                slot,
                ConstraintTypeSource::SelectBase,
                ty.clone(),
            )?),
        });
    }
    record_field_value_type_opt(ty, field).ok_or_else(|| ConstraintError::MissingRecordField {
        slot: slot.into(),
        field: field.clone(),
    })
}

fn record_field_value_type_opt<'a>(ty: &'a Type, field: &Name) -> Option<&'a Type> {
    let Type::Record(record) = ty else {
        return None;
    };
    record
        .fields
        .iter()
        .find(|record_field| record_field.name == *field)
        .map(|record_field| &record_field.value)
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
            Lit::Unit => return unit_type(),
        },
        args: Vec::new(),
    }
}

fn bool_type() -> Type {
    Type::Named {
        path: Path::from_name(Name("bool".to_string())),
        args: Vec::new(),
    }
}

fn unit_type() -> Type {
    Type::Named {
        path: Path::from_name(Name("unit".to_string())),
        args: Vec::new(),
    }
}

fn concrete_type(
    slot: DraftComputationId,
    source: ConstraintTypeSource,
    ty: Type,
) -> Result<ConcreteType, ConstraintError> {
    let ty = normalize_concrete_candidate(ty);
    ConcreteType::try_from_type(ty).map_err(|error| ConstraintError::NonConcreteType {
        slot: slot.into(),
        source,
        error,
    })
}

fn mono_type_to_type(slot: DraftComputationId, typ: &MonoType) -> Result<Type, ConstraintError> {
    match typ {
        MonoType::Value(value) => Ok(value.as_type().clone()),
        MonoType::Function(_) | MonoType::EffectiveThunk(_) => {
            Err(ConstraintError::ExpectedValue {
                slot: slot.into(),
                found: typ.clone(),
            })
        }
    }
}

fn collect_concrete_candidates(ty: &Type, candidates: &mut Vec<Type>) {
    if ConcreteType::try_from_type(ty.clone()).is_ok() {
        push_unique_candidate(candidates, normalize_concrete_candidate(ty.clone()));
        return;
    }
    match ty {
        Type::Union(items) | Type::Inter(items) => {
            for item in items {
                collect_concrete_candidates(item, candidates);
            }
        }
        Type::Named { .. }
        | Type::Fun { .. }
        | Type::Tuple(_)
        | Type::Record(_)
        | Type::Variant(_)
        | Type::Row { .. } => {
            if let Some(candidate) = concretize_type_candidate(ty) {
                push_unique_candidate(candidates, candidate);
            }
        }
        Type::Unknown | Type::Never | Type::Any | Type::Var(_) | Type::Recursive { .. } => {}
    }
}

fn normalize_concrete_candidate(ty: Type) -> Type {
    match ty {
        Type::Named { path, args } => Type::Named {
            path,
            args: args
                .into_iter()
                .map(normalize_concrete_candidate_arg)
                .collect(),
        },
        Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => Type::Fun {
            param: Box::new(normalize_concrete_candidate(*param)),
            param_effect: Box::new(normalize_concrete_candidate(*param_effect)),
            ret_effect: Box::new(normalize_concrete_candidate(*ret_effect)),
            ret: Box::new(normalize_concrete_candidate(*ret)),
        },
        Type::Tuple(items) => Type::Tuple(
            items
                .into_iter()
                .map(normalize_concrete_candidate)
                .collect(),
        ),
        Type::Record(record) => Type::Record(yulang_erased_ir::RecordType {
            fields: record
                .fields
                .into_iter()
                .map(|field| yulang_erased_ir::RecordField {
                    name: field.name,
                    value: normalize_concrete_candidate(field.value),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.map(normalize_concrete_record_spread),
        }),
        Type::Variant(variant) => Type::Variant(yulang_erased_ir::VariantType {
            cases: variant
                .cases
                .into_iter()
                .map(|case| yulang_erased_ir::VariantCase {
                    name: case.name,
                    payloads: case
                        .payloads
                        .into_iter()
                        .map(normalize_concrete_candidate)
                        .collect(),
                })
                .collect(),
            tail: variant
                .tail
                .map(|tail| Box::new(normalize_concrete_candidate(*tail))),
        }),
        Type::Row { items, tail } => {
            let items = dedup_normalized_types(items);
            let tail = normalize_concrete_candidate(*tail);
            effect_row_from_parts(items, tail)
        }
        Type::Union(items) => normalize_variadic_candidate(TypeVariant::Union, items),
        Type::Inter(items) => normalize_variadic_candidate(TypeVariant::Inter, items),
        Type::Recursive { var, body } => Type::Recursive {
            var,
            body: Box::new(normalize_concrete_candidate(*body)),
        },
        Type::Var(_) | Type::Unknown | Type::Never | Type::Any => ty,
    }
}

fn normalize_concrete_candidate_arg(arg: yulang_erased_ir::TypeArg) -> yulang_erased_ir::TypeArg {
    match arg {
        yulang_erased_ir::TypeArg::Type(ty) => {
            yulang_erased_ir::TypeArg::Type(normalize_concrete_candidate(ty))
        }
        yulang_erased_ir::TypeArg::Bounds(bounds) => {
            if let Some(candidate) = type_bounds_concrete_candidate(&bounds) {
                yulang_erased_ir::TypeArg::Type(normalize_concrete_candidate(candidate))
            } else {
                yulang_erased_ir::TypeArg::Bounds(yulang_erased_ir::TypeBounds {
                    lower: bounds
                        .lower
                        .map(|lower| Box::new(normalize_concrete_candidate(*lower))),
                    upper: bounds
                        .upper
                        .map(|upper| Box::new(normalize_concrete_candidate(*upper))),
                })
            }
        }
    }
}

fn normalize_concrete_record_spread(
    spread: yulang_erased_ir::RecordSpread,
) -> yulang_erased_ir::RecordSpread {
    match spread {
        yulang_erased_ir::RecordSpread::Head(ty) => {
            yulang_erased_ir::RecordSpread::Head(Box::new(normalize_concrete_candidate(*ty)))
        }
        yulang_erased_ir::RecordSpread::Tail(ty) => {
            yulang_erased_ir::RecordSpread::Tail(Box::new(normalize_concrete_candidate(*ty)))
        }
    }
}

fn normalize_variadic_candidate(variant: TypeVariant, items: Vec<Type>) -> Type {
    let items = dedup_normalized_types(items);
    match items.as_slice() {
        [] => match variant {
            TypeVariant::Union => Type::Never,
            TypeVariant::Inter => Type::Any,
        },
        [item] => item.clone(),
        _ => match variant {
            TypeVariant::Union => Type::Union(items),
            TypeVariant::Inter => Type::Inter(items),
        },
    }
}

fn dedup_normalized_types(items: Vec<Type>) -> Vec<Type> {
    let mut out = Vec::new();
    for item in items {
        push_unique_candidate(&mut out, normalize_concrete_candidate(item));
    }
    out
}

fn concretize_type_candidate(ty: &Type) -> Option<Type> {
    if ConcreteType::try_from_type(ty.clone()).is_ok() {
        return Some(normalize_concrete_candidate(ty.clone()));
    }
    match ty {
        Type::Union(items) | Type::Inter(items) => unique_type_candidate(items),
        Type::Named { path, args } => Some(Type::Named {
            path: path.clone(),
            args: args
                .iter()
                .map(concretize_type_arg_candidate)
                .collect::<Option<Vec<_>>>()?,
        }),
        Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => Some(Type::Fun {
            param: Box::new(concretize_type_candidate(param)?),
            param_effect: Box::new(concretize_type_candidate(param_effect)?),
            ret_effect: Box::new(concretize_type_candidate(ret_effect)?),
            ret: Box::new(concretize_type_candidate(ret)?),
        }),
        Type::Tuple(items) => Some(Type::Tuple(
            items
                .iter()
                .map(concretize_type_candidate)
                .collect::<Option<Vec<_>>>()?,
        )),
        Type::Record(record) => Some(Type::Record(yulang_erased_ir::RecordType {
            fields: record
                .fields
                .iter()
                .map(|field| {
                    Some(yulang_erased_ir::RecordField {
                        name: field.name.clone(),
                        value: concretize_type_candidate(&field.value)?,
                        optional: field.optional,
                    })
                })
                .collect::<Option<Vec<_>>>()?,
            spread: record.spread.as_ref().map_or(Some(None), |spread| {
                concretize_record_spread_candidate(spread).map(Some)
            })?,
        })),
        Type::Variant(variant) => Some(Type::Variant(yulang_erased_ir::VariantType {
            cases: variant
                .cases
                .iter()
                .map(|case| {
                    Some(yulang_erased_ir::VariantCase {
                        name: case.name.clone(),
                        payloads: case
                            .payloads
                            .iter()
                            .map(concretize_type_candidate)
                            .collect::<Option<Vec<_>>>()?,
                    })
                })
                .collect::<Option<Vec<_>>>()?,
            tail: variant.tail.as_ref().map_or(Some(None), |tail| {
                concretize_type_candidate(tail).map(Box::new).map(Some)
            })?,
        })),
        Type::Row { items, tail } => Some(Type::Row {
            items: items
                .iter()
                .map(concretize_type_candidate)
                .collect::<Option<Vec<_>>>()?,
            tail: Box::new(concretize_type_candidate(tail)?),
        }),
        Type::Unknown | Type::Never | Type::Any | Type::Var(_) | Type::Recursive { .. } => None,
    }
}

fn concretize_type_arg_candidate(
    arg: &yulang_erased_ir::TypeArg,
) -> Option<yulang_erased_ir::TypeArg> {
    match arg {
        yulang_erased_ir::TypeArg::Type(ty) => Some(yulang_erased_ir::TypeArg::Type(
            concretize_type_candidate(ty)?,
        )),
        yulang_erased_ir::TypeArg::Bounds(bounds) => {
            let candidate = type_bounds_concrete_candidate(bounds)?;
            Some(yulang_erased_ir::TypeArg::Type(candidate))
        }
    }
}

fn type_bounds_concrete_candidate(bounds: &TypeBounds) -> Option<Type> {
    let mut candidates = Vec::new();
    if let Some(lower) = &bounds.lower {
        collect_concrete_candidates(lower, &mut candidates);
    }
    if let Some(upper) = &bounds.upper {
        collect_concrete_candidates(upper, &mut candidates);
    }
    (candidates.len() == 1).then(|| candidates.remove(0))
}

fn concretize_record_spread_candidate(
    spread: &yulang_erased_ir::RecordSpread,
) -> Option<yulang_erased_ir::RecordSpread> {
    match spread {
        yulang_erased_ir::RecordSpread::Head(ty) => concretize_type_candidate(ty)
            .map(Box::new)
            .map(yulang_erased_ir::RecordSpread::Head),
        yulang_erased_ir::RecordSpread::Tail(ty) => concretize_type_candidate(ty)
            .map(Box::new)
            .map(yulang_erased_ir::RecordSpread::Tail),
    }
}

fn unique_type_candidate(items: &[Type]) -> Option<Type> {
    let mut candidates = Vec::new();
    for item in items {
        collect_concrete_candidates(item, &mut candidates);
    }
    (candidates.len() == 1).then(|| candidates.remove(0))
}

fn push_unique_candidate(candidates: &mut Vec<Type>, candidate: Type) {
    if !candidates.iter().any(|existing| existing == &candidate) {
        candidates.push(candidate);
    }
}

fn effect_is_pure(effect: &MonoEffect) -> bool {
    effect_row_is_empty(effect.row().as_type())
}

fn effect_row_is_empty(row: &Type) -> bool {
    match row {
        Type::Never => true,
        Type::Row { items, tail } => items.is_empty() && effect_row_is_empty(tail),
        _ => false,
    }
}

fn pure_effect() -> MonoEffect {
    MonoEffect::new(ConcreteType::try_from_type(Type::Never).expect("Never is concrete"))
}

fn default_for_quantified_type_var(scheme: &Scheme, var: &TypeVar) -> UnboundedTypeDefault {
    let mut positions = TypeVarUsePositions::default();
    collect_type_var_positions(&scheme.body, TypeUsePosition::Value, &mut positions);
    for requirement in &scheme.requirements {
        collect_role_requirement_var_positions(requirement, &mut positions);
    }
    let Some(position) = positions.get(var) else {
        return UnboundedTypeDefault::Value;
    };
    if position.effect && !position.value {
        UnboundedTypeDefault::Effect
    } else {
        UnboundedTypeDefault::Value
    }
}

#[derive(Default)]
struct TypeVarUsePositions {
    positions: BTreeMap<TypeVar, TypeVarUsePosition>,
}

impl TypeVarUsePositions {
    fn mark(&mut self, var: &TypeVar, position: TypeUsePosition) {
        let entry = self.positions.entry(var.clone()).or_default();
        match position {
            TypeUsePosition::Value => entry.value = true,
            TypeUsePosition::Effect => entry.effect = true,
        }
    }

    fn get(&self, var: &TypeVar) -> Option<&TypeVarUsePosition> {
        self.positions.get(var)
    }
}

#[derive(Default)]
struct TypeVarUsePosition {
    value: bool,
    effect: bool,
}

#[derive(Clone, Copy)]
enum TypeUsePosition {
    Value,
    Effect,
}

fn collect_role_requirement_var_positions(
    requirement: &RoleRequirement,
    positions: &mut TypeVarUsePositions,
) {
    for arg in &requirement.args {
        match arg {
            RoleRequirementArg::Input(bounds) | RoleRequirementArg::Associated { bounds, .. } => {
                collect_type_bounds_var_positions(bounds, positions);
            }
        }
    }
}

fn collect_type_bounds_var_positions(
    bounds: &yulang_erased_ir::TypeBounds,
    positions: &mut TypeVarUsePositions,
) {
    if let Some(lower) = &bounds.lower {
        collect_type_var_positions(lower, TypeUsePosition::Value, positions);
    }
    if let Some(upper) = &bounds.upper {
        collect_type_var_positions(upper, TypeUsePosition::Value, positions);
    }
}

fn collect_type_var_positions(
    ty: &Type,
    position: TypeUsePosition,
    positions: &mut TypeVarUsePositions,
) {
    match ty {
        Type::Var(var) => positions.mark(var, position),
        Type::Named { args, .. } => {
            for arg in args {
                collect_type_arg_var_positions(arg, positions);
            }
        }
        Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_type_var_positions(param, TypeUsePosition::Value, positions);
            collect_type_var_positions(param_effect, TypeUsePosition::Effect, positions);
            collect_type_var_positions(ret_effect, TypeUsePosition::Effect, positions);
            collect_type_var_positions(ret, TypeUsePosition::Value, positions);
        }
        Type::Tuple(items) => {
            for item in items {
                collect_type_var_positions(item, TypeUsePosition::Value, positions);
            }
        }
        Type::Record(record) => {
            for field in &record.fields {
                collect_type_var_positions(&field.value, TypeUsePosition::Value, positions);
            }
            if let Some(spread) = &record.spread {
                match spread {
                    yulang_erased_ir::RecordSpread::Head(ty)
                    | yulang_erased_ir::RecordSpread::Tail(ty) => {
                        collect_type_var_positions(ty, TypeUsePosition::Value, positions);
                    }
                }
            }
        }
        Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_type_var_positions(payload, TypeUsePosition::Value, positions);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_type_var_positions(tail, TypeUsePosition::Value, positions);
            }
        }
        Type::Row { items, tail } => {
            for item in items {
                collect_type_var_positions(item, TypeUsePosition::Effect, positions);
            }
            collect_type_var_positions(tail, TypeUsePosition::Effect, positions);
        }
        Type::Union(items) | Type::Inter(items) => {
            for item in items {
                collect_type_var_positions(item, position, positions);
            }
        }
        Type::Recursive { var, body } => {
            let before = positions.positions.remove(var);
            collect_type_var_positions(body, position, positions);
            if let Some(before) = before {
                positions.positions.insert(var.clone(), before);
            } else {
                positions.positions.remove(var);
            }
        }
        Type::Unknown | Type::Never | Type::Any => {}
    }
}

fn collect_type_arg_var_positions(
    arg: &yulang_erased_ir::TypeArg,
    positions: &mut TypeVarUsePositions,
) {
    match arg {
        yulang_erased_ir::TypeArg::Type(ty) => {
            collect_type_var_positions(ty, TypeUsePosition::Value, positions);
        }
        yulang_erased_ir::TypeArg::Bounds(bounds) => {
            collect_type_bounds_var_positions(bounds, positions);
        }
    }
}

#[derive(Clone, Default)]
struct TypeInstantiation {
    quantifiable: BTreeSet<yulang_erased_ir::TypeVar>,
    assignments: BTreeMap<yulang_erased_ir::TypeVar, Type>,
    defaults: BTreeMap<yulang_erased_ir::TypeVar, UnboundedTypeDefault>,
}

impl TypeInstantiation {
    fn new(scheme: &Scheme) -> Self {
        let mut quantifiable = BTreeSet::new();
        let mut defaults = BTreeMap::new();
        for var in &scheme.quantified_types {
            quantifiable.insert(var.clone());
            defaults.insert(var.clone(), default_for_quantified_type_var(scheme, var));
        }
        for var in &scheme.quantified_effects {
            let var = yulang_erased_ir::TypeVar(var.0.clone());
            quantifiable.insert(var.clone());
            defaults.insert(var, UnboundedTypeDefault::Effect);
        }
        Self {
            quantifiable,
            assignments: BTreeMap::new(),
            defaults,
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
        self.substitute_type_inner(ty, false)
    }

    fn substitute_type_bounds(
        &self,
        bounds: &yulang_erased_ir::TypeBounds,
    ) -> yulang_erased_ir::TypeBounds {
        yulang_erased_ir::TypeBounds {
            lower: bounds
                .lower
                .as_ref()
                .map(|ty| Box::new(self.substitute_type(ty))),
            upper: bounds
                .upper
                .as_ref()
                .map(|ty| Box::new(self.substitute_type(ty))),
        }
    }

    fn substitute_type_with_defaults(&self, ty: &Type) -> Type {
        self.substitute_type_inner(ty, true)
    }

    fn substitute_type_bounds_with_defaults(
        &self,
        bounds: &yulang_erased_ir::TypeBounds,
    ) -> yulang_erased_ir::TypeBounds {
        yulang_erased_ir::TypeBounds {
            lower: bounds
                .lower
                .as_ref()
                .map(|ty| Box::new(self.substitute_type_with_defaults(ty))),
            upper: bounds
                .upper
                .as_ref()
                .map(|ty| Box::new(self.substitute_type_with_defaults(ty))),
        }
    }

    fn substitute_type_inner(&self, ty: &Type, use_defaults: bool) -> Type {
        match ty {
            Type::Var(var) => self
                .assignments
                .get(var)
                .cloned()
                .or_else(|| {
                    use_defaults
                        .then(|| self.defaults.get(var).map(|default| default.as_type()))
                        .flatten()
                })
                .unwrap_or_else(|| ty.clone()),
            Type::Named { path, args } => Type::Named {
                path: path.clone(),
                args: args
                    .iter()
                    .map(|arg| self.substitute_type_arg(arg, use_defaults))
                    .collect(),
            },
            Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => Type::Fun {
                param: Box::new(self.substitute_type_inner(param, use_defaults)),
                param_effect: Box::new(self.substitute_type_inner(param_effect, use_defaults)),
                ret_effect: Box::new(self.substitute_type_inner(ret_effect, use_defaults)),
                ret: Box::new(self.substitute_type_inner(ret, use_defaults)),
            },
            Type::Tuple(items) => Type::Tuple(
                items
                    .iter()
                    .map(|item| self.substitute_type_inner(item, use_defaults))
                    .collect(),
            ),
            Type::Record(record) => Type::Record(yulang_erased_ir::RecordType {
                fields: record
                    .fields
                    .iter()
                    .map(|field| yulang_erased_ir::RecordField {
                        name: field.name.clone(),
                        value: self.substitute_type_inner(&field.value, use_defaults),
                        optional: field.optional,
                    })
                    .collect(),
                spread: record.spread.as_ref().map(|spread| match spread {
                    yulang_erased_ir::RecordSpread::Head(ty) => {
                        yulang_erased_ir::RecordSpread::Head(Box::new(
                            self.substitute_type_inner(ty, use_defaults),
                        ))
                    }
                    yulang_erased_ir::RecordSpread::Tail(ty) => {
                        yulang_erased_ir::RecordSpread::Tail(Box::new(
                            self.substitute_type_inner(ty, use_defaults),
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
                            .map(|payload| self.substitute_type_inner(payload, use_defaults))
                            .collect(),
                    })
                    .collect(),
                tail: variant
                    .tail
                    .as_ref()
                    .map(|tail| Box::new(self.substitute_type_inner(tail, use_defaults))),
            }),
            Type::Row { items, tail } => Type::Row {
                items: items
                    .iter()
                    .map(|item| self.substitute_type_inner(item, use_defaults))
                    .collect(),
                tail: Box::new(self.substitute_type_inner(tail, use_defaults)),
            },
            Type::Union(items) => Type::Union(
                items
                    .iter()
                    .map(|item| self.substitute_type_inner(item, use_defaults))
                    .collect(),
            ),
            Type::Inter(items) => Type::Inter(
                items
                    .iter()
                    .map(|item| self.substitute_type_inner(item, use_defaults))
                    .collect(),
            ),
            Type::Recursive { var, body } => Type::Recursive {
                var: var.clone(),
                body: Box::new(self.substitute_type_under_binder(var, body, use_defaults)),
            },
            Type::Unknown | Type::Never | Type::Any => ty.clone(),
        }
    }

    fn substitute_type_arg(
        &self,
        arg: &yulang_erased_ir::TypeArg,
        use_defaults: bool,
    ) -> yulang_erased_ir::TypeArg {
        match arg {
            yulang_erased_ir::TypeArg::Type(ty) => {
                yulang_erased_ir::TypeArg::Type(self.substitute_type_inner(ty, use_defaults))
            }
            yulang_erased_ir::TypeArg::Bounds(bounds) => {
                yulang_erased_ir::TypeArg::Bounds(yulang_erased_ir::TypeBounds {
                    lower: bounds
                        .lower
                        .as_ref()
                        .map(|lower| Box::new(self.substitute_type_inner(lower, use_defaults))),
                    upper: bounds
                        .upper
                        .as_ref()
                        .map(|upper| Box::new(self.substitute_type_inner(upper, use_defaults))),
                })
            }
        }
    }

    fn substitute_type_under_binder(
        &self,
        var: &yulang_erased_ir::TypeVar,
        body: &Type,
        use_defaults: bool,
    ) -> Type {
        let mut nested = Self {
            quantifiable: self.quantifiable.clone(),
            assignments: self.assignments.clone(),
            defaults: self.defaults.clone(),
        };
        nested.quantifiable.remove(var);
        nested.assignments.remove(var);
        nested.defaults.remove(var);
        nested.substitute_type_inner(body, use_defaults)
    }

    fn without_var<T>(
        &mut self,
        var: &yulang_erased_ir::TypeVar,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let removed_assignment = self.assignments.remove(var);
        let removed_quantifiable = self.quantifiable.remove(var);
        let removed_default = self.defaults.remove(var);
        let out = f(self);
        if let Some(assignment) = removed_assignment {
            self.assignments.insert(var.clone(), assignment);
        }
        if removed_quantifiable {
            self.quantifiable.insert(var.clone());
        }
        if let Some(default) = removed_default {
            self.defaults.insert(var.clone(), default);
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
        let env = ConstraintEnvironment::new(&refs, &[], &[], &[]);
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
            .build_substitution_with_defaults(
                DraftComputationId(0),
                ConstraintTypeSource::BoundsSelection,
            )
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

    #[test]
    fn unbounded_fresh_vars_default_inside_structural_candidate() {
        let mut solver = empty_solver();
        let slot = DraftComputationId(0);
        let alpha = TypeVar("$elab0$a".to_string());
        let epsilon = TypeVar("$elab1$e".to_string());
        solver
            .type_var_defaults
            .insert(alpha.clone(), UnboundedTypeDefault::Value);
        solver
            .type_var_defaults
            .insert(epsilon.clone(), UnboundedTypeDefault::Effect);
        let int = named_type("int");

        solver
            .add_exact_type(
                TypeNode::value(slot),
                Type::Fun {
                    param: Box::new(Type::Var(alpha)),
                    param_effect: Box::new(Type::Var(epsilon)),
                    ret_effect: Box::new(Type::Never),
                    ret: Box::new(int.clone()),
                },
            )
            .expect("add value bound");
        solver
            .add_exact_type(TypeNode::effect(slot), Type::Never)
            .expect("add effect bound");
        solver.drain_pending_bounds().expect("drain bounds");

        let computation = solver.require_assigned(slot).expect("solve computation");

        assert_eq!(
            computation.value,
            MonoType::Value(
                ConcreteType::try_from_type(Type::Fun {
                    param: Box::new(named_type("unit")),
                    param_effect: Box::new(Type::Never),
                    ret_effect: Box::new(Type::Never),
                    ret: Box::new(int),
                })
                .expect("function is concrete")
            )
        );
        assert_eq!(computation.effect, pure_effect());
    }

    #[test]
    fn unbounded_computation_bounds_default_to_unit_and_never() {
        let mut solver = empty_solver();
        let slot = DraftComputationId(0);
        solver.type_bounds_mut(TypeNode::value(slot));
        solver.type_bounds_mut(TypeNode::effect(slot));

        let computation = solver.require_assigned(slot).expect("solve computation");

        assert_eq!(
            computation,
            MonoComputation {
                value: MonoType::Value(concrete_named("unit")),
                effect: pure_effect(),
            }
        );
    }

    #[test]
    fn direct_apply_ret_effect_defaults_unbounded_effect_var_to_never() {
        let refs = RefExportTable::default();
        let env = ConstraintEnvironment::new(&refs, &[], &[], &[]);
        let effect = yulang_erased_ir::EffectVar("e".to_string());
        let scheme = Scheme {
            body: Type::Fun {
                param: Box::new(named_type("unit")),
                param_effect: Box::new(Type::Never),
                ret_effect: Box::new(Type::Var(TypeVar(effect.0.clone()))),
                ret: Box::new(named_type("int")),
            },
            quantified_types: Vec::new(),
            quantified_effects: vec![effect],
            quantified_refs: Vec::new(),
            typeclass_obligations: Vec::new(),
            requirements: Vec::new(),
        };
        let arg = ErasedExpr::Lit(Lit::Unit);

        let ret_effect =
            direct_apply_ret_effect_from_scheme_spine(&scheme, &named_type("int"), &[&arg], &env)
                .expect("ret effect");

        assert_eq!(ret_effect, Type::Never);
    }

    fn empty_solver() -> ConstraintSolver {
        ConstraintSolver {
            explicit_computations: BTreeMap::new(),
            bounds: BTreeMap::new(),
            pending_bounds: Vec::new(),
            subtype_edges: BTreeSet::new(),
            type_var_defaults: BTreeMap::new(),
            next_type_var: 0,
            local_def_computations: Vec::new(),
            direct_ref_instances: BTreeMap::new(),
            resolved_typeclass_instances: BTreeMap::new(),
            typeclass_obligation_instances: BTreeMap::new(),
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
