//! Elaborate erased principal inference output into runtime-ready demands.
//!
//! This crate is the new post-inference boundary. It intentionally accepts
//! `yulang_erased_ir::InferExport` instead of typed IR or infer internals, so
//! later implementation cannot read expression-node types, apply evidence, or
//! annotation evidence through the public entrypoint.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};

mod constraints;
mod draft;

use yulang_erased_ir::{
    DefId, ErasedExpr, InferExport, InferredBinding, InferredExpr, Path, PrincipalRoot,
    RefCoverageReport, RefExportTable, RefId, ResolvedTypeClassRef, Scheme, Type, TypeBounds,
    TypeClassObligation,
};

pub use constraints::ConstraintError;
pub use yulang_elaborated_ir as elaborated_ir;

use yulang_elaborated_ir::{
    ConcreteType, ConcreteTypeError, DemandSource, ElaboratedExpr, ElaboratedExprKind,
    ElaboratedModule, ElaboratedProgram, ElaboratedRoot, MonoComputation, MonoEffect, MonoInstance,
    MonoInstanceId, MonoType, ResolvedRef, ResolvedRefKey, ResolvedRefSource, ResolvedRefTable,
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

    pub fn build_program(&self) -> Result<ElaboratedProgram, ElaborateProgramError> {
        self.validate_input()
            .map_err(ElaborateProgramError::Input)?;
        ProgramBuilder::new(self.export).build()
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
pub enum ElaborateProgramError {
    Input(ElaborateInputError),
    Constraint(ConstraintError),
    NonExactComputationBounds {
        site: ElaborateSite,
        field: ComputationField,
        bounds: TypeBounds,
    },
    NonConcreteComputationType {
        site: ElaborateSite,
        field: ComputationField,
        error: ConcreteTypeError,
    },
    UnsupportedRoot {
        root: PrincipalRoot,
    },
    MissingBinding {
        def: DefId,
    },
    UnsupportedExpr {
        site: ElaborateSite,
        kind: ErasedExprKind,
    },
    ExpectedEffectiveThunk {
        site: ElaborateSite,
        found: MonoType,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ElaborateSite {
    RootExpr(usize),
    Binding(DefId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ComputationField {
    Value,
    Effect,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErasedExprKind {
    Def,
    Ref,
    PrimitiveOp,
    Lit,
    Lambda,
    Apply,
    RefSet,
    Tuple,
    Record,
    Variant,
    Select,
    Match,
    Handle,
    Block,
    BindHere,
    Pack,
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

struct ProgramBuilder<'a> {
    export: &'a InferExport,
    env: constraints::ConstraintEnvironment<'a>,
    bindings_by_def: BTreeMap<DefId, &'a InferredBinding>,
    defs_by_path: Vec<(Path, DefId)>,
    instances: Vec<MonoInstance>,
    instance_by_def: BTreeMap<DefId, MonoInstanceId>,
    specialized_instances: Vec<SpecializedInstance>,
    root_instance_by_index: BTreeMap<usize, MonoInstanceId>,
    refs: ResolvedRefTable,
}

impl<'a> ProgramBuilder<'a> {
    fn new(export: &'a InferExport) -> Self {
        let bindings_by_def = export
            .erased
            .module
            .bindings
            .iter()
            .map(|binding| (binding.def, binding))
            .collect();
        let defs_by_path = export
            .erased
            .module
            .bindings
            .iter()
            .map(|binding| (binding.name.clone(), binding.def))
            .collect();
        Self {
            export,
            env: constraints::ConstraintEnvironment::new(
                &export.erased.refs,
                &export.erased.module.bindings,
            ),
            bindings_by_def,
            defs_by_path,
            instances: Vec::new(),
            instance_by_def: BTreeMap::new(),
            specialized_instances: Vec::new(),
            root_instance_by_index: BTreeMap::new(),
            refs: ResolvedRefTable::default(),
        }
    }

    fn build(mut self) -> Result<ElaboratedProgram, ElaborateProgramError> {
        let mut root_exprs = Vec::new();
        for (index, expr) in self.export.erased.module.root_exprs.iter().enumerate() {
            let body = elaborate_root_expr(index, expr, &self.env)?;
            let instance = self.push_instance(
                DemandSource::RootExpr(index),
                body.expr.comp.clone(),
                body.expr.clone(),
            );
            self.root_instance_by_index.insert(index, instance);
            self.resolve_direct_refs_for_instance(instance, &expr.ir, &body.direct_ref_instances)?;
            self.resolve_typeclass_refs_for_instance(
                instance,
                &expr.ir,
                &body.resolved_typeclass_instances,
            )?;
            root_exprs.push(body.expr);
        }

        let roots = self
            .export
            .erased
            .module
            .roots
            .iter()
            .map(|root| self.elaborate_root(root))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(ElaboratedProgram {
            module: ElaboratedModule {
                path: self.export.erased.module.path.clone(),
                instances: self.instances,
                root_exprs,
                roots,
            },
            refs: self.refs,
        })
    }

    fn elaborate_root(
        &mut self,
        root: &PrincipalRoot,
    ) -> Result<ElaboratedRoot, ElaborateProgramError> {
        match root {
            PrincipalRoot::Expr(index) => {
                let Some(instance) = self.root_instance_by_index.get(index).copied() else {
                    return Err(ElaborateProgramError::UnsupportedRoot { root: root.clone() });
                };
                Ok(ElaboratedRoot::Instance(instance))
            }
            PrincipalRoot::Binding(path) => {
                let Some((_, def)) = self
                    .defs_by_path
                    .iter()
                    .find(|(binding_path, _)| binding_path == path)
                else {
                    return Err(ElaborateProgramError::UnsupportedRoot { root: root.clone() });
                };
                self.ensure_def_instance(*def).map(ElaboratedRoot::Instance)
            }
        }
    }

    fn ensure_def_instance(&mut self, def: DefId) -> Result<MonoInstanceId, ElaborateProgramError> {
        if let Some(instance) = self.instance_by_def.get(&def).copied() {
            return Ok(instance);
        }
        let binding = self
            .bindings_by_def
            .get(&def)
            .copied()
            .ok_or(ElaborateProgramError::MissingBinding { def })?;
        if constraints::scheme_needs_instantiation(&binding.scheme) {
            return Err(ElaborateProgramError::Constraint(
                ConstraintError::GenericDirectRefScheme { def },
            ));
        }
        let signature =
            concrete_computation_from_scheme(ElaborateSite::Binding(def), &binding.scheme)?;
        let instance = self.ensure_def_instance_with_signature(def, signature)?;
        self.instance_by_def.insert(def, instance);
        Ok(instance)
    }

    fn ensure_def_instance_with_signature(
        &mut self,
        def: DefId,
        signature: MonoComputation,
    ) -> Result<MonoInstanceId, ElaborateProgramError> {
        if let Some(instance) = self
            .specialized_instances
            .iter()
            .find(|instance| instance.def == def && instance.signature == signature)
            .map(|instance| instance.instance)
        {
            return Ok(instance);
        }
        let binding = self
            .bindings_by_def
            .get(&def)
            .copied()
            .ok_or(ElaborateProgramError::MissingBinding { def })?;
        let body =
            elaborate_binding_expr_with_signature(def, binding, signature.clone(), &self.env)?;
        let instance = self.push_instance(DemandSource::Def(def), signature.clone(), body.expr);
        self.specialized_instances.push(SpecializedInstance {
            def,
            signature,
            instance,
        });
        if !constraints::scheme_needs_instantiation(&binding.scheme) {
            self.instance_by_def.insert(def, instance);
        }
        self.resolve_direct_refs_for_instance(
            instance,
            &binding.body.ir,
            &body.direct_ref_instances,
        )?;
        self.resolve_typeclass_refs_for_instance(
            instance,
            &binding.body.ir,
            &body.resolved_typeclass_instances,
        )?;
        Ok(instance)
    }

    fn push_instance(
        &mut self,
        source: DemandSource,
        signature: MonoComputation,
        body: ElaboratedExpr,
    ) -> MonoInstanceId {
        let id = MonoInstanceId(self.instances.len() as u32);
        self.instances.push(MonoInstance {
            id,
            source,
            signature,
            body,
        });
        id
    }

    fn resolve_direct_refs_for_instance(
        &mut self,
        instance: MonoInstanceId,
        expr: &ErasedExpr,
        direct_ref_instances: &BTreeMap<RefId, constraints::DirectRefInstanceDemand>,
    ) -> Result<(), ElaborateProgramError> {
        let mut refs = BTreeSet::new();
        collect_expr_refs(expr, &mut refs);
        for ref_id in refs {
            let Some(def) = self.export.erased.refs.direct.get(&ref_id).copied() else {
                continue;
            };
            let target = if let Some(demand) = direct_ref_instances.get(&ref_id) {
                self.ensure_def_instance_with_signature(demand.def, demand.signature.clone())?
            } else {
                self.ensure_def_instance(def)?
            };
            self.refs.entries.insert(
                ResolvedRefKey { instance, ref_id },
                ResolvedRef {
                    target,
                    source: ResolvedRefSource::Direct { def },
                },
            );
        }
        Ok(())
    }

    fn resolve_typeclass_refs_for_instance(
        &mut self,
        instance: MonoInstanceId,
        expr: &ErasedExpr,
        resolved_typeclass_instances: &BTreeMap<
            RefId,
            constraints::ResolvedTypeclassInstanceDemand,
        >,
    ) -> Result<(), ElaborateProgramError> {
        let mut refs = BTreeSet::new();
        collect_expr_refs(expr, &mut refs);
        for ref_id in refs {
            let Some(resolved) = self
                .export
                .erased
                .refs
                .resolved_typeclass
                .get(&ref_id)
                .cloned()
            else {
                continue;
            };
            let target = if let Some(demand) = resolved_typeclass_instances.get(&ref_id) {
                self.ensure_def_instance_with_signature(
                    demand.resolved.impl_member,
                    demand.signature.clone(),
                )?
            } else {
                self.ensure_def_instance(resolved.impl_member)?
            };
            self.refs.entries.insert(
                ResolvedRefKey { instance, ref_id },
                ResolvedRef {
                    target,
                    source: ResolvedRefSource::InferResolvedTypeclass { resolved },
                },
            );
        }
        Ok(())
    }
}

struct SpecializedInstance {
    def: DefId,
    signature: MonoComputation,
    instance: MonoInstanceId,
}

struct ElaboratedBody {
    expr: ElaboratedExpr,
    direct_ref_instances: BTreeMap<RefId, constraints::DirectRefInstanceDemand>,
    resolved_typeclass_instances: BTreeMap<RefId, constraints::ResolvedTypeclassInstanceDemand>,
}

fn elaborate_root_expr(
    index: usize,
    expr: &InferredExpr,
    env: &constraints::ConstraintEnvironment<'_>,
) -> Result<ElaboratedBody, ElaborateProgramError> {
    let site = ElaborateSite::RootExpr(index);
    let draft = draft::ElaborationDraft::from_root_expr(index, &expr.ir);
    let comp = concrete_computation(site.clone(), &expr.ir, &expr.typ, &expr.eff, env)?;
    let solution = constraints::ConstraintSet::seed_root(&draft, comp)
        .solve(&draft, &expr.ir, env)
        .map_err(ElaborateProgramError::Constraint)?;
    let expr = elaborate_expr(site, &draft, draft.root, &expr.ir, &solution)?;
    Ok(ElaboratedBody {
        expr,
        direct_ref_instances: solution.direct_ref_instances().clone(),
        resolved_typeclass_instances: solution.resolved_typeclass_instances().clone(),
    })
}

fn elaborate_binding_expr_with_signature(
    def: DefId,
    binding: &InferredBinding,
    signature: MonoComputation,
    env: &constraints::ConstraintEnvironment<'_>,
) -> Result<ElaboratedBody, ElaborateProgramError> {
    let site = ElaborateSite::Binding(def);
    let draft = draft::ElaborationDraft::from_root_expr(0, &binding.body.ir);
    let solution = constraints::ConstraintSet::seed_root(&draft, signature)
        .solve(&draft, &binding.body.ir, env)
        .map_err(ElaborateProgramError::Constraint)?;
    let expr = elaborate_expr(site, &draft, draft.root, &binding.body.ir, &solution)?;
    Ok(ElaboratedBody {
        expr,
        direct_ref_instances: solution.direct_ref_instances().clone(),
        resolved_typeclass_instances: solution.resolved_typeclass_instances().clone(),
    })
}

fn concrete_computation_from_scheme(
    site: ElaborateSite,
    scheme: &Scheme,
) -> Result<MonoComputation, ElaborateProgramError> {
    Ok(MonoComputation {
        value: MonoType::Value(ConcreteType::try_from_type(scheme.body.clone()).map_err(
            |error| ElaborateProgramError::NonConcreteComputationType {
                site: site.clone(),
                field: ComputationField::Value,
                error,
            },
        )?),
        effect: MonoEffect::new(ConcreteType::try_from_type(Type::Never).map_err(|error| {
            ElaborateProgramError::NonConcreteComputationType {
                site,
                field: ComputationField::Effect,
                error,
            }
        })?),
    })
}

fn concrete_computation(
    site: ElaborateSite,
    expr: &ErasedExpr,
    typ: &TypeBounds,
    eff: &TypeBounds,
    env: &constraints::ConstraintEnvironment<'_>,
) -> Result<MonoComputation, ElaborateProgramError> {
    let value = exact_concrete_type(site.clone(), ComputationField::Value, typ)?;
    Ok(MonoComputation {
        effect: MonoEffect::new(concrete_effect_type(site, expr, &value, eff, env)?),
        value: MonoType::Value(value),
    })
}

fn concrete_effect_type(
    site: ElaborateSite,
    expr: &ErasedExpr,
    value: &ConcreteType,
    bounds: &TypeBounds,
    env: &constraints::ConstraintEnvironment<'_>,
) -> Result<ConcreteType, ElaborateProgramError> {
    match exact_concrete_type(site.clone(), ComputationField::Effect, bounds) {
        Err(ElaborateProgramError::NonExactComputationBounds { .. })
            if syntactically_pure_expr(expr) =>
        {
            ConcreteType::try_from_type(Type::Never).map_err(|error| {
                ElaborateProgramError::NonConcreteComputationType {
                    site,
                    field: ComputationField::Effect,
                    error,
                }
            })
        }
        Err(error @ ElaborateProgramError::NonExactComputationBounds { .. }) => {
            if let Some(effect) = direct_ref_apply_effect(site, expr, value, env)? {
                Ok(effect)
            } else {
                Err(error)
            }
        }
        other => other,
    }
}

fn direct_ref_apply_effect(
    site: ElaborateSite,
    expr: &ErasedExpr,
    value: &ConcreteType,
    env: &constraints::ConstraintEnvironment<'_>,
) -> Result<Option<ConcreteType>, ElaborateProgramError> {
    let ErasedExpr::Apply { callee, arg } = expr else {
        return Ok(None);
    };
    let ErasedExpr::Ref(ref_id) = callee.as_ref() else {
        return Ok(None);
    };
    let scheme = env
        .direct_scheme(*ref_id)
        .map(|(_, scheme)| scheme)
        .or_else(|| {
            env.resolved_typeclass_scheme(*ref_id)
                .map(|(_, scheme)| scheme)
        });
    let Some(scheme) = scheme else {
        return Ok(None);
    };
    let Some(ret_effect) =
        constraints::direct_apply_ret_effect_from_scheme(scheme, value.as_type(), arg, env)
    else {
        return Ok(None);
    };
    ConcreteType::try_from_type(ret_effect)
        .map(Some)
        .map_err(|error| ElaborateProgramError::NonConcreteComputationType {
            site,
            field: ComputationField::Effect,
            error,
        })
}

fn syntactically_pure_expr(expr: &ErasedExpr) -> bool {
    match expr {
        ErasedExpr::Def(_)
        | ErasedExpr::Ref(_)
        | ErasedExpr::PrimitiveOp(_)
        | ErasedExpr::Lit(_)
        | ErasedExpr::Lambda { .. } => true,
        ErasedExpr::Tuple(items) => items.iter().all(syntactically_pure_expr),
        ErasedExpr::Record { fields, spread } => {
            fields
                .iter()
                .all(|field| syntactically_pure_expr(&field.value))
                && spread.as_ref().is_none_or(|spread| match spread {
                    yulang_erased_ir::RecordSpreadExpr::Head(expr)
                    | yulang_erased_ir::RecordSpreadExpr::Tail(expr) => {
                        syntactically_pure_expr(expr)
                    }
                })
        }
        ErasedExpr::Variant { value, .. } => value
            .as_ref()
            .is_none_or(|value| syntactically_pure_expr(value)),
        ErasedExpr::Select { base, .. } | ErasedExpr::Pack { expr: base, .. } => {
            syntactically_pure_expr(base)
        }
        ErasedExpr::Apply { .. }
        | ErasedExpr::RefSet { .. }
        | ErasedExpr::Match { .. }
        | ErasedExpr::Handle { .. }
        | ErasedExpr::Block(_)
        | ErasedExpr::BindHere { .. } => false,
    }
}

fn exact_concrete_type(
    site: ElaborateSite,
    field: ComputationField,
    bounds: &TypeBounds,
) -> Result<ConcreteType, ElaborateProgramError> {
    let Some(lower) = &bounds.lower else {
        return Err(ElaborateProgramError::NonExactComputationBounds {
            site,
            field,
            bounds: bounds.clone(),
        });
    };
    let Some(upper) = &bounds.upper else {
        return Err(ElaborateProgramError::NonExactComputationBounds {
            site,
            field,
            bounds: bounds.clone(),
        });
    };
    if lower != upper {
        if let Some(candidate) = unique_concrete_candidate(bounds) {
            return ConcreteType::try_from_type(candidate).map_err(|error| {
                ElaborateProgramError::NonConcreteComputationType { site, field, error }
            });
        }
        return Err(ElaborateProgramError::NonExactComputationBounds {
            site,
            field,
            bounds: bounds.clone(),
        });
    }
    ConcreteType::try_from_type((**lower).clone())
        .map_err(|error| ElaborateProgramError::NonConcreteComputationType { site, field, error })
}

fn unique_concrete_candidate(bounds: &TypeBounds) -> Option<Type> {
    let mut candidates = Vec::new();
    if let Some(lower) = &bounds.lower {
        collect_concrete_candidates(lower, &mut candidates);
    }
    if let Some(upper) = &bounds.upper {
        collect_concrete_candidates(upper, &mut candidates);
    }
    if candidates.len() == 1 {
        candidates.pop()
    } else {
        None
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

fn concretize_type_candidate(ty: &Type) -> Option<Type> {
    if ConcreteType::try_from_type(ty.clone()).is_ok() {
        return Some(ty.clone());
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
        yulang_erased_ir::TypeArg::Bounds(bounds) => Some(yulang_erased_ir::TypeArg::Bounds(
            yulang_erased_ir::TypeBounds {
                lower: bounds.lower.as_ref().map_or(Some(None), |lower| {
                    concretize_type_candidate(lower).map(Box::new).map(Some)
                })?,
                upper: bounds.upper.as_ref().map_or(Some(None), |upper| {
                    concretize_type_candidate(upper).map(Box::new).map(Some)
                })?,
            },
        )),
    }
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

fn collect_expr_refs(expr: &ErasedExpr, out: &mut BTreeSet<RefId>) {
    match expr {
        ErasedExpr::Ref(ref_id) => {
            out.insert(*ref_id);
        }
        ErasedExpr::Apply { callee, arg } => {
            collect_expr_refs(callee, out);
            collect_expr_refs(arg, out);
        }
        ErasedExpr::RefSet { reference, value } => {
            collect_expr_refs(reference, out);
            collect_expr_refs(value, out);
        }
        ErasedExpr::Lambda { body, .. }
        | ErasedExpr::BindHere { expr: body }
        | ErasedExpr::Pack { expr: body, .. } => collect_expr_refs(body, out),
        ErasedExpr::Tuple(items) => {
            for item in items {
                collect_expr_refs(item, out);
            }
        }
        ErasedExpr::Record { fields, spread } => {
            for field in fields {
                collect_expr_refs(&field.value, out);
            }
            if let Some(spread) = spread {
                match spread {
                    yulang_erased_ir::RecordSpreadExpr::Head(expr)
                    | yulang_erased_ir::RecordSpreadExpr::Tail(expr) => {
                        collect_expr_refs(expr, out);
                    }
                }
            }
        }
        ErasedExpr::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr_refs(value, out);
            }
        }
        ErasedExpr::Select { base, .. } => collect_expr_refs(base, out),
        ErasedExpr::Match { scrutinee, arms } => {
            collect_expr_refs(scrutinee, out);
            for arm in arms {
                collect_pattern_refs(&arm.pattern, out);
                if let Some(guard) = &arm.guard {
                    collect_expr_refs(guard, out);
                }
                collect_expr_refs(&arm.body, out);
            }
        }
        ErasedExpr::Handle { body, arms } => {
            collect_expr_refs(body, out);
            for arm in arms {
                collect_pattern_refs(&arm.payload, out);
                if let Some(guard) = &arm.guard {
                    collect_expr_refs(guard, out);
                }
                collect_expr_refs(&arm.body, out);
            }
        }
        ErasedExpr::Block(block) => collect_block_refs(block, out),
        ErasedExpr::Def(_) | ErasedExpr::PrimitiveOp(_) | ErasedExpr::Lit(_) => {}
    }
}

fn collect_block_refs(block: &yulang_erased_ir::ErasedBlock, out: &mut BTreeSet<RefId>) {
    for stmt in &block.stmts {
        match stmt {
            yulang_erased_ir::ErasedStmt::Let { pattern, value } => {
                collect_pattern_refs(pattern, out);
                collect_expr_refs(value, out);
            }
            yulang_erased_ir::ErasedStmt::Expr(expr) => collect_expr_refs(expr, out),
            yulang_erased_ir::ErasedStmt::Module { body, .. } => collect_block_refs(body, out),
        }
    }
    if let Some(tail) = &block.tail {
        collect_expr_refs(tail, out);
    }
}

fn collect_pattern_refs(pattern: &yulang_erased_ir::Pattern, out: &mut BTreeSet<RefId>) {
    match pattern {
        yulang_erased_ir::Pattern::Tuple(items) => {
            for item in items {
                collect_pattern_refs(item, out);
            }
        }
        yulang_erased_ir::Pattern::Or { left, right } => {
            collect_pattern_refs(left, out);
            collect_pattern_refs(right, out);
        }
        yulang_erased_ir::Pattern::List {
            prefix,
            spread,
            suffix,
        } => {
            for item in prefix {
                collect_pattern_refs(item, out);
            }
            if let Some(spread) = spread {
                collect_pattern_refs(spread, out);
            }
            for item in suffix {
                collect_pattern_refs(item, out);
            }
        }
        yulang_erased_ir::Pattern::Constructor { ref_id, payload } => {
            out.insert(*ref_id);
            if let Some(payload) = payload {
                collect_pattern_refs(payload, out);
            }
        }
        yulang_erased_ir::Pattern::Record { fields, spread } => {
            for field in fields {
                collect_pattern_refs(&field.pattern, out);
                if let Some(default) = &field.default {
                    collect_expr_refs(default, out);
                }
            }
            if let Some(spread) = spread {
                match spread {
                    yulang_erased_ir::RecordSpreadPattern::Head(pattern)
                    | yulang_erased_ir::RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_refs(pattern, out);
                    }
                }
            }
        }
        yulang_erased_ir::Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                collect_pattern_refs(value, out);
            }
        }
        yulang_erased_ir::Pattern::As { pattern, .. } => collect_pattern_refs(pattern, out),
        yulang_erased_ir::Pattern::Wildcard
        | yulang_erased_ir::Pattern::Bind(_)
        | yulang_erased_ir::Pattern::Lit(_)
        | yulang_erased_ir::Pattern::UnresolvedName(_) => {}
    }
}

fn elaborate_expr(
    site: ElaborateSite,
    draft: &draft::ElaborationDraft,
    id: draft::DraftExprId,
    expr: &ErasedExpr,
    solution: &constraints::ComputationSolution,
) -> Result<ElaboratedExpr, ElaborateProgramError> {
    let comp = solution
        .computation_for_expr(draft, id)
        .map_err(ElaborateProgramError::Constraint)?
        .clone();
    let kind = match expr {
        ErasedExpr::Def(def) => ElaboratedExprKind::Def(*def),
        ErasedExpr::Ref(ref_id) => ElaboratedExprKind::Ref(*ref_id),
        ErasedExpr::PrimitiveOp(op) => ElaboratedExprKind::PrimitiveOp(*op),
        ErasedExpr::Lit(lit) => ElaboratedExprKind::Lit(lit.clone()),
        ErasedExpr::Lambda { param, body } => {
            let [body_id] = draft.expr(id).children.as_slice() else {
                return Err(ElaborateProgramError::UnsupportedExpr {
                    site,
                    kind: ErasedExprKind::Lambda,
                });
            };
            ElaboratedExprKind::Lambda {
                param: *param,
                param_type: lambda_param_type(&comp),
                body: Box::new(elaborate_expr(
                    site.clone(),
                    draft,
                    *body_id,
                    body,
                    solution,
                )?),
            }
        }
        ErasedExpr::Apply { callee, arg } => {
            let [callee_id, arg_id] = draft.expr(id).children.as_slice() else {
                return Err(ElaborateProgramError::UnsupportedExpr {
                    site,
                    kind: ErasedExprKind::Apply,
                });
            };
            ElaboratedExprKind::Apply {
                callee: Box::new(elaborate_expr(
                    site.clone(),
                    draft,
                    *callee_id,
                    callee,
                    solution,
                )?),
                arg: Box::new(elaborate_expr(site.clone(), draft, *arg_id, arg, solution)?),
            }
        }
        ErasedExpr::Tuple(items) => {
            let children = draft.expr(id).children.clone();
            ElaboratedExprKind::Tuple(
                children
                    .into_iter()
                    .zip(items)
                    .map(|(child_id, item)| {
                        elaborate_expr(site.clone(), draft, child_id, item, solution)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            )
        }
        ErasedExpr::Record { fields, spread } => {
            let children = draft.expr(id).children.clone();
            let elaborated_fields = fields
                .iter()
                .zip(children.iter().copied())
                .map(|(field, child_id)| {
                    Ok(elaborated_ir::RecordExprField {
                        name: field.name.clone(),
                        value: elaborate_expr(
                            site.clone(),
                            draft,
                            child_id,
                            &field.value,
                            solution,
                        )?,
                    })
                })
                .collect::<Result<Vec<_>, ElaborateProgramError>>()?;
            let elaborated_spread = spread
                .as_ref()
                .zip(children.get(fields.len()).copied())
                .map(|(spread, spread_id)| match spread {
                    yulang_erased_ir::RecordSpreadExpr::Head(expr) => {
                        elaborate_expr(site.clone(), draft, spread_id, expr, solution)
                            .map(Box::new)
                            .map(elaborated_ir::RecordSpreadExpr::Head)
                    }
                    yulang_erased_ir::RecordSpreadExpr::Tail(expr) => {
                        elaborate_expr(site.clone(), draft, spread_id, expr, solution)
                            .map(Box::new)
                            .map(elaborated_ir::RecordSpreadExpr::Tail)
                    }
                })
                .transpose()?;
            ElaboratedExprKind::Record {
                fields: elaborated_fields,
                spread: elaborated_spread,
            }
        }
        ErasedExpr::Variant { tag, value, .. } => {
            let value = value
                .as_ref()
                .zip(draft.expr(id).children.first().copied())
                .map(|(value, child_id)| {
                    elaborate_expr(site.clone(), draft, child_id, value, solution).map(Box::new)
                })
                .transpose()?;
            ElaboratedExprKind::Variant {
                tag: tag.clone(),
                value,
            }
        }
        ErasedExpr::Select { base, field } => {
            let [base_id] = draft.expr(id).children.as_slice() else {
                return Err(ElaborateProgramError::UnsupportedExpr {
                    site,
                    kind: ErasedExprKind::Select,
                });
            };
            ElaboratedExprKind::Select {
                base: Box::new(elaborate_expr(
                    site.clone(),
                    draft,
                    *base_id,
                    base,
                    solution,
                )?),
                field: field.clone(),
            }
        }
        ErasedExpr::BindHere { expr } => {
            let [thunk_id] = draft.expr(id).children.as_slice() else {
                return Err(ElaborateProgramError::UnsupportedExpr {
                    site,
                    kind: ErasedExprKind::BindHere,
                });
            };
            let thunk = elaborate_expr(site.clone(), draft, *thunk_id, expr, solution)?;
            let source = match &thunk.comp.value {
                MonoType::EffectiveThunk(source) => source.clone(),
                found => {
                    return Err(ElaborateProgramError::ExpectedEffectiveThunk {
                        site,
                        found: found.clone(),
                    });
                }
            };
            ElaboratedExprKind::ForceThunk {
                thunk: Box::new(thunk),
                source,
                target: comp.clone(),
            }
        }
        ErasedExpr::Pack { var, expr } => {
            let [body_id] = draft.expr(id).children.as_slice() else {
                return Err(ElaborateProgramError::UnsupportedExpr {
                    site,
                    kind: ErasedExprKind::Pack,
                });
            };
            ElaboratedExprKind::Pack {
                var: var.clone(),
                expr: Box::new(elaborate_expr(
                    site.clone(),
                    draft,
                    *body_id,
                    expr,
                    solution,
                )?),
            }
        }
        _ => {
            return Err(ElaborateProgramError::UnsupportedExpr {
                site,
                kind: ErasedExprKind::from_expr(expr),
            });
        }
    };
    Ok(ElaboratedExpr::new(kind, comp))
}

fn lambda_param_type(comp: &MonoComputation) -> MonoType {
    let MonoType::Value(value) = &comp.value else {
        unreachable!("lambda solver only assigns function value computations to lambdas");
    };
    let yulang_erased_ir::Type::Fun { param, .. } = value.as_type() else {
        unreachable!("lambda solver only assigns function value computations to lambdas");
    };
    MonoType::Value(
        ConcreteType::try_from_type((**param).clone())
            .expect("lambda function parameter was validated as concrete"),
    )
}

impl ErasedExprKind {
    pub(crate) fn from_expr(expr: &ErasedExpr) -> Self {
        match expr {
            ErasedExpr::Def(_) => Self::Def,
            ErasedExpr::Ref(_) => Self::Ref,
            ErasedExpr::PrimitiveOp(_) => Self::PrimitiveOp,
            ErasedExpr::Lit(_) => Self::Lit,
            ErasedExpr::Lambda { .. } => Self::Lambda,
            ErasedExpr::Apply { .. } => Self::Apply,
            ErasedExpr::RefSet { .. } => Self::RefSet,
            ErasedExpr::Tuple(_) => Self::Tuple,
            ErasedExpr::Record { .. } => Self::Record,
            ErasedExpr::Variant { .. } => Self::Variant,
            ErasedExpr::Select { .. } => Self::Select,
            ErasedExpr::Match { .. } => Self::Match,
            ErasedExpr::Handle { .. } => Self::Handle,
            ErasedExpr::Block(_) => Self::Block,
            ErasedExpr::BindHere { .. } => Self::BindHere,
            ErasedExpr::Pack { .. } => Self::Pack,
        }
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
                def: yulang_erased_ir::DefId(4),
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
                def: yulang_erased_ir::DefId(40),
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

    #[test]
    fn elaborate_program_accepts_actual_literal_infer_export() {
        let mut lowered = yulang_infer::lower_virtual_source_with_options(
            "1\n",
            None,
            yulang_infer::SourceOptions::default(),
        )
        .expect("lower virtual source");
        let export = yulang_infer::export_erased_program(&mut lowered.state);

        let program = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_program()
            .expect("literal root can be elaborated from actual infer export");

        assert_eq!(program.module.root_exprs.len(), 1);
        assert!(matches!(
            &program.module.root_exprs[0].kind,
            elaborated_ir::ElaboratedExprKind::Lit(yulang_erased_ir::Lit::Int(value))
                if value == "1"
        ));
    }

    #[test]
    fn elaborate_program_accepts_actual_monomorphic_direct_ref_apply_export() {
        let mut lowered = yulang_infer::lower_virtual_source_with_options(
            "my f(x: int) = x\nf 1\n",
            None,
            yulang_infer::SourceOptions::default(),
        )
        .expect("lower virtual source");
        let export = yulang_infer::export_erased_program(&mut lowered.state);

        let program = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_program()
            .expect("monomorphic direct ref apply can be elaborated from actual infer export");

        assert!(matches!(
            &program.module.root_exprs[0].kind,
            elaborated_ir::ElaboratedExprKind::Apply { .. }
        ));
    }

    #[test]
    fn elaborate_program_accepts_actual_generic_direct_ref_apply_export() {
        let mut lowered = yulang_infer::lower_virtual_source_with_options(
            "my id x = x\nid 1\n",
            None,
            yulang_infer::SourceOptions::default(),
        )
        .expect("lower virtual source");
        let export = yulang_infer::export_erased_program(&mut lowered.state);

        let program = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_program()
            .expect("generic direct ref apply can be instantiated from actual infer export");

        assert!(matches!(
            &program.module.root_exprs[0].kind,
            elaborated_ir::ElaboratedExprKind::Apply { .. }
        ));
        assert_eq!(
            program.module.instances.len(),
            2,
            "root and instantiated id binding should both be materialized",
        );
        assert!(
            program
                .module
                .instances
                .iter()
                .any(|instance| matches!(instance.source, elaborated_ir::DemandSource::Def(_)))
        );
    }

    #[test]
    fn elaborate_program_accepts_actual_generic_direct_ref_apply_with_ref_arg_export() {
        let mut lowered = yulang_infer::lower_virtual_source_with_options(
            "my one = 1\nmy id x = x\nid one\n",
            None,
            yulang_infer::SourceOptions::default(),
        )
        .expect("lower virtual source");
        let export = yulang_infer::export_erased_program(&mut lowered.state);

        let program = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_program()
            .expect("generic direct ref apply should instantiate from monomorphic direct ref arg");

        assert!(matches!(
            &program.module.root_exprs[0].kind,
            elaborated_ir::ElaboratedExprKind::Apply { .. }
        ));
        assert!(
            program.module.instances.len() >= 2,
            "root and instantiated id binding should be materialized, got {:?}",
            program.module.instances,
        );
    }

    #[test]
    fn elaborate_program_accepts_actual_record_literal_export() {
        let mut lowered = yulang_infer::lower_virtual_source_with_options(
            "{x: 1, y: 2}\n",
            None,
            yulang_infer::SourceOptions::default(),
        )
        .expect("lower virtual source");
        let export = yulang_infer::export_erased_program(&mut lowered.state);

        let program = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_program()
            .expect("record literal should elaborate from actual infer export");

        let elaborated_ir::ElaboratedExprKind::Record { fields, .. } =
            &program.module.root_exprs[0].kind
        else {
            panic!("root should elaborate as record");
        };
        assert_eq!(fields.len(), 2);
    }

    #[test]
    fn elaborate_program_accepts_actual_record_field_select_export() {
        let mut lowered = yulang_infer::lower_virtual_source_with_options(
            "my r = {x: 1, y: 2}\nr.x\n",
            None,
            yulang_infer::SourceOptions::default(),
        )
        .expect("lower virtual source");
        let export = yulang_infer::export_erased_program(&mut lowered.state);

        let program = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_program()
            .expect("record field selection should elaborate from actual infer export");

        assert!(matches!(
            &program.module.root_exprs[0].kind,
            elaborated_ir::ElaboratedExprKind::Select { field, .. } if field.0 == "x"
        ));
    }

    #[test]
    fn elaborate_program_resolves_actual_infer_resolved_typeclass_ref() {
        let mut lowered = yulang_infer::lower_virtual_source_with_options(
            "role Display 'a:\n  our a.display: string\n\n\
impl Display int:\n  our x.display = \"int\"\n\n\
1.display\n",
            None,
            yulang_infer::SourceOptions::default(),
        )
        .expect("lower virtual source");
        let export = yulang_infer::export_erased_program(&mut lowered.state);

        let program = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_program()
            .expect("infer-resolved typeclass ref should elaborate");

        assert!(program.refs.entries.values().any(|resolved| matches!(
            &resolved.source,
            elaborated_ir::ResolvedRefSource::InferResolvedTypeclass { resolved }
                if resolved
                    .class
                    .segments
                    .last()
                    .is_some_and(|name| name.0 == "Display")
        )));
    }

    #[test]
    fn elaborator_builds_program_for_concrete_leaf_root() {
        let int = named_type("int");
        let empty_effect = yulang_erased_ir::Type::Never;
        let mut export = InferExport::default();
        export.erased.module.root_exprs.push(inferred_root(
            yulang_erased_ir::ErasedExpr::Lit(yulang_erased_ir::Lit::Int("1".to_string())),
            int.clone(),
            empty_effect.clone(),
        ));
        export.erased.module.roots.push(PrincipalRoot::Expr(0));

        let program = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_program()
            .expect("initial elaborated program");

        let root_instance = elaborated_ir::MonoInstanceId(0);
        assert_eq!(
            program.module.roots,
            vec![elaborated_ir::ElaboratedRoot::Instance(root_instance)]
        );
        assert_eq!(program.module.instances.len(), 1);
        assert_eq!(
            program.module.instances[0].source,
            elaborated_ir::DemandSource::RootExpr(0)
        );
        assert_eq!(program.module.root_exprs.len(), 1);
        assert!(matches!(
            &program.module.root_exprs[0].kind,
            elaborated_ir::ElaboratedExprKind::Lit(yulang_erased_ir::Lit::Int(value))
                if value == "1"
        ));
        assert!(matches!(
            &program.module.instances[0].body.kind,
            elaborated_ir::ElaboratedExprKind::Lit(yulang_erased_ir::Lit::Int(value))
                if value == "1"
        ));
        assert_eq!(
            program.module.root_exprs[0].comp.value,
            elaborated_ir::MonoType::Value(
                elaborated_ir::ConcreteType::try_from_type(int).expect("int is concrete")
            )
        );
        assert_eq!(
            program.module.root_exprs[0].comp.effect,
            elaborated_ir::MonoEffect::new(
                elaborated_ir::ConcreteType::try_from_type(empty_effect)
                    .expect("Never is a concrete empty effect row")
            )
        );
    }

    #[test]
    fn elaborator_rejects_unknown_root_type_without_fallback() {
        let mut export = InferExport::default();
        export.erased.module.root_exprs.push(inferred_root(
            yulang_erased_ir::ErasedExpr::Lit(yulang_erased_ir::Lit::Int("1".to_string())),
            yulang_erased_ir::Type::Unknown,
            yulang_erased_ir::Type::Never,
        ));

        let Err(ElaborateProgramError::NonConcreteComputationType {
            site: ElaborateSite::RootExpr(0),
            field: ComputationField::Value,
            error: elaborated_ir::ConcreteTypeError::Unknown,
        }) = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_program()
        else {
            panic!("Unknown root type must not be used as a concrete elaborated type");
        };
    }

    #[test]
    fn elaborator_builds_tuple_program_from_root_tuple_type() {
        let mut export = InferExport::default();
        export.erased.module.root_exprs.push(inferred_root(
            yulang_erased_ir::ErasedExpr::Tuple(vec![
                yulang_erased_ir::ErasedExpr::Lit(yulang_erased_ir::Lit::Int("1".to_string())),
                yulang_erased_ir::ErasedExpr::Lit(yulang_erased_ir::Lit::Int("2".to_string())),
            ]),
            yulang_erased_ir::Type::Tuple(vec![named_type("int"), named_type("int")]),
            yulang_erased_ir::Type::Never,
        ));

        let program = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_program()
            .expect("tuple root can be elaborated from exact root tuple type");

        let elaborated_ir::ElaboratedExprKind::Tuple(items) = &program.module.root_exprs[0].kind
        else {
            panic!("tuple root should elaborate as a tuple expression");
        };
        assert_eq!(items.len(), 2);
        assert!(matches!(
            &items[0].kind,
            elaborated_ir::ElaboratedExprKind::Lit(yulang_erased_ir::Lit::Int(value))
                if value == "1"
        ));
        assert!(matches!(
            &items[1].kind,
            elaborated_ir::ElaboratedExprKind::Lit(yulang_erased_ir::Lit::Int(value))
                if value == "2"
        ));
        assert_eq!(
            items[0].comp.value,
            elaborated_ir::MonoType::Value(
                elaborated_ir::ConcreteType::try_from_type(named_type("int"))
                    .expect("int is concrete")
            )
        );
    }

    #[test]
    fn elaborator_instantiates_generic_direct_ref_apply_from_use_site() {
        let int = named_type("int");
        let mut export = InferExport::default();
        let var = yulang_erased_ir::Type::Var(yulang_erased_ir::TypeVar("a".to_string()));
        let fn_type = yulang_erased_ir::Type::Fun {
            param: Box::new(var.clone()),
            param_effect: Box::new(yulang_erased_ir::Type::Never),
            ret_effect: Box::new(yulang_erased_ir::Type::Never),
            ret: Box::new(var),
        };
        export
            .erased
            .module
            .bindings
            .push(yulang_erased_ir::InferredBinding {
                def: yulang_erased_ir::DefId(2),
                name: yulang_erased_ir::Path::from_name(yulang_erased_ir::Name("id".to_string())),
                scheme: yulang_erased_ir::Scheme {
                    body: fn_type.clone(),
                    quantified_types: vec![yulang_erased_ir::TypeVar("a".to_string())],
                    quantified_effects: Vec::new(),
                    quantified_refs: Vec::new(),
                    typeclass_obligations: Vec::new(),
                    requirements: Vec::new(),
                },
                body: inferred_root(
                    yulang_erased_ir::ErasedExpr::Lambda {
                        param: yulang_erased_ir::DefId(10),
                        body: Box::new(yulang_erased_ir::ErasedExpr::Def(yulang_erased_ir::DefId(
                            10,
                        ))),
                    },
                    fn_type,
                    yulang_erased_ir::Type::Never,
                ),
            });
        export.erased.module.root_exprs.push(inferred_root(
            yulang_erased_ir::ErasedExpr::Apply {
                callee: Box::new(yulang_erased_ir::ErasedExpr::Ref(yulang_erased_ir::RefId(
                    1,
                ))),
                arg: Box::new(yulang_erased_ir::ErasedExpr::Lit(
                    yulang_erased_ir::Lit::Int("1".to_string()),
                )),
            },
            named_type("int"),
            yulang_erased_ir::Type::Never,
        ));
        export
            .erased
            .refs
            .direct
            .insert(yulang_erased_ir::RefId(1), yulang_erased_ir::DefId(2));

        let program = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_program()
            .expect("generic direct ref apply should instantiate from arg and result");

        let specialized_signature = elaborated_ir::MonoComputation {
            value: elaborated_ir::MonoType::Value(
                elaborated_ir::ConcreteType::try_from_type(yulang_erased_ir::Type::Fun {
                    param: Box::new(int.clone()),
                    param_effect: Box::new(yulang_erased_ir::Type::Never),
                    ret_effect: Box::new(yulang_erased_ir::Type::Never),
                    ret: Box::new(int.clone()),
                })
                .expect("instantiated function type is concrete"),
            ),
            effect: elaborated_ir::MonoEffect::new(
                elaborated_ir::ConcreteType::try_from_type(yulang_erased_ir::Type::Never)
                    .expect("Never is concrete"),
            ),
        };
        assert!(
            program
                .module
                .instances
                .iter()
                .any(|instance| instance.source
                    == elaborated_ir::DemandSource::Def(yulang_erased_ir::DefId(2))
                    && instance.signature == specialized_signature),
            "generic id should be materialized as int -> int, instances={:?}",
            program.module.instances,
        );
        assert_eq!(
            program.refs.entries.get(&elaborated_ir::ResolvedRefKey {
                instance: elaborated_ir::MonoInstanceId(0),
                ref_id: yulang_erased_ir::RefId(1),
            }),
            Some(&elaborated_ir::ResolvedRef {
                target: elaborated_ir::MonoInstanceId(1),
                source: elaborated_ir::ResolvedRefSource::Direct {
                    def: yulang_erased_ir::DefId(2),
                },
            })
        );
    }

    #[test]
    fn elaborator_rejects_generic_direct_ref_apply_without_concrete_use_site() {
        let int = named_type("int");
        let var = yulang_erased_ir::Type::Var(yulang_erased_ir::TypeVar("a".to_string()));
        let fn_type = yulang_erased_ir::Type::Fun {
            param: Box::new(var.clone()),
            param_effect: Box::new(yulang_erased_ir::Type::Never),
            ret_effect: Box::new(yulang_erased_ir::Type::Never),
            ret: Box::new(var),
        };
        let mut export = InferExport::default();
        export
            .erased
            .module
            .bindings
            .push(yulang_erased_ir::InferredBinding {
                def: yulang_erased_ir::DefId(2),
                name: yulang_erased_ir::Path::from_name(yulang_erased_ir::Name("id".to_string())),
                scheme: yulang_erased_ir::Scheme {
                    body: fn_type.clone(),
                    quantified_types: vec![yulang_erased_ir::TypeVar("a".to_string())],
                    quantified_effects: Vec::new(),
                    quantified_refs: Vec::new(),
                    typeclass_obligations: Vec::new(),
                    requirements: Vec::new(),
                },
                body: inferred_root(
                    yulang_erased_ir::ErasedExpr::Lambda {
                        param: yulang_erased_ir::DefId(10),
                        body: Box::new(yulang_erased_ir::ErasedExpr::Def(yulang_erased_ir::DefId(
                            10,
                        ))),
                    },
                    fn_type,
                    yulang_erased_ir::Type::Never,
                ),
            });
        export.erased.module.root_exprs.push(inferred_root(
            yulang_erased_ir::ErasedExpr::Apply {
                callee: Box::new(yulang_erased_ir::ErasedExpr::Ref(yulang_erased_ir::RefId(
                    1,
                ))),
                arg: Box::new(yulang_erased_ir::ErasedExpr::Def(yulang_erased_ir::DefId(
                    99,
                ))),
            },
            int,
            yulang_erased_ir::Type::Never,
        ));
        export
            .erased
            .refs
            .direct
            .insert(yulang_erased_ir::RefId(1), yulang_erased_ir::DefId(2));

        let Err(ElaborateProgramError::Constraint(ConstraintError::GenericDirectRefScheme {
            def: yulang_erased_ir::DefId(2),
        })) = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_program()
        else {
            panic!("generic direct ref apply should wait when the use site is not concrete enough");
        };
    }

    #[test]
    fn elaborator_builds_monomorphic_direct_ref_apply_from_scheme() {
        let int = named_type("int");
        let fn_type = yulang_erased_ir::Type::Fun {
            param: Box::new(int.clone()),
            param_effect: Box::new(yulang_erased_ir::Type::Never),
            ret_effect: Box::new(yulang_erased_ir::Type::Never),
            ret: Box::new(int.clone()),
        };
        let mut export = InferExport::default();
        export
            .erased
            .module
            .bindings
            .push(yulang_erased_ir::InferredBinding {
                def: yulang_erased_ir::DefId(2),
                name: yulang_erased_ir::Path::from_name(yulang_erased_ir::Name(
                    "id_int".to_string(),
                )),
                scheme: yulang_erased_ir::Scheme {
                    body: fn_type.clone(),
                    quantified_types: Vec::new(),
                    quantified_effects: Vec::new(),
                    quantified_refs: Vec::new(),
                    typeclass_obligations: Vec::new(),
                    requirements: Vec::new(),
                },
                body: inferred_root(
                    yulang_erased_ir::ErasedExpr::Lambda {
                        param: yulang_erased_ir::DefId(10),
                        body: Box::new(yulang_erased_ir::ErasedExpr::Def(yulang_erased_ir::DefId(
                            10,
                        ))),
                    },
                    fn_type,
                    yulang_erased_ir::Type::Never,
                ),
            });
        export
            .erased
            .refs
            .direct
            .insert(yulang_erased_ir::RefId(1), yulang_erased_ir::DefId(2));
        export.erased.module.root_exprs.push(inferred_root(
            yulang_erased_ir::ErasedExpr::Apply {
                callee: Box::new(yulang_erased_ir::ErasedExpr::Ref(yulang_erased_ir::RefId(
                    1,
                ))),
                arg: Box::new(yulang_erased_ir::ErasedExpr::Lit(
                    yulang_erased_ir::Lit::Int("1".to_string()),
                )),
            },
            int.clone(),
            yulang_erased_ir::Type::Never,
        ));
        export.erased.module.roots.push(PrincipalRoot::Expr(0));

        let program = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_program()
            .expect("monomorphic direct ref apply can be elaborated from its scheme");

        let elaborated_ir::ElaboratedExprKind::Apply { callee, arg } =
            &program.module.root_exprs[0].kind
        else {
            panic!("root should elaborate as apply");
        };
        assert!(matches!(
            &callee.kind,
            elaborated_ir::ElaboratedExprKind::Ref(yulang_erased_ir::RefId(1))
        ));
        assert!(matches!(
            &arg.kind,
            elaborated_ir::ElaboratedExprKind::Lit(yulang_erased_ir::Lit::Int(value))
                if value == "1"
        ));
        assert_eq!(
            program.module.root_exprs[0].comp.value,
            elaborated_ir::MonoType::Value(
                elaborated_ir::ConcreteType::try_from_type(int).expect("int is concrete")
            )
        );
        assert_eq!(program.module.instances.len(), 2);
        assert_eq!(
            program.module.roots,
            vec![elaborated_ir::ElaboratedRoot::Instance(
                elaborated_ir::MonoInstanceId(0)
            )]
        );
        assert_eq!(
            program.module.instances[0].source,
            elaborated_ir::DemandSource::RootExpr(0)
        );
        assert_eq!(
            program.module.instances[1].source,
            elaborated_ir::DemandSource::Def(yulang_erased_ir::DefId(2))
        );
        assert_eq!(
            program.refs.entries.get(&elaborated_ir::ResolvedRefKey {
                instance: elaborated_ir::MonoInstanceId(0),
                ref_id: yulang_erased_ir::RefId(1),
            }),
            Some(&elaborated_ir::ResolvedRef {
                target: elaborated_ir::MonoInstanceId(1),
                source: elaborated_ir::ResolvedRefSource::Direct {
                    def: yulang_erased_ir::DefId(2),
                },
            })
        );
    }

    #[test]
    fn elaborator_builds_inline_lambda_apply_from_root_result_type() {
        let int = named_type("int");
        let mut export = InferExport::default();
        export.erased.module.root_exprs.push(inferred_root(
            yulang_erased_ir::ErasedExpr::Apply {
                callee: Box::new(yulang_erased_ir::ErasedExpr::Lambda {
                    param: yulang_erased_ir::DefId(1),
                    body: Box::new(yulang_erased_ir::ErasedExpr::Def(yulang_erased_ir::DefId(
                        1,
                    ))),
                }),
                arg: Box::new(yulang_erased_ir::ErasedExpr::Lit(
                    yulang_erased_ir::Lit::Int("1".to_string()),
                )),
            },
            int.clone(),
            yulang_erased_ir::Type::Never,
        ));

        let program = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_program()
            .expect("inline lambda apply can be elaborated");

        let elaborated_ir::ElaboratedExprKind::Apply { callee, arg } =
            &program.module.root_exprs[0].kind
        else {
            panic!("root should elaborate as apply");
        };
        assert!(matches!(
            &callee.kind,
            elaborated_ir::ElaboratedExprKind::Lambda {
                param: yulang_erased_ir::DefId(1),
                ..
            }
        ));
        assert!(matches!(
            &arg.kind,
            elaborated_ir::ElaboratedExprKind::Lit(yulang_erased_ir::Lit::Int(value))
                if value == "1"
        ));
        assert_eq!(
            program.module.root_exprs[0].comp.value,
            elaborated_ir::MonoType::Value(
                elaborated_ir::ConcreteType::try_from_type(int).expect("int is concrete")
            )
        );
        let elaborated_ir::ElaboratedExprKind::Lambda {
            param_type, body, ..
        } = &callee.kind
        else {
            panic!("callee should be lambda");
        };
        assert_eq!(
            param_type,
            &elaborated_ir::MonoType::Value(
                elaborated_ir::ConcreteType::try_from_type(named_type("int"))
                    .expect("int is concrete")
            )
        );
        assert!(matches!(
            &body.kind,
            elaborated_ir::ElaboratedExprKind::Def(yulang_erased_ir::DefId(1))
        ));
        assert_eq!(
            body.comp.value,
            elaborated_ir::MonoType::Value(
                elaborated_ir::ConcreteType::try_from_type(named_type("int"))
                    .expect("int is concrete")
            )
        );
    }

    #[test]
    fn elaborator_builds_root_lambda_from_exact_function_type() {
        let int = named_type("int");
        let mut export = InferExport::default();
        export.erased.module.root_exprs.push(inferred_root(
            yulang_erased_ir::ErasedExpr::Lambda {
                param: yulang_erased_ir::DefId(1),
                body: Box::new(yulang_erased_ir::ErasedExpr::Def(yulang_erased_ir::DefId(
                    1,
                ))),
            },
            yulang_erased_ir::Type::Fun {
                param: Box::new(int.clone()),
                param_effect: Box::new(yulang_erased_ir::Type::Never),
                ret_effect: Box::new(yulang_erased_ir::Type::Never),
                ret: Box::new(int.clone()),
            },
            yulang_erased_ir::Type::Never,
        ));

        let program = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_program()
            .expect("root lambda can be elaborated from exact function type");

        let elaborated_ir::ElaboratedExprKind::Lambda {
            param_type, body, ..
        } = &program.module.root_exprs[0].kind
        else {
            panic!("root should elaborate as lambda");
        };
        assert_eq!(
            param_type,
            &elaborated_ir::MonoType::Value(
                elaborated_ir::ConcreteType::try_from_type(int.clone()).expect("int is concrete")
            )
        );
        assert!(matches!(
            &body.kind,
            elaborated_ir::ElaboratedExprKind::Def(yulang_erased_ir::DefId(1))
        ));
        assert_eq!(
            body.comp.value,
            elaborated_ir::MonoType::Value(
                elaborated_ir::ConcreteType::try_from_type(int).expect("int is concrete")
            )
        );
    }

    #[test]
    fn elaborator_lowers_bind_here_to_force_thunk_boundary() {
        let int = named_type("int");
        let io = named_type("io");
        let mut export = InferExport::default();
        export.erased.module.root_exprs.push(inferred_root(
            yulang_erased_ir::ErasedExpr::BindHere {
                expr: Box::new(yulang_erased_ir::ErasedExpr::Def(yulang_erased_ir::DefId(
                    1,
                ))),
            },
            int.clone(),
            io.clone(),
        ));

        let program = Elaborator::try_new(&export)
            .expect("valid erased export")
            .build_program()
            .expect("bind-here should elaborate as a force-thunk boundary");

        let elaborated_ir::ElaboratedExprKind::ForceThunk {
            thunk,
            source,
            target,
        } = &program.module.root_exprs[0].kind
        else {
            panic!("bind-here should elaborate as ForceThunk");
        };
        assert_eq!(
            source.effect,
            elaborated_ir::MonoEffect::new(
                elaborated_ir::ConcreteType::try_from_type(io).expect("io is concrete")
            )
        );
        assert_eq!(
            source.value.as_ref(),
            &elaborated_ir::MonoType::Value(
                elaborated_ir::ConcreteType::try_from_type(int.clone()).expect("int is concrete")
            )
        );
        assert_eq!(
            target.value,
            elaborated_ir::MonoType::Value(
                elaborated_ir::ConcreteType::try_from_type(int).expect("int is concrete")
            )
        );
        assert!(matches!(
            &thunk.comp.value,
            elaborated_ir::MonoType::EffectiveThunk(_)
        ));
        assert!(matches!(
            &thunk.kind,
            elaborated_ir::ElaboratedExprKind::Def(yulang_erased_ir::DefId(1))
        ));
    }

    fn inferred_root(
        ir: yulang_erased_ir::ErasedExpr,
        typ: yulang_erased_ir::Type,
        eff: yulang_erased_ir::Type,
    ) -> yulang_erased_ir::InferredExpr {
        yulang_erased_ir::InferredExpr {
            typ: yulang_erased_ir::TypeBounds::exact(typ),
            eff: yulang_erased_ir::TypeBounds::exact(eff),
            ir,
        }
    }

    fn named_type(name: &str) -> yulang_erased_ir::Type {
        yulang_erased_ir::Type::Named {
            path: yulang_erased_ir::Path::from_name(yulang_erased_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }
}
