use std::collections::{HashMap, HashSet};

use super::*;
use crate::ir::{Binding, Expr, ExprKind, HandleArm, Module, Pattern, Stmt, Type as RuntimeType};

pub struct DemandChecker<'a> {
    bindings: HashMap<core_ir::Path, &'a Binding>,
    generic_bindings: HashSet<core_ir::Path>,
    generic_role_impls: HashMap<core_ir::Name, Vec<RoleImplDemandCandidate>>,
    pure_handler_bindings: HashMap<core_ir::Path, Vec<core_ir::Path>>,
}

impl<'a> DemandChecker<'a> {
    pub fn from_module(module: &'a Module) -> Self {
        Self {
            pure_handler_bindings: pure_handler_bindings(module),
            bindings: module
                .bindings
                .iter()
                .map(|binding| (binding.name.clone(), binding))
                .collect(),
            generic_bindings: module
                .bindings
                .iter()
                .filter(|binding| binding_needs_demand_monomorphization(binding))
                .map(|binding| binding.name.clone())
                .collect(),
            generic_role_impls: generic_role_impl_candidates(module),
        }
    }

    pub fn check_demand(&self, demand: &Demand) -> Result<CheckedDemand, DemandCheckError> {
        let binding = self
            .bindings
            .get(&demand.target)
            .copied()
            .ok_or_else(|| DemandCheckError::MissingBinding(demand.target.clone()))?;
        let consumed_effects =
            consumed_effects_for_target(&self.pure_handler_bindings, &demand.target);
        let mut checker = ExprChecker::new(
            &self.generic_bindings,
            &self.generic_role_impls,
            &consumed_effects,
            &demand.target,
        );
        let expected =
            normalize_check_demand_signature(&demand.target, demand.key.signature.clone());
        let actual = match checker.check_expr(&binding.body, &expected) {
            Ok(actual) => actual,
            Err(DemandCheckError::Unify(DemandUnifyError::EffectMismatch { actual, .. }))
                if expected.is_closed()
                    && !consumed_effects.is_empty()
                    && demand_effect_is_consumed(&actual, &consumed_effects) =>
            {
                expected.clone()
            }
            Err(_)
                if expected.is_closed()
                    && (path_ends_with(&demand.target, &["std", "list", "fold_impl"])
                        || binding_references_path(binding, &demand.target)) =>
            {
                expected.clone()
            }
            Err(error) => {
                debug_check_demand_error(&demand.target, &expected, &error);
                return Err(error);
            }
        };
        let (substitutions, child_demands, local_signatures) = checker.finish(&expected);
        debug_checked_locals(&demand.target, &local_signatures, &child_demands);
        let solved_shape = preserve_operational_shapes(&expected, &actual);
        let solved = close_pure_handler_result(
            close_consumed_effect_holes(
                close_constructor_effect_args(substitutions.apply_signature(&solved_shape)),
                &consumed_effects,
            ),
            &consumed_effects,
        );
        let solved = close_known_associated_type_signature(&demand.target, solved);
        let solved = close_default_effect_holes(solved);
        let solved = close_known_associated_type_signature(&demand.target, solved);
        Ok(CheckedDemand {
            target: demand.target.clone(),
            expected,
            actual,
            solved,
            substitutions,
            child_demands,
            local_signatures,
        })
    }

    pub fn missing_demands_queue(&self, missing: &[MissingDemand]) -> DemandQueue {
        let mut queue = DemandQueue::default();
        for demand in missing {
            self.push_missing_demand(&mut queue, demand);
        }
        queue
    }

    fn push_missing_demand(&self, queue: &mut DemandQueue, demand: &MissingDemand) {
        let target = demand_call_target(&demand.target);
        if self.generic_bindings.contains(&target) {
            queue.push_signature(target, runtime_any_type(), demand.signature.clone());
            return;
        }
        if !is_role_method_path(&target) {
            return;
        }
        let Some(method) = target.segments.last() else {
            return;
        };
        let Some(candidates) = self.generic_role_impls.get(method) else {
            return;
        };
        let impl_signature = role_impl_demand_signature(&demand.signature);
        for candidate in candidates {
            if !role_impl_candidate_accepts(&candidate.signature, &demand.signature) {
                continue;
            }
            queue.push_signature(
                candidate.path.clone(),
                runtime_any_type(),
                impl_signature.clone(),
            );
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedDemand {
    pub target: core_ir::Path,
    pub expected: DemandSignature,
    pub actual: DemandSignature,
    pub solved: DemandSignature,
    pub substitutions: DemandSubstitution,
    pub child_demands: DemandQueue,
    pub local_signatures: HashMap<core_ir::Path, DemandSignature>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DemandCheckError {
    MissingBinding(core_ir::Path),
    Unify(DemandUnifyError),
}

impl From<DemandUnifyError> for DemandCheckError {
    fn from(error: DemandUnifyError) -> Self {
        Self::Unify(error)
    }
}

struct ExprChecker<'a> {
    generic_bindings: &'a HashSet<core_ir::Path>,
    generic_role_impls: &'a HashMap<core_ir::Name, Vec<RoleImplDemandCandidate>>,
    consumed_effects: &'a [core_ir::Path],
    current_target: &'a core_ir::Path,
    enclosing_thunk_effects: Vec<DemandEffect>,
    locals: HashMap<core_ir::Path, DemandSignature>,
    next_hole: u32,
    unifier: DemandUnifier,
    child_demands: Vec<PendingChildDemand>,
    local_signatures: Vec<(core_ir::Path, DemandSignature)>,
}

#[derive(Clone)]
struct PendingChildDemand {
    target: core_ir::Path,
    expected: RuntimeType,
    signature: DemandSignature,
}

struct LocalBinding {
    local: core_ir::Path,
    previous: Option<DemandSignature>,
    signature: DemandSignature,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RoleImplDemandCandidate {
    path: core_ir::Path,
    signature: DemandSignature,
}

#[derive(Clone)]
struct ExprCheckerCheckpoint {
    enclosing_thunk_effects: Vec<DemandEffect>,
    locals: HashMap<core_ir::Path, DemandSignature>,
    next_hole: u32,
    unifier: DemandUnifier,
    child_demands: Vec<PendingChildDemand>,
    local_signatures: Vec<(core_ir::Path, DemandSignature)>,
}

impl<'a> ExprChecker<'a> {
    fn new(
        generic_bindings: &'a HashSet<core_ir::Path>,
        generic_role_impls: &'a HashMap<core_ir::Name, Vec<RoleImplDemandCandidate>>,
        consumed_effects: &'a [core_ir::Path],
        current_target: &'a core_ir::Path,
    ) -> Self {
        Self {
            generic_bindings,
            generic_role_impls,
            consumed_effects,
            current_target,
            enclosing_thunk_effects: Vec::new(),
            locals: HashMap::new(),
            next_hole: 0,
            unifier: DemandUnifier::new(),
            child_demands: Vec::new(),
            local_signatures: Vec::new(),
        }
    }

    fn check_expr(
        &mut self,
        expr: &Expr,
        expected: &DemandSignature,
    ) -> Result<DemandSignature, DemandCheckError> {
        self.next_hole = self.next_hole.max(expected.next_hole_after());
        let actual = self.synth_expr(expr, Some(expected))?;
        if let DemandSignature::Thunk { value, .. } = expected
            && !matches!(actual, DemandSignature::Thunk { .. })
        {
            self.unify_pure_actual_with_thunk_value(value, &actual)?;
            return Ok(expected.clone());
        }
        if !matches!(expected, DemandSignature::Thunk { .. })
            && let Some(value) = self.consumed_thunk_value(&actual)
        {
            self.unify_signature(expected, value)?;
            return Ok(actual);
        }
        if !matches!(expected, DemandSignature::Thunk { .. })
            && self.accept_enclosed_thunk_value(expected, &actual)
        {
            return Ok(actual);
        }
        self.unify_call_return(expected, &actual)?;
        Ok(actual)
    }

    fn unify_signature(
        &mut self,
        expected: &DemandSignature,
        actual: &DemandSignature,
    ) -> Result<(), DemandCheckError> {
        self.unifier.unify(expected, actual).map_err(|error| {
            debug_unify_signature_error(self.current_target, expected, actual, &error);
            DemandCheckError::from(error)
        })
    }

    fn consumed_thunk_value<'b>(
        &self,
        signature: &'b DemandSignature,
    ) -> Option<&'b DemandSignature> {
        let DemandSignature::Thunk { effect, value } = signature else {
            return None;
        };
        demand_effect_is_consumed(effect, self.consumed_effects).then_some(value.as_ref())
    }

    fn accept_enclosed_thunk_value(
        &mut self,
        expected: &DemandSignature,
        actual: &DemandSignature,
    ) -> bool {
        let DemandSignature::Thunk { .. } = actual else {
            return false;
        };
        let Some(effect) = self.enclosing_thunk_effects.last().cloned() else {
            return false;
        };
        let expected_thunk = DemandSignature::Thunk {
            effect,
            value: Box::new(expected.clone()),
        };
        self.unifier.unify(&expected_thunk, actual).is_ok()
    }

    fn lift_known_handler_return_to_enclosing_effect(
        &self,
        target: &core_ir::Path,
        ret: DemandSignature,
    ) -> DemandSignature {
        if known_handler_consumed_effects(target).is_empty()
            || matches!(ret, DemandSignature::Thunk { .. })
        {
            return ret;
        }
        let Some(effect) = self.enclosing_thunk_effects.last().cloned() else {
            return ret;
        };
        if demand_effect_is_empty(&effect) {
            return ret;
        }
        DemandSignature::Thunk {
            effect,
            value: Box::new(ret),
        }
    }

    fn lift_recursive_return_to_enclosing_effect(
        &self,
        target: &core_ir::Path,
        ret: DemandSignature,
    ) -> DemandSignature {
        if target != self.current_target || matches!(ret, DemandSignature::Thunk { .. }) {
            return ret;
        }
        let Some(effect) = self.enclosing_thunk_effects.last().cloned() else {
            return ret;
        };
        if demand_effect_is_empty(&effect) {
            return ret;
        }
        DemandSignature::Thunk {
            effect,
            value: Box::new(ret),
        }
    }

    fn lift_effectful_expr_return_to_enclosing_effect(
        &self,
        expr: &Expr,
        evidence: Option<&core_ir::ApplyEvidence>,
        ret: DemandSignature,
    ) -> DemandSignature {
        if matches!(ret, DemandSignature::Thunk { .. })
            || !expr_or_evidence_has_effectful_result(expr, evidence)
        {
            return ret;
        }
        let Some(effect) = self.enclosing_thunk_effects.last().cloned() else {
            return ret;
        };
        if demand_effect_is_empty(&effect) {
            return ret;
        }
        DemandSignature::Thunk {
            effect,
            value: Box::new(ret),
        }
    }

    fn synth_expr(
        &mut self,
        expr: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        if let (
            ExprKind::Lambda { param, body, .. },
            Some(DemandSignature::Thunk { effect, value }),
        ) = (&expr.kind, expected)
        {
            self.enclosing_thunk_effects.push(effect.clone());
            let result = self.synth_lambda(expr, param, body, Some(value));
            self.enclosing_thunk_effects.pop();
            let value = result?;
            return Ok(DemandSignature::Thunk {
                effect: effect.clone(),
                value: Box::new(value),
            });
        }
        match &expr.kind {
            ExprKind::Lambda { param, body, .. } => self.synth_lambda(expr, param, body, expected),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => self.synth_if(cond, then_branch, else_branch, expected),
            ExprKind::Tuple(items) => self.synth_tuple(items, expected),
            ExprKind::Record { fields, spread } => self.synth_record(fields, spread, expected),
            ExprKind::Variant { tag, value } => {
                self.synth_variant(expr, tag, value.as_deref(), expected)
            }
            ExprKind::Select { base, field } => self.synth_select(expr, base, field, expected),
            ExprKind::Match {
                scrutinee, arms, ..
            } => self.synth_match(expr, scrutinee, arms, expected),
            ExprKind::Block { stmts, tail } => self.synth_block(stmts, tail.as_deref(), expected),
            ExprKind::Handle { body, arms, .. } => self.synth_handle(expr, body, arms, expected),
            ExprKind::BindHere { expr: inner } => self.synth_bind_here(expr, inner, expected),
            ExprKind::Thunk {
                effect,
                value,
                expr: inner,
            } => self.synth_thunk(expr, effect, value, inner, expected),
            ExprKind::LocalPushId { body, .. } => self.synth_expr(body, expected),
            ExprKind::AddId { thunk, .. } => self.synth_expr(thunk, expected),
            ExprKind::Coerce {
                from, expr: inner, ..
            } => self.synth_coerce(expr, from, inner, expected),
            ExprKind::Pack { expr: inner, .. } => self.synth_expr(inner, expected),
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                ..
            } => {
                if let Some((target, head, args)) = applied_call_with_head(expr)
                    && self.generic_bindings.contains(target)
                {
                    let principal_hints = applied_call_principal_signature_hints(expr, args.len());
                    let ret = expected.cloned().unwrap_or_else(|| {
                        if let Some((_, ret)) = &principal_hints {
                            return ret.clone();
                        }
                        let fallback = self.signature_from_type(&expr.ty);
                        evidence
                            .as_ref()
                            .map(|evidence| {
                                apply_evidence_merged_signature(evidence, fallback.clone())
                            })
                            .unwrap_or(fallback)
                    });
                    let ret = self.lift_known_handler_return_to_enclosing_effect(target, ret);
                    let ret = self.lift_recursive_return_to_enclosing_effect(target, ret);
                    let ret = self.lift_effectful_expr_return_to_enclosing_effect(
                        expr,
                        evidence.as_ref(),
                        ret,
                    );
                    let (param_hints, ret) = self.closed_call_signature(
                        target,
                        head,
                        &args,
                        ret,
                        principal_hints.map(|(params, _)| params),
                    );
                    let evidence_hints = applied_call_param_evidence_signatures(expr);
                    let mut arg_signatures = Vec::with_capacity(args.len());
                    for (index, ((arg, hint), evidence_hint)) in args
                        .iter()
                        .zip(param_hints.iter().cloned())
                        .zip(evidence_hints.into_iter())
                        .enumerate()
                    {
                        let hint = merge_optional_signature_hints(hint, evidence_hint);
                        match self.generic_arg_signature(arg, hint.clone()) {
                            Ok(signature) => arg_signatures.push(signature),
                            Err(error) => {
                                debug_demand_arg_rejection(target, index, hint.as_ref(), &error);
                                return Err(error);
                            }
                        }
                    }
                    let arg_signatures = strengthen_handler_arg_signatures(
                        target,
                        arg_signatures,
                        &param_hints,
                        &ret,
                    );
                    let signature = curried_signatures(&arg_signatures, ret.clone());
                    self.child_demands.push(PendingChildDemand {
                        target: target.clone(),
                        expected: curried_call_type(&args, expr.ty.clone()),
                        signature,
                    });
                    return Ok(ret);
                }
                if let Some((target, head, args)) = applied_call_with_head(expr)
                    && is_role_method_path(target)
                    && let Some(method) = target.segments.last()
                    && let Some(candidates) = self.generic_role_impls.get(method).cloned()
                {
                    let principal_hints = applied_call_principal_signature_hints(expr, args.len());
                    let ret = expected.cloned().unwrap_or_else(|| {
                        if let Some((_, ret)) = &principal_hints {
                            return ret.clone();
                        }
                        let fallback = self.signature_from_type(&expr.ty);
                        evidence
                            .as_ref()
                            .map(|evidence| {
                                apply_evidence_merged_signature(evidence, fallback.clone())
                            })
                            .unwrap_or(fallback)
                    });
                    let ret = self.lift_effectful_expr_return_to_enclosing_effect(
                        expr,
                        evidence.as_ref(),
                        ret,
                    );
                    let (param_hints, ret) = self.closed_call_signature(
                        target,
                        head,
                        &args,
                        ret,
                        principal_hints.map(|(params, _)| params),
                    );
                    let evidence_hints = applied_call_param_evidence_signatures(expr);
                    let mut arg_signatures = Vec::with_capacity(args.len());
                    for (index, ((arg, hint), evidence_hint)) in args
                        .iter()
                        .zip(param_hints)
                        .zip(evidence_hints.into_iter())
                        .enumerate()
                    {
                        let hint = merge_optional_signature_hints(hint, evidence_hint);
                        match self.generic_arg_signature(arg, hint.clone()) {
                            Ok(signature) => arg_signatures.push(signature),
                            Err(error) => {
                                debug_demand_arg_rejection(target, index, hint.as_ref(), &error);
                                return Err(error);
                            }
                        }
                    }
                    let ret = return_effect_from_args(ret, &arg_signatures);
                    let signature = curried_signatures(&arg_signatures, ret.clone());
                    let signature = self.apply_current_signature(&signature);
                    let ret = self.apply_current_signature(&ret);
                    let impl_signature = role_impl_demand_signature(&signature);
                    let mut queued = false;
                    for candidate in candidates {
                        if !role_impl_candidate_accepts(&candidate.signature, &signature) {
                            continue;
                        }
                        self.child_demands.push(PendingChildDemand {
                            target: candidate.path,
                            expected: curried_call_type(&args, expr.ty.clone()),
                            signature: impl_signature.clone(),
                        });
                        queued = true;
                    }
                    if queued {
                        return Ok(ret);
                    }
                }
                let callee_signature = self.synth_expr(callee, None)?;
                let callee = if self.has_precise_local_callee_signature(callee, &callee_signature) {
                    callee_signature
                } else {
                    evidence
                        .as_ref()
                        .and_then(apply_evidence_callee_signature)
                        .map(|hint| merge_signature_hint(callee_signature.clone(), hint))
                        .unwrap_or(callee_signature)
                };
                let callee = force_thunk_callee_signature(callee);
                match callee {
                    DemandSignature::Fun { param, ret } => {
                        if let Some(expected) = expected {
                            self.constrain_call_return(expected, &ret)?;
                        }
                        let param = self.apply_current_signature(&param);
                        let ret = self.apply_current_signature(&ret);
                        self.check_expr(arg, &param)?;
                        Ok(ret)
                    }
                    DemandSignature::Core(DemandCoreType::Fun {
                        param,
                        param_effect,
                        ret_effect,
                        ret,
                    }) => {
                        let param = effected_core_signature(*param, *param_effect);
                        let ret = effected_core_signature(*ret, *ret_effect);
                        if let Some(expected) = expected {
                            self.constrain_call_return(expected, &ret)?;
                        }
                        let param = self.apply_current_signature(&param);
                        let ret = self.apply_current_signature(&ret);
                        self.check_expr(arg, &param)?;
                        Ok(ret)
                    }
                    _ => Ok(self.signature_from_type(&expr.ty)),
                }
            }
            ExprKind::Var(path) => Ok(self
                .locals
                .get(path)
                .cloned()
                .map(|signature| self.apply_current_signature(&signature))
                .unwrap_or_else(|| self.signature_from_type(&expr.ty))),
            ExprKind::Lit(_) => Ok(self.signature_from_type(&expr.ty)),
            _ => Ok(self.signature_from_type(&expr.ty)),
        }
    }

    fn synth_lambda(
        &mut self,
        expr: &Expr,
        param: &core_ir::Name,
        body: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        let expected = expected
            .cloned()
            .unwrap_or_else(|| self.signature_from_type(&expr.ty));
        let (param_ty, ret) = match &expected {
            DemandSignature::Fun { param, ret } => (param.as_ref().clone(), ret.as_ref().clone()),
            DemandSignature::Core(DemandCoreType::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            }) => (
                effected_core_signature(param.as_ref().clone(), param_effect.as_ref().clone()),
                effected_core_signature(ret.as_ref().clone(), ret_effect.as_ref().clone()),
            ),
            _ => return Ok(expected),
        };
        let param_ty = self.preserve_lambda_param_runtime_shape(&expr.ty, param_ty);
        let actual = lambda_actual_signature(&expected, param_ty.clone(), ret.clone());
        let local = core_ir::Path::from_name(param.clone());
        let previous = self.locals.insert(local.clone(), param_ty);
        let outer_thunk_effects = std::mem::take(&mut self.enclosing_thunk_effects);
        let result = self.check_expr(body, &ret);
        self.enclosing_thunk_effects = outer_thunk_effects;
        result?;
        restore_local(&mut self.locals, local, previous);
        Ok(actual)
    }

    fn synth_if(
        &mut self,
        cond: &Expr,
        then_branch: &Expr,
        else_branch: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        self.synth_expr(cond, None)?;
        if let Some(expected) = expected {
            self.check_expr(then_branch, expected)?;
            self.check_expr(else_branch, expected)?;
            return Ok(expected.clone());
        }
        let then_ty = self.synth_expr(then_branch, None)?;
        let else_ty = self.synth_expr(else_branch, None)?;
        self.unifier.unify(&then_ty, &else_ty)?;
        Ok(then_ty)
    }

    fn synth_tuple(
        &mut self,
        items: &[Expr],
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        if let Some(expected @ DemandSignature::Core(DemandCoreType::Tuple(expected_items))) =
            expected
            && expected_items.len() == items.len()
        {
            for (item, expected_item) in items.iter().zip(expected_items) {
                self.check_expr(item, &DemandSignature::Core(expected_item.clone()))?;
            }
            return Ok(expected.clone());
        }
        let items = items
            .iter()
            .map(|item| {
                self.synth_expr(item, None)
                    .map(|item| signature_core_value(&item))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(DemandSignature::Core(DemandCoreType::Tuple(items)))
    }

    fn synth_record(
        &mut self,
        fields: &[crate::ir::RecordExprField],
        spread: &Option<crate::ir::RecordSpreadExpr>,
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        if let Some(expected @ DemandSignature::Core(DemandCoreType::Record(expected_fields))) =
            expected
        {
            for field in fields {
                if let Some(expected_field) = expected_fields
                    .iter()
                    .find(|expected| expected.name == field.name)
                {
                    self.check_expr(
                        &field.value,
                        &DemandSignature::Core(expected_field.value.clone()),
                    )?;
                } else {
                    self.synth_expr(&field.value, None)?;
                }
            }
            self.synth_record_spread(spread)?;
            return Ok(expected.clone());
        }
        let fields = fields
            .iter()
            .map(|field| {
                Ok(DemandRecordField {
                    name: field.name.clone(),
                    value: signature_core_value(&self.synth_expr(&field.value, None)?),
                    optional: false,
                })
            })
            .collect::<Result<Vec<_>, DemandCheckError>>()?;
        self.synth_record_spread(spread)?;
        Ok(DemandSignature::Core(DemandCoreType::Record(fields)))
    }

    fn synth_record_spread(
        &mut self,
        spread: &Option<crate::ir::RecordSpreadExpr>,
    ) -> Result<(), DemandCheckError> {
        if let Some(spread) = spread {
            match spread {
                crate::ir::RecordSpreadExpr::Head(expr)
                | crate::ir::RecordSpreadExpr::Tail(expr) => {
                    self.synth_expr(expr, None)?;
                }
            }
        }
        Ok(())
    }

    fn synth_variant(
        &mut self,
        expr: &Expr,
        tag: &core_ir::Name,
        value: Option<&Expr>,
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        if let Some(expected @ DemandSignature::Core(DemandCoreType::Variant(cases))) = expected {
            if let Some(value) = value
                && let Some(case) = cases.iter().find(|case| case.name == *tag)
                && let Some(payload) = case.payloads.first()
            {
                self.check_expr(value, &DemandSignature::Core(payload.clone()))?;
            }
            return Ok(expected.clone());
        }
        if let Some(expected @ DemandSignature::Core(DemandCoreType::Named { args, .. })) = expected
        {
            if let Some(value) = value
                && let Some(payload) = single_payload_from_type_args(args)
            {
                self.check_expr(value, &DemandSignature::Core(payload))?;
            }
            return Ok(expected.clone());
        }
        let payloads = value
            .map(|value| {
                self.synth_expr(value, None)
                    .map(|ty| vec![signature_core_value(&ty)])
            })
            .transpose()?
            .unwrap_or_default();
        if payloads.is_empty() && value.is_some() {
            return Ok(self.signature_from_type(&expr.ty));
        }
        Ok(DemandSignature::Core(DemandCoreType::Variant(vec![
            DemandVariantCase {
                name: tag.clone(),
                payloads,
            },
        ])))
    }

    fn synth_select(
        &mut self,
        expr: &Expr,
        base: &Expr,
        field: &core_ir::Name,
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        let base_ty = self.synth_expr(base, None)?;
        if let DemandSignature::Core(DemandCoreType::Record(fields)) = base_ty
            && let Some(field) = fields.iter().find(|candidate| candidate.name == *field)
        {
            let actual = DemandSignature::Core(field.value.clone());
            if let Some(expected) = expected {
                self.unifier.unify(expected, &actual)?;
                return Ok(expected.clone());
            }
            return Ok(actual);
        }
        Ok(expected
            .cloned()
            .unwrap_or_else(|| self.signature_from_type(&expr.ty)))
    }

    fn synth_match(
        &mut self,
        expr: &Expr,
        scrutinee: &Expr,
        arms: &[crate::ir::MatchArm],
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        let scrutinee_hint = self
            .match_scrutinee_expr_hint(scrutinee)?
            .or_else(|| self.match_scrutinee_hint(arms));
        let scrutinee_actual = self.synth_expr(scrutinee, None)?;
        let scrutinee_ty = match scrutinee_hint {
            Some(hint) if signature_is_uninformative(&scrutinee_actual) => {
                self.unify_signature(&hint, &scrutinee_actual)?;
                hint
            }
            Some(hint) => {
                let _ = self.unifier.unify(&hint, &scrutinee_actual);
                scrutinee_actual
            }
            None => scrutinee_actual,
        };
        let result_ty = expected
            .cloned()
            .unwrap_or_else(|| self.signature_from_type(&expr.ty));
        for arm in arms {
            let mut inserted = Vec::new();
            self.push_pattern_bindings(
                &arm.pattern,
                Some(&signature_value(&scrutinee_ty)),
                &mut inserted,
            );
            if let Some(guard) = &arm.guard {
                self.check_expr(guard, &DemandSignature::Core(named_core("bool")))?;
            }
            self.check_expr(&arm.body, &result_ty)?;
            for binding in inserted.into_iter().rev() {
                restore_local(&mut self.locals, binding.local, binding.previous);
            }
        }
        Ok(result_ty)
    }

    fn match_scrutinee_hint(&mut self, arms: &[crate::ir::MatchArm]) -> Option<DemandSignature> {
        let ty = pattern_runtime_type(&arms.first()?.pattern);
        (!runtime_type_is_any(ty)).then(|| self.signature_from_type(ty))
    }

    fn match_scrutinee_expr_hint(
        &mut self,
        scrutinee: &Expr,
    ) -> Result<Option<DemandSignature>, DemandCheckError> {
        let Some((target, _, args)) = applied_call_with_head(scrutinee) else {
            return Ok(None);
        };
        if !path_ends_with(target, &["std", "list", "view_raw"]) {
            return Ok(None);
        }
        let Some(xs) = args.first() else {
            return Ok(None);
        };
        let xs = self.synth_expr(xs, None)?;
        let Some(item) = list_item_signature(&xs) else {
            return Ok(None);
        };
        Ok(Some(DemandSignature::Core(DemandCoreType::Named {
            path: path_segments(&["std", "list", "list_view"]),
            args: vec![DemandTypeArg::Type(item)],
        })))
    }

    fn synth_block(
        &mut self,
        stmts: &[Stmt],
        tail: Option<&Expr>,
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        let mut inserted = Vec::new();
        for stmt in stmts {
            inserted.extend(self.synth_stmt(stmt)?);
        }
        let result = match (tail, expected) {
            (Some(tail), Some(expected)) => {
                self.check_expr(tail, expected).map(|_| expected.clone())
            }
            (Some(tail), None) => self.synth_expr(tail, None),
            (None, Some(expected)) => {
                self.unifier
                    .unify(expected, &DemandSignature::Core(named_core("unit")))?;
                Ok(expected.clone())
            }
            (None, None) => Ok(DemandSignature::Core(named_core("unit"))),
        };
        let result = result.and_then(|result| {
            self.recheck_block_local_functions(stmts)?;
            Ok(result)
        });
        for binding in inserted.into_iter().rev() {
            restore_local(&mut self.locals, binding.local, binding.previous);
        }
        result
    }

    fn recheck_block_local_functions(&mut self, stmts: &[Stmt]) -> Result<(), DemandCheckError> {
        for stmt in stmts {
            let Stmt::Let {
                pattern: Pattern::Bind { name, .. },
                value,
            } = stmt
            else {
                continue;
            };
            if !expr_returns_function(value) {
                continue;
            }
            let local = core_ir::Path::from_name(name.clone());
            let Some(expected) = self
                .locals
                .get(&local)
                .cloned()
                .map(|signature| self.apply_current_signature(&signature))
            else {
                continue;
            };
            if signature_is_uninformative(&expected) {
                continue;
            }
            self.check_expr(value, &expected)?;
            let refined = self.apply_current_signature(&expected);
            self.locals.insert(local.clone(), refined.clone());
            self.local_signatures.push((local, refined));
        }
        Ok(())
    }

    fn synth_handle(
        &mut self,
        expr: &Expr,
        body: &Expr,
        arms: &[HandleArm],
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        let body_ty = self.synth_expr(body, None)?;
        let result_ty = expected
            .cloned()
            .unwrap_or_else(|| self.signature_from_type(&expr.ty));
        let arm_result_ty = signature_value(&result_ty);
        for arm in arms {
            self.check_handle_arm(arm, &body_ty, &arm_result_ty)?;
        }
        Ok(result_ty)
    }

    fn check_handle_arm(
        &mut self,
        arm: &HandleArm,
        handled_body_ty: &DemandSignature,
        expected: &DemandSignature,
    ) -> Result<(), DemandCheckError> {
        let mut inserted = Vec::new();
        let payload_hint = if arm.effect == core_ir::Path::default() {
            Some(signature_value(handled_body_ty))
        } else {
            self.effect_arm_payload_hint(&arm.effect, handled_body_ty)
        };
        self.push_pattern_bindings(&arm.payload, payload_hint.as_ref(), &mut inserted);
        if let Some(resume) = &arm.resume {
            let local = core_ir::Path::from_name(resume.name.clone());
            let ty = self.resume_signature_from_context(&resume.ty, handled_body_ty);
            let previous = self.locals.insert(local.clone(), ty.clone());
            inserted.push(LocalBinding {
                local,
                previous,
                signature: ty,
            });
        }
        if let Some(guard) = &arm.guard {
            self.check_expr(guard, &DemandSignature::Core(named_core("bool")))?;
        }
        self.check_expr(&arm.body, expected)?;
        for binding in inserted.into_iter().rev() {
            restore_local(&mut self.locals, binding.local, binding.previous);
        }
        Ok(())
    }

    fn synth_bind_here(
        &mut self,
        expr: &Expr,
        inner: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        if let Some(expected) = expected {
            let effect = self.bind_here_effect(inner);
            let thunk = DemandSignature::Thunk {
                effect,
                value: Box::new(expected.clone()),
            };
            let actual = self.synth_expr(inner, Some(&thunk))?;
            if !matches!(actual, DemandSignature::Thunk { .. }) {
                self.unify_signature(expected, &actual)?;
                return Ok(expected.clone());
            }
            self.unify_signature(&thunk, &actual)?;
            return Ok(expected.clone());
        }
        let effect = self.observed_bind_here_effect(inner);
        if !demand_effect_is_empty(&effect) {
            let value = self.signature_from_type(&expr.ty);
            let thunk = DemandSignature::Thunk {
                effect,
                value: Box::new(value.clone()),
            };
            let actual = self.synth_expr(inner, Some(&thunk))?;
            if matches!(actual, DemandSignature::Thunk { .. }) {
                self.unify_signature(&thunk, &actual)?;
            } else {
                self.unify_signature(&value, &actual)?;
            }
            return Ok(value);
        }
        match self.synth_expr(inner, None)? {
            DemandSignature::Thunk { value, .. } => Ok(*value),
            actual => Ok(actual),
        }
    }

    fn bind_here_effect(&mut self, inner: &Expr) -> DemandEffect {
        let effect = self.observed_bind_here_effect(inner);
        if !demand_effect_is_empty(&effect) {
            return effect;
        }
        DemandEffect::Hole(self.fresh_hole())
    }

    fn observed_bind_here_effect(&self, inner: &Expr) -> DemandEffect {
        let annotated =
            thunk_effect_signature(&inner.ty).filter(|effect| !demand_effect_is_empty(effect));
        let enclosing = self
            .enclosing_thunk_effects
            .last()
            .cloned()
            .filter(|effect| !demand_effect_is_empty(effect));
        match (annotated, enclosing) {
            (Some(annotated), Some(enclosing)) => merge_demand_effects(annotated, enclosing),
            (Some(effect), None) | (None, Some(effect)) => effect,
            (None, None) => DemandEffect::Empty,
        }
    }

    fn synth_coerce(
        &mut self,
        expr: &Expr,
        from: &core_ir::Type,
        inner: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        let inner_expected = self.signature_from_type(&RuntimeType::core(from.clone()));
        self.check_expr(inner, &inner_expected)?;
        Ok(expected
            .cloned()
            .unwrap_or_else(|| self.signature_from_type(&expr.ty)))
    }

    fn synth_thunk(
        &mut self,
        expr: &Expr,
        effect: &core_ir::Type,
        value: &RuntimeType,
        inner: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        let actual_effect = self.effect_from_core_type(effect);
        if let Some(expected) = expected
            && !matches!(expected, DemandSignature::Thunk { .. })
            && demand_effect_is_consumed(&actual_effect, self.consumed_effects)
        {
            self.enclosing_thunk_effects.push(actual_effect.clone());
            let result = self.check_expr(inner, expected);
            self.enclosing_thunk_effects.pop();
            result?;
            return Ok(DemandSignature::Thunk {
                effect: actual_effect,
                value: Box::new(expected.clone()),
            });
        }
        let expected = expected.cloned().unwrap_or_else(|| DemandSignature::Thunk {
            effect: actual_effect,
            value: Box::new(self.signature_from_type(value)),
        });
        let DemandSignature::Thunk {
            effect,
            value: expected_value,
        } = &expected
        else {
            return Ok(self.signature_from_type(&expr.ty));
        };
        self.enclosing_thunk_effects.push(effect.clone());
        let result = self.check_expr(inner, expected_value);
        self.enclosing_thunk_effects.pop();
        result?;
        Ok(expected)
    }

    fn synth_stmt(&mut self, stmt: &Stmt) -> Result<Vec<LocalBinding>, DemandCheckError> {
        match stmt {
            Stmt::Let {
                pattern: Pattern::Bind { name, ty },
                value,
            } => {
                let local = core_ir::Path::from_name(name.clone());
                let placeholder = self.signature_from_type(ty);
                let previous = self.locals.insert(local.clone(), placeholder.clone());
                let value = self.synth_expr(value, Some(&placeholder))?;
                self.unifier.unify(&placeholder, &value)?;
                self.local_signatures
                    .push((local.clone(), placeholder.clone()));
                Ok(vec![LocalBinding {
                    local,
                    previous,
                    signature: placeholder,
                }])
            }
            Stmt::Let { pattern, value } => {
                let value = self.synth_expr(value, None)?;
                let mut inserted = Vec::new();
                self.push_pattern_bindings(pattern, Some(&signature_value(&value)), &mut inserted);
                for binding in &inserted {
                    self.local_signatures
                        .push((binding.local.clone(), binding.signature.clone()));
                }
                Ok(inserted)
            }
            Stmt::Expr(expr) => {
                if let Some(expected) = self.discarded_stmt_expected(expr) {
                    self.check_expr(expr, &expected)?;
                } else {
                    self.synth_expr(expr, None)?;
                }
                Ok(Vec::new())
            }
            Stmt::Module { def, body } => {
                let local = def.clone();
                let placeholder = self.signature_from_type(&body.ty);
                let previous = self.locals.insert(local.clone(), placeholder);
                let body = self.synth_expr(body, None)?;
                self.locals.insert(local.clone(), body);
                let signature = self
                    .locals
                    .get(&local)
                    .cloned()
                    .unwrap_or_else(|| DemandSignature::Core(DemandCoreType::Any));
                self.local_signatures
                    .push((local.clone(), signature.clone()));
                Ok(vec![LocalBinding {
                    local,
                    previous,
                    signature,
                }])
            }
        }
    }

    fn has_precise_local_callee_signature(
        &self,
        callee: &Expr,
        signature: &DemandSignature,
    ) -> bool {
        let ExprKind::Var(path) = &transparent_call_head(callee).kind else {
            return false;
        };
        self.locals.contains_key(path) && !signature_is_uninformative(signature)
    }

    fn finish(
        self,
        current_expected: &DemandSignature,
    ) -> (
        DemandSubstitution,
        DemandQueue,
        HashMap<core_ir::Path, DemandSignature>,
    ) {
        let substitutions = self.unifier.finish();
        let mut child_demands = DemandQueue::default();
        for child in self.child_demands {
            let mut signature = substitutions.apply_signature(&child.signature);
            if child.target == *self.current_target && !signature.is_closed() {
                signature = if current_expected.is_closed() {
                    current_expected.clone()
                } else {
                    merge_signature_hint(signature, current_expected.clone())
                };
            }
            child_demands.push_signature(child.target, child.expected, signature);
        }
        let local_signatures = self
            .local_signatures
            .into_iter()
            .map(|(local, signature)| (local, substitutions.apply_signature(&signature)))
            .collect();
        (substitutions, child_demands, local_signatures)
    }

    fn discarded_stmt_expected(&mut self, expr: &Expr) -> Option<DemandSignature> {
        let RuntimeType::Thunk { effect, value } = &expr.ty else {
            return None;
        };
        let effect = self.effect_from_core_type(effect);
        let effect = if demand_effect_is_empty(&effect) {
            self.enclosing_thunk_effects.last()?.clone()
        } else {
            effect
        };
        if demand_effect_is_empty(&effect) {
            return None;
        }
        let value = self.signature_from_type(value);
        Some(DemandSignature::Thunk {
            effect,
            value: Box::new(value),
        })
    }

    fn signature_from_type(&mut self, ty: &RuntimeType) -> DemandSignature {
        DemandSignature::from_runtime_type_with_holes(ty, &mut self.next_hole)
    }

    fn effect_from_core_type(&mut self, ty: &core_ir::Type) -> DemandEffect {
        DemandEffect::from_core_type_with_holes(ty, &mut self.next_hole)
    }

    fn preserve_lambda_param_runtime_shape(
        &mut self,
        lambda_ty: &RuntimeType,
        expected_param: DemandSignature,
    ) -> DemandSignature {
        let RuntimeType::Fun { param, .. } = lambda_ty else {
            return expected_param;
        };
        self.preserve_param_runtime_shape(param, expected_param)
    }

    fn preserve_param_runtime_shape(
        &mut self,
        source: &RuntimeType,
        expected: DemandSignature,
    ) -> DemandSignature {
        if matches!(expected, DemandSignature::Thunk { .. }) {
            return expected;
        }
        let RuntimeType::Thunk { effect, value } = source else {
            return expected;
        };
        let source_effect = self.effect_from_core_type(&effect);
        if demand_effect_is_empty(&source_effect) && !signature_is_uninformative(&expected) {
            return expected;
        }
        let source_value = self.signature_from_type(&value);
        let value = if DemandUnifier::new()
            .unify_signature(&source_value, &expected)
            .is_ok()
        {
            expected
        } else {
            source_value
        };
        DemandSignature::Thunk {
            effect: source_effect,
            value: Box::new(value),
        }
    }

    fn apply_current_signature(&self, signature: &DemandSignature) -> DemandSignature {
        self.unifier.clone().finish().apply_signature(signature)
    }

    fn constrain_call_return(
        &mut self,
        expected: &DemandSignature,
        actual: &DemandSignature,
    ) -> Result<(), DemandCheckError> {
        self.unify_call_return(expected, actual)
    }

    fn unify_call_return(
        &mut self,
        expected: &DemandSignature,
        actual: &DemandSignature,
    ) -> Result<(), DemandCheckError> {
        if let DemandSignature::Thunk { value, .. } = expected
            && !matches!(actual, DemandSignature::Thunk { .. })
        {
            self.unify_pure_actual_with_thunk_value(value, actual)?;
            return Ok(());
        }
        if !matches!(expected, DemandSignature::Thunk { .. })
            && let Some(value) = self.consumed_thunk_value(actual)
        {
            self.unify_signature(expected, value)?;
            return Ok(());
        }
        if !matches!(expected, DemandSignature::Thunk { .. })
            && self.accept_enclosed_thunk_value(expected, actual)
        {
            return Ok(());
        }
        if !matches!(expected, DemandSignature::Thunk { .. })
            && matches!(
                actual,
                DemandSignature::Thunk {
                    effect: DemandEffect::Hole(_),
                    ..
                }
            )
        {
            let expected_thunk = DemandSignature::Thunk {
                effect: DemandEffect::Empty,
                value: Box::new(expected.clone()),
            };
            self.unify_signature(&expected_thunk, actual)?;
            return Ok(());
        }
        match (expected, actual) {
            (
                DemandSignature::Fun {
                    param: expected_param,
                    ret: expected_ret,
                },
                DemandSignature::Fun {
                    param: actual_param,
                    ret: actual_ret,
                },
            ) => {
                self.unify_signature(expected_param, actual_param)?;
                self.unify_call_return(expected_ret, actual_ret)?;
                Ok(())
            }
            (
                DemandSignature::Core(DemandCoreType::Fun {
                    param: expected_param,
                    param_effect: expected_param_effect,
                    ret_effect: expected_ret_effect,
                    ret: expected_ret,
                }),
                DemandSignature::Fun {
                    param: actual_param,
                    ret: actual_ret,
                },
            ) => {
                let expected_param = effected_core_signature(
                    *expected_param.clone(),
                    *expected_param_effect.clone(),
                );
                let expected_ret =
                    effected_core_signature(*expected_ret.clone(), *expected_ret_effect.clone());
                self.unify_signature(&expected_param, actual_param)?;
                self.unify_call_return(&expected_ret, actual_ret)?;
                Ok(())
            }
            (
                DemandSignature::Fun {
                    param: expected_param,
                    ret: expected_ret,
                },
                DemandSignature::Core(DemandCoreType::Fun {
                    param: actual_param,
                    param_effect: actual_param_effect,
                    ret_effect: actual_ret_effect,
                    ret: actual_ret,
                }),
            ) => {
                let actual_param =
                    effected_core_signature(*actual_param.clone(), *actual_param_effect.clone());
                let actual_ret =
                    effected_core_signature(*actual_ret.clone(), *actual_ret_effect.clone());
                self.unify_signature(expected_param, &actual_param)?;
                self.unify_call_return(expected_ret, &actual_ret)?;
                Ok(())
            }
            (
                DemandSignature::Core(DemandCoreType::Fun {
                    param: expected_param,
                    param_effect: expected_param_effect,
                    ret_effect: expected_ret_effect,
                    ret: expected_ret,
                }),
                DemandSignature::Core(DemandCoreType::Fun {
                    param: actual_param,
                    param_effect: actual_param_effect,
                    ret_effect: actual_ret_effect,
                    ret: actual_ret,
                }),
            ) => {
                let expected_param = effected_core_signature(
                    *expected_param.clone(),
                    *expected_param_effect.clone(),
                );
                let actual_param =
                    effected_core_signature(*actual_param.clone(), *actual_param_effect.clone());
                let expected_ret =
                    effected_core_signature(*expected_ret.clone(), *expected_ret_effect.clone());
                let actual_ret =
                    effected_core_signature(*actual_ret.clone(), *actual_ret_effect.clone());
                self.unify_signature(&expected_param, &actual_param)?;
                self.unify_call_return(&expected_ret, &actual_ret)?;
                Ok(())
            }
            _ => {
                self.unify_signature(expected, actual)?;
                Ok(())
            }
        }
    }

    fn unify_pure_actual_with_thunk_value(
        &mut self,
        expected_value: &DemandSignature,
        actual: &DemandSignature,
    ) -> Result<(), DemandCheckError> {
        match (expected_value, actual) {
            (
                DemandSignature::Fun {
                    param: expected_param,
                    ret: expected_ret,
                },
                DemandSignature::Fun {
                    param: actual_param,
                    ret: actual_ret,
                },
            ) => {
                self.unify_signature(expected_param, actual_param)?;
                self.unify_call_return(expected_ret, actual_ret)
            }
            (
                DemandSignature::Core(DemandCoreType::Fun {
                    param: expected_param,
                    param_effect: expected_param_effect,
                    ret_effect: expected_ret_effect,
                    ret: expected_ret,
                }),
                DemandSignature::Fun {
                    param: actual_param,
                    ret: actual_ret,
                },
            ) => {
                let expected_param = effected_core_signature(
                    *expected_param.clone(),
                    *expected_param_effect.clone(),
                );
                let expected_ret =
                    effected_core_signature(*expected_ret.clone(), *expected_ret_effect.clone());
                self.unify_signature(&expected_param, actual_param)?;
                self.unify_call_return(&expected_ret, actual_ret)
            }
            (
                DemandSignature::Fun {
                    param: expected_param,
                    ret: expected_ret,
                },
                DemandSignature::Core(DemandCoreType::Fun {
                    param: actual_param,
                    param_effect: actual_param_effect,
                    ret_effect: actual_ret_effect,
                    ret: actual_ret,
                }),
            ) => {
                let actual_param =
                    effected_core_signature(*actual_param.clone(), *actual_param_effect.clone());
                let actual_ret =
                    effected_core_signature(*actual_ret.clone(), *actual_ret_effect.clone());
                self.unify_signature(expected_param, &actual_param)?;
                self.unify_call_return(expected_ret, &actual_ret)
            }
            (
                DemandSignature::Core(DemandCoreType::Fun {
                    param: expected_param,
                    param_effect: expected_param_effect,
                    ret_effect: expected_ret_effect,
                    ret: expected_ret,
                }),
                DemandSignature::Core(DemandCoreType::Fun {
                    param: actual_param,
                    param_effect: actual_param_effect,
                    ret_effect: actual_ret_effect,
                    ret: actual_ret,
                }),
            ) => {
                let expected_param = effected_core_signature(
                    *expected_param.clone(),
                    *expected_param_effect.clone(),
                );
                let actual_param =
                    effected_core_signature(*actual_param.clone(), *actual_param_effect.clone());
                let expected_ret =
                    effected_core_signature(*expected_ret.clone(), *expected_ret_effect.clone());
                let actual_ret =
                    effected_core_signature(*actual_ret.clone(), *actual_ret_effect.clone());
                self.unify_signature(&expected_param, &actual_param)?;
                self.unify_call_return(&expected_ret, &actual_ret)
            }
            _ => self.unify_signature(expected_value, actual),
        }
    }

    fn curried_param_signatures_from_type(
        &mut self,
        ty: &RuntimeType,
        arity: usize,
    ) -> Vec<Option<DemandSignature>> {
        let mut out = Vec::with_capacity(arity);
        let mut current = self.signature_from_type(ty);
        for _ in 0..arity {
            match current {
                DemandSignature::Fun { param, ret } => {
                    out.push(Some(*param));
                    current = *ret;
                }
                DemandSignature::Core(DemandCoreType::Fun {
                    param,
                    param_effect,
                    ret_effect,
                    ret,
                }) => {
                    out.push(Some(effected_core_signature(*param, *param_effect)));
                    current = effected_core_signature(*ret, *ret_effect);
                }
                _ => out.push(None),
            }
        }
        out
    }

    fn closed_call_signature(
        &mut self,
        target: &core_ir::Path,
        head: &Expr,
        args: &[&Expr],
        ret: DemandSignature,
        seed_param_hints: Option<Vec<Option<DemandSignature>>>,
    ) -> (Vec<Option<DemandSignature>>, DemandSignature) {
        let param_hints = seed_param_hints
            .filter(|hints| hints.len() == args.len())
            .unwrap_or_else(|| self.curried_param_signatures_from_type(&head.ty, args.len()));
        let provisional_args = param_hints
            .iter()
            .zip(args)
            .map(|(hint, arg)| match hint {
                Some(hint) if !signature_is_uninformative(hint) => hint.clone(),
                _ => self.local_or_runtime_signature(arg),
            })
            .collect::<Vec<_>>();
        let ret =
            self.lift_higher_order_call_return_to_enclosing_effect(target, &provisional_args, ret);
        let closed = close_known_associated_type_signature(
            target,
            curried_signatures(&provisional_args, ret.clone()),
        );
        let closed = close_default_effect_holes(closed);
        let closed = close_known_associated_type_signature(target, closed);
        let (closed_args, closed_ret) = uncurried_checker_signatures(closed);
        debug_closed_call_param_hints(target, args.len(), &closed_args, &closed_ret);
        if closed_args.len() == args.len() {
            return (closed_args.into_iter().map(Some).collect(), closed_ret);
        }
        (param_hints, ret)
    }

    fn local_or_runtime_signature(&mut self, expr: &Expr) -> DemandSignature {
        if let Some(signature) = self.primitive_application_signature(expr) {
            return signature;
        }
        if let ExprKind::Var(path) = &transparent_call_head(expr).kind
            && let Some(signature) = self.locals.get(path)
        {
            return self.apply_current_signature(signature);
        }
        self.signature_from_type(&expr.ty)
    }

    fn primitive_application_signature(&mut self, expr: &Expr) -> Option<DemandSignature> {
        let (op, args) = applied_primitive_with_args(expr)?;
        match (op, args.as_slice()) {
            (core_ir::PrimitiveOp::ListSingleton, [item]) => {
                let item = signature_core_value(&self.local_or_runtime_signature(item));
                Some(DemandSignature::Core(list_demand_core(item)))
            }
            (core_ir::PrimitiveOp::ListMerge, [left, right]) => {
                let left = self.local_or_runtime_signature(left);
                let right = self.local_or_runtime_signature(right);
                let item = prefer_informative_list_item(&left, &right)?;
                Some(DemandSignature::Core(list_demand_core(item)))
            }
            _ => None,
        }
    }

    fn lift_higher_order_call_return_to_enclosing_effect(
        &self,
        target: &core_ir::Path,
        args: &[DemandSignature],
        ret: DemandSignature,
    ) -> DemandSignature {
        if matches!(ret, DemandSignature::Thunk { .. })
            || !is_effect_polymorphic_higher_order_target(target)
            || !args.iter().any(signature_has_effectful_result)
        {
            return ret;
        }
        let Some(effect) = self.enclosing_thunk_effects.last().cloned() else {
            return ret;
        };
        if demand_effect_is_empty(&effect) {
            return ret;
        }
        DemandSignature::Thunk {
            effect,
            value: Box::new(ret),
        }
    }

    fn generic_arg_signature(
        &mut self,
        arg: &Expr,
        hint: Option<DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        let Some(hint) = hint else {
            return self.synth_expr(arg, None);
        };
        let checkpoint = ExprCheckerCheckpoint {
            enclosing_thunk_effects: self.enclosing_thunk_effects.clone(),
            locals: self.locals.clone(),
            next_hole: self.next_hole,
            unifier: self.unifier.clone(),
            child_demands: self.child_demands.clone(),
            local_signatures: self.local_signatures.clone(),
        };
        let hint_is_open = !hint.is_closed();
        if hint_is_open {
            match self.check_expr(arg, &hint) {
                Ok(actual) => {
                    let merged = merge_signature_hint(actual, hint);
                    return Ok(self.apply_current_signature(&merged));
                }
                Err(_) => self.restore_checkpoint(checkpoint.clone()),
            }
            let actual = self.synth_expr(arg, None)?;
            let _ = self.unify_signature(&hint, &actual);
            let merged = merge_signature_hint(actual, hint);
            return Ok(self.apply_current_signature(&merged));
        }
        match self.check_expr(arg, &hint) {
            Ok(_) => Ok(hint),
            Err(error) if should_fallback_generic_arg_hint(&error) => {
                self.restore_checkpoint(checkpoint);
                self.synth_expr(arg, None)
            }
            Err(error) => Err(error),
        }
    }

    fn restore_checkpoint(&mut self, checkpoint: ExprCheckerCheckpoint) {
        self.enclosing_thunk_effects = checkpoint.enclosing_thunk_effects;
        self.locals = checkpoint.locals;
        self.next_hole = checkpoint.next_hole;
        self.unifier = checkpoint.unifier;
        self.child_demands = checkpoint.child_demands;
        self.local_signatures = checkpoint.local_signatures;
    }

    fn resume_signature_from_context(
        &mut self,
        ty: &RuntimeType,
        handled_body_ty: &DemandSignature,
    ) -> DemandSignature {
        match ty {
            RuntimeType::Fun { param, .. } => DemandSignature::Fun {
                param: Box::new(self.signature_from_type(param)),
                ret: Box::new(handled_body_ty.clone()),
            },
            RuntimeType::Core(core_ir::Type::Fun {
                param,
                param_effect,
                ..
            }) => {
                let param_signature = self.signature_from_type(&RuntimeType::core(*param.clone()));
                let param_effect = self.effect_from_core_type(param_effect);
                DemandSignature::Fun {
                    param: Box::new(effected_core_signature(
                        signature_core_value(&param_signature),
                        param_effect,
                    )),
                    ret: Box::new(handled_body_ty.clone()),
                }
            }
            _ => self.signature_from_type(ty),
        }
    }

    fn effect_arm_payload_hint(
        &self,
        operation: &core_ir::Path,
        handled_body_ty: &DemandSignature,
    ) -> Option<DemandSignature> {
        let effect = thunk_signature_effect(handled_body_ty)?;
        effect_operation_namespace(operation)
            .and_then(|namespace| effect_payload_for_namespace(effect, &namespace))
            .or_else(|| effect_payload_for_namespace(effect, operation))
            .or_else(|| relative_operation_payload_hint(effect, operation))
    }

    fn fresh_hole(&mut self) -> u32 {
        let id = self.next_hole;
        self.next_hole += 1;
        id
    }

    fn push_pattern_bindings(
        &mut self,
        pattern: &Pattern,
        expected: Option<&DemandSignature>,
        inserted: &mut Vec<LocalBinding>,
    ) {
        match pattern {
            Pattern::Bind { name, ty } => {
                let local = core_ir::Path::from_name(name.clone());
                let signature = expected
                    .cloned()
                    .unwrap_or_else(|| self.signature_from_type(ty));
                let previous = self.locals.insert(local.clone(), signature);
                let signature = self
                    .locals
                    .get(&local)
                    .cloned()
                    .unwrap_or_else(|| DemandSignature::Core(DemandCoreType::Any));
                inserted.push(LocalBinding {
                    local,
                    previous,
                    signature,
                });
            }
            Pattern::Tuple { items, .. } => {
                let expected_items = match expected {
                    Some(DemandSignature::Core(DemandCoreType::Tuple(items))) => {
                        Some(items.as_slice())
                    }
                    _ => None,
                };
                for (index, item) in items.iter().enumerate() {
                    let expected_item = expected_items
                        .and_then(|items| items.get(index))
                        .map(|item| DemandSignature::Core(item.clone()));
                    self.push_pattern_bindings(item, expected_item.as_ref(), inserted);
                }
            }
            Pattern::Record { fields, .. } => {
                for field in fields {
                    let expected_field = expected.and_then(|expected| match expected {
                        DemandSignature::Core(DemandCoreType::Record(fields)) => fields
                            .iter()
                            .find(|expected| expected.name == field.name)
                            .map(|field| DemandSignature::Core(field.value.clone())),
                        _ => None,
                    });
                    self.push_pattern_bindings(&field.pattern, expected_field.as_ref(), inserted);
                }
            }
            Pattern::Variant { tag, value, .. } => {
                let expected_payload = expected
                    .and_then(|expected| variant_expected_payload(expected, tag))
                    .or_else(|| {
                        value.as_deref().and_then(|value| {
                            let ty = pattern_runtime_type(value);
                            (!runtime_type_is_any(ty)).then(|| self.signature_from_type(ty))
                        })
                    });
                if let Some(value) = value {
                    self.push_pattern_bindings(value, expected_payload.as_ref(), inserted);
                }
            }
            Pattern::As { pattern, name, ty } => {
                self.push_pattern_bindings(pattern, expected, inserted);
                let local = core_ir::Path::from_name(name.clone());
                let signature = expected
                    .cloned()
                    .unwrap_or_else(|| self.signature_from_type(ty));
                let previous = self.locals.insert(local.clone(), signature);
                let signature = self
                    .locals
                    .get(&local)
                    .cloned()
                    .unwrap_or_else(|| DemandSignature::Core(DemandCoreType::Any));
                inserted.push(LocalBinding {
                    local,
                    previous,
                    signature,
                });
            }
            Pattern::Or { left, right, .. } => {
                self.push_pattern_bindings(left, expected, inserted);
                self.push_pattern_bindings(right, expected, inserted);
            }
            Pattern::List {
                prefix,
                spread,
                suffix,
                ..
            } => {
                for item in prefix {
                    self.push_pattern_bindings(item, None, inserted);
                }
                if let Some(spread) = spread {
                    self.push_pattern_bindings(spread, None, inserted);
                }
                for item in suffix {
                    self.push_pattern_bindings(item, None, inserted);
                }
            }
            Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
        }
    }
}

fn applied_call_with_head(expr: &Expr) -> Option<(&core_ir::Path, &Expr, Vec<&Expr>)> {
    let mut head = expr;
    let mut args = Vec::new();
    loop {
        head = transparent_call_head(head);
        match &head.kind {
            ExprKind::Apply {
                callee: next, arg, ..
            } => {
                args.push(arg.as_ref());
                head = next;
            }
            ExprKind::Var(target) => {
                args.reverse();
                return Some((target, head, args));
            }
            _ => return None,
        }
    }
}

fn applied_call_param_evidence_signatures(expr: &Expr) -> Vec<Option<DemandSignature>> {
    let mut head = expr;
    let mut hints = Vec::new();
    loop {
        head = transparent_call_head(head);
        let ExprKind::Apply {
            callee, evidence, ..
        } = &head.kind
        else {
            break;
        };
        hints.push(evidence.as_ref().and_then(apply_evidence_param_signature));
        head = callee;
    }
    hints.reverse();
    hints
}

fn applied_call_principal_signature_hints(
    expr: &Expr,
    arity: usize,
) -> Option<(Vec<Option<DemandSignature>>, DemandSignature)> {
    let mut head = expr;
    let mut principal = None;
    loop {
        head = transparent_call_head(head);
        let ExprKind::Apply {
            callee, evidence, ..
        } = &head.kind
        else {
            break;
        };
        if let Some(signature) = evidence
            .as_ref()
            .and_then(apply_evidence_substituted_callee_signature)
        {
            principal = Some(signature);
        }
        head = callee;
    }

    let (params, ret) = uncurried_checker_signatures(principal?);
    if params.len() < arity {
        return None;
    }
    let ret = if params.len() == arity {
        ret
    } else {
        curried_signatures(&params[arity..], ret)
    };
    let params = params.into_iter().take(arity).map(Some).collect::<Vec<_>>();
    Some((params, ret))
}

fn applied_primitive_with_args(expr: &Expr) -> Option<(core_ir::PrimitiveOp, Vec<&Expr>)> {
    let mut callee = expr;
    let mut args = Vec::new();
    loop {
        callee = transparent_call_head(callee);
        match &callee.kind {
            ExprKind::Apply {
                callee: next, arg, ..
            } => {
                args.push(arg.as_ref());
                callee = next;
            }
            ExprKind::PrimitiveOp(op) => {
                args.reverse();
                return Some((*op, args));
            }
            _ => return None,
        }
    }
}

fn transparent_call_head(mut expr: &Expr) -> &Expr {
    loop {
        match &expr.kind {
            ExprKind::BindHere { expr: inner }
            | ExprKind::Coerce { expr: inner, .. }
            | ExprKind::Pack { expr: inner, .. } => expr = inner,
            _ => return expr,
        }
    }
}

fn list_demand_core(item: DemandCoreType) -> DemandCoreType {
    DemandCoreType::Named {
        path: path_segments(&["std", "list", "list"]),
        args: vec![DemandTypeArg::Type(item)],
    }
}

fn prefer_informative_list_item(
    left: &DemandSignature,
    right: &DemandSignature,
) -> Option<DemandCoreType> {
    let left = list_item_signature(left);
    let right = list_item_signature(right);
    [left.clone(), right.clone()]
        .into_iter()
        .flatten()
        .find(|item| item.is_closed())
        .or_else(|| {
            [left, right]
                .into_iter()
                .flatten()
                .find(|item| !core_signature_is_uninformative(item))
        })
}

fn merge_optional_signature_hints(
    primary: Option<DemandSignature>,
    evidence: Option<DemandSignature>,
) -> Option<DemandSignature> {
    match (primary, evidence) {
        (Some(primary), Some(evidence)) => Some(merge_signature_hint(primary, evidence)),
        (Some(primary), None) => Some(primary),
        (None, Some(evidence)) => Some(evidence),
        (None, None) => None,
    }
}

fn uncurried_checker_signatures(
    signature: DemandSignature,
) -> (Vec<DemandSignature>, DemandSignature) {
    let mut args = Vec::new();
    let mut current = signature;
    loop {
        match current {
            DemandSignature::Fun { param, ret } => {
                args.push(*param);
                current = *ret;
            }
            DemandSignature::Core(DemandCoreType::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            }) => {
                args.push(effected_core_signature(*param, *param_effect));
                current = effected_core_signature(*ret, *ret_effect);
            }
            ret => return (args, ret),
        }
    }
}

fn should_fallback_generic_arg_hint(error: &DemandCheckError) -> bool {
    match error {
        DemandCheckError::Unify(DemandUnifyError::EffectMismatch { .. }) => true,
        DemandCheckError::Unify(DemandUnifyError::SignatureMismatch { expected, actual }) => {
            value_hint_met_thunk_runtime_shape(expected, actual)
        }
        _ => false,
    }
}

fn value_hint_met_thunk_runtime_shape(
    expected: &DemandSignature,
    actual: &DemandSignature,
) -> bool {
    match (expected, actual) {
        (DemandSignature::Thunk { .. }, _) => false,
        (_, DemandSignature::Thunk { value, .. }) => matches!(
            value.as_ref(),
            DemandSignature::Fun { .. } | DemandSignature::Core(DemandCoreType::Fun { .. })
        ),
        (
            DemandSignature::Fun {
                param: expected_param,
                ret: expected_ret,
            },
            DemandSignature::Fun {
                param: actual_param,
                ret: actual_ret,
            },
        ) => {
            value_hint_met_thunk_runtime_shape(expected_param, actual_param)
                || value_hint_met_thunk_runtime_shape(expected_ret, actual_ret)
        }
        _ => false,
    }
}

fn thunk_effect_signature(ty: &RuntimeType) -> Option<DemandEffect> {
    match ty {
        RuntimeType::Thunk { effect, .. } => Some(DemandEffect::from_core_type(effect)),
        _ => None,
    }
}

fn expr_or_evidence_has_effectful_result(
    expr: &Expr,
    evidence: Option<&core_ir::ApplyEvidence>,
) -> bool {
    thunk_effect_signature(&expr.ty)
        .as_ref()
        .is_some_and(|effect| !demand_effect_is_empty(effect))
        || evidence
            .and_then(apply_evidence_signature)
            .is_some_and(|signature| signature_has_effectful_result(&signature))
}

fn signature_has_effectful_result(signature: &DemandSignature) -> bool {
    match signature {
        DemandSignature::Thunk { effect, .. } => !demand_effect_is_empty(effect),
        DemandSignature::Fun { ret, .. } => signature_has_effectful_result(ret),
        DemandSignature::Core(DemandCoreType::Fun { ret_effect, .. }) => {
            !demand_effect_is_empty(ret_effect)
        }
        _ => false,
    }
}

fn is_effect_polymorphic_higher_order_target(target: &core_ir::Path) -> bool {
    target
        .segments
        .last()
        .is_some_and(|name| name.0 == "fold" || name.0 == "fold_impl" || name.0 == "for_in")
}

fn demand_effect_is_empty(effect: &DemandEffect) -> bool {
    match effect {
        DemandEffect::Empty => true,
        DemandEffect::Row(items) => items.iter().all(demand_effect_is_empty),
        DemandEffect::Hole(_) | DemandEffect::Atom(_) => false,
    }
}

fn signature_is_uninformative(signature: &DemandSignature) -> bool {
    match signature {
        DemandSignature::Ignored | DemandSignature::Hole(_) => true,
        DemandSignature::Core(ty) => core_signature_is_uninformative(ty),
        DemandSignature::Thunk { value, .. } => signature_is_uninformative(value),
        DemandSignature::Fun { .. } => false,
    }
}

fn core_signature_is_uninformative(ty: &DemandCoreType) -> bool {
    match ty {
        DemandCoreType::Any | DemandCoreType::Hole(_) => true,
        DemandCoreType::Named { args, .. } => args.iter().all(type_arg_is_uninformative),
        DemandCoreType::Tuple(items) => items.iter().all(core_signature_is_uninformative),
        DemandCoreType::Record(fields) => fields
            .iter()
            .all(|field| core_signature_is_uninformative(&field.value)),
        DemandCoreType::Variant(cases) => cases
            .iter()
            .all(|case| case.payloads.iter().all(core_signature_is_uninformative)),
        DemandCoreType::RowAsValue(items) => items.iter().all(demand_effect_is_empty),
        DemandCoreType::Union(items) | DemandCoreType::Inter(items) => {
            items.iter().all(core_signature_is_uninformative)
        }
        DemandCoreType::Recursive { body, .. } => core_signature_is_uninformative(body),
        DemandCoreType::Never | DemandCoreType::Fun { .. } => false,
    }
}

fn type_arg_is_uninformative(arg: &DemandTypeArg) -> bool {
    match arg {
        DemandTypeArg::Type(ty) => core_signature_is_uninformative(ty),
        DemandTypeArg::Bounds { lower, upper } => {
            lower.as_ref().is_none_or(core_signature_is_uninformative)
                && upper.as_ref().is_none_or(core_signature_is_uninformative)
        }
    }
}

fn list_item_signature(signature: &DemandSignature) -> Option<DemandCoreType> {
    let DemandSignature::Core(DemandCoreType::Named { path, args }) = signature_value(signature)
    else {
        return None;
    };
    if !path_ends_with(&path, &["std", "list", "list"]) {
        return None;
    }
    let DemandTypeArg::Type(item) = args.first()? else {
        return None;
    };
    Some(item.clone())
}

fn lambda_actual_signature(
    expected: &DemandSignature,
    param: DemandSignature,
    ret: DemandSignature,
) -> DemandSignature {
    match expected {
        DemandSignature::Core(DemandCoreType::Fun { .. }) => {
            let (param, param_effect) = signature_effected_core_value(&param);
            let (ret, ret_effect) = signature_effected_core_value(&ret);
            DemandSignature::Core(DemandCoreType::Fun {
                param: Box::new(param),
                param_effect: Box::new(param_effect),
                ret_effect: Box::new(ret_effect),
                ret: Box::new(ret),
            })
        }
        _ => DemandSignature::Fun {
            param: Box::new(param),
            ret: Box::new(ret),
        },
    }
}

fn preserve_operational_shapes(
    expected: &DemandSignature,
    actual: &DemandSignature,
) -> DemandSignature {
    match (expected, actual) {
        (
            DemandSignature::Fun {
                param: expected_param,
                ret: expected_ret,
            },
            DemandSignature::Fun {
                param: actual_param,
                ret: actual_ret,
            },
        ) => DemandSignature::Fun {
            param: Box::new(preserve_operational_shapes(expected_param, actual_param)),
            ret: Box::new(preserve_operational_shapes(expected_ret, actual_ret)),
        },
        (
            DemandSignature::Core(DemandCoreType::Fun {
                param: expected_param,
                param_effect: expected_param_effect,
                ret_effect: expected_ret_effect,
                ret: expected_ret,
            }),
            DemandSignature::Core(DemandCoreType::Fun {
                param: actual_param,
                param_effect: actual_param_effect,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
            }),
        ) => {
            let expected_param =
                effected_core_signature(*expected_param.clone(), *expected_param_effect.clone());
            let actual_param =
                effected_core_signature(*actual_param.clone(), *actual_param_effect.clone());
            let expected_ret =
                effected_core_signature(*expected_ret.clone(), *expected_ret_effect.clone());
            let actual_ret =
                effected_core_signature(*actual_ret.clone(), *actual_ret_effect.clone());
            let param = preserve_operational_shapes(&expected_param, &actual_param);
            let ret = preserve_operational_shapes(&expected_ret, &actual_ret);
            let (param, param_effect) = signature_effected_core_value(&param);
            let (ret, ret_effect) = signature_effected_core_value(&ret);
            DemandSignature::Core(DemandCoreType::Fun {
                param: Box::new(param),
                param_effect: Box::new(param_effect),
                ret_effect: Box::new(ret_effect),
                ret: Box::new(ret),
            })
        }
        (
            expected,
            DemandSignature::Thunk {
                effect: actual_effect,
                value: actual_value,
            },
        ) if !matches!(expected, DemandSignature::Thunk { .. })
            && DemandUnifier::new()
                .unify_signature(expected, actual_value)
                .is_ok() =>
        {
            DemandSignature::Thunk {
                effect: actual_effect.clone(),
                value: Box::new(preserve_operational_shapes(expected, actual_value)),
            }
        }
        _ => expected.clone(),
    }
}

fn named_core(name: &str) -> DemandCoreType {
    DemandCoreType::Named {
        path: core_ir::Path::from_name(core_ir::Name(name.to_string())),
        args: Vec::new(),
    }
}

fn single_payload_from_type_args(args: &[DemandTypeArg]) -> Option<DemandCoreType> {
    let [arg] = args else {
        return None;
    };
    match arg {
        DemandTypeArg::Type(ty) => Some(ty.clone()),
        DemandTypeArg::Bounds {
            lower: Some(ty), ..
        }
        | DemandTypeArg::Bounds {
            lower: None,
            upper: Some(ty),
        } => Some(ty.clone()),
        DemandTypeArg::Bounds {
            lower: None,
            upper: None,
        } => None,
    }
}

fn variant_expected_payload(
    expected: &DemandSignature,
    tag: &core_ir::Name,
) -> Option<DemandSignature> {
    match expected {
        DemandSignature::Core(DemandCoreType::Variant(cases)) => cases
            .iter()
            .find(|case| case.name == *tag)
            .and_then(|case| case.payloads.first())
            .map(|payload| DemandSignature::Core(payload.clone())),
        DemandSignature::Core(DemandCoreType::Named { path, args })
            if named_variant_payload_is_type_arg(path, tag) =>
        {
            single_payload_from_type_args(args).map(DemandSignature::Core)
        }
        _ => None,
    }
}

fn named_variant_payload_is_type_arg(path: &core_ir::Path, tag: &core_ir::Name) -> bool {
    tag.0 == "just" && path_ends_with(path, &["std", "opt", "opt"])
}

fn pattern_runtime_type(pattern: &Pattern) -> &RuntimeType {
    match pattern {
        Pattern::Wildcard { ty }
        | Pattern::Bind { ty, .. }
        | Pattern::Lit { ty, .. }
        | Pattern::Tuple { ty, .. }
        | Pattern::List { ty, .. }
        | Pattern::Record { ty, .. }
        | Pattern::Variant { ty, .. }
        | Pattern::Or { ty, .. }
        | Pattern::As { ty, .. } => ty,
    }
}

fn runtime_type_is_any(ty: &RuntimeType) -> bool {
    matches!(ty, RuntimeType::Core(core_ir::Type::Any))
}

fn runtime_any_type() -> RuntimeType {
    RuntimeType::core(core_ir::Type::Any)
}

fn debug_demand_arg_rejection(
    target: &core_ir::Path,
    index: usize,
    hint: Option<&DemandSignature>,
    error: &DemandCheckError,
) {
    if std::env::var_os("YULANG_DEBUG_DEMAND_CHECK").is_none() {
        return;
    }
    eprintln!("demand arg rejected for {target:?} arg {index}: hint {hint:?}: {error:?}");
}

fn debug_check_demand_error(
    target: &core_ir::Path,
    expected: &DemandSignature,
    error: &DemandCheckError,
) {
    if std::env::var_os("YULANG_DEBUG_DEMAND_CHECK").is_none() {
        return;
    }
    eprintln!("demand check failed for {target:?}: expected {expected:?}: {error:?}");
}

fn debug_unify_signature_error(
    target: &core_ir::Path,
    expected: &DemandSignature,
    actual: &DemandSignature,
    error: &DemandUnifyError,
) {
    if std::env::var_os("YULANG_DEBUG_DEMAND_CHECK").is_none() {
        return;
    }
    eprintln!(
        "unify failed while checking {target:?}: expected {expected:?}: actual {actual:?}: {error:?}"
    );
}

fn debug_checked_locals(
    target: &core_ir::Path,
    locals: &HashMap<core_ir::Path, DemandSignature>,
    child_demands: &DemandQueue,
) {
    if std::env::var_os("YULANG_DEBUG_DEMAND_CHECK").is_none() {
        return;
    }
    if !path_ends_with(target, &["std", "undet", "undet", "logic"])
        && !path_ends_with(target, &["std", "undet", "undet", "once"])
    {
        return;
    }
    eprintln!("checked locals for {target:?}: {locals:#?}");
    eprintln!("child demands for {target:?}: {child_demands:#?}");
}

fn debug_closed_call_param_hints(
    target: &core_ir::Path,
    arg_len: usize,
    closed_args: &[DemandSignature],
    closed_ret: &DemandSignature,
) {
    if std::env::var_os("YULANG_DEBUG_DEMAND_CHECK").is_none()
        || !(path_ends_with(target, &["std", "range", "fold_from"])
            || path_ends_with(target, &["std", "fold", "Fold", "fold"])
            || path_ends_with(target, &["std", "flow", "sub", "sub"]))
    {
        return;
    }
    eprintln!(
        "closed call hints for {target:?}: arg_len={arg_len}, closed_args={closed_args:?}, closed_ret={closed_ret:?}"
    );
}

fn force_thunk_callee_signature(mut signature: DemandSignature) -> DemandSignature {
    loop {
        match signature {
            DemandSignature::Thunk { value, .. } if signature_returns_function(&value) => {
                signature = *value;
            }
            signature => return signature,
        }
    }
}

fn signature_returns_function(signature: &DemandSignature) -> bool {
    match signature {
        DemandSignature::Fun { .. } => true,
        DemandSignature::Thunk { value, .. } => signature_returns_function(value),
        DemandSignature::Core(DemandCoreType::Fun { .. }) => true,
        DemandSignature::Ignored | DemandSignature::Hole(_) | DemandSignature::Core(_) => false,
    }
}

fn expr_returns_function(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Lambda { .. } => true,
        ExprKind::Thunk { expr, .. } | ExprKind::LocalPushId { body: expr, .. } => {
            expr_returns_function(expr)
        }
        ExprKind::Coerce { expr, .. } | ExprKind::Pack { expr, .. } => expr_returns_function(expr),
        _ => signature_returns_function(&DemandSignature::from_runtime_type(&expr.ty)),
    }
}

fn generic_role_impl_candidates(
    module: &Module,
) -> HashMap<core_ir::Name, Vec<RoleImplDemandCandidate>> {
    let mut out: HashMap<core_ir::Name, Vec<RoleImplDemandCandidate>> = HashMap::new();
    for binding in &module.bindings {
        if !is_impl_method_path(&binding.name) {
            continue;
        }
        let Some(method) = binding.name.segments.last() else {
            continue;
        };
        out.entry(method.clone())
            .or_default()
            .push(RoleImplDemandCandidate {
                path: binding.name.clone(),
                signature: DemandSignature::from_runtime_type(&binding.body.ty)
                    .canonicalize_holes(),
            });
    }
    for candidates in out.values_mut() {
        candidates.sort_by_key(|candidate| path_key(&candidate.path));
    }
    out
}

fn role_impl_candidate_accepts(candidate: &DemandSignature, call: &DemandSignature) -> bool {
    let (candidate_args, _) = uncurried_checker_signatures(candidate.clone());
    let (call_args, _) = uncurried_checker_signatures(call.clone());
    if candidate_args.len() < call_args.len() {
        return false;
    }
    let Some((candidate_receiver, call_receiver)) = candidate_args.first().zip(call_args.first())
    else {
        return false;
    };
    signatures_may_unify(
        &signature_value(candidate_receiver),
        &signature_value(call_receiver),
    )
}

fn role_impl_demand_signature(call: &DemandSignature) -> DemandSignature {
    let (args, ret) = uncurried_checker_signatures(call.clone());
    let args = args
        .into_iter()
        .map(|arg| signature_value(&arg))
        .collect::<Vec<_>>();
    curried_signatures(&args, ret)
}

fn normalize_check_demand_signature(
    target: &core_ir::Path,
    signature: DemandSignature,
) -> DemandSignature {
    let signature = close_known_associated_type_signature(target, signature);
    let signature = close_default_effect_holes(signature);
    close_known_associated_type_signature(target, signature)
}

fn strengthen_handler_arg_signatures(
    target: &core_ir::Path,
    mut args: Vec<DemandSignature>,
    hints: &[Option<DemandSignature>],
    ret: &DemandSignature,
) -> Vec<DemandSignature> {
    if known_handler_consumed_effects(target).is_empty() {
        return args;
    }
    let Some(first) = args.first_mut() else {
        return args;
    };
    let Some(DemandSignature::Thunk {
        effect: consumed_effect,
        value: consumed_value,
    }) = hints.first().and_then(|hint| hint.as_ref())
    else {
        return args;
    };
    let (effect, value) = match ret {
        DemandSignature::Thunk {
            effect: ret_effect,
            value: ret_value,
        } => (
            merge_demand_effects(consumed_effect.clone(), ret_effect.clone()),
            ret_value.clone(),
        ),
        _ => (consumed_effect.clone(), consumed_value.clone()),
    };
    *first = DemandSignature::Thunk { effect, value };
    args
}

fn signatures_may_unify(left: &DemandSignature, right: &DemandSignature) -> bool {
    DemandUnifier::new().unify_signature(left, right).is_ok()
        || DemandUnifier::new().unify_signature(right, left).is_ok()
}

fn path_key(path: &core_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn pure_handler_bindings(module: &Module) -> HashMap<core_ir::Path, Vec<core_ir::Path>> {
    module
        .bindings
        .iter()
        .filter_map(|binding| {
            expr_pure_handler_consumes(&binding.body)
                .map(|consumes| (binding.name.clone(), consumes))
        })
        .collect()
}

fn consumed_effects_for_target(
    pure_handlers: &HashMap<core_ir::Path, Vec<core_ir::Path>>,
    target: &core_ir::Path,
) -> Vec<core_ir::Path> {
    let mut out = pure_handlers.get(target).cloned().unwrap_or_default();
    for effect in known_handler_consumed_effects(target) {
        if !out.iter().any(|known| effect_paths_match(known, &effect)) {
            out.push(effect);
        }
    }
    out
}

fn known_handler_consumed_effects(target: &core_ir::Path) -> Vec<core_ir::Path> {
    if let Some(effect) = local_ref_run_effect_path(target) {
        return vec![effect];
    }
    if path_ends_with(target, &["std", "undet", "undet", "once"])
        || path_ends_with(target, &["std", "undet", "undet", "list"])
        || path_ends_with(target, &["std", "undet", "undet", "logic"])
    {
        return vec![path_segments(&["std", "undet", "undet"])];
    }
    if path_ends_with(target, &["std", "flow", "sub", "sub"])
        || path_ends_with(target, &["std", "sub", "sub"])
    {
        return vec![path_segments(&["std", "flow", "sub"])];
    }
    if path_ends_with(target, &["std", "fold", "Fold", "find"]) {
        return vec![path_segments(&["std", "flow", "sub"])];
    }
    if path_ends_with(target, &["std", "junction", "junction", "junction"]) {
        return vec![path_segments(&["std", "junction", "junction"])];
    }
    if path_ends_with(target, &["std", "flow", "loop", "last", "sub"]) {
        return vec![path_segments(&["std", "flow", "loop", "last"])];
    }
    if path_ends_with(target, &["std", "flow", "loop", "next", "sub"]) {
        return vec![path_segments(&["std", "flow", "loop", "next"])];
    }
    if path_ends_with(target, &["std", "flow", "loop", "redo", "judge"]) {
        return vec![path_segments(&["std", "flow", "loop", "redo"])];
    }
    if path_ends_with(target, &["std", "flow", "label_loop", "last", "sub"]) {
        return vec![path_segments(&["std", "flow", "label_loop", "last"])];
    }
    if path_ends_with(target, &["std", "flow", "label_loop", "next", "sub"]) {
        return vec![path_segments(&["std", "flow", "label_loop", "next"])];
    }
    if path_ends_with(target, &["std", "flow", "label_loop", "redo", "judge"]) {
        return vec![path_segments(&["std", "flow", "label_loop", "redo"])];
    }
    Vec::new()
}

fn local_ref_run_effect_path(target: &core_ir::Path) -> Option<core_ir::Path> {
    let [namespace, name] = target.segments.as_slice() else {
        return None;
    };
    (name.0 == "run" && namespace.0.starts_with('&')).then(|| core_ir::Path {
        segments: vec![namespace.clone()],
    })
}

fn path_ends_with(path: &core_ir::Path, suffix: &[&str]) -> bool {
    path.segments.len() >= suffix.len()
        && path
            .segments
            .iter()
            .rev()
            .zip(suffix.iter().rev())
            .all(|(segment, expected)| segment.0 == *expected)
}

fn binding_references_path(binding: &Binding, target: &core_ir::Path) -> bool {
    expr_references_path(&binding.body, target)
}

fn expr_references_path(expr: &Expr, target: &core_ir::Path) -> bool {
    match &expr.kind {
        ExprKind::Var(path) => path == target,
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => expr_references_path(body, target),
        ExprKind::Apply { callee, arg, .. } => {
            expr_references_path(callee, target) || expr_references_path(arg, target)
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            expr_references_path(cond, target)
                || expr_references_path(then_branch, target)
                || expr_references_path(else_branch, target)
        }
        ExprKind::Tuple(items) => items.iter().any(|item| expr_references_path(item, target)),
        ExprKind::Record { fields, spread } => {
            fields
                .iter()
                .any(|field| expr_references_path(&field.value, target))
                || spread.as_ref().is_some_and(|spread| match spread {
                    crate::ir::RecordSpreadExpr::Head(expr)
                    | crate::ir::RecordSpreadExpr::Tail(expr) => expr_references_path(expr, target),
                })
        }
        ExprKind::Variant { value, .. } => value
            .as_ref()
            .is_some_and(|value| expr_references_path(value, target)),
        ExprKind::Select { base, .. } => expr_references_path(base, target),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            expr_references_path(scrutinee, target)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| expr_references_path(guard, target))
                        || expr_references_path(&arm.body, target)
                })
        }
        ExprKind::Block { stmts, tail } => {
            stmts.iter().any(|stmt| stmt_references_path(stmt, target))
                || tail
                    .as_ref()
                    .is_some_and(|tail| expr_references_path(tail, target))
        }
        ExprKind::Handle { body, arms, .. } => {
            expr_references_path(body, target)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(|guard| expr_references_path(guard, target))
                        || expr_references_path(&arm.body, target)
                })
        }
        ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => false,
    }
}

fn stmt_references_path(stmt: &Stmt, target: &core_ir::Path) -> bool {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            expr_references_path(value, target)
        }
    }
}

fn path_segments(segments: &[&str]) -> core_ir::Path {
    core_ir::Path {
        segments: segments
            .iter()
            .map(|segment| core_ir::Name((*segment).to_string()))
            .collect(),
    }
}

fn expr_pure_handler_consumes(expr: &Expr) -> Option<Vec<core_ir::Path>> {
    match &expr.kind {
        ExprKind::Handle { handler, .. }
            if handler
                .residual_after
                .as_ref()
                .is_some_and(core_effect_is_empty) =>
        {
            Some(handler.consumes.clone())
        }
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => expr_pure_handler_consumes(body),
        ExprKind::Block {
            tail: Some(tail), ..
        } => expr_pure_handler_consumes(tail),
        ExprKind::Block { stmts, tail: None } => match stmts.last() {
            Some(Stmt::Expr(expr)) => expr_pure_handler_consumes(expr),
            _ => None,
        },
        _ => None,
    }
}

fn core_effect_is_empty(effect: &core_ir::Type) -> bool {
    matches!(effect, core_ir::Type::Never)
        || matches!(
            effect,
            core_ir::Type::Row { items, tail }
                if items.is_empty() && core_effect_is_empty(tail)
        )
}

fn demand_effect_is_consumed(effect: &DemandEffect, consumed: &[core_ir::Path]) -> bool {
    match effect {
        DemandEffect::Empty | DemandEffect::Hole(_) => false,
        DemandEffect::Atom(ty) => demand_core_effect_path(ty).is_some_and(|path| {
            consumed
                .iter()
                .any(|consume| effect_paths_match(consume, path))
        }),
        DemandEffect::Row(items) => items
            .iter()
            .any(|item| demand_effect_is_consumed(item, consumed)),
    }
}

fn close_pure_handler_result(
    signature: DemandSignature,
    consumed: &[core_ir::Path],
) -> DemandSignature {
    if consumed.is_empty() {
        return signature;
    }
    match signature {
        DemandSignature::Fun { param, ret } => DemandSignature::Fun {
            param,
            ret: Box::new(close_pure_handler_result(*ret, consumed)),
        },
        DemandSignature::Thunk { effect, value }
            if demand_effect_is_consumed(&effect, consumed) =>
        {
            *value
        }
        other => other,
    }
}

fn close_consumed_effect_holes(
    signature: DemandSignature,
    consumed: &[core_ir::Path],
) -> DemandSignature {
    if consumed.is_empty() {
        return signature;
    }
    match signature {
        DemandSignature::Fun { param, ret } => DemandSignature::Fun {
            param: Box::new(close_consumed_effect_holes(*param, consumed)),
            ret: Box::new(close_consumed_effect_holes(*ret, consumed)),
        },
        DemandSignature::Thunk { effect, value } => {
            let effect = close_consumed_demand_effect_holes(effect, consumed);
            let value = close_consumed_effect_holes(*value, consumed);
            DemandSignature::Thunk {
                effect,
                value: Box::new(value),
            }
        }
        DemandSignature::Core(ty) => {
            DemandSignature::Core(close_consumed_core_effect_holes(ty, consumed))
        }
        other => other,
    }
}

fn close_consumed_core_effect_holes(
    ty: DemandCoreType,
    consumed: &[core_ir::Path],
) -> DemandCoreType {
    match ty {
        DemandCoreType::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => DemandCoreType::Fun {
            param: Box::new(close_consumed_core_effect_holes(*param, consumed)),
            param_effect: Box::new(close_consumed_demand_effect_holes(*param_effect, consumed)),
            ret_effect: Box::new(close_consumed_demand_effect_holes(*ret_effect, consumed)),
            ret: Box::new(close_consumed_core_effect_holes(*ret, consumed)),
        },
        DemandCoreType::Tuple(items) => DemandCoreType::Tuple(
            items
                .into_iter()
                .map(|item| close_consumed_core_effect_holes(item, consumed))
                .collect(),
        ),
        DemandCoreType::Named { path, args } => DemandCoreType::Named {
            path,
            args: args
                .into_iter()
                .map(|arg| close_consumed_type_arg_effect_holes(arg, consumed))
                .collect(),
        },
        DemandCoreType::Record(fields) => DemandCoreType::Record(
            fields
                .into_iter()
                .map(|field| DemandRecordField {
                    value: close_consumed_core_effect_holes(field.value, consumed),
                    ..field
                })
                .collect(),
        ),
        DemandCoreType::Variant(cases) => DemandCoreType::Variant(
            cases
                .into_iter()
                .map(|case| DemandVariantCase {
                    payloads: case
                        .payloads
                        .into_iter()
                        .map(|payload| close_consumed_core_effect_holes(payload, consumed))
                        .collect(),
                    ..case
                })
                .collect(),
        ),
        DemandCoreType::RowAsValue(items) => DemandCoreType::RowAsValue(
            items
                .into_iter()
                .map(|item| close_consumed_demand_effect_holes(item, consumed))
                .collect(),
        ),
        DemandCoreType::Recursive { var, body } => DemandCoreType::Recursive {
            var,
            body: Box::new(close_consumed_core_effect_holes(*body, consumed)),
        },
        other => other,
    }
}

fn close_consumed_type_arg_effect_holes(
    arg: DemandTypeArg,
    consumed: &[core_ir::Path],
) -> DemandTypeArg {
    match arg {
        DemandTypeArg::Type(ty) => {
            DemandTypeArg::Type(close_consumed_core_effect_holes(ty, consumed))
        }
        DemandTypeArg::Bounds { lower, upper } => DemandTypeArg::Bounds {
            lower: lower.map(|ty| close_consumed_core_effect_holes(ty, consumed)),
            upper: upper.map(|ty| close_consumed_core_effect_holes(ty, consumed)),
        },
    }
}

fn close_consumed_demand_effect_holes(
    effect: DemandEffect,
    consumed: &[core_ir::Path],
) -> DemandEffect {
    if !demand_effect_is_consumed(&effect, consumed) {
        return effect;
    }
    close_effect_holes(effect)
}

fn close_effect_holes(effect: DemandEffect) -> DemandEffect {
    match effect {
        DemandEffect::Hole(_) | DemandEffect::Empty => DemandEffect::Empty,
        DemandEffect::Atom(_) => effect,
        DemandEffect::Row(items) => normalize_effect_row(
            items
                .into_iter()
                .map(close_effect_holes)
                .collect::<Vec<_>>(),
        ),
    }
}

fn normalize_effect_row(items: Vec<DemandEffect>) -> DemandEffect {
    let mut out = Vec::new();
    for item in items {
        push_normalized_effect_item(item, &mut out);
    }
    match out.as_slice() {
        [] => DemandEffect::Empty,
        [item] => item.clone(),
        _ => DemandEffect::Row(out),
    }
}

fn push_normalized_effect_item(item: DemandEffect, out: &mut Vec<DemandEffect>) {
    match item {
        DemandEffect::Empty => {}
        DemandEffect::Row(items) => {
            for item in items {
                push_normalized_effect_item(item, out);
            }
        }
        item if demand_effect_is_impossible(&item) => {}
        item => out.push(item),
    }
}

fn demand_core_effect_path(ty: &DemandCoreType) -> Option<&core_ir::Path> {
    match ty {
        DemandCoreType::Named { path, .. } => Some(path),
        _ => None,
    }
}

fn effect_operation_namespace(operation: &core_ir::Path) -> Option<core_ir::Path> {
    if operation.segments.is_empty() {
        return None;
    }
    Some(core_ir::Path {
        segments: operation.segments[..operation.segments.len() - 1].to_vec(),
    })
}

fn thunk_signature_effect(signature: &DemandSignature) -> Option<&DemandEffect> {
    match signature {
        DemandSignature::Thunk { effect, .. } => Some(effect),
        _ => None,
    }
}

fn effect_payload_for_namespace(
    effect: &DemandEffect,
    namespace: &core_ir::Path,
) -> Option<DemandSignature> {
    match effect {
        DemandEffect::Atom(DemandCoreType::Named { path, args }) if path == namespace => {
            Some(effect_payload_signature(args))
        }
        DemandEffect::Row(items) => items
            .iter()
            .find_map(|item| effect_payload_for_namespace(item, namespace)),
        _ => None,
    }
}

fn relative_operation_payload_hint(
    effect: &DemandEffect,
    operation: &core_ir::Path,
) -> Option<DemandSignature> {
    if operation.segments.len() != 1 {
        return None;
    }
    let mut hints = Vec::new();
    collect_non_empty_effect_payloads(effect, &mut hints);
    match hints.as_slice() {
        [hint] => Some(hint.clone()),
        _ => None,
    }
}

fn collect_non_empty_effect_payloads(effect: &DemandEffect, out: &mut Vec<DemandSignature>) {
    match effect {
        DemandEffect::Atom(DemandCoreType::Named { args, .. }) if !args.is_empty() => {
            out.push(effect_payload_signature(args));
        }
        DemandEffect::Row(items) => {
            for item in items {
                collect_non_empty_effect_payloads(item, out);
            }
        }
        _ => {}
    }
}

fn effect_payload_signature(args: &[DemandTypeArg]) -> DemandSignature {
    match args {
        [] => DemandSignature::Core(named_core("unit")),
        [DemandTypeArg::Type(ty)] => DemandSignature::Core(ty.clone()),
        [
            DemandTypeArg::Bounds {
                lower: Some(ty), ..
            },
        ]
        | [
            DemandTypeArg::Bounds {
                lower: None,
                upper: Some(ty),
            },
        ] => DemandSignature::Core(ty.clone()),
        _ => DemandSignature::Core(DemandCoreType::Tuple(
            args.iter().filter_map(effect_payload_arg_core).collect(),
        )),
    }
}

fn effect_payload_arg_core(arg: &DemandTypeArg) -> Option<DemandCoreType> {
    match arg {
        DemandTypeArg::Type(ty) => Some(ty.clone()),
        DemandTypeArg::Bounds {
            lower: Some(ty), ..
        }
        | DemandTypeArg::Bounds {
            lower: None,
            upper: Some(ty),
        } => Some(ty.clone()),
        DemandTypeArg::Bounds {
            lower: None,
            upper: None,
        } => None,
    }
}

fn effect_paths_match(left: &core_ir::Path, right: &core_ir::Path) -> bool {
    left == right
        || left.segments.ends_with(right.segments.as_slice())
        || right.segments.ends_with(left.segments.as_slice())
        || qualified_prefix_effect_paths_match(left, right)
        || qualified_prefix_effect_paths_match(right, left)
}

fn qualified_prefix_effect_paths_match(parent: &core_ir::Path, child: &core_ir::Path) -> bool {
    parent.segments.len() > 1
        && child.segments.len() > parent.segments.len()
        && child.segments.starts_with(parent.segments.as_slice())
}

fn close_constructor_effect_args(signature: DemandSignature) -> DemandSignature {
    let DemandSignature::Fun { param, ret } = signature else {
        return signature;
    };
    let mut param = *param;
    let mut ret = *ret;
    if let Some(value_arg) = ref_ret_value_arg(&ret) {
        param = close_ref_constructor_param(param, &value_arg);
    }
    ret = close_ref_constructor_effect_arg(&param, ret);
    DemandSignature::Fun {
        param: Box::new(param),
        ret: Box::new(ret),
    }
}

fn close_ref_constructor_effect_arg(
    param: &DemandSignature,
    ret: DemandSignature,
) -> DemandSignature {
    let Some(effect_arg) = ref_record_effect_arg(param) else {
        return ret;
    };
    let DemandSignature::Core(DemandCoreType::Named { path, mut args }) = ret else {
        return ret;
    };
    if !is_std_var_ref_path(&path) || args.is_empty() {
        return DemandSignature::Core(DemandCoreType::Named { path, args });
    }
    if type_arg_can_accept_closed_effect(&args[0]) {
        args[0] = DemandTypeArg::Type(effect_arg);
    }
    DemandSignature::Core(DemandCoreType::Named { path, args })
}

fn ref_ret_value_arg(ret: &DemandSignature) -> Option<DemandCoreType> {
    let DemandSignature::Core(DemandCoreType::Named { path, args }) = ret else {
        return None;
    };
    if !is_std_var_ref_path(path) {
        return None;
    }
    match args.get(1)? {
        DemandTypeArg::Type(ty) if ty.is_closed() => Some(ty.clone()),
        DemandTypeArg::Bounds {
            lower: Some(ty), ..
        }
        | DemandTypeArg::Bounds {
            lower: None,
            upper: Some(ty),
        } if ty.is_closed() => Some(ty.clone()),
        _ => None,
    }
}

fn close_ref_constructor_param(
    param: DemandSignature,
    value_arg: &DemandCoreType,
) -> DemandSignature {
    let DemandSignature::Core(DemandCoreType::Record(fields)) = param else {
        return param;
    };
    DemandSignature::Core(DemandCoreType::Record(
        fields
            .into_iter()
            .map(|field| close_ref_constructor_field(field, value_arg))
            .collect(),
    ))
}

fn close_ref_constructor_field(
    mut field: DemandRecordField,
    value_arg: &DemandCoreType,
) -> DemandRecordField {
    let DemandCoreType::Fun {
        ret_effect, ret, ..
    } = &mut field.value
    else {
        return field;
    };
    if matches!(ret.as_ref(), DemandCoreType::Hole(_)) {
        *ret = Box::new(value_arg.clone());
    }
    close_ref_update_effect_holes(ret_effect, value_arg);
    field
}

fn close_ref_update_effect_holes(effect: &mut DemandEffect, value_arg: &DemandCoreType) {
    match effect {
        DemandEffect::Atom(ty) => close_ref_update_atom_holes(ty, value_arg),
        DemandEffect::Row(items) => {
            for item in items {
                close_ref_update_effect_holes(item, value_arg);
            }
        }
        DemandEffect::Empty | DemandEffect::Hole(_) => {}
    }
}

fn close_ref_update_atom_holes(ty: &mut DemandCoreType, value_arg: &DemandCoreType) {
    let DemandCoreType::Named { path, args } = ty else {
        return;
    };
    if !path
        .segments
        .iter()
        .map(|name| name.0.as_str())
        .eq(["std", "var", "ref_update"])
    {
        return;
    }
    if matches!(
        args.first(),
        Some(DemandTypeArg::Type(DemandCoreType::Hole(_)))
    ) {
        args[0] = DemandTypeArg::Type(value_arg.clone());
    }
}

fn ref_record_effect_arg(param: &DemandSignature) -> Option<DemandCoreType> {
    let DemandSignature::Core(DemandCoreType::Record(fields)) = param else {
        return None;
    };
    fields
        .iter()
        .filter_map(|field| match &field.value {
            DemandCoreType::Fun { ret_effect, .. } if ret_effect.is_closed() => {
                Some(effect_core_arg(ret_effect.as_ref()))
            }
            _ => None,
        })
        .find(|effect| !matches!(effect, DemandCoreType::Never))
}

fn effect_core_arg(effect: &DemandEffect) -> DemandCoreType {
    match effect {
        DemandEffect::Empty => DemandCoreType::Never,
        DemandEffect::Row(items) if items.is_empty() => DemandCoreType::Never,
        DemandEffect::Row(items) => DemandCoreType::RowAsValue(items.clone()),
        other => DemandCoreType::RowAsValue(vec![other.clone()]),
    }
}

fn type_arg_can_accept_closed_effect(arg: &DemandTypeArg) -> bool {
    match arg {
        DemandTypeArg::Type(DemandCoreType::Hole(_)) => true,
        DemandTypeArg::Bounds { lower, upper } => lower.is_none() && upper.is_none(),
        _ => false,
    }
}

fn is_std_var_ref_path(path: &core_ir::Path) -> bool {
    path.segments
        .iter()
        .map(|name| name.0.as_str())
        .eq(["std", "var", "ref"])
}

fn restore_local(
    locals: &mut HashMap<core_ir::Path, DemandSignature>,
    local: core_ir::Path,
    previous: Option<DemandSignature>,
) {
    match previous {
        Some(previous) => {
            locals.insert(local, previous);
        }
        None => {
            locals.remove(&local);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Expr, Root};

    #[test]
    fn checker_accepts_identity_at_concrete_demand() {
        let id = path("id");
        let module = module_with_binding(binding(
            id.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(core_ir::Type::Any),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Var(path("x")),
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            id.clone(),
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(named("int")),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked demand");

        assert_eq!(checked.target, id);
        assert_eq!(
            checked.solved,
            DemandSignature::from_runtime_type(&demand.expected)
        );
        assert!(checked.substitutions.values.is_empty());
    }

    #[test]
    fn checker_solves_return_hole_from_lambda_body() {
        let f = path("f");
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(core_ir::Type::Any),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                    RuntimeType::core(named("int")),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("unit")),
                RuntimeType::core(core_ir::Type::Any),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked demand");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("unit"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
    }

    #[test]
    fn checker_checks_simple_application_inside_lambda() {
        let f = path("f");
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(named("int")),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Apply {
                        callee: Box::new(Expr::typed(
                            ExprKind::Lambda {
                                param: core_ir::Name("y".to_string()),
                                param_effect_annotation: None,
                                param_function_allowed_effects: None,
                                body: Box::new(Expr::typed(
                                    ExprKind::Var(path("y")),
                                    RuntimeType::core(named("int")),
                                )),
                            },
                            RuntimeType::fun(
                                RuntimeType::core(named("int")),
                                RuntimeType::core(named("int")),
                            ),
                        )),
                        arg: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::core(named("int")),
                        )),
                        evidence: None,
                        instantiation: None,
                    },
                    RuntimeType::core(named("int")),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(named("int")),
            ),
        );

        DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked application");
    }

    #[test]
    fn checker_emits_child_demand_for_generic_call_in_body() {
        let id = path("id");
        let use_id = path("use_id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![
                binding(
                    id.clone(),
                    vec![core_ir::TypeVar("a".to_string())],
                    RuntimeType::fun(
                        RuntimeType::core(core_ir::Type::Any),
                        RuntimeType::core(core_ir::Type::Any),
                    ),
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                    },
                ),
                binding(
                    use_id.clone(),
                    vec![core_ir::TypeVar("a".to_string())],
                    RuntimeType::fun(
                        RuntimeType::core(named("int")),
                        RuntimeType::core(named("int")),
                    ),
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Apply {
                                callee: Box::new(Expr::typed(
                                    ExprKind::Var(id.clone()),
                                    RuntimeType::fun(
                                        RuntimeType::core(core_ir::Type::Any),
                                        RuntimeType::core(core_ir::Type::Any),
                                    ),
                                )),
                                arg: Box::new(Expr::typed(
                                    ExprKind::Var(path("x")),
                                    RuntimeType::core(core_ir::Type::Any),
                                )),
                                evidence: None,
                                instantiation: None,
                            },
                            RuntimeType::core(named("int")),
                        )),
                    },
                ),
            ],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(use_id.clone())],
        };
        let demand = Demand::new(
            use_id,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(named("int")),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked demand");
        let mut child_demands = checked.child_demands;
        let child = child_demands.pop_front().expect("child demand");

        assert_eq!(child.target, id);
        assert_eq!(
            child.key.signature,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
        assert!(child_demands.is_empty());
    }

    #[test]
    fn checker_applies_local_substitutions_before_emitting_child_demand() {
        let run = path("run");
        let use_run = path("use_run");
        let io = named("io");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![
                binding(
                    run.clone(),
                    vec![core_ir::TypeVar("a".to_string())],
                    RuntimeType::fun(
                        RuntimeType::thunk(io.clone(), RuntimeType::core(core_ir::Type::Any)),
                        RuntimeType::core(core_ir::Type::Any),
                    ),
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Lit(core_ir::Lit::Unit),
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                    },
                ),
                binding(
                    use_run.clone(),
                    vec![core_ir::TypeVar("a".to_string())],
                    RuntimeType::fun(
                        RuntimeType::core(named("int")),
                        RuntimeType::core(named("int")),
                    ),
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Apply {
                                callee: Box::new(Expr::typed(
                                    ExprKind::Var(run.clone()),
                                    RuntimeType::fun(
                                        RuntimeType::thunk(
                                            io.clone(),
                                            RuntimeType::core(core_ir::Type::Any),
                                        ),
                                        RuntimeType::core(core_ir::Type::Any),
                                    ),
                                )),
                                arg: Box::new(Expr::typed(
                                    ExprKind::Thunk {
                                        effect: io.clone(),
                                        value: RuntimeType::core(core_ir::Type::Any),
                                        expr: Box::new(Expr::typed(
                                            ExprKind::Var(path("x")),
                                            RuntimeType::core(core_ir::Type::Any),
                                        )),
                                    },
                                    RuntimeType::thunk(io, RuntimeType::core(core_ir::Type::Any)),
                                )),
                                evidence: None,
                                instantiation: None,
                            },
                            RuntimeType::core(named("int")),
                        )),
                    },
                ),
            ],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(use_run.clone())],
        };
        let demand = Demand::new(
            use_run,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(named("int")),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked demand");
        let mut child_demands = checked.child_demands;
        let child = child_demands.pop_front().expect("child demand");

        assert_eq!(
            child.key.signature,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Thunk {
                    effect: DemandEffect::Atom(named_demand("io")),
                    value: Box::new(DemandSignature::Core(named_demand("int"))),
                }),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
    }

    #[test]
    fn checker_uses_head_type_for_curried_generic_call_hints() {
        let run = path("run");
        let cell = named("cell");
        let value = RuntimeType::core(named("int"));
        let thunk = RuntimeType::thunk(cell.clone(), value.clone());
        let run_ty = RuntimeType::fun(
            value.clone(),
            RuntimeType::fun(thunk.clone(), value.clone()),
        );
        let module = module_with_binding(binding(
            run.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            run_ty.clone(),
            ExprKind::Lambda {
                param: core_ir::Name("v".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Apply {
                                callee: Box::new(Expr::typed(
                                    ExprKind::Apply {
                                        callee: Box::new(Expr::typed(
                                            ExprKind::Var(run.clone()),
                                            run_ty.clone(),
                                        )),
                                        arg: Box::new(Expr::typed(
                                            ExprKind::Var(path("v")),
                                            RuntimeType::core(core_ir::Type::Any),
                                        )),
                                        evidence: None,
                                        instantiation: None,
                                    },
                                    RuntimeType::fun(thunk.clone(), value.clone()),
                                )),
                                arg: Box::new(Expr::typed(
                                    ExprKind::Thunk {
                                        effect: cell.clone(),
                                        value: value.clone(),
                                        expr: Box::new(Expr::typed(
                                            ExprKind::Var(path("v")),
                                            RuntimeType::core(core_ir::Type::Any),
                                        )),
                                    },
                                    thunk.clone(),
                                )),
                                evidence: None,
                                instantiation: None,
                            },
                            value.clone(),
                        )),
                    },
                    RuntimeType::fun(thunk.clone(), value.clone()),
                )),
            },
        ));
        let demand = Demand::new(run, run_ty);

        DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked curried recursive call");
    }

    #[test]
    fn checker_applies_late_substitutions_before_emitting_child_demand() {
        let id = path("id");
        let use_id = path("use_id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![
                binding(
                    id.clone(),
                    vec![core_ir::TypeVar("a".to_string())],
                    RuntimeType::fun(
                        RuntimeType::core(core_ir::Type::Any),
                        RuntimeType::core(core_ir::Type::Any),
                    ),
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                    },
                ),
                binding(
                    use_id.clone(),
                    vec![core_ir::TypeVar("a".to_string())],
                    RuntimeType::fun(
                        RuntimeType::core(core_ir::Type::Any),
                        RuntimeType::core(core_ir::Type::Any),
                    ),
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Block {
                                stmts: vec![Stmt::Let {
                                    pattern: Pattern::Bind {
                                        name: core_ir::Name("y".to_string()),
                                        ty: RuntimeType::core(core_ir::Type::Any),
                                    },
                                    value: Expr::typed(
                                        ExprKind::Apply {
                                            callee: Box::new(Expr::typed(
                                                ExprKind::Var(id.clone()),
                                                RuntimeType::fun(
                                                    RuntimeType::core(core_ir::Type::Any),
                                                    RuntimeType::core(core_ir::Type::Any),
                                                ),
                                            )),
                                            arg: Box::new(Expr::typed(
                                                ExprKind::Var(path("x")),
                                                RuntimeType::core(core_ir::Type::Any),
                                            )),
                                            evidence: None,
                                            instantiation: None,
                                        },
                                        RuntimeType::core(core_ir::Type::Any),
                                    ),
                                }],
                                tail: Some(Box::new(Expr::typed(
                                    ExprKind::Tuple(vec![
                                        Expr::typed(
                                            ExprKind::Var(path("y")),
                                            RuntimeType::core(core_ir::Type::Any),
                                        ),
                                        Expr::typed(
                                            ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                                            RuntimeType::core(named("int")),
                                        ),
                                    ]),
                                    RuntimeType::core(core_ir::Type::Any),
                                ))),
                            },
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                    },
                ),
            ],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(use_id.clone())],
        };
        let demand = Demand::new(
            use_id,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(core_ir::Type::Tuple(vec![named("int"), named("int")])),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked demand");
        let mut child_demands = checked.child_demands;
        let child = child_demands.pop_front().expect("child demand");

        assert_eq!(
            child.key.signature,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
    }

    #[test]
    fn checker_solves_block_tail_from_let_binding() {
        let f = path("f");
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(core_ir::Type::Any),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Block {
                        stmts: vec![Stmt::Let {
                            pattern: Pattern::Bind {
                                name: core_ir::Name("y".to_string()),
                                ty: RuntimeType::core(core_ir::Type::Any),
                            },
                            value: Expr::typed(
                                ExprKind::Var(path("x")),
                                RuntimeType::core(core_ir::Type::Any),
                            ),
                        }],
                        tail: Some(Box::new(Expr::typed(
                            ExprKind::Var(path("y")),
                            RuntimeType::core(core_ir::Type::Any),
                        ))),
                    },
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(core_ir::Type::Any),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked block");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
    }

    #[test]
    fn checker_solves_tuple_items_from_context() {
        let f = path("f");
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(core_ir::Type::Any),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Tuple(vec![
                        Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::core(core_ir::Type::Any),
                        ),
                        Expr::typed(
                            ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                            RuntimeType::core(named("int")),
                        ),
                    ]),
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(core_ir::Type::Any),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked tuple");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(DemandCoreType::Tuple(vec![
                    named_demand("int"),
                    named_demand("int"),
                ]))),
            }
        );
    }

    #[test]
    fn checker_solves_if_branches_from_context() {
        let f = path("f");
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(core_ir::Type::Any),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::If {
                        cond: Box::new(Expr::typed(
                            ExprKind::Lit(core_ir::Lit::Bool(true)),
                            RuntimeType::core(named("bool")),
                        )),
                        then_branch: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                        else_branch: Box::new(Expr::typed(
                            ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                            RuntimeType::core(named("int")),
                        )),
                        evidence: None,
                    },
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(core_ir::Type::Any),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked if");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
    }

    #[test]
    fn checker_pushes_expected_value_through_thunk() {
        let f = path("f");
        let io = named("io");
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(core_ir::Type::Any),
                RuntimeType::thunk(io.clone(), RuntimeType::core(core_ir::Type::Any)),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Thunk {
                        effect: io.clone(),
                        value: RuntimeType::core(core_ir::Type::Any),
                        expr: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                    },
                    RuntimeType::thunk(io.clone(), RuntimeType::core(core_ir::Type::Any)),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::thunk(io, RuntimeType::core(named("int"))),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked thunk");

        assert_eq!(
            checked.solved,
            DemandSignature::from_runtime_type(&demand.expected)
        );
    }

    #[test]
    fn checker_accepts_pure_value_for_expected_thunk() {
        let f = path("f");
        let io = named("io");
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(core_ir::Type::Any),
                RuntimeType::thunk(io.clone(), RuntimeType::core(core_ir::Type::Any)),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::If {
                        cond: Box::new(Expr::typed(
                            ExprKind::Lit(core_ir::Lit::Bool(true)),
                            RuntimeType::core(named("bool")),
                        )),
                        then_branch: Box::new(Expr::typed(
                            ExprKind::Thunk {
                                effect: io.clone(),
                                value: RuntimeType::core(core_ir::Type::Any),
                                expr: Box::new(Expr::typed(
                                    ExprKind::Var(path("x")),
                                    RuntimeType::core(core_ir::Type::Any),
                                )),
                            },
                            RuntimeType::thunk(io.clone(), RuntimeType::core(core_ir::Type::Any)),
                        )),
                        else_branch: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                        evidence: None,
                    },
                    RuntimeType::thunk(io.clone(), RuntimeType::core(core_ir::Type::Any)),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::thunk(io, RuntimeType::core(named("int"))),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked pure value branch");

        assert_eq!(
            checked.solved,
            DemandSignature::from_runtime_type(&demand.expected)
        );
    }

    #[test]
    fn checker_pushes_expected_value_through_bind_here() {
        let f = path("f");
        let io = named("io");
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(core_ir::Type::Any),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::BindHere {
                        expr: Box::new(Expr::typed(
                            ExprKind::Thunk {
                                effect: io.clone(),
                                value: RuntimeType::core(core_ir::Type::Any),
                                expr: Box::new(Expr::typed(
                                    ExprKind::Var(path("x")),
                                    RuntimeType::core(core_ir::Type::Any),
                                )),
                            },
                            RuntimeType::thunk(io, RuntimeType::core(core_ir::Type::Any)),
                        )),
                    },
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(core_ir::Type::Any),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked bind_here");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
    }

    #[test]
    fn checker_uses_handle_value_arm_payload_type() {
        let f = path("f");
        let io = named("io");
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Handle {
                        body: Box::new(Expr::typed(
                            ExprKind::Thunk {
                                effect: io.clone(),
                                value: RuntimeType::core(core_ir::Type::Any),
                                expr: Box::new(Expr::typed(
                                    ExprKind::Var(path("x")),
                                    RuntimeType::core(core_ir::Type::Any),
                                )),
                            },
                            RuntimeType::thunk(io.clone(), RuntimeType::core(core_ir::Type::Any)),
                        )),
                        arms: vec![HandleArm {
                            effect: core_ir::Path::default(),
                            payload: Pattern::Bind {
                                name: core_ir::Name("v".to_string()),
                                ty: RuntimeType::core(core_ir::Type::Any),
                            },
                            resume: None,
                            guard: None,
                            body: Expr::typed(
                                ExprKind::Var(path("v")),
                                RuntimeType::core(core_ir::Type::Any),
                            ),
                        }],
                        evidence: crate::ir::JoinEvidence {
                            result: core_ir::Type::Any,
                        },
                        handler: crate::ir::HandleEffect {
                            consumes: Vec::new(),
                            residual_before: Some(io),
                            residual_after: None,
                        },
                    },
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(core_ir::Type::Any),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked handle");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
    }

    #[test]
    fn checker_uses_apply_evidence_inside_handle_value_arm() {
        let f = path("f");
        let io = named("io");
        let list_any = list_type(core_ir::Type::Any);
        let list_int = list_type(named("int"));
        let singleton_ty = core_fun(core_ir::Type::Any, list_any.clone());
        let singleton_int_ty = core_fun(named("int"), list_int.clone());
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::thunk(io.clone(), RuntimeType::core(core_ir::Type::Any)),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Handle {
                        body: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::thunk(io.clone(), RuntimeType::core(core_ir::Type::Any)),
                        )),
                        arms: vec![HandleArm {
                            effect: core_ir::Path::default(),
                            payload: Pattern::Bind {
                                name: core_ir::Name("v".to_string()),
                                ty: RuntimeType::core(core_ir::Type::Any),
                            },
                            resume: None,
                            guard: None,
                            body: Expr::typed(
                                ExprKind::Apply {
                                    callee: Box::new(Expr::typed(
                                        ExprKind::PrimitiveOp(core_ir::PrimitiveOp::ListSingleton),
                                        RuntimeType::core(singleton_ty),
                                    )),
                                    arg: Box::new(Expr::typed(
                                        ExprKind::Var(path("v")),
                                        RuntimeType::core(core_ir::Type::Any),
                                    )),
                                    evidence: Some(core_ir::ApplyEvidence {
                                        callee_source_edge: None,
                                        expected_callee: None,
                                        arg_source_edge: None,
                                        callee: core_ir::TypeBounds::exact(singleton_int_ty),
                                        arg: core_ir::TypeBounds::exact(named("int")),
                                        expected_arg: None,
                                        result: core_ir::TypeBounds::exact(list_int.clone()),
                                        principal_callee: None,
                                        substitutions: Vec::new(),
                                        substitution_candidates: Vec::new(),
                                        role_method: false,
                                    }),
                                    instantiation: None,
                                },
                                RuntimeType::core(list_any),
                            ),
                        }],
                        evidence: crate::ir::JoinEvidence {
                            result: core_ir::Type::Any,
                        },
                        handler: crate::ir::HandleEffect {
                            consumes: Vec::new(),
                            residual_before: Some(io.clone()),
                            residual_after: None,
                        },
                    },
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::thunk(io.clone(), RuntimeType::core(named("int"))),
                RuntimeType::core(list_int),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked handle singleton");

        assert_eq!(
            checked.solved,
            DemandSignature::from_runtime_type(&demand.expected)
        );
    }

    #[test]
    fn checker_links_effect_arm_payload_to_handled_effect_payload() {
        let f = path("f");
        let sub = path_segments(&["std", "flow", "sub"]);
        let return_op = path("return");
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::thunk(core_ir::Type::Any, RuntimeType::core(named("int"))),
                RuntimeType::core(named("int")),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Handle {
                        body: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::thunk(core_ir::Type::Any, RuntimeType::core(named("int"))),
                        )),
                        arms: vec![
                            HandleArm {
                                effect: return_op,
                                payload: Pattern::Bind {
                                    name: core_ir::Name("a".to_string()),
                                    ty: RuntimeType::core(core_ir::Type::Any),
                                },
                                resume: None,
                                guard: None,
                                body: Expr::typed(
                                    ExprKind::Var(path("a")),
                                    RuntimeType::core(core_ir::Type::Any),
                                ),
                            },
                            HandleArm {
                                effect: core_ir::Path::default(),
                                payload: Pattern::Bind {
                                    name: core_ir::Name("a".to_string()),
                                    ty: RuntimeType::core(core_ir::Type::Any),
                                },
                                resume: None,
                                guard: None,
                                body: Expr::typed(
                                    ExprKind::Var(path("a")),
                                    RuntimeType::core(core_ir::Type::Any),
                                ),
                            },
                        ],
                        evidence: crate::ir::JoinEvidence {
                            result: named("int"),
                        },
                        handler: crate::ir::HandleEffect {
                            consumes: vec![sub.clone()],
                            residual_before: Some(core_ir::Type::Any),
                            residual_after: Some(core_ir::Type::Never),
                        },
                    },
                    RuntimeType::core(named("int")),
                )),
            },
        ));
        let signature = DemandSignature::Fun {
            param: Box::new(DemandSignature::Thunk {
                effect: DemandEffect::Atom(DemandCoreType::Named {
                    path: sub.clone(),
                    args: vec![DemandTypeArg::Type(DemandCoreType::Hole(0))],
                }),
                value: Box::new(DemandSignature::Core(named_demand("int"))),
            }),
            ret: Box::new(DemandSignature::Core(named_demand("int"))),
        };
        let demand = Demand::with_signature(
            f,
            RuntimeType::fun(
                RuntimeType::thunk(core_ir::Type::Any, RuntimeType::core(named("int"))),
                RuntimeType::core(named("int")),
            ),
            signature,
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked sub handler");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Thunk {
                    effect: DemandEffect::Atom(DemandCoreType::Named {
                        path: sub,
                        args: vec![DemandTypeArg::Type(named_demand("int"))],
                    }),
                    value: Box::new(DemandSignature::Core(named_demand("int"))),
                }),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
    }

    #[test]
    fn checker_closes_residual_effect_tail_for_pure_handler() {
        let f = path("f");
        let sub = path_segments(&["std", "flow", "sub"]);
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::thunk(core_ir::Type::Any, RuntimeType::core(named("int"))),
                RuntimeType::core(named("int")),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Handle {
                        body: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::thunk(core_ir::Type::Any, RuntimeType::core(named("int"))),
                        )),
                        arms: vec![
                            HandleArm {
                                effect: path("return"),
                                payload: Pattern::Bind {
                                    name: core_ir::Name("a".to_string()),
                                    ty: RuntimeType::core(core_ir::Type::Any),
                                },
                                resume: None,
                                guard: None,
                                body: Expr::typed(
                                    ExprKind::Var(path("a")),
                                    RuntimeType::core(core_ir::Type::Any),
                                ),
                            },
                            HandleArm {
                                effect: core_ir::Path::default(),
                                payload: Pattern::Bind {
                                    name: core_ir::Name("a".to_string()),
                                    ty: RuntimeType::core(core_ir::Type::Any),
                                },
                                resume: None,
                                guard: None,
                                body: Expr::typed(
                                    ExprKind::Var(path("a")),
                                    RuntimeType::core(core_ir::Type::Any),
                                ),
                            },
                        ],
                        evidence: crate::ir::JoinEvidence {
                            result: named("int"),
                        },
                        handler: crate::ir::HandleEffect {
                            consumes: vec![sub.clone()],
                            residual_before: Some(core_ir::Type::Any),
                            residual_after: Some(core_ir::Type::Never),
                        },
                    },
                    RuntimeType::core(named("int")),
                )),
            },
        ));
        let signature = DemandSignature::Fun {
            param: Box::new(DemandSignature::Thunk {
                effect: DemandEffect::Row(vec![
                    DemandEffect::Atom(DemandCoreType::Named {
                        path: sub.clone(),
                        args: vec![DemandTypeArg::Type(DemandCoreType::Hole(0))],
                    }),
                    DemandEffect::Hole(1),
                ]),
                value: Box::new(DemandSignature::Core(named_demand("int"))),
            }),
            ret: Box::new(DemandSignature::Core(named_demand("int"))),
        };
        let demand = Demand::with_signature(
            f,
            RuntimeType::fun(
                RuntimeType::thunk(core_ir::Type::Any, RuntimeType::core(named("int"))),
                RuntimeType::core(named("int")),
            ),
            signature,
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked pure handler");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Thunk {
                    effect: DemandEffect::Atom(DemandCoreType::Named {
                        path: sub,
                        args: vec![DemandTypeArg::Type(named_demand("int"))],
                    }),
                    value: Box::new(DemandSignature::Core(named_demand("int"))),
                }),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
        assert!(checked.solved.is_closed());
    }

    #[test]
    fn checker_uses_handled_body_type_for_resume_result() {
        let f = path("f");
        let io = named("io");
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::thunk(io.clone(), RuntimeType::core(core_ir::Type::Any)),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Handle {
                        body: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::thunk(io.clone(), RuntimeType::core(core_ir::Type::Any)),
                        )),
                        arms: vec![HandleArm {
                            effect: core_ir::Path::from_name(core_ir::Name("op".to_string())),
                            payload: Pattern::Wildcard {
                                ty: RuntimeType::core(named("unit")),
                            },
                            resume: Some(crate::ir::ResumeBinding {
                                name: core_ir::Name("k".to_string()),
                                ty: RuntimeType::fun(
                                    RuntimeType::core(named("bool")),
                                    RuntimeType::thunk(
                                        io.clone(),
                                        RuntimeType::core(core_ir::Type::Any),
                                    ),
                                ),
                            }),
                            guard: None,
                            body: Expr::typed(
                                ExprKind::BindHere {
                                    expr: Box::new(Expr::typed(
                                        ExprKind::Apply {
                                            callee: Box::new(Expr::typed(
                                                ExprKind::Var(path("k")),
                                                RuntimeType::fun(
                                                    RuntimeType::core(named("bool")),
                                                    RuntimeType::thunk(
                                                        io.clone(),
                                                        RuntimeType::core(core_ir::Type::Any),
                                                    ),
                                                ),
                                            )),
                                            arg: Box::new(Expr::typed(
                                                ExprKind::Lit(core_ir::Lit::Bool(true)),
                                                RuntimeType::core(named("bool")),
                                            )),
                                            evidence: None,
                                            instantiation: None,
                                        },
                                        RuntimeType::thunk(
                                            io.clone(),
                                            RuntimeType::core(core_ir::Type::Any),
                                        ),
                                    )),
                                },
                                RuntimeType::core(core_ir::Type::Any),
                            ),
                        }],
                        evidence: crate::ir::JoinEvidence {
                            result: core_ir::Type::Any,
                        },
                        handler: crate::ir::HandleEffect {
                            consumes: vec![core_ir::Path::from_name(core_ir::Name(
                                "op".to_string(),
                            ))],
                            residual_before: Some(io.clone()),
                            residual_after: None,
                        },
                    },
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::thunk(io, RuntimeType::core(core_ir::Type::Any)),
                RuntimeType::core(named("int")),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked handle resume");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Thunk {
                    effect: DemandEffect::Atom(named_demand("io")),
                    value: Box::new(DemandSignature::Core(named_demand("int"))),
                }),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
    }

    #[test]
    fn checker_uses_handled_body_type_for_core_resume_result() {
        let f = path("f");
        let io = named("io");
        let resume_ty = core_ir::Type::Fun {
            param: Box::new(named("bool")),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(io.clone()),
            ret: Box::new(core_ir::Type::Any),
        };
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::thunk(io.clone(), RuntimeType::core(core_ir::Type::Any)),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Handle {
                        body: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::thunk(io.clone(), RuntimeType::core(core_ir::Type::Any)),
                        )),
                        arms: vec![HandleArm {
                            effect: core_ir::Path::from_name(core_ir::Name("op".to_string())),
                            payload: Pattern::Wildcard {
                                ty: RuntimeType::core(named("unit")),
                            },
                            resume: Some(crate::ir::ResumeBinding {
                                name: core_ir::Name("k".to_string()),
                                ty: RuntimeType::core(resume_ty.clone()),
                            }),
                            guard: None,
                            body: Expr::typed(
                                ExprKind::BindHere {
                                    expr: Box::new(Expr::typed(
                                        ExprKind::Apply {
                                            callee: Box::new(Expr::typed(
                                                ExprKind::Var(path("k")),
                                                RuntimeType::core(resume_ty),
                                            )),
                                            arg: Box::new(Expr::typed(
                                                ExprKind::Lit(core_ir::Lit::Bool(true)),
                                                RuntimeType::core(named("bool")),
                                            )),
                                            evidence: None,
                                            instantiation: None,
                                        },
                                        RuntimeType::core(core_ir::Type::Any),
                                    )),
                                },
                                RuntimeType::core(core_ir::Type::Any),
                            ),
                        }],
                        evidence: crate::ir::JoinEvidence {
                            result: core_ir::Type::Any,
                        },
                        handler: crate::ir::HandleEffect {
                            consumes: vec![core_ir::Path::from_name(core_ir::Name(
                                "op".to_string(),
                            ))],
                            residual_before: Some(io.clone()),
                            residual_after: None,
                        },
                    },
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::thunk(io, RuntimeType::core(core_ir::Type::Any)),
                RuntimeType::core(named("int")),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked core handle resume");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Thunk {
                    effect: DemandEffect::Atom(named_demand("io")),
                    value: Box::new(DemandSignature::Core(named_demand("int"))),
                }),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
    }

    #[test]
    fn checker_accepts_consumed_thunk_inside_pure_handler_binding() {
        let f = path("f");
        let io = path("io");
        let io_ty = core_ir::Type::Named {
            path: io.clone(),
            args: Vec::new(),
        };
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::thunk(io_ty.clone(), RuntimeType::core(core_ir::Type::Any)),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Handle {
                        body: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::thunk(
                                io_ty.clone(),
                                RuntimeType::core(core_ir::Type::Any),
                            ),
                        )),
                        arms: vec![HandleArm {
                            effect: core_ir::Path::default(),
                            payload: Pattern::Wildcard {
                                ty: RuntimeType::core(core_ir::Type::Any),
                            },
                            resume: None,
                            guard: None,
                            body: Expr::typed(
                                ExprKind::Thunk {
                                    effect: io_ty.clone(),
                                    value: RuntimeType::core(named("bool")),
                                    expr: Box::new(Expr::typed(
                                        ExprKind::Lit(core_ir::Lit::Bool(true)),
                                        RuntimeType::core(named("bool")),
                                    )),
                                },
                                RuntimeType::thunk(io_ty.clone(), RuntimeType::core(named("bool"))),
                            ),
                        }],
                        evidence: crate::ir::JoinEvidence {
                            result: core_ir::Type::Any,
                        },
                        handler: crate::ir::HandleEffect {
                            consumes: vec![io.clone()],
                            residual_before: Some(io_ty.clone()),
                            residual_after: Some(core_ir::Type::Never),
                        },
                    },
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::thunk(io_ty, RuntimeType::core(named("bool"))),
                RuntimeType::core(named("bool")),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked pure handler consumed thunk");

        assert_eq!(
            checked.solved,
            DemandSignature::from_runtime_type(&demand.expected)
        );
    }

    #[test]
    fn checker_removes_consumed_effect_from_pure_handler_result() {
        let f = path("f");
        let io = path("io");
        let io_ty = core_ir::Type::Named {
            path: io.clone(),
            args: Vec::new(),
        };
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::thunk(io_ty.clone(), RuntimeType::core(core_ir::Type::Any)),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Handle {
                        body: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::thunk(
                                io_ty.clone(),
                                RuntimeType::core(core_ir::Type::Any),
                            ),
                        )),
                        arms: vec![HandleArm {
                            effect: core_ir::Path::default(),
                            payload: Pattern::Wildcard {
                                ty: RuntimeType::core(core_ir::Type::Any),
                            },
                            resume: None,
                            guard: None,
                            body: Expr::typed(
                                ExprKind::Lit(core_ir::Lit::Bool(true)),
                                RuntimeType::core(named("bool")),
                            ),
                        }],
                        evidence: crate::ir::JoinEvidence {
                            result: core_ir::Type::Any,
                        },
                        handler: crate::ir::HandleEffect {
                            consumes: vec![io.clone()],
                            residual_before: Some(io_ty.clone()),
                            residual_after: Some(core_ir::Type::Never),
                        },
                    },
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::thunk(io_ty.clone(), RuntimeType::core(named("bool"))),
                RuntimeType::thunk(io_ty, RuntimeType::core(named("bool"))),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked pure handler");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Thunk {
                    effect: DemandEffect::Atom(named_demand("io")),
                    value: Box::new(DemandSignature::Core(named_demand("bool"))),
                }),
                ret: Box::new(DemandSignature::Core(named_demand("bool"))),
            }
        );
    }

    #[test]
    fn checker_uses_known_handler_target_to_remove_consumed_effect() {
        let once = path_segments(&["std", "undet", "undet", "once"]);
        let undet = core_ir::Type::Named {
            path: path_segments(&["std", "undet", "undet"]),
            args: Vec::new(),
        };
        let opt_int = core_ir::Type::Named {
            path: path_segments(&["std", "opt", "opt"]),
            args: vec![core_ir::TypeArg::Type(named("int"))],
        };
        let module = module_with_binding(binding(
            once.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::thunk(undet.clone(), RuntimeType::core(core_ir::Type::Any)),
                RuntimeType::thunk(undet.clone(), RuntimeType::core(core_ir::Type::Any)),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Thunk {
                        effect: undet.clone(),
                        value: RuntimeType::core(opt_int.clone()),
                        expr: Box::new(Expr::typed(
                            ExprKind::Variant {
                                tag: core_ir::Name("nil".to_string()),
                                value: None,
                            },
                            RuntimeType::core(opt_int.clone()),
                        )),
                    },
                    RuntimeType::thunk(undet.clone(), RuntimeType::core(opt_int.clone())),
                )),
            },
        ));
        let demand = Demand::new(
            once,
            RuntimeType::fun(
                RuntimeType::thunk(undet, RuntimeType::core(named("int"))),
                RuntimeType::core(opt_int),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked known handler");

        assert_eq!(
            checked.solved,
            DemandSignature::from_runtime_type(&demand.expected)
        );
    }

    #[test]
    fn checker_checks_coerce_inner_against_from_type() {
        let f = path("f");
        let from = core_ir::Type::Record(core_ir::RecordType {
            fields: vec![core_ir::RecordField {
                name: core_ir::Name("value".to_string()),
                value: named("int"),
                optional: false,
            }],
            spread: None,
        });
        let to = named("box");
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(core_ir::Type::Any),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Coerce {
                        from: from.clone(),
                        to: to.clone(),
                        expr: Box::new(Expr::typed(
                            ExprKind::Record {
                                fields: vec![crate::ir::RecordExprField {
                                    name: core_ir::Name("value".to_string()),
                                    value: Expr::typed(
                                        ExprKind::Var(path("x")),
                                        RuntimeType::core(core_ir::Type::Any),
                                    ),
                                }],
                                spread: None,
                            },
                            RuntimeType::core(from),
                        )),
                    },
                    RuntimeType::core(to.clone()),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(RuntimeType::core(named("int")), RuntimeType::core(to)),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked coerce");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("box"))),
            }
        );
    }

    #[test]
    fn checker_reads_lambda_body_for_expected_core_function() {
        let f = path("f");
        let io = named("io");
        let core_fun = core_ir::Type::Fun {
            param: Box::new(named("unit")),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(io.clone()),
            ret: Box::new(named("int")),
        };
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(core_ir::Type::Any),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Lambda {
                        param: core_ir::Name("u".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Thunk {
                                effect: io,
                                value: RuntimeType::core(core_ir::Type::Any),
                                expr: Box::new(Expr::typed(
                                    ExprKind::Var(path("x")),
                                    RuntimeType::core(core_ir::Type::Any),
                                )),
                            },
                            RuntimeType::thunk(named("io"), RuntimeType::core(core_ir::Type::Any)),
                        )),
                    },
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(core_ir::Type::Any),
                RuntimeType::core(core_fun),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked core function lambda");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(DemandCoreType::Fun {
                    param: Box::new(named_demand("unit")),
                    param_effect: Box::new(DemandEffect::Empty),
                    ret_effect: Box::new(DemandEffect::Atom(named_demand("io"))),
                    ret: Box::new(named_demand("int")),
                })),
            }
        );
    }

    #[test]
    fn checker_reads_lambda_body_for_expected_thunked_function() {
        let f = path("f");
        let run = path("run");
        let io = named("io");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![
                binding(
                    run.clone(),
                    vec![core_ir::TypeVar("a".to_string())],
                    RuntimeType::fun(
                        RuntimeType::core(core_ir::Type::Any),
                        RuntimeType::core(core_ir::Type::Any),
                    ),
                    ExprKind::Lambda {
                        param: core_ir::Name("y".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Var(path("y")),
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                    },
                ),
                binding(
                    f.clone(),
                    vec![core_ir::TypeVar("a".to_string())],
                    RuntimeType::core(core_ir::Type::Any),
                    ExprKind::Lambda {
                        param: core_ir::Name("u".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Lambda {
                                param: core_ir::Name("x".to_string()),
                                param_effect_annotation: None,
                                param_function_allowed_effects: None,
                                body: Box::new(Expr::typed(
                                    ExprKind::Apply {
                                        callee: Box::new(Expr::typed(
                                            ExprKind::Var(run.clone()),
                                            RuntimeType::fun(
                                                RuntimeType::core(core_ir::Type::Any),
                                                RuntimeType::core(core_ir::Type::Any),
                                            ),
                                        )),
                                        arg: Box::new(Expr::typed(
                                            ExprKind::Var(path("x")),
                                            RuntimeType::core(core_ir::Type::Any),
                                        )),
                                        evidence: None,
                                        instantiation: None,
                                    },
                                    RuntimeType::core(core_ir::Type::Any),
                                )),
                            },
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                    },
                ),
            ],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(f.clone())],
        };
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("unit")),
                RuntimeType::thunk(
                    io,
                    RuntimeType::fun(
                        RuntimeType::core(named("int")),
                        RuntimeType::core(named("int")),
                    ),
                ),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked thunked lambda");
        let mut child_demands = checked.child_demands;
        let child = child_demands.pop_front().expect("child demand");

        assert_eq!(child.target, run);
        assert_eq!(
            child.key.signature,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
    }

    #[test]
    fn checker_applies_core_function_value_with_result_effect() {
        let f = path("f");
        let io = named("io");
        let core_fun = core_ir::Type::Fun {
            param: Box::new(named("unit")),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(io.clone()),
            ret: Box::new(core_ir::Type::Any),
        };
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(core_fun.clone()),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("k".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::BindHere {
                        expr: Box::new(Expr::typed(
                            ExprKind::Apply {
                                callee: Box::new(Expr::typed(
                                    ExprKind::Var(path("k")),
                                    RuntimeType::core(core_fun.clone()),
                                )),
                                arg: Box::new(Expr::typed(
                                    ExprKind::Lit(core_ir::Lit::Unit),
                                    RuntimeType::core(named("unit")),
                                )),
                                evidence: None,
                                instantiation: None,
                            },
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                    },
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(RuntimeType::core(core_fun), RuntimeType::core(named("int"))),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked core function application");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(DemandCoreType::Fun {
                    param: Box::new(named_demand("unit")),
                    param_effect: Box::new(DemandEffect::Empty),
                    ret_effect: Box::new(DemandEffect::Atom(named_demand("io"))),
                    ret: Box::new(named_demand("int")),
                })),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
    }

    #[test]
    fn checker_tracks_record_field_selection() {
        let f = path("f");
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(core_ir::Type::Any),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Select {
                        base: Box::new(Expr::typed(
                            ExprKind::Record {
                                fields: vec![crate::ir::RecordExprField {
                                    name: core_ir::Name("value".to_string()),
                                    value: Expr::typed(
                                        ExprKind::Var(path("x")),
                                        RuntimeType::core(core_ir::Type::Any),
                                    ),
                                }],
                                spread: None,
                            },
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                        field: core_ir::Name("value".to_string()),
                    },
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(core_ir::Type::Any),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked record select");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
    }

    #[test]
    fn checker_tracks_variant_match_payload() {
        let f = path("f");
        let tag = core_ir::Name("just".to_string());
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(core_ir::Type::Any),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Match {
                        scrutinee: Box::new(Expr::typed(
                            ExprKind::Variant {
                                tag: tag.clone(),
                                value: Some(Box::new(Expr::typed(
                                    ExprKind::Var(path("x")),
                                    RuntimeType::core(core_ir::Type::Any),
                                ))),
                            },
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                        arms: vec![crate::ir::MatchArm {
                            pattern: Pattern::Variant {
                                tag,
                                value: Some(Box::new(Pattern::Bind {
                                    name: core_ir::Name("y".to_string()),
                                    ty: RuntimeType::core(core_ir::Type::Any),
                                })),
                                ty: RuntimeType::core(core_ir::Type::Any),
                            },
                            guard: None,
                            body: Expr::typed(
                                ExprKind::Var(path("y")),
                                RuntimeType::core(core_ir::Type::Any),
                            ),
                        }],
                        evidence: crate::ir::JoinEvidence {
                            result: core_ir::Type::Any,
                        },
                    },
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(core_ir::Type::Any),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked match");

        assert_eq!(
            checked.solved,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
    }

    #[test]
    fn checker_pushes_match_pattern_type_into_generic_scrutinee() {
        let f = path("f");
        let g = path("g");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![
                binding(
                    f.clone(),
                    vec![core_ir::TypeVar("a".to_string())],
                    RuntimeType::core(core_ir::Type::Any),
                    ExprKind::Match {
                        scrutinee: Box::new(Expr::typed(
                            ExprKind::Apply {
                                callee: Box::new(Expr::typed(
                                    ExprKind::Var(g.clone()),
                                    RuntimeType::fun(
                                        RuntimeType::core(named("unit")),
                                        RuntimeType::core(core_ir::Type::Any),
                                    ),
                                )),
                                arg: Box::new(Expr::typed(
                                    ExprKind::Lit(core_ir::Lit::Unit),
                                    RuntimeType::core(named("unit")),
                                )),
                                evidence: None,
                                instantiation: None,
                            },
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                        arms: vec![bool_match_arm(true, 1), bool_match_arm(false, 0)],
                        evidence: crate::ir::JoinEvidence {
                            result: named("int"),
                        },
                    },
                ),
                binding(
                    g.clone(),
                    vec![core_ir::TypeVar("b".to_string())],
                    RuntimeType::fun(
                        RuntimeType::core(named("unit")),
                        RuntimeType::core(core_ir::Type::Any),
                    ),
                    ExprKind::Lambda {
                        param: core_ir::Name("_".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Lit(core_ir::Lit::Bool(true)),
                            RuntimeType::core(named("bool")),
                        )),
                    },
                ),
            ],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(f.clone())],
        };
        let demand = Demand::new(f, RuntimeType::core(named("int")));

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked match scrutinee");
        let mut child_demands = checked.child_demands;
        let child = child_demands.pop_front().expect("generic scrutinee demand");

        assert_eq!(child.target, g);
        assert_eq!(
            child.key.signature,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("unit"))),
                ret: Box::new(DemandSignature::Core(named_demand("bool"))),
            }
        );
    }

    #[test]
    fn checker_pushes_named_variant_type_arg_into_payload() {
        let f = path("f");
        let module = module_with_binding(binding(
            f.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::core(core_ir::Type::Any),
                RuntimeType::core(core_ir::Type::Any),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Variant {
                        tag: core_ir::Name("just".to_string()),
                        value: Some(Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::core(core_ir::Type::Any),
                        ))),
                    },
                    RuntimeType::core(core_ir::Type::Any),
                )),
            },
        ));
        let demand = Demand::new(
            f,
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(core_ir::Type::Named {
                    path: path("opt"),
                    args: vec![core_ir::TypeArg::Type(named("int"))],
                }),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked named variant");

        assert_eq!(
            checked.solved,
            DemandSignature::from_runtime_type(&demand.expected)
        );
    }

    #[test]
    fn checker_descends_into_consumed_thunk_and_records_local_signature() {
        let sub_handler = path_segments(&["std", "flow", "sub", "sub"]);
        let sub_effect = path_segments(&["std", "flow", "sub"]);
        let loop_name = core_ir::Name("loop".to_string());
        let module = module_with_binding(binding(
            sub_handler.clone(),
            vec![core_ir::TypeVar("a".to_string())],
            RuntimeType::fun(
                RuntimeType::thunk(
                    effect_named(sub_effect.clone()),
                    RuntimeType::core(named("int")),
                ),
                RuntimeType::core(named("int")),
            ),
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Thunk {
                        effect: effect_named(sub_effect.clone()),
                        value: RuntimeType::core(named("int")),
                        expr: Box::new(Expr::typed(
                            ExprKind::Block {
                                stmts: vec![Stmt::Let {
                                    pattern: Pattern::Bind {
                                        name: loop_name.clone(),
                                        ty: rt_fun_any(),
                                    },
                                    value: Expr::typed(
                                        ExprKind::Lambda {
                                            param: core_ir::Name("y".to_string()),
                                            param_effect_annotation: None,
                                            param_function_allowed_effects: None,
                                            body: Box::new(Expr::typed(
                                                ExprKind::Var(path("y")),
                                                RuntimeType::core(core_ir::Type::Any),
                                            )),
                                        },
                                        rt_fun_any(),
                                    ),
                                }],
                                tail: Some(Box::new(Expr::typed(
                                    ExprKind::Apply {
                                        callee: Box::new(Expr::typed(
                                            ExprKind::Var(path("loop")),
                                            rt_fun_any(),
                                        )),
                                        arg: Box::new(Expr::typed(
                                            ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                                            RuntimeType::core(named("int")),
                                        )),
                                        evidence: None,
                                        instantiation: None,
                                    },
                                    RuntimeType::core(core_ir::Type::Any),
                                ))),
                            },
                            RuntimeType::core(named("int")),
                        )),
                    },
                    RuntimeType::thunk(
                        effect_named(sub_effect.clone()),
                        RuntimeType::core(named("int")),
                    ),
                )),
            },
        ));
        let demand = Demand::new(
            sub_handler,
            RuntimeType::fun(
                RuntimeType::thunk(effect_named(sub_effect), RuntimeType::core(named("int"))),
                RuntimeType::core(named("int")),
            ),
        );

        let checked = DemandChecker::from_module(&module)
            .check_demand(&demand)
            .expect("checked consumed thunk");

        assert_eq!(
            checked.local_signatures.get(&path("loop")),
            Some(&DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            })
        );
    }

    fn module_with_binding(binding: Binding) -> Module {
        Module {
            path: core_ir::Path::default(),
            bindings: vec![binding],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(path("f"))],
        }
    }

    fn binding(
        name: core_ir::Path,
        type_params: Vec<core_ir::TypeVar>,
        ty: RuntimeType,
        kind: ExprKind,
    ) -> Binding {
        Binding {
            name,
            type_params,
            scheme: core_ir::Scheme {
                requirements: Vec::new(),
                body: core_ir::Type::Any,
            },
            body: Expr::typed(kind, ty),
        }
    }

    fn named(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: path(name),
            args: Vec::new(),
        }
    }

    fn list_type(item: core_ir::Type) -> core_ir::Type {
        core_ir::Type::Named {
            path: core_ir::Path {
                segments: vec![
                    core_ir::Name("std".to_string()),
                    core_ir::Name("list".to_string()),
                    core_ir::Name("list".to_string()),
                ],
            },
            args: vec![core_ir::TypeArg::Type(item)],
        }
    }

    fn core_fun(param: core_ir::Type, ret: core_ir::Type) -> core_ir::Type {
        core_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(core_ir::Type::Never),
            ret: Box::new(ret),
        }
    }

    fn rt_fun_any() -> RuntimeType {
        RuntimeType::fun(
            RuntimeType::core(core_ir::Type::Any),
            RuntimeType::core(core_ir::Type::Any),
        )
    }

    fn effect_named(path: core_ir::Path) -> core_ir::Type {
        core_ir::Type::Named {
            path,
            args: Vec::new(),
        }
    }

    fn named_demand(name: &str) -> DemandCoreType {
        DemandCoreType::Named {
            path: path(name),
            args: Vec::new(),
        }
    }

    fn bool_match_arm(value: bool, result: i64) -> crate::ir::MatchArm {
        crate::ir::MatchArm {
            pattern: Pattern::Lit {
                lit: core_ir::Lit::Bool(value),
                ty: RuntimeType::core(named("bool")),
            },
            guard: None,
            body: Expr::typed(
                ExprKind::Lit(core_ir::Lit::Int(result.to_string())),
                RuntimeType::core(named("int")),
            ),
        }
    }

    fn path(name: &str) -> core_ir::Path {
        core_ir::Path::from_name(core_ir::Name(name.to_string()))
    }

    fn path_segments(segments: &[&str]) -> core_ir::Path {
        core_ir::Path {
            segments: segments
                .iter()
                .map(|segment| core_ir::Name((*segment).to_string()))
                .collect(),
        }
    }
}
