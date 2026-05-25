use std::collections::BTreeSet;

use yulang_typed_ir as typed_ir;

use crate::diagnostic::{RuntimeError, RuntimeResult};
use crate::ir::{
    Expr, ExprKind, HandleEffect, JoinEvidence, MatchArm, Module, Pattern, RecordExprField,
    RecordPatternField, RecordSpreadExpr, RecordSpreadPattern, Stmt, Type as RuntimeType,
};
use crate::types::{core_type_is_runtime_projection_fallback, type_compatible};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuntimeStage {
    Lowered,
    Monomorphized,
    BeforeVm,
}

impl RuntimeStage {
    fn name(self) -> &'static str {
        match self {
            RuntimeStage::Lowered => "runtime lowering",
            RuntimeStage::Monomorphized => "monomorphization",
            RuntimeStage::BeforeVm => "VM erase",
        }
    }
}

pub fn check_runtime_invariants(module: &Module, stage: RuntimeStage) -> RuntimeResult<()> {
    let mut checker = InvariantChecker {
        stage,
        strict_value_types: false,
        strict_type_surfaces: false,
    };
    for binding in &module.bindings {
        if matches!(stage, RuntimeStage::BeforeVm) && !binding.type_params.is_empty() {
            return Err(RuntimeError::InvariantViolation {
                stage: stage.name(),
                context: format!("binding {}", path_name(&binding.name)),
                message: "VM input binding must be monomorphic",
            });
        }
        checker.expr(
            &binding.body,
            format!("binding {}", path_name(&binding.name)),
        )?;
    }
    for (index, expr) in module.root_exprs.iter().enumerate() {
        checker.expr(expr, format!("root #{index}"))?;
    }
    Ok(())
}

pub fn check_strict_runtime_value_types(module: &Module, stage: RuntimeStage) -> RuntimeResult<()> {
    let mut checker = InvariantChecker {
        stage,
        strict_value_types: true,
        strict_type_surfaces: false,
    };
    for binding in &module.bindings {
        checker.expr(
            &binding.body,
            format!("binding {}", path_name(&binding.name)),
        )?;
    }
    for (index, expr) in module.root_exprs.iter().enumerate() {
        checker.expr(expr, format!("root #{index}"))?;
    }
    Ok(())
}

pub fn check_strict_runtime_type_surfaces(
    module: &Module,
    stage: RuntimeStage,
) -> RuntimeResult<()> {
    let mut checker = InvariantChecker {
        stage,
        strict_value_types: true,
        strict_type_surfaces: true,
    };
    for binding in &module.bindings {
        checker.expr(
            &binding.body,
            format!("binding {}", path_name(&binding.name)),
        )?;
    }
    for (index, expr) in module.root_exprs.iter().enumerate() {
        checker.expr(expr, format!("root #{index}"))?;
    }
    Ok(())
}

struct InvariantChecker {
    stage: RuntimeStage,
    strict_value_types: bool,
    strict_type_surfaces: bool,
}

impl InvariantChecker {
    fn expr(&mut self, expr: &Expr, context: String) -> RuntimeResult<()> {
        if self.strict_value_types
            && matches!(
                self.stage,
                RuntimeStage::Monomorphized | RuntimeStage::BeforeVm
            )
            && !matches!(expr.kind, ExprKind::Thunk { .. })
            && runtime_type_has_runtime_fallback_in_value_position(&expr.ty)
        {
            return self.fail(
                format!("{context}: {:?}", expr.ty),
                "runtime expression type must not contain unresolved runtime fallback",
            );
        }
        if self.strict_surfaces_enabled() && !matches!(expr.kind, ExprKind::Thunk { .. }) {
            self.strict_runtime_type_surface(&expr.ty, format!("{context}.ty"))?;
        }
        match &expr.kind {
            ExprKind::Lambda { body, .. } => self.expr(body, format!("{context}/lambda")),
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            } => {
                self.expr(callee, format!("{context}/apply.callee"))?;
                self.expr(arg, format!("{context}/apply.arg"))?;
                if self.strict_surfaces_enabled() {
                    if let Some(evidence) = evidence {
                        self.apply_evidence(evidence, format!("{context}/apply.evidence"))?;
                    }
                    if let Some(instantiation) = instantiation {
                        self.type_instantiation(
                            instantiation,
                            format!("{context}/apply.instantiation"),
                        )?;
                    }
                }
                Ok(())
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                evidence,
            } => {
                self.expr(cond, format!("{context}/if.cond"))?;
                self.expr(then_branch, format!("{context}/if.then"))?;
                self.expr(else_branch, format!("{context}/if.else"))?;
                if self.strict_surfaces_enabled()
                    && let Some(evidence) = evidence
                {
                    self.join_evidence(evidence, format!("{context}/if.evidence"))?;
                }
                Ok(())
            }
            ExprKind::Tuple(items) => {
                for (index, item) in items.iter().enumerate() {
                    self.expr(item, format!("{context}/tuple[{index}]"))?;
                }
                Ok(())
            }
            ExprKind::Record { fields, spread } => {
                for RecordExprField { name, value } in fields {
                    self.expr(value, format!("{context}/record.{}", name.0))?;
                }
                self.record_spread(spread, context)
            }
            ExprKind::Variant { value, .. } => {
                if let Some(value) = value {
                    self.expr(value, format!("{context}/variant"))?;
                }
                Ok(())
            }
            ExprKind::Select { base, .. } => self.expr(base, format!("{context}/select")),
            ExprKind::Match {
                scrutinee,
                arms,
                evidence,
            } => {
                self.expr(scrutinee, format!("{context}/match.scrutinee"))?;
                for (index, arm) in arms.iter().enumerate() {
                    self.match_arm(arm, format!("{context}/match.arm[{index}]"))?;
                }
                if self.strict_surfaces_enabled() {
                    self.join_evidence(evidence, format!("{context}/match.evidence"))?;
                }
                Ok(())
            }
            ExprKind::Block { stmts, tail } => {
                for (index, stmt) in stmts.iter().enumerate() {
                    self.stmt(stmt, format!("{context}/stmt[{index}]"))?;
                }
                if let Some(tail) = tail {
                    self.expr(tail, format!("{context}/tail"))?;
                }
                Ok(())
            }
            ExprKind::Handle {
                body,
                arms,
                handler,
                evidence,
                ..
            } => {
                if !handler.consumes.is_empty() && !matches!(body.ty, RuntimeType::Thunk { .. }) {
                    return self.fail(context, "effectful handler body must be a thunk");
                }
                if self.strict_surfaces_enabled() {
                    self.join_evidence(evidence, format!("{context}/handle.evidence"))?;
                    self.handle_effect(handler, format!("{context}/handle.effect"))?;
                }
                self.expr(body, format!("{context}/handle.body"))?;
                for (index, arm) in arms.iter().enumerate() {
                    self.pattern(
                        &arm.payload,
                        format!("{context}/handle.arm[{index}].payload"),
                    )?;
                    if self.strict_surfaces_enabled()
                        && let Some(resume) = &arm.resume
                    {
                        self.strict_runtime_type_surface(
                            &resume.ty,
                            format!("{context}/handle.arm[{index}].resume"),
                        )?;
                    }
                    if let Some(guard) = &arm.guard {
                        self.expr(guard, format!("{context}/handle.arm[{index}].guard"))?;
                    }
                    self.expr(&arm.body, format!("{context}/handle.arm[{index}].body"))?;
                }
                Ok(())
            }
            ExprKind::BindHere { expr: inner } => {
                if !matches!(inner.ty, RuntimeType::Thunk { .. }) {
                    return self.fail(context, "bind_here must force a thunk");
                }
                self.expr(inner, format!("{context}/bind_here"))
            }
            ExprKind::Thunk {
                effect,
                value,
                expr: inner,
            } => {
                if self.strict_value_types
                    && matches!(self.stage, RuntimeStage::BeforeVm)
                    && runtime_type_has_runtime_fallback_in_value_position(value)
                {
                    return self.fail(
                        context,
                        "VM thunk value type must not contain runtime fallback Any",
                    );
                }
                if self.strict_surfaces_enabled() {
                    self.strict_core_type_surface(effect, format!("{context}/thunk.effect"))?;
                    self.strict_runtime_type_surface(value, format!("{context}/thunk.value"))?;
                }
                match &expr.ty {
                    RuntimeType::Thunk {
                        effect: ty_effect,
                        value: ty_value,
                    } if ty_effect == effect && ty_value.as_ref() == value => {}
                    RuntimeType::Thunk { .. } => {
                        return self.fail(context, "thunk node type must match thunk payload");
                    }
                    _ => return self.fail(context, "thunk node must have thunk type"),
                }
                self.expr(inner, format!("{context}/thunk"))
            }
            ExprKind::LocalPushId { body, .. } => {
                self.expr(body, format!("{context}/local_push_id"))
            }
            ExprKind::AddId { allowed, thunk, .. } => {
                if self.strict_surfaces_enabled() {
                    self.strict_core_type_surface(allowed, format!("{context}/add_id.allowed"))?;
                }
                self.expr(thunk, format!("{context}/add_id"))
            }
            ExprKind::Coerce {
                expr: inner,
                from,
                to,
            } => {
                if self.strict_value_types
                    && matches!(self.stage, RuntimeStage::BeforeVm)
                    && (core_type_has_runtime_fallback_in_value_position(from, false)
                        || core_type_has_runtime_fallback_in_value_position(to, false))
                {
                    return self.fail(
                        context,
                        "VM coerce type must not contain runtime fallback Any",
                    );
                }
                if self.strict_surfaces_enabled() {
                    self.strict_core_type_surface(from, format!("{context}/coerce.from"))?;
                    self.strict_core_type_surface(to, format!("{context}/coerce.to"))?;
                }
                self.expr(inner, format!("{context}/coerce"))
            }
            ExprKind::Pack { expr: inner, .. } => self.expr(inner, format!("{context}/pack")),
            ExprKind::Var(_)
            | ExprKind::EffectOp(_)
            | ExprKind::PrimitiveOp(_)
            | ExprKind::Lit(_)
            | ExprKind::PeekId
            | ExprKind::FindId { .. } => Ok(()),
        }
    }

    fn stmt(&mut self, stmt: &Stmt, context: String) -> RuntimeResult<()> {
        match stmt {
            Stmt::Let { pattern, value } => {
                self.pattern(pattern, format!("{context}/pattern"))?;
                self.expr(value, format!("{context}/let.value"))
            }
            Stmt::Expr(expr) => self.expr(expr, context),
            Stmt::Module { body, .. } => self.expr(body, format!("{context}/module")),
        }
    }

    fn match_arm(&mut self, arm: &MatchArm, context: String) -> RuntimeResult<()> {
        self.pattern(&arm.pattern, format!("{context}/pattern"))?;
        if let Some(guard) = &arm.guard {
            self.expr(guard, format!("{context}/guard"))?;
        }
        self.expr(&arm.body, format!("{context}/body"))
    }

    fn pattern(&mut self, pattern: &Pattern, context: String) -> RuntimeResult<()> {
        if self.strict_value_types
            && matches!(
                self.stage,
                RuntimeStage::Monomorphized | RuntimeStage::BeforeVm
            )
            && runtime_type_has_runtime_fallback_in_value_position(pattern_ty(pattern))
        {
            return self.fail(
                format!("{context}: {:?}", pattern_ty(pattern)),
                "runtime pattern type must not contain unresolved runtime fallback",
            );
        }
        if self.strict_surfaces_enabled() {
            self.strict_runtime_type_surface(pattern_ty(pattern), format!("{context}.ty"))?;
        }
        match pattern {
            Pattern::Tuple { items, .. } | Pattern::List { prefix: items, .. } => {
                for (index, item) in items.iter().enumerate() {
                    self.pattern(item, format!("{context}[{index}]"))?;
                }
                if let Pattern::List { spread, suffix, .. } = pattern {
                    if let Some(spread) = spread {
                        self.pattern(spread, format!("{context}/spread"))?;
                    }
                    for (index, item) in suffix.iter().enumerate() {
                        self.pattern(item, format!("{context}/suffix[{index}]"))?;
                    }
                }
                Ok(())
            }
            Pattern::Record { fields, spread, .. } => {
                for RecordPatternField {
                    name,
                    pattern,
                    default,
                } in fields
                {
                    self.pattern(pattern, format!("{context}.{}", name.0))?;
                    if let Some(default) = default {
                        self.expr(default, format!("{context}.{}.default", name.0))?;
                    }
                }
                self.record_pattern_spread(spread, context)
            }
            Pattern::Variant { value, .. } => {
                if let Some(value) = value {
                    self.pattern(value, format!("{context}/variant"))?;
                }
                Ok(())
            }
            Pattern::Or { left, right, .. } => {
                self.pattern(left, format!("{context}/or.left"))?;
                self.pattern(right, format!("{context}/or.right"))
            }
            Pattern::As { pattern, .. } => self.pattern(pattern, format!("{context}/as")),
            Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => Ok(()),
        }
    }

    fn strict_surfaces_enabled(&self) -> bool {
        self.strict_type_surfaces
            && matches!(
                self.stage,
                RuntimeStage::Monomorphized | RuntimeStage::BeforeVm
            )
    }

    fn apply_evidence(
        &mut self,
        evidence: &typed_ir::ApplyEvidence,
        context: String,
    ) -> RuntimeResult<()> {
        self.type_bounds(&evidence.callee, format!("{context}.callee"))?;
        if let Some(bounds) = &evidence.expected_callee {
            self.type_bounds(bounds, format!("{context}.expected_callee"))?;
        }
        self.type_bounds(&evidence.arg, format!("{context}.arg"))?;
        if let Some(bounds) = &evidence.expected_arg {
            self.type_bounds(bounds, format!("{context}.expected_arg"))?;
        }
        self.type_bounds(&evidence.result, format!("{context}.result"))?;
        if let Some(principal) = &evidence.principal_callee {
            self.strict_core_type_surface(principal, format!("{context}.principal_callee"))?;
        }
        for (index, substitution) in evidence.substitutions.iter().enumerate() {
            self.strict_core_type_surface(
                &substitution.ty,
                format!("{context}.substitution[{index}]"),
            )?;
        }
        for (index, candidate) in evidence.substitution_candidates.iter().enumerate() {
            self.strict_core_type_surface(&candidate.ty, format!("{context}.candidate[{index}]"))?;
        }
        if let Some(plan) = &evidence.principal_elaboration {
            self.principal_elaboration_plan(plan, format!("{context}.principal_elaboration"))?;
        }
        Ok(())
    }

    fn principal_elaboration_plan(
        &mut self,
        plan: &typed_ir::PrincipalElaborationPlan,
        context: String,
    ) -> RuntimeResult<()> {
        self.strict_core_type_surface(
            &plan.principal_callee,
            format!("{context}.principal_callee"),
        )?;
        for (index, substitution) in plan.substitutions.iter().enumerate() {
            self.strict_core_type_surface(
                &substitution.ty,
                format!("{context}.substitution[{index}]"),
            )?;
        }
        for arg in &plan.args {
            self.type_bounds(
                &arg.intrinsic,
                format!("{context}.arg[{}].intrinsic", arg.index),
            )?;
            if let Some(bounds) = &arg.contextual {
                self.type_bounds(bounds, format!("{context}.arg[{}].contextual", arg.index))?;
            }
            if let Some(ty) = &arg.expected_runtime {
                self.strict_core_type_surface(
                    ty,
                    format!("{context}.arg[{}].expected_runtime", arg.index),
                )?;
            }
        }
        self.type_bounds(
            &plan.result.intrinsic,
            format!("{context}.result.intrinsic"),
        )?;
        if let Some(bounds) = &plan.result.contextual {
            self.type_bounds(bounds, format!("{context}.result.contextual"))?;
        }
        if let Some(ty) = &plan.result.expected_runtime {
            self.strict_core_type_surface(ty, format!("{context}.result.expected_runtime"))?;
        }
        for (index, adapter) in plan.adapters.iter().enumerate() {
            self.strict_core_type_surface(
                &adapter.actual,
                format!("{context}.adapter[{index}].actual"),
            )?;
            self.strict_core_type_surface(
                &adapter.expected,
                format!("{context}.adapter[{index}].expected"),
            )?;
        }
        Ok(())
    }

    fn type_instantiation(
        &mut self,
        instantiation: &crate::ir::TypeInstantiation,
        context: String,
    ) -> RuntimeResult<()> {
        for (index, substitution) in instantiation.args.iter().enumerate() {
            self.strict_core_type_surface(&substitution.ty, format!("{context}.arg[{index}]"))?;
        }
        Ok(())
    }

    fn join_evidence(&mut self, evidence: &JoinEvidence, context: String) -> RuntimeResult<()> {
        self.strict_core_type_surface(&evidence.result, format!("{context}.result"))
    }

    fn handle_effect(&mut self, handler: &HandleEffect, context: String) -> RuntimeResult<()> {
        if let Some(ty) = &handler.residual_before {
            self.strict_core_type_surface(ty, format!("{context}.residual_before"))?;
        }
        if let Some(ty) = &handler.residual_after {
            self.strict_core_type_surface(ty, format!("{context}.residual_after"))?;
        }
        Ok(())
    }

    fn type_bounds(&mut self, bounds: &typed_ir::TypeBounds, context: String) -> RuntimeResult<()> {
        if let Some(lower) = bounds.lower.as_deref() {
            self.strict_core_type_surface(lower, format!("{context}.lower"))?;
        }
        if let Some(upper) = bounds.upper.as_deref() {
            self.strict_core_type_surface(upper, format!("{context}.upper"))?;
        }
        if let (Some(lower), Some(upper)) = (bounds.lower.as_deref(), bounds.upper.as_deref())
            && !type_compatible(upper, lower)
        {
            return self.fail(context, "type bounds lower must be compatible with upper");
        }
        Ok(())
    }

    fn strict_runtime_type_surface(
        &mut self,
        ty: &RuntimeType,
        context: String,
    ) -> RuntimeResult<()> {
        if runtime_type_has_unresolved_hole(ty) {
            return self.fail(
                format!("{context}: {:?}", ty),
                "runtime type surface must not contain unresolved type hole",
            );
        }
        Ok(())
    }

    fn strict_core_type_surface(
        &mut self,
        ty: &typed_ir::Type,
        context: String,
    ) -> RuntimeResult<()> {
        if core_type_has_unresolved_hole(ty) {
            return self.fail(
                format!("{context}: {:?}", ty),
                "runtime type surface must not contain unresolved type hole",
            );
        }
        Ok(())
    }

    fn record_spread(
        &mut self,
        spread: &Option<RecordSpreadExpr>,
        context: String,
    ) -> RuntimeResult<()> {
        match spread {
            Some(RecordSpreadExpr::Head(expr)) => self.expr(expr, format!("{context}/spread.head")),
            Some(RecordSpreadExpr::Tail(expr)) => self.expr(expr, format!("{context}/spread.tail")),
            None => Ok(()),
        }
    }

    fn record_pattern_spread(
        &mut self,
        spread: &Option<RecordSpreadPattern>,
        context: String,
    ) -> RuntimeResult<()> {
        match spread {
            Some(RecordSpreadPattern::Head(pattern)) => {
                self.pattern(pattern, format!("{context}/spread.head"))
            }
            Some(RecordSpreadPattern::Tail(pattern)) => {
                self.pattern(pattern, format!("{context}/spread.tail"))
            }
            None => Ok(()),
        }
    }

    fn fail<T>(&self, context: String, message: &'static str) -> RuntimeResult<T> {
        Err(RuntimeError::InvariantViolation {
            stage: self.stage.name(),
            context,
            message,
        })
    }
}

fn path_name(path: &typed_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn pattern_ty(pattern: &Pattern) -> &RuntimeType {
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

fn runtime_type_has_runtime_fallback_in_value_position(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => true,
        RuntimeType::Value(ty) => core_type_has_runtime_fallback_in_value_position(ty, false),
        RuntimeType::Fun { param, ret } => {
            runtime_type_has_runtime_fallback_in_value_position(param)
                || runtime_type_has_runtime_fallback_in_value_position(ret)
        }
        RuntimeType::Thunk { value, .. } => {
            runtime_type_has_runtime_fallback_in_value_position(value)
        }
    }
}

fn runtime_type_has_unresolved_hole(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => true,
        RuntimeType::Value(ty) => core_type_has_unresolved_hole(ty),
        RuntimeType::Fun { param, ret } => {
            runtime_type_has_unresolved_hole(param) || runtime_type_has_unresolved_hole(ret)
        }
        RuntimeType::Thunk { effect, value } => {
            core_type_has_unresolved_hole(effect) || runtime_type_has_unresolved_hole(value)
        }
    }
}

fn core_type_has_unresolved_hole(ty: &typed_ir::Type) -> bool {
    core_type_has_unresolved_hole_inner(ty, &mut BTreeSet::new())
}

fn core_type_has_unresolved_hole_inner(
    ty: &typed_ir::Type,
    bound: &mut BTreeSet<typed_ir::TypeVar>,
) -> bool {
    match ty {
        typed_ir::Type::Unknown => true,
        typed_ir::Type::Var(var) => !bound.contains(var),
        typed_ir::Type::Named { args, .. } => args.iter().any(|arg| match arg {
            typed_ir::TypeArg::Type(ty) => core_type_has_unresolved_hole_inner(ty, bound),
            typed_ir::TypeArg::Bounds(bounds) => {
                bounds
                    .lower
                    .as_deref()
                    .is_some_and(|ty| core_type_has_unresolved_hole_inner(ty, bound))
                    || bounds
                        .upper
                        .as_deref()
                        .is_some_and(|ty| core_type_has_unresolved_hole_inner(ty, bound))
            }
        }),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_has_unresolved_hole_inner(param, bound)
                || core_type_has_unresolved_hole_inner(param_effect, bound)
                || core_type_has_unresolved_hole_inner(ret_effect, bound)
                || core_type_has_unresolved_hole_inner(ret, bound)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items
            .iter()
            .any(|item| core_type_has_unresolved_hole_inner(item, bound)),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| core_type_has_unresolved_hole_inner(&field.value, bound))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        core_type_has_unresolved_hole_inner(ty, bound)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant.cases.iter().any(|case| {
                case.payloads
                    .iter()
                    .any(|payload| core_type_has_unresolved_hole_inner(payload, bound))
            }) || variant
                .tail
                .as_deref()
                .is_some_and(|tail| core_type_has_unresolved_hole_inner(tail, bound))
        }
        typed_ir::Type::Row { items, tail } => {
            items
                .iter()
                .any(|item| core_type_has_unresolved_hole_inner(item, bound))
                || core_type_has_unresolved_hole_inner(tail, bound)
        }
        typed_ir::Type::Recursive { var, body } => {
            let inserted = bound.insert(var.clone());
            let has_hole = core_type_has_unresolved_hole_inner(body, bound);
            if inserted {
                bound.remove(var);
            }
            has_hole
        }
        typed_ir::Type::Never | typed_ir::Type::Any => false,
    }
}

fn core_type_has_runtime_fallback_in_value_position(
    ty: &typed_ir::Type,
    effect_slot: bool,
) -> bool {
    match ty {
        typed_ir::Type::Unknown => !effect_slot,
        typed_ir::Type::Any => !effect_slot && core_type_is_runtime_projection_fallback(ty),
        typed_ir::Type::Named { args, .. } => {
            args.iter().any(|arg| match arg {
                typed_ir::TypeArg::Type(ty) => {
                    core_type_has_runtime_fallback_in_value_position(ty, false)
                }
                typed_ir::TypeArg::Bounds(bounds) => {
                    bounds.lower.as_deref().is_some_and(|ty| {
                        core_type_has_runtime_fallback_in_value_position(ty, false)
                    }) || bounds.upper.as_deref().is_some_and(|ty| {
                        core_type_has_runtime_fallback_in_value_position(ty, false)
                    })
                }
            })
        }
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_has_runtime_fallback_in_value_position(param, false)
                || core_type_has_runtime_fallback_in_value_position(param_effect, true)
                || core_type_has_runtime_fallback_in_value_position(ret_effect, true)
                || core_type_has_runtime_fallback_in_value_position(ret, false)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items
            .iter()
            .any(|item| core_type_has_runtime_fallback_in_value_position(item, false)),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| core_type_has_runtime_fallback_in_value_position(&field.value, false))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        core_type_has_runtime_fallback_in_value_position(ty, false)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant.cases.iter().any(|case| {
                case.payloads
                    .iter()
                    .any(|payload| core_type_has_runtime_fallback_in_value_position(payload, false))
            }) || variant
                .tail
                .as_deref()
                .is_some_and(|tail| core_type_has_runtime_fallback_in_value_position(tail, false))
        }
        typed_ir::Type::Row { items, tail } => {
            items
                .iter()
                .any(|item| core_type_has_runtime_fallback_in_value_position(item, true))
                || core_type_has_runtime_fallback_in_value_position(tail, true)
        }
        typed_ir::Type::Recursive { body, .. } => {
            core_type_has_runtime_fallback_in_value_position(body, effect_slot)
        }
        typed_ir::Type::Var(_) | typed_ir::Type::Never => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Binding, EffectIdRef, Root};

    #[test]
    fn accepts_add_id_that_does_not_wrap_thunk_as_noop() {
        let module = module_with_expr(Expr::typed(
            ExprKind::AddId {
                id: EffectIdRef::Peek,
                allowed: named("io"),
                active: false,
                thunk: Box::new(Expr::typed(ExprKind::Lit(typed_ir::Lit::Unit), unit())),
            },
            unit(),
        ));

        check_runtime_invariants(&module, RuntimeStage::Lowered).unwrap();
    }

    #[test]
    fn rejects_bind_here_that_does_not_force_thunk() {
        let module = module_with_expr(Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(Expr::typed(ExprKind::Lit(typed_ir::Lit::Unit), unit())),
            },
            unit(),
        ));

        let err = check_runtime_invariants(&module, RuntimeStage::Lowered).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "bind_here must force a thunk",
                ..
            }
        ));
    }

    #[test]
    fn rejects_thunk_node_with_mismatched_type() {
        let module = module_with_expr(Expr::typed(
            ExprKind::Thunk {
                effect: named("io"),
                value: RuntimeType::value(unit()),
                expr: Box::new(Expr::typed(ExprKind::Lit(typed_ir::Lit::Unit), unit())),
            },
            RuntimeType::thunk(named("other"), RuntimeType::value(unit())),
        ));

        let err = check_runtime_invariants(&module, RuntimeStage::Lowered).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "thunk node type must match thunk payload",
                ..
            }
        ));
    }

    #[test]
    fn rejects_polymorphic_binding_before_vm() {
        let mut module = module_with_expr(Expr::typed(ExprKind::Lit(typed_ir::Lit::Unit), unit()));
        module.bindings[0].type_params = vec![typed_ir::TypeVar("a".to_string())];

        let err = check_runtime_invariants(&module, RuntimeStage::BeforeVm).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "VM input binding must be monomorphic",
                ..
            }
        ));
    }

    #[test]
    fn rejects_any_thunk_value_type_before_vm() {
        let module = module_with_expr(Expr::typed(
            ExprKind::Thunk {
                effect: named("io"),
                value: RuntimeType::value(typed_ir::Type::Unknown),
                expr: Box::new(Expr::typed(ExprKind::Lit(typed_ir::Lit::Unit), unit())),
            },
            RuntimeType::thunk(named("io"), RuntimeType::value(typed_ir::Type::Unknown)),
        ));

        let err = check_strict_runtime_value_types(&module, RuntimeStage::BeforeVm).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "VM thunk value type must not contain runtime fallback Any",
                ..
            }
        ));
    }

    #[test]
    fn rejects_any_coerce_type_before_vm() {
        let module = module_with_expr(Expr::typed(
            ExprKind::Coerce {
                from: unit(),
                to: typed_ir::Type::Unknown,
                expr: Box::new(Expr::typed(ExprKind::Lit(typed_ir::Lit::Unit), unit())),
            },
            unit(),
        ));

        let err = check_strict_runtime_value_types(&module, RuntimeStage::BeforeVm).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "VM coerce type must not contain runtime fallback Any",
                ..
            }
        ));
    }

    #[test]
    fn rejects_unknown_expression_type_after_monomorphize() {
        let module = module_with_expr(Expr::typed(
            ExprKind::Lit(typed_ir::Lit::Unit),
            RuntimeType::Unknown,
        ));

        let err =
            check_strict_runtime_type_surfaces(&module, RuntimeStage::Monomorphized).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "runtime expression type must not contain unresolved runtime fallback",
                ..
            }
        ));
    }

    #[test]
    fn rejects_unknown_pattern_type_after_monomorphize() {
        let module = module_with_expr(Expr::typed(
            ExprKind::Block {
                stmts: vec![Stmt::Let {
                    pattern: Pattern::Bind {
                        name: typed_ir::Name("x".to_string()),
                        ty: RuntimeType::Unknown,
                    },
                    value: Expr::typed(ExprKind::Lit(typed_ir::Lit::Unit), unit()),
                }],
                tail: Some(Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Unit),
                    unit(),
                ))),
            },
            RuntimeType::value(unit()),
        ));

        let err =
            check_strict_runtime_type_surfaces(&module, RuntimeStage::Monomorphized).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "runtime pattern type must not contain unresolved runtime fallback",
                ..
            }
        ));
    }

    #[test]
    fn rejects_unknown_add_id_allowed_after_monomorphize() {
        let module = module_with_expr(Expr::typed(
            ExprKind::AddId {
                id: EffectIdRef::Peek,
                allowed: typed_ir::Type::Unknown,
                active: true,
                thunk: Box::new(unit_thunk()),
            },
            RuntimeType::thunk(typed_ir::Type::Never, RuntimeType::value(unit())),
        ));

        let err =
            check_strict_runtime_type_surfaces(&module, RuntimeStage::Monomorphized).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "runtime type surface must not contain unresolved type hole",
                ..
            }
        ));
    }

    #[test]
    fn rejects_unknown_handle_effect_after_monomorphize() {
        let module = module_with_expr(Expr::typed(
            ExprKind::Handle {
                body: Box::new(unit_expr()),
                arms: Vec::new(),
                evidence: JoinEvidence { result: unit() },
                handler: HandleEffect {
                    consumes: Vec::new(),
                    residual_before: Some(typed_ir::Type::Unknown),
                    residual_after: None,
                },
            },
            RuntimeType::value(unit()),
        ));

        let err =
            check_strict_runtime_type_surfaces(&module, RuntimeStage::Monomorphized).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "runtime type surface must not contain unresolved type hole",
                ..
            }
        ));
    }

    #[test]
    fn rejects_unknown_apply_evidence_after_monomorphize() {
        let module = module_with_expr(apply_expr_with_evidence(typed_ir::ApplyEvidence {
            callee_source_edge: None,
            arg_source_edge: None,
            callee: typed_ir::TypeBounds::exact(fun_type(unit(), unit())),
            expected_callee: None,
            arg: typed_ir::TypeBounds::exact(unit()),
            expected_arg: None,
            result: typed_ir::TypeBounds::exact(unit()),
            principal_callee: None,
            substitutions: Vec::new(),
            substitution_candidates: vec![typed_ir::PrincipalSubstitutionCandidate {
                var: typed_ir::TypeVar("a".to_string()),
                relation: typed_ir::PrincipalCandidateRelation::Exact,
                ty: typed_ir::Type::Unknown,
                source_edge: None,
                path: Vec::new(),
            }],
            role_method: false,
            principal_elaboration: None,
        }));

        let err =
            check_strict_runtime_type_surfaces(&module, RuntimeStage::Monomorphized).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "runtime type surface must not contain unresolved type hole",
                ..
            }
        ));
    }

    #[test]
    fn rejects_conflicting_apply_evidence_bounds_after_monomorphize() {
        let module = module_with_expr(apply_expr_with_evidence(typed_ir::ApplyEvidence {
            callee_source_edge: None,
            arg_source_edge: None,
            callee: typed_ir::TypeBounds {
                lower: Some(Box::new(named("int"))),
                upper: Some(Box::new(named("str"))),
            },
            expected_callee: None,
            arg: typed_ir::TypeBounds::exact(unit()),
            expected_arg: None,
            result: typed_ir::TypeBounds::exact(unit()),
            principal_callee: None,
            substitutions: Vec::new(),
            substitution_candidates: Vec::new(),
            role_method: false,
            principal_elaboration: None,
        }));

        let err =
            check_strict_runtime_type_surfaces(&module, RuntimeStage::Monomorphized).unwrap_err();

        assert!(matches!(
            err,
            RuntimeError::InvariantViolation {
                message: "type bounds lower must be compatible with upper",
                ..
            }
        ));
    }

    fn module_with_expr(expr: Expr) -> Module {
        Module {
            path: typed_ir::Path::default(),
            bindings: vec![Binding {
                name: typed_ir::Path::from_name(typed_ir::Name("main".to_string())),
                type_params: Vec::new(),
                scheme: typed_ir::Scheme {
                    requirements: Vec::new(),
                    body: unit(),
                },
                body: expr,
            }],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(typed_ir::Path::from_name(typed_ir::Name(
                "main".to_string(),
            )))],
            role_impls: Vec::new(),
        }
    }

    fn apply_expr_with_evidence(evidence: typed_ir::ApplyEvidence) -> Expr {
        Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Var(typed_ir::Path::from_name(typed_ir::Name("f".to_string()))),
                    RuntimeType::fun(RuntimeType::value(unit()), RuntimeType::value(unit())),
                )),
                arg: Box::new(unit_expr()),
                evidence: Some(evidence),
                instantiation: None,
            },
            RuntimeType::value(unit()),
        )
    }

    fn unit_expr() -> Expr {
        Expr::typed(
            ExprKind::Lit(typed_ir::Lit::Unit),
            RuntimeType::value(unit()),
        )
    }

    fn unit_thunk() -> Expr {
        Expr::typed(
            ExprKind::Thunk {
                effect: typed_ir::Type::Never,
                value: RuntimeType::value(unit()),
                expr: Box::new(unit_expr()),
            },
            RuntimeType::thunk(typed_ir::Type::Never, RuntimeType::value(unit())),
        )
    }

    fn unit() -> typed_ir::Type {
        named("unit")
    }

    fn fun_type(param: typed_ir::Type, ret: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(ret),
        }
    }

    fn named(name: &str) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }
}
