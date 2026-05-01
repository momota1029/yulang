use std::collections::{HashMap, HashSet};

use super::*;
use crate::ir::{Binding, Expr, ExprKind, HandleArm, Module, Pattern, Stmt, Type as RuntimeType};

pub struct DemandChecker<'a> {
    bindings: HashMap<core_ir::Path, &'a Binding>,
    generic_bindings: HashSet<core_ir::Path>,
}

impl<'a> DemandChecker<'a> {
    pub fn from_module(module: &'a Module) -> Self {
        Self {
            bindings: module
                .bindings
                .iter()
                .map(|binding| (binding.name.clone(), binding))
                .collect(),
            generic_bindings: module
                .bindings
                .iter()
                .filter(|binding| !binding.type_params.is_empty())
                .map(|binding| binding.name.clone())
                .collect(),
        }
    }

    pub fn check_demand(&self, demand: &Demand) -> Result<CheckedDemand, DemandCheckError> {
        let binding = self
            .bindings
            .get(&demand.target)
            .copied()
            .ok_or_else(|| DemandCheckError::MissingBinding(demand.target.clone()))?;
        let mut checker = ExprChecker::new(&self.generic_bindings);
        let actual = checker.check_expr(&binding.body, &demand.key.signature)?;
        let (substitutions, child_demands) = checker.finish();
        Ok(CheckedDemand {
            target: demand.target.clone(),
            expected: demand.key.signature.clone(),
            actual,
            solved: substitutions.apply_signature(&demand.key.signature),
            substitutions,
            child_demands,
        })
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
    locals: HashMap<core_ir::Path, DemandSignature>,
    next_hole: u32,
    unifier: DemandUnifier,
    child_demands: Vec<PendingChildDemand>,
}

struct PendingChildDemand {
    target: core_ir::Path,
    expected: RuntimeType,
    signature: DemandSignature,
}

impl<'a> ExprChecker<'a> {
    fn new(generic_bindings: &'a HashSet<core_ir::Path>) -> Self {
        Self {
            generic_bindings,
            locals: HashMap::new(),
            next_hole: 0,
            unifier: DemandUnifier::new(),
            child_demands: Vec::new(),
        }
    }

    fn check_expr(
        &mut self,
        expr: &Expr,
        expected: &DemandSignature,
    ) -> Result<DemandSignature, DemandCheckError> {
        self.next_hole = self.next_hole.max(expected.next_hole_after());
        let actual = self.synth_expr(expr, Some(expected))?;
        self.unifier.unify(expected, &actual)?;
        Ok(actual)
    }

    fn synth_expr(
        &mut self,
        expr: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
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
            ExprKind::Coerce { expr: inner, .. } | ExprKind::Pack { expr: inner, .. } => {
                self.synth_expr(inner, expected)
            }
            ExprKind::Apply { callee, arg, .. } => {
                if let Some((target, args)) = applied_call(expr)
                    && self.generic_bindings.contains(target)
                {
                    let ret = expected
                        .cloned()
                        .unwrap_or_else(|| self.signature_from_type(&expr.ty));
                    let arg_signatures = args
                        .iter()
                        .map(|arg| self.synth_expr(arg, None))
                        .collect::<Result<Vec<_>, _>>()?;
                    let signature = curried_signatures(&arg_signatures, ret.clone());
                    self.child_demands.push(PendingChildDemand {
                        target: target.clone(),
                        expected: curried_call_type(&args, expr.ty.clone()),
                        signature,
                    });
                    return Ok(ret);
                }
                let callee = self.synth_expr(callee, None)?;
                let DemandSignature::Fun { param, ret } = callee else {
                    return Ok(self.signature_from_type(&expr.ty));
                };
                self.check_expr(arg, &param)?;
                Ok(*ret)
            }
            ExprKind::Var(path) => Ok(self
                .locals
                .get(path)
                .cloned()
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
        let DemandSignature::Fun {
            param: param_ty,
            ret,
        } = &expected
        else {
            return Ok(expected);
        };
        let local = core_ir::Path::from_name(param.clone());
        let previous = self.locals.insert(local.clone(), param_ty.as_ref().clone());
        self.check_expr(body, ret)?;
        restore_local(&mut self.locals, local, previous);
        Ok(expected)
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
        let scrutinee_ty = self.synth_expr(scrutinee, None)?;
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
            for (local, previous) in inserted.into_iter().rev() {
                restore_local(&mut self.locals, local, previous);
            }
        }
        Ok(result_ty)
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
        for (local, previous) in inserted.into_iter().rev() {
            restore_local(&mut self.locals, local, previous);
        }
        result
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
        for arm in arms {
            self.check_handle_arm(arm, &body_ty, &result_ty)?;
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
            None
        };
        self.push_pattern_bindings(&arm.payload, payload_hint.as_ref(), &mut inserted);
        if let Some(resume) = &arm.resume {
            let local = core_ir::Path::from_name(resume.name.clone());
            let ty = self.resume_signature_from_context(&resume.ty, handled_body_ty);
            let previous = self.locals.insert(local.clone(), ty);
            inserted.push((local, previous));
        }
        if let Some(guard) = &arm.guard {
            self.check_expr(guard, &DemandSignature::Core(named_core("bool")))?;
        }
        self.check_expr(&arm.body, expected)?;
        for (local, previous) in inserted.into_iter().rev() {
            restore_local(&mut self.locals, local, previous);
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
            let effect = thunk_effect_signature(&inner.ty)
                .unwrap_or_else(|| DemandEffect::Hole(self.fresh_hole()));
            let thunk = DemandSignature::Thunk {
                effect,
                value: Box::new(expected.clone()),
            };
            self.check_expr(inner, &thunk)?;
            return Ok(expected.clone());
        }
        match self.synth_expr(inner, None)? {
            DemandSignature::Thunk { value, .. } => Ok(*value),
            _ => Ok(self.signature_from_type(&expr.ty)),
        }
    }

    fn synth_thunk(
        &mut self,
        expr: &Expr,
        effect: &core_ir::Type,
        value: &RuntimeType,
        inner: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<DemandSignature, DemandCheckError> {
        let expected = expected.cloned().unwrap_or_else(|| DemandSignature::Thunk {
            effect: self.effect_from_core_type(effect),
            value: Box::new(self.signature_from_type(value)),
        });
        let DemandSignature::Thunk {
            effect: _,
            value: expected_value,
        } = &expected
        else {
            return Ok(self.signature_from_type(&expr.ty));
        };
        self.check_expr(inner, expected_value)?;
        Ok(expected)
    }

    fn synth_stmt(
        &mut self,
        stmt: &Stmt,
    ) -> Result<Vec<(core_ir::Path, Option<DemandSignature>)>, DemandCheckError> {
        match stmt {
            Stmt::Let { pattern, value } => {
                let value = self.synth_expr(value, None)?;
                let mut inserted = Vec::new();
                self.push_pattern_bindings(pattern, Some(&signature_value(&value)), &mut inserted);
                Ok(inserted)
            }
            Stmt::Expr(expr) => {
                self.synth_expr(expr, None)?;
                Ok(Vec::new())
            }
            Stmt::Module { def, body } => {
                let local = def.clone();
                let placeholder = self.signature_from_type(&body.ty);
                let previous = self.locals.insert(local.clone(), placeholder);
                let body = self.synth_expr(body, None)?;
                self.locals.insert(local.clone(), body);
                Ok(vec![(local, previous)])
            }
        }
    }

    fn finish(self) -> (DemandSubstitution, DemandQueue) {
        let substitutions = self.unifier.finish();
        let mut child_demands = DemandQueue::default();
        for child in self.child_demands {
            child_demands.push_signature(
                child.target,
                child.expected,
                substitutions.apply_signature(&child.signature),
            );
        }
        (substitutions, child_demands)
    }

    fn signature_from_type(&mut self, ty: &RuntimeType) -> DemandSignature {
        DemandSignature::from_runtime_type_with_holes(ty, &mut self.next_hole)
    }

    fn effect_from_core_type(&mut self, ty: &core_ir::Type) -> DemandEffect {
        DemandEffect::from_core_type_with_holes(ty, &mut self.next_hole)
    }

    fn resume_signature_from_context(
        &mut self,
        ty: &RuntimeType,
        handled_body_ty: &DemandSignature,
    ) -> DemandSignature {
        let RuntimeType::Fun { param, .. } = ty else {
            return self.signature_from_type(ty);
        };
        DemandSignature::Fun {
            param: Box::new(self.signature_from_type(param)),
            ret: Box::new(handled_body_ty.clone()),
        }
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
        inserted: &mut Vec<(core_ir::Path, Option<DemandSignature>)>,
    ) {
        match pattern {
            Pattern::Bind { name, ty } => {
                let local = core_ir::Path::from_name(name.clone());
                let signature = expected
                    .cloned()
                    .unwrap_or_else(|| self.signature_from_type(ty));
                let previous = self.locals.insert(local.clone(), signature);
                inserted.push((local, previous));
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
                let expected_payload = expected.and_then(|expected| match expected {
                    DemandSignature::Core(DemandCoreType::Variant(cases)) => cases
                        .iter()
                        .find(|case| case.name == *tag)
                        .and_then(|case| case.payloads.first())
                        .map(|payload| DemandSignature::Core(payload.clone())),
                    _ => None,
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
                inserted.push((local, previous));
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

fn signature_core_value(signature: &DemandSignature) -> DemandCoreType {
    match signature {
        DemandSignature::Hole(id) => DemandCoreType::Hole(*id),
        DemandSignature::Core(ty) => ty.clone(),
        DemandSignature::Fun { param, ret } => {
            let (param, param_effect) = signature_effected_core_value(param);
            let (ret, ret_effect) = signature_effected_core_value(ret);
            DemandCoreType::Fun {
                param: Box::new(param),
                param_effect: Box::new(param_effect),
                ret_effect: Box::new(ret_effect),
                ret: Box::new(ret),
            }
        }
        DemandSignature::Thunk { value, .. } => signature_core_value(value),
    }
}

fn signature_value(signature: &DemandSignature) -> DemandSignature {
    match signature {
        DemandSignature::Thunk { value, .. } => signature_value(value),
        other => other.clone(),
    }
}

fn signature_effected_core_value(signature: &DemandSignature) -> (DemandCoreType, DemandEffect) {
    match signature {
        DemandSignature::Thunk { effect, value } => (signature_core_value(value), effect.clone()),
        other => (signature_core_value(other), DemandEffect::Empty),
    }
}

fn thunk_effect_signature(ty: &RuntimeType) -> Option<DemandEffect> {
    match ty {
        RuntimeType::Thunk { effect, .. } => Some(DemandEffect::from_core_type(effect)),
        _ => None,
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

pub(super) fn curried_signatures(
    args: &[DemandSignature],
    ret: DemandSignature,
) -> DemandSignature {
    args.iter()
        .rev()
        .fold(ret, |ret, arg| DemandSignature::Fun {
            param: Box::new(arg.clone()),
            ret: Box::new(ret),
        })
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

    fn named_demand(name: &str) -> DemandCoreType {
        DemandCoreType::Named {
            path: path(name),
            args: Vec::new(),
        }
    }

    fn path(name: &str) -> core_ir::Path {
        core_ir::Path::from_name(core_ir::Name(name.to_string()))
    }
}
