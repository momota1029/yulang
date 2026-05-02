use std::collections::HashMap;

use super::*;
use crate::ir::{
    Binding, EffectIdRef, EffectIdVar, Expr, ExprKind, MatchArm, Module, Pattern, RecordExprField,
    RecordSpreadExpr, Stmt, Type as RuntimeType,
};
use crate::types::{runtime_core_type, thunk_effect};

pub struct DemandEmitter<'a> {
    bindings: HashMap<core_ir::Path, &'a Binding>,
    ordered_specializations: &'a [DemandSpecialization],
    specializations: HashMap<DemandKey, &'a DemandSpecialization>,
    checked: HashMap<DemandKey, &'a CheckedDemand>,
}

impl<'a> DemandEmitter<'a> {
    pub fn from_module(module: &'a Module, specializations: &'a [DemandSpecialization]) -> Self {
        Self::from_module_with_known(module, specializations, specializations)
    }

    pub fn from_module_with_known(
        module: &'a Module,
        emit_specializations: &'a [DemandSpecialization],
        known_specializations: &'a [DemandSpecialization],
    ) -> Self {
        Self::from_module_with_checked(module, emit_specializations, known_specializations, &[])
    }

    pub fn from_module_with_checked(
        module: &'a Module,
        emit_specializations: &'a [DemandSpecialization],
        known_specializations: &'a [DemandSpecialization],
        checked: &'a [CheckedDemand],
    ) -> Self {
        Self {
            bindings: module
                .bindings
                .iter()
                .map(|binding| (binding.name.clone(), binding))
                .collect(),
            ordered_specializations: emit_specializations,
            specializations: known_specializations
                .iter()
                .map(|specialization| (specialization.key.clone(), specialization))
                .collect(),
            checked: checked
                .iter()
                .map(|checked| {
                    (
                        DemandKey::from_signature(checked.target.clone(), checked.expected.clone()),
                        checked,
                    )
                })
                .collect(),
        }
    }

    pub fn emit_all(&self) -> Result<Vec<Binding>, DemandEmitError> {
        self.emit_all_report().map(|output| output.bindings)
    }

    pub fn emit_all_report(&self) -> Result<DemandEmitAllOutput, DemandEmitError> {
        let mut bindings = Vec::with_capacity(self.ordered_specializations.len());
        let mut missing_demands = Vec::new();
        for specialization in self.ordered_specializations {
            let output = self.emit_report(specialization)?;
            bindings.push(output.binding);
            missing_demands.extend(output.missing_demands);
        }
        Ok(DemandEmitAllOutput {
            bindings,
            missing_demands,
        })
    }

    pub fn rewrite_module_uses(&self, module: Module) -> Result<Module, DemandEmitError> {
        self.rewrite_module_uses_report(module)
            .map(|output| output.module)
    }

    pub fn rewrite_module_uses_report(
        &self,
        module: Module,
    ) -> Result<DemandRewriteOutput, DemandEmitError> {
        rewrite_module_uses_with_context(module, &self.specializations, &self.checked)
    }

    pub fn rewrite_module_uses_with_specializations(
        module: Module,
        specializations: &'a [DemandSpecialization],
    ) -> Result<Module, DemandEmitError> {
        let specializations = specializations
            .iter()
            .map(|specialization| (specialization.key.clone(), specialization))
            .collect::<HashMap<_, _>>();
        rewrite_module_uses_with_context(module, &specializations, &HashMap::new())
            .map(|output| output.module)
    }

    pub fn rewrite_module_uses_with_specializations_report(
        module: Module,
        specializations: &'a [DemandSpecialization],
    ) -> Result<DemandRewriteOutput, DemandEmitError> {
        let specializations = specializations
            .iter()
            .map(|specialization| (specialization.key.clone(), specialization))
            .collect::<HashMap<_, _>>();
        rewrite_module_uses_with_context(module, &specializations, &HashMap::new())
    }

    pub fn rewrite_module_uses_with_checked_report(
        module: Module,
        specializations: &'a [DemandSpecialization],
        checked: &'a [CheckedDemand],
    ) -> Result<DemandRewriteOutput, DemandEmitError> {
        let specializations = specializations
            .iter()
            .map(|specialization| (specialization.key.clone(), specialization))
            .collect::<HashMap<_, _>>();
        let checked = checked
            .iter()
            .map(|checked| {
                (
                    DemandKey::from_signature(checked.target.clone(), checked.expected.clone()),
                    checked,
                )
            })
            .collect::<HashMap<_, _>>();
        rewrite_module_uses_with_context(module, &specializations, &checked)
    }

    pub fn emit(&self, specialization: &DemandSpecialization) -> Result<Binding, DemandEmitError> {
        self.emit_report(specialization)
            .map(|output| output.binding)
    }

    pub fn emit_report(
        &self,
        specialization: &DemandSpecialization,
    ) -> Result<DemandEmitBindingOutput, DemandEmitError> {
        self.emit_inner(specialization)
            .map_err(|source| DemandEmitError::Specialization {
                target: specialization.target.clone(),
                path: specialization.path.clone(),
                source: Box::new(source),
            })
    }

    fn emit_inner(
        &self,
        specialization: &DemandSpecialization,
    ) -> Result<DemandEmitBindingOutput, DemandEmitError> {
        let original = self
            .bindings
            .get(&specialization.target)
            .copied()
            .ok_or_else(|| DemandEmitError::MissingBinding(specialization.target.clone()))?;
        let solved_ty = runtime_type(&specialization.solved)?;
        let checked = self.checked.get(&specialization.key);
        let mut rewriter = BodyEmitter::new(&self.specializations)
            .with_current_specialization(specialization)
            .with_checked_locals(checked.map(|checked| &checked.local_signatures))
            .with_next_effect_id(next_effect_id_after_expr(&original.body));
        let mut body = rewriter.rewrite_expr(&original.body, Some(&specialization.solved))?;
        let missing_demands = rewriter.into_missing_demands();
        body.ty = solved_ty;
        Ok(DemandEmitBindingOutput {
            binding: Binding {
                name: specialization.path.clone(),
                type_params: Vec::new(),
                scheme: core_ir::Scheme {
                    requirements: Vec::new(),
                    body: runtime_core_type(&body.ty),
                },
                body,
            },
            missing_demands,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DemandEmitAllOutput {
    pub bindings: Vec<Binding>,
    pub missing_demands: Vec<MissingDemand>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DemandEmitBindingOutput {
    pub binding: Binding,
    pub missing_demands: Vec<MissingDemand>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MissingDemand {
    pub target: core_ir::Path,
    pub signature: DemandSignature,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DemandRewriteOutput {
    pub module: Module,
    pub changed_roots: usize,
    pub changed_bindings: usize,
    pub missing_demands: Vec<MissingDemand>,
}

fn rewrite_module_uses_with_context(
    module: Module,
    specializations: &HashMap<DemandKey, &DemandSpecialization>,
    checked: &HashMap<DemandKey, &CheckedDemand>,
) -> Result<DemandRewriteOutput, DemandEmitError> {
    let specializations_by_path = specializations
        .values()
        .map(|specialization| (specialization.path.clone(), *specialization))
        .collect::<HashMap<_, _>>();
    let mut changed_roots = 0;
    let mut missing_demands = Vec::new();
    let mut root_exprs = Vec::with_capacity(module.root_exprs.len());
    for (index, expr) in module.root_exprs.into_iter().enumerate() {
        let rewritten = rewrite_root_expr(expr.clone(), specializations).map_err(|source| {
            DemandEmitError::RootRewrite {
                index,
                source: Box::new(source),
            }
        })?;
        if rewritten.expr != expr {
            changed_roots += 1;
        }
        missing_demands.extend(rewritten.missing_demands);
        root_exprs.push(rewritten.expr);
    }

    let mut changed_bindings = 0;
    let mut bindings = Vec::with_capacity(module.bindings.len());
    for binding in module.bindings.into_iter() {
        let path = binding.name.clone();
        let rewritten = rewrite_binding_uses(
            binding.clone(),
            specializations,
            &specializations_by_path,
            checked,
        )
        .map_err(|source| DemandEmitError::BindingRewrite {
            path,
            source: Box::new(source),
        })?;
        if rewritten.binding != binding {
            changed_bindings += 1;
        }
        missing_demands.extend(rewritten.missing_demands);
        bindings.push(rewritten.binding);
    }

    Ok(DemandRewriteOutput {
        module: Module {
            path: module.path,
            bindings,
            root_exprs,
            roots: module.roots,
        },
        changed_roots,
        changed_bindings,
        missing_demands,
    })
}

struct DemandExprRewriteOutput {
    expr: Expr,
    missing_demands: Vec<MissingDemand>,
}

struct DemandBindingRewriteOutput {
    binding: Binding,
    missing_demands: Vec<MissingDemand>,
}

fn rewrite_root_expr(
    expr: Expr,
    specializations: &HashMap<DemandKey, &DemandSpecialization>,
) -> Result<DemandExprRewriteOutput, DemandEmitError> {
    let expected = DemandSignature::from_runtime_type(&expr.ty);
    let expected = expected.is_closed().then_some(expected);
    let mut rewriter = BodyEmitter::new(specializations);
    let expr = rewriter.rewrite_expr(&expr, expected.as_ref())?;
    Ok(DemandExprRewriteOutput {
        expr,
        missing_demands: rewriter.into_missing_demands(),
    })
}

fn rewrite_binding_uses(
    binding: Binding,
    specializations: &HashMap<DemandKey, &DemandSpecialization>,
    specializations_by_path: &HashMap<core_ir::Path, &DemandSpecialization>,
    checked: &HashMap<DemandKey, &CheckedDemand>,
) -> Result<DemandBindingRewriteOutput, DemandEmitError> {
    if binding_needs_demand_monomorphization(&binding) {
        return Ok(DemandBindingRewriteOutput {
            binding,
            missing_demands: Vec::new(),
        });
    }
    let current_specialization = specializations_by_path.get(&binding.name).copied();
    let expected = current_specialization
        .map(|specialization| specialization.solved.clone())
        .unwrap_or_else(|| DemandSignature::from_runtime_type(&binding.body.ty));
    let expected = expected.is_closed().then_some(expected);
    let mut rewriter = BodyEmitter::new(specializations);
    if let Some(specialization) = current_specialization {
        rewriter = rewriter.with_current_specialization(specialization);
        rewriter = rewriter.with_checked_locals(
            checked
                .get(&specialization.key)
                .map(|checked| &checked.local_signatures),
        );
    }
    let body = match rewriter.rewrite_expr(&binding.body, expected.as_ref()) {
        Ok(body) => body,
        Err(error)
            if is_legacy_mono_binding(&binding.name)
                && is_recoverable_legacy_rewrite_error(&error) =>
        {
            return Ok(DemandBindingRewriteOutput {
                binding,
                missing_demands: Vec::new(),
            });
        }
        Err(error) => return Err(error),
    };
    Ok(DemandBindingRewriteOutput {
        binding: Binding { body, ..binding },
        missing_demands: rewriter.into_missing_demands(),
    })
}

fn is_legacy_mono_binding(path: &core_ir::Path) -> bool {
    path.segments
        .last()
        .and_then(|name| name.0.rsplit_once("__mono"))
        .is_some_and(|(_, suffix)| suffix.chars().all(|ch| ch.is_ascii_digit()))
}

fn is_recoverable_legacy_rewrite_error(error: &DemandEmitError) -> bool {
    matches!(
        error,
        DemandEmitError::UnresolvedValueHole(_)
            | DemandEmitError::UnresolvedCoreHole(_)
            | DemandEmitError::UnresolvedEffectHole(_)
    )
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DemandEmitError {
    MissingBinding(core_ir::Path),
    UnresolvedValueHole(u32),
    UnresolvedCoreHole(u32),
    UnresolvedEffectHole(u32),
    NonFunctionCall(DemandSignature),
    RootRewrite {
        index: usize,
        source: Box<DemandEmitError>,
    },
    BindingRewrite {
        path: core_ir::Path,
        source: Box<DemandEmitError>,
    },
    Specialization {
        target: core_ir::Path,
        path: core_ir::Path,
        source: Box<DemandEmitError>,
    },
}

struct BodyEmitter<'a> {
    specializations: &'a HashMap<DemandKey, &'a DemandSpecialization>,
    current_specialization: Option<&'a DemandSpecialization>,
    enclosing_thunk_effects: Vec<DemandEffect>,
    locals: HashMap<core_ir::Path, DemandSignature>,
    checked_locals: HashMap<core_ir::Path, DemandSignature>,
    missing_demands: Vec<MissingDemand>,
    next_effect_id: usize,
}

impl<'a> BodyEmitter<'a> {
    fn new(specializations: &'a HashMap<DemandKey, &'a DemandSpecialization>) -> Self {
        Self {
            specializations,
            current_specialization: None,
            enclosing_thunk_effects: Vec::new(),
            locals: HashMap::new(),
            checked_locals: HashMap::new(),
            missing_demands: Vec::new(),
            next_effect_id: 0,
        }
    }

    fn with_current_specialization(mut self, specialization: &'a DemandSpecialization) -> Self {
        self.current_specialization = Some(specialization);
        self
    }

    fn with_next_effect_id(mut self, next_effect_id: usize) -> Self {
        self.next_effect_id = next_effect_id;
        self
    }

    fn with_checked_locals(
        mut self,
        locals: Option<&HashMap<core_ir::Path, DemandSignature>>,
    ) -> Self {
        if let Some(locals) = locals {
            self.checked_locals = locals.clone();
        }
        self
    }

    fn into_missing_demands(self) -> Vec<MissingDemand> {
        self.missing_demands
    }

    fn rewrite_expr(
        &mut self,
        expr: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<Expr, DemandEmitError> {
        if matches!(expr.kind, ExprKind::Lambda { .. })
            && let Some(DemandSignature::Thunk { effect, value }) = expected
        {
            let value_ty = runtime_type(value)?;
            return Ok(Expr::typed(
                ExprKind::Thunk {
                    effect: effect_type(effect)?,
                    value: value_ty.clone(),
                    expr: Box::new(self.rewrite_expr(expr, Some(value))?),
                },
                RuntimeType::thunk(effect_type(effect)?, value_ty),
            ));
        }
        let rewritten = match &expr.kind {
            ExprKind::Lambda { param, body, .. } => {
                self.rewrite_lambda(expr, param, body, expected)
            }
            ExprKind::Apply { .. } => {
                if let Some(call) = self.rewrite_enclosed_thunk_call(expr, expected)? {
                    Ok(call)
                } else if let Some(call) = self.rewrite_specialized_call(expr, expected, true)? {
                    Ok(call)
                } else {
                    self.rewrite_apply(expr)
                }
            }
            ExprKind::Var(path) => {
                let ty = self
                    .locals
                    .get(path)
                    .map(runtime_shape_type)
                    .transpose()?
                    .unwrap_or_else(|| expr.ty.clone());
                Ok(Expr::typed(ExprKind::Var(path.clone()), ty))
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                evidence,
            } => Ok(Expr::typed(
                ExprKind::If {
                    cond: Box::new(self.rewrite_expr(cond, None)?),
                    then_branch: Box::new(self.rewrite_expr(then_branch, expected)?),
                    else_branch: Box::new(self.rewrite_expr(else_branch, expected)?),
                    evidence: evidence.clone(),
                },
                self.expr_type(expr, expected)?,
            )),
            ExprKind::Tuple(items) => Ok(Expr::typed(
                ExprKind::Tuple(
                    items
                        .iter()
                        .enumerate()
                        .map(|(index, item)| {
                            let item_expected = tuple_item_signature(expected, index, items.len());
                            self.rewrite_expr(item, item_expected.as_ref())
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                self.value_expr_type(expr, expected)?,
            )),
            ExprKind::Record { fields, spread } => Ok(Expr::typed(
                ExprKind::Record {
                    fields: fields
                        .iter()
                        .map(|field| {
                            let field_expected = record_field_signature(expected, &field.name);
                            Ok(RecordExprField {
                                name: field.name.clone(),
                                value: self.rewrite_expr(&field.value, field_expected.as_ref())?,
                            })
                        })
                        .collect::<Result<Vec<_>, DemandEmitError>>()?,
                    spread: spread
                        .as_ref()
                        .map(|spread| self.rewrite_record_spread(spread))
                        .transpose()?,
                },
                self.value_expr_type(expr, expected)?,
            )),
            ExprKind::Variant { tag, value } => Ok(Expr::typed(
                ExprKind::Variant {
                    tag: tag.clone(),
                    value: value
                        .as_ref()
                        .map(|value| {
                            let payload = variant_payload_signature(tag, expected);
                            self.rewrite_expr(value, payload.as_ref()).map(Box::new)
                        })
                        .transpose()?,
                },
                self.value_expr_type(expr, expected)?,
            )),
            ExprKind::Select { base, field } => Ok(Expr::typed(
                ExprKind::Select {
                    base: Box::new(self.rewrite_expr(base, None)?),
                    field: field.clone(),
                },
                self.value_expr_type(expr, expected)?,
            )),
            ExprKind::Match {
                scrutinee,
                arms,
                evidence,
            } => Ok(Expr::typed(
                ExprKind::Match {
                    scrutinee: Box::new(self.rewrite_expr(scrutinee, None)?),
                    arms: arms
                        .iter()
                        .map(|arm| {
                            let inserted = self.insert_checked_pattern_bindings(&arm.pattern);
                            let guard = arm
                                .guard
                                .as_ref()
                                .map(|guard| self.rewrite_expr(guard, None))
                                .transpose()?;
                            let body = self.rewrite_expr(&arm.body, expected)?;
                            self.restore_inserted_locals(inserted);
                            Ok(MatchArm {
                                pattern: arm.pattern.clone(),
                                guard,
                                body,
                            })
                        })
                        .collect::<Result<Vec<_>, DemandEmitError>>()?,
                    evidence: evidence.clone(),
                },
                self.expr_type(expr, expected)?,
            )),
            ExprKind::Block { stmts, tail } => self.rewrite_block(expr, stmts, tail, expected),
            ExprKind::Handle {
                body,
                arms,
                evidence,
                handler,
            } => {
                let body = self.rewrite_expr(body, None)?;
                let handled_body_for_resume = body.clone();
                let handler = self.rewrite_handle_effect(handler, &body);
                Ok(Expr::typed(
                    ExprKind::Handle {
                        body: Box::new(body),
                        arms: arms
                            .iter()
                            .map(|arm| {
                                let mut inserted =
                                    self.insert_checked_pattern_bindings(&arm.payload);
                                if let Some(resume) = &arm.resume {
                                    let local = core_ir::Path::from_name(resume.name.clone());
                                    let signature =
                                        self.checked_locals.get(&local).cloned().unwrap_or_else(
                                            || {
                                                resume_signature_from_context(
                                                    &resume.ty,
                                                    &handled_body_for_resume,
                                                )
                                            },
                                        );
                                    let previous = self.locals.insert(local.clone(), signature);
                                    inserted.push((local, previous));
                                }
                                let guard = arm
                                    .guard
                                    .as_ref()
                                    .map(|guard| self.rewrite_expr(guard, None))
                                    .transpose()?;
                                let body = self.rewrite_expr(&arm.body, expected)?;
                                self.restore_inserted_locals(inserted);
                                Ok(crate::ir::HandleArm {
                                    effect: arm.effect.clone(),
                                    payload: arm.payload.clone(),
                                    resume: arm.resume.clone(),
                                    guard,
                                    body,
                                })
                            })
                            .collect::<Result<Vec<_>, DemandEmitError>>()?,
                        evidence: evidence.clone(),
                        handler,
                    },
                    self.expr_type(expr, expected)?,
                ))
            }
            ExprKind::BindHere { expr: inner } => {
                let inner_expected = self.bind_here_inner_expected(expr, inner, expected);
                let inner = self.rewrite_expr(inner, inner_expected.as_ref())?;
                if !matches!(inner.ty, RuntimeType::Thunk { .. }) {
                    return self.lift_value_to_expected_thunk(inner, expected);
                }
                let ty = bind_here_result_type(expr, &inner, expected)?;
                Ok(Expr::typed(
                    ExprKind::BindHere {
                        expr: Box::new(inner),
                    },
                    ty,
                ))
            }
            ExprKind::Thunk {
                effect,
                value,
                expr: inner,
            } => {
                let (effect, value, inner_expected) = if let Some(DemandSignature::Thunk {
                    effect: expected_effect,
                    value: expected_value,
                }) = expected
                {
                    (
                        if expected_effect.is_closed() {
                            effect_type(expected_effect)?
                        } else {
                            effect.clone()
                        },
                        if expected_value.is_closed() {
                            runtime_type(expected_value)?
                        } else {
                            value.clone()
                        },
                        expected_value
                            .is_closed()
                            .then_some(expected_value.as_ref()),
                    )
                } else {
                    (effect.clone(), value.clone(), None)
                };
                self.enclosing_thunk_effects
                    .push(DemandEffect::from_core_type(&effect));
                let inner = self.rewrite_expr(inner, inner_expected)?;
                self.enclosing_thunk_effects.pop();
                Ok(Expr::typed(
                    ExprKind::Thunk {
                        effect: effect.clone(),
                        value: value.clone(),
                        expr: Box::new(inner),
                    },
                    RuntimeType::thunk(effect, value),
                ))
            }
            ExprKind::LocalPushId { id, body } => Ok(Expr::typed(
                ExprKind::LocalPushId {
                    id: *id,
                    body: Box::new(self.rewrite_expr(body, expected)?),
                },
                self.expr_type(expr, expected)?,
            )),
            ExprKind::AddId { id, allowed, thunk } => Ok(Expr::typed(
                ExprKind::AddId {
                    id: *id,
                    allowed: allowed.clone(),
                    thunk: Box::new(self.rewrite_expr(thunk, expected)?),
                },
                self.expr_type(expr, expected)?,
            )),
            ExprKind::Coerce {
                from,
                to,
                expr: inner,
            } => {
                let from_hint = coerce_from_type(from, expected)?;
                let to = coerce_to_type(to, expected)?;
                let from_signature =
                    DemandSignature::from_runtime_type(&RuntimeType::core(from_hint));
                let inner = self.rewrite_expr(inner, Some(&from_signature))?;
                let from = runtime_core_type(&inner.ty);
                Ok(Expr::typed(
                    ExprKind::Coerce {
                        from,
                        to,
                        expr: Box::new(inner),
                    },
                    self.value_expr_type(expr, expected)?,
                ))
            }
            ExprKind::Pack { var, expr: inner } => Ok(Expr::typed(
                ExprKind::Pack {
                    var: var.clone(),
                    expr: Box::new(self.rewrite_expr(inner, expected)?),
                },
                self.value_expr_type(expr, expected)?,
            )),
            ExprKind::EffectOp(path) => Ok(Expr::typed(
                ExprKind::EffectOp(path.clone()),
                self.value_expr_type(expr, expected)?,
            )),
            ExprKind::PrimitiveOp(op) => Ok(Expr::typed(
                ExprKind::PrimitiveOp(op.clone()),
                self.value_expr_type(expr, expected)?,
            )),
            ExprKind::Lit(lit) => Ok(Expr::typed(
                ExprKind::Lit(lit.clone()),
                self.value_expr_type(expr, expected)?,
            )),
            ExprKind::PeekId => Ok(Expr::typed(
                ExprKind::PeekId,
                self.value_expr_type(expr, expected)?,
            )),
            ExprKind::FindId { id } => Ok(Expr::typed(
                ExprKind::FindId { id: *id },
                self.value_expr_type(expr, expected)?,
            )),
        }?;
        self.lift_value_to_expected_thunk(rewritten, expected)
    }

    fn rewrite_lambda(
        &mut self,
        expr: &Expr,
        param: &core_ir::Name,
        body: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<Expr, DemandEmitError> {
        let Some(
            expected @ DemandSignature::Fun {
                param: param_ty,
                ret,
            },
        ) = expected
        else {
            let ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body,
            } = &expr.kind
            else {
                unreachable!();
            };
            return Ok(Expr::typed(
                ExprKind::Lambda {
                    param: param.clone(),
                    param_effect_annotation: param_effect_annotation.clone(),
                    param_function_allowed_effects: param_function_allowed_effects.clone(),
                    body: Box::new(self.rewrite_expr(body, None)?),
                },
                expr.ty.clone(),
            ));
        };
        let local = core_ir::Path::from_name(param.clone());
        let previous = self.locals.insert(local.clone(), param_ty.as_ref().clone());
        let body = self.rewrite_expr(body, Some(ret))?;
        restore_local(&mut self.locals, local, previous);
        let body = self.wrap_known_handler_return(body, ret)?;
        let ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            ..
        } = &expr.kind
        else {
            unreachable!();
        };
        Ok(Expr::typed(
            ExprKind::Lambda {
                param: param.clone(),
                param_effect_annotation: param_effect_annotation.clone(),
                param_function_allowed_effects: param_function_allowed_effects.clone(),
                body: Box::new(body),
            },
            runtime_shape_type(expected)?,
        ))
    }

    fn rewrite_handle_effect(
        &self,
        handler: &crate::ir::HandleEffect,
        body: &Expr,
    ) -> crate::ir::HandleEffect {
        let mut handler = handler.clone();
        if handler.consumes.is_empty()
            && let Some(consumed) = self
                .current_specialization
                .map(|specialization| known_consumed_effects_for_target(&specialization.target))
            && !consumed.is_empty()
        {
            handler.consumes = consumed;
        }
        if !handler.consumes.is_empty()
            && let Some(effect) = thunk_effect(&body.ty)
            && handler
                .residual_before
                .as_ref()
                .is_none_or(core_effect_is_unknown)
        {
            handler.residual_before = Some(effect.clone());
            handler.residual_after = Some(remove_core_effects(effect, &handler.consumes));
        }
        handler
    }

    fn wrap_known_handler_return(
        &mut self,
        body: Expr,
        ret: &DemandSignature,
    ) -> Result<Expr, DemandEmitError> {
        if !ret.is_closed()
            || signature_returns_function(ret)
            || matches!(ret, DemandSignature::Thunk { .. })
            || matches!(body.kind, ExprKind::LocalPushId { .. })
        {
            return Ok(body);
        }
        let Some(specialization) = self.current_specialization else {
            return Ok(body);
        };
        let Some(consumed) = known_consumed_effects_for_target(&specialization.target)
            .into_iter()
            .next()
        else {
            return Ok(body);
        };
        let effect = core_ir::Type::Named {
            path: consumed,
            args: Vec::new(),
        };
        let value_ty = runtime_type(ret)?;
        let thunk_ty = RuntimeType::thunk(effect.clone(), value_ty.clone());
        let thunk = Expr::typed(
            ExprKind::Thunk {
                effect: effect.clone(),
                value: value_ty.clone(),
                expr: Box::new(body),
            },
            thunk_ty.clone(),
        );
        let add_id = Expr::typed(
            ExprKind::AddId {
                id: EffectIdRef::Peek,
                allowed: effect,
                thunk: Box::new(thunk),
            },
            thunk_ty,
        );
        let forced = Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(add_id),
            },
            value_ty.clone(),
        );
        let id = EffectIdVar(self.next_effect_id);
        self.next_effect_id += 1;
        Ok(Expr::typed(
            ExprKind::LocalPushId {
                id,
                body: Box::new(forced),
            },
            value_ty,
        ))
    }

    fn rewrite_specialized_call(
        &mut self,
        expr: &Expr,
        expected: Option<&DemandSignature>,
        record_missing: bool,
    ) -> Result<Option<Expr>, DemandEmitError> {
        let Some((target, head, args)) = applied_call_with_head(expr) else {
            return Ok(None);
        };
        let demand_target = demand_call_target(target);
        let principal_hints = applied_call_principal_signature_hints(expr, args.len());
        let ret = expected.cloned().unwrap_or_else(|| {
            principal_hints
                .as_ref()
                .map(|(_, ret)| ret.clone())
                .unwrap_or_else(|| DemandSignature::from_runtime_type(&expr.ty))
        });
        let ret = self.lift_known_handler_return_to_enclosing_effect(&demand_target, ret);
        let ret = self.lift_recursive_return_to_enclosing_effect(&demand_target, ret);
        let (param_hints, ret) = self.closed_call_signature(
            &demand_target,
            head,
            &args,
            ret,
            principal_hints.map(|(params, _)| params),
        );
        let evidence_hints = applied_call_arg_evidence_signatures(expr);
        let arg_signatures = args
            .iter()
            .zip(param_hints.iter().cloned())
            .zip(evidence_hints)
            .map(|((arg, hint), evidence_hint)| {
                let signature = self.expr_signature(arg);
                let signature = evidence_hint
                    .map(|hint| merge_signature_hint(signature.clone(), hint))
                    .unwrap_or(signature);
                hint.map(|hint| merge_signature_hint(hint, signature.clone()))
                    .unwrap_or(signature)
            })
            .collect::<Vec<_>>();
        let arg_signatures =
            strengthen_handler_arg_signatures(&demand_target, arg_signatures, &param_hints, &ret);
        let ret = if is_role_method_path(&demand_target) {
            return_effect_from_args(ret, &arg_signatures)
        } else {
            ret
        };
        let signature = close_known_associated_type_signature(
            &demand_target,
            curried_signatures(&arg_signatures, ret),
        );
        let signature = close_default_effect_holes(signature);
        let signature = close_known_associated_type_signature(&demand_target, signature);
        let key = DemandKey::from_signature(demand_target.clone(), signature);
        let Some(specialization) = self
            .find_specialization(&key)
            .or_else(|| self.find_role_impl_specialization(&demand_target, &key.signature))
        else {
            if record_missing {
                self.record_missing_demand(&demand_target, &key.signature, &expr.ty);
            }
            debug_missing_specialization(&demand_target, &key.signature);
            return Ok(None);
        };
        let mut callee_signature = specialization.solved.clone();
        let mut call = Expr::typed(
            ExprKind::Var(specialization.path.clone()),
            runtime_type(&callee_signature)?,
        );
        for arg in args {
            while let DemandSignature::Thunk { value, .. } = callee_signature {
                let value_ty = runtime_type(&value)?;
                call = Expr::typed(
                    ExprKind::BindHere {
                        expr: Box::new(call),
                    },
                    value_ty,
                );
                callee_signature = *value;
            }
            let DemandSignature::Fun { param, ret } = callee_signature else {
                return Err(DemandEmitError::NonFunctionCall(callee_signature));
            };
            let arg = force_arg_to_expected_value(self.rewrite_expr(arg, Some(&param))?, &param)?;
            let ret_ty = runtime_type(&ret)?;
            call = Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(call),
                    arg: Box::new(arg),
                    evidence: None,
                    instantiation: None,
                },
                ret_ty,
            );
            callee_signature = *ret;
        }
        Ok(Some(call))
    }

    fn record_missing_demand(
        &mut self,
        target: &core_ir::Path,
        signature: &DemandSignature,
        expr_ty: &RuntimeType,
    ) {
        let signature = missing_signature_with_runtime_return(signature.clone(), expr_ty);
        if !signature.is_closed() {
            return;
        }
        self.missing_demands.push(MissingDemand {
            target: target.clone(),
            signature,
        });
    }

    fn rewrite_enclosed_thunk_call(
        &mut self,
        expr: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<Option<Expr>, DemandEmitError> {
        let Some(expected) = expected else {
            return Ok(None);
        };
        if matches!(expected, DemandSignature::Thunk { .. }) {
            return Ok(None);
        }
        let Some(effect) = self.enclosing_thunk_effects.last().cloned() else {
            return Ok(None);
        };
        if demand_effect_is_empty(&effect) {
            return Ok(None);
        }
        let expected_thunk = DemandSignature::Thunk {
            effect,
            value: Box::new(expected.clone()),
        };
        let Some(call) = self.rewrite_specialized_call(expr, Some(&expected_thunk), false)? else {
            return Ok(None);
        };
        if !matches!(call.ty, RuntimeType::Thunk { .. }) {
            return Ok(Some(call));
        }
        Ok(Some(Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(call),
            },
            runtime_type(expected)?,
        )))
    }

    fn lift_known_handler_return_to_enclosing_effect(
        &self,
        target: &core_ir::Path,
        ret: DemandSignature,
    ) -> DemandSignature {
        if known_consumed_effects_for_target(target).is_empty()
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
        if matches!(ret, DemandSignature::Thunk { .. })
            || !self
                .current_specialization
                .is_some_and(|specialization| specialization.target == *target)
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

    fn closed_call_signature(
        &self,
        target: &core_ir::Path,
        head: &Expr,
        args: &[&Expr],
        ret: DemandSignature,
        seed_param_hints: Option<Vec<Option<DemandSignature>>>,
    ) -> (Vec<Option<DemandSignature>>, DemandSignature) {
        let param_hints = seed_param_hints
            .filter(|hints| hints.len() == args.len())
            .unwrap_or_else(|| curried_param_signatures_from_type(&head.ty, args.len()));
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
        let (closed_args, closed_ret) = uncurried_emit_signatures(closed);
        if closed_args.len() == args.len() {
            return (closed_args.into_iter().map(Some).collect(), closed_ret);
        }
        (param_hints, ret)
    }

    fn local_or_runtime_signature(&self, expr: &Expr) -> DemandSignature {
        if let Some(signature) = self.primitive_application_signature(expr) {
            return signature;
        }
        if let ExprKind::Var(path) = &transparent_call_head(expr).kind
            && let Some(signature) = self.locals.get(path)
        {
            return signature.clone();
        }
        self.expr_signature(expr)
    }

    fn primitive_application_signature(&self, expr: &Expr) -> Option<DemandSignature> {
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

    fn find_specialization(&self, key: &DemandKey) -> Option<&'a DemandSpecialization> {
        if let Some(specialization) = self.current_specialization
            && specialization.target == key.target
            && signature_arity(&key.signature) == signature_arity(&specialization.solved)
        {
            return Some(specialization);
        }
        if let Some(specialization) = self.specializations.get(key) {
            return Some(*specialization);
        }
        let mut matches = self
            .specializations
            .values()
            .copied()
            .filter(|specialization| {
                specialization.target == key.target
                    && signature_arity(&key.signature) == signature_arity(&specialization.solved)
                    && signatures_compatible_for_target_call(
                        &key.target,
                        &key.signature,
                        &specialization.solved,
                    )
            })
            .collect::<Vec<_>>();
        sort_specialization_candidates(&mut matches);
        match matches.as_slice() {
            [] => None,
            [specialization] => Some(*specialization),
            [first, rest @ ..]
                if rest
                    .iter()
                    .all(|specialization| specialization.solved == first.solved) =>
            {
                Some(*first)
            }
            _ => most_specific_specialization(&key.signature, &matches),
        }
    }

    fn find_role_impl_specialization(
        &self,
        target: &core_ir::Path,
        signature: &DemandSignature,
    ) -> Option<&'a DemandSpecialization> {
        if !is_role_method_path(target) {
            return None;
        }
        let method = target.segments.last()?;
        let mut full_matches = self
            .specializations
            .values()
            .copied()
            .filter(|specialization| {
                specialization.target.segments.last() == Some(method)
                    && is_impl_method_path(&specialization.target)
                    && signature_arity(signature) == signature_arity(&specialization.solved)
                    && role_impl_call_compatible(&specialization.solved, signature)
            })
            .collect::<Vec<_>>();
        if full_matches.is_empty() {
            full_matches = self
                .specializations
                .values()
                .copied()
                .filter(|specialization| {
                    specialization.target.segments.last() == Some(method)
                        && is_impl_method_path(&specialization.target)
                        && signature_arity(signature) == signature_arity(&specialization.solved)
                        && role_impl_receiver_compatible(&specialization.solved, signature)
                })
                .collect();
        }
        let mut matches = full_matches;
        sort_specialization_candidates(&mut matches);
        match matches.as_slice() {
            [] => None,
            [specialization] => Some(*specialization),
            [first, rest @ ..]
                if rest
                    .iter()
                    .all(|specialization| specialization.solved == first.solved) =>
            {
                Some(*first)
            }
            _ => most_specific_specialization(signature, &matches),
        }
    }

    fn rewrite_apply(&mut self, expr: &Expr) -> Result<Expr, DemandEmitError> {
        let ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } = &expr.kind
        else {
            unreachable!();
        };
        let callee = force_thunk_callee_to_function(self.rewrite_expr(callee, None)?)?;
        let arg = if let Some(param) = apply_param_signature(&callee.ty) {
            force_arg_to_expected_value(self.rewrite_expr(arg, Some(&param))?, &param)?
        } else {
            self.rewrite_expr(arg, None)?
        };
        let ty = apply_result_runtime_type(&callee).unwrap_or_else(|| expr.ty.clone());
        Ok(Expr::typed(
            ExprKind::Apply {
                callee: Box::new(callee),
                arg: Box::new(arg),
                evidence: evidence.clone(),
                instantiation: instantiation.clone(),
            },
            ty,
        ))
    }

    fn expr_signature(&self, expr: &Expr) -> DemandSignature {
        match &expr.kind {
            ExprKind::Var(path) => self
                .locals
                .get(path)
                .cloned()
                .unwrap_or_else(|| DemandSignature::from_runtime_type(&expr.ty)),
            ExprKind::Apply {
                evidence: Some(evidence),
                ..
            } => apply_evidence_merged_signature(
                evidence,
                DemandSignature::from_runtime_type(&expr.ty),
            ),
            _ => DemandSignature::from_runtime_type(&expr.ty),
        }
    }

    fn rewrite_record_spread(
        &mut self,
        spread: &RecordSpreadExpr,
    ) -> Result<RecordSpreadExpr, DemandEmitError> {
        Ok(match spread {
            RecordSpreadExpr::Head(expr) => {
                RecordSpreadExpr::Head(Box::new(self.rewrite_expr(expr, None)?))
            }
            RecordSpreadExpr::Tail(expr) => {
                RecordSpreadExpr::Tail(Box::new(self.rewrite_expr(expr, None)?))
            }
        })
    }

    fn rewrite_block(
        &mut self,
        expr: &Expr,
        stmts: &[Stmt],
        tail: &Option<Box<Expr>>,
        expected: Option<&DemandSignature>,
    ) -> Result<Expr, DemandEmitError> {
        let mut inserted = Vec::new();
        let mut rewritten_stmts = Vec::with_capacity(stmts.len());
        for stmt in stmts {
            let rewritten = match stmt {
                Stmt::Let { pattern, value } => {
                    let bindings = self.checked_pattern_bindings(pattern);
                    let value_expected = single_binding_signature(pattern, &bindings);
                    for (local, signature) in &bindings {
                        let previous = self.locals.insert(local.clone(), signature.clone());
                        inserted.push((local.clone(), previous));
                    }
                    Stmt::Let {
                        pattern: pattern.clone(),
                        value: self.rewrite_expr(value, value_expected)?,
                    }
                }
                Stmt::Expr(expr) => {
                    let expected = self.discarded_stmt_expected(expr);
                    Stmt::Expr(self.rewrite_expr(expr, expected.as_ref())?)
                }
                Stmt::Module { def, body } => Stmt::Module {
                    def: def.clone(),
                    body: self.rewrite_expr(body, None)?,
                },
            };
            rewritten_stmts.push(rewritten);
        }
        let tail = tail
            .as_ref()
            .map(|tail| self.rewrite_expr(tail, expected).map(Box::new))
            .transpose()?;
        for (local, previous) in inserted.into_iter().rev() {
            restore_local(&mut self.locals, local, previous);
        }
        Ok(Expr::typed(
            ExprKind::Block {
                stmts: rewritten_stmts,
                tail,
            },
            self.expr_type(expr, expected)?,
        ))
    }

    fn discarded_stmt_expected(&self, expr: &Expr) -> Option<DemandSignature> {
        let RuntimeType::Thunk { effect, value } = &expr.ty else {
            return None;
        };
        let effect = DemandEffect::from_core_type(effect);
        let effect = if demand_effect_is_empty(&effect) {
            self.enclosing_thunk_effects.last()?.clone()
        } else {
            effect
        };
        if demand_effect_is_empty(&effect) {
            return None;
        }
        Some(DemandSignature::Thunk {
            effect,
            value: Box::new(DemandSignature::from_runtime_type(value)),
        })
    }

    fn checked_pattern_bindings(&self, pattern: &Pattern) -> Vec<(core_ir::Path, DemandSignature)> {
        let mut paths = Vec::new();
        collect_pattern_bind_paths(pattern, &mut paths);
        paths
            .into_iter()
            .filter_map(|path| {
                self.checked_locals
                    .get(&path)
                    .cloned()
                    .map(|signature| (path, signature))
            })
            .collect()
    }

    fn insert_checked_pattern_bindings(
        &mut self,
        pattern: &Pattern,
    ) -> Vec<(core_ir::Path, Option<DemandSignature>)> {
        self.checked_pattern_bindings(pattern)
            .into_iter()
            .map(|(local, signature)| {
                let previous = self.locals.insert(local.clone(), signature);
                (local, previous)
            })
            .collect()
    }

    fn restore_inserted_locals(&mut self, inserted: Vec<(core_ir::Path, Option<DemandSignature>)>) {
        for (local, previous) in inserted.into_iter().rev() {
            restore_local(&mut self.locals, local, previous);
        }
    }

    fn expr_type(
        &self,
        expr: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<RuntimeType, DemandEmitError> {
        expected
            .filter(|signature| signature.is_closed())
            .map(runtime_type)
            .transpose()
            .map(|ty| ty.unwrap_or_else(|| expr.ty.clone()))
    }

    fn value_expr_type(
        &self,
        expr: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<RuntimeType, DemandEmitError> {
        if matches!(expected, Some(DemandSignature::Thunk { .. })) {
            return Ok(expr.ty.clone());
        }
        self.expr_type(expr, expected)
    }

    fn bind_here_inner_expected(
        &self,
        expr: &Expr,
        inner: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Option<DemandSignature> {
        let effect = self.bind_here_effect(inner);
        let value = expected
            .cloned()
            .or_else(|| (!demand_effect_is_empty(&effect)).then(|| self.expr_signature(expr)))?;
        Some(DemandSignature::Thunk {
            effect,
            value: Box::new(value),
        })
    }

    fn bind_here_effect(&self, inner: &Expr) -> DemandEffect {
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

    fn lift_value_to_expected_thunk(
        &self,
        expr: Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<Expr, DemandEmitError> {
        let Some(DemandSignature::Thunk { effect, value }) = expected else {
            return Ok(expr);
        };
        if matches!(expr.ty, RuntimeType::Thunk { .. }) {
            return Ok(expr);
        }
        let actual = DemandSignature::from_runtime_type(&expr.ty);
        if DemandUnifier::new()
            .unify_signature(value, &actual)
            .is_err()
        {
            return Ok(expr);
        }
        if !effect.is_closed() {
            return Ok(expr);
        }
        let value = if value.is_closed() {
            value.as_ref().clone()
        } else if actual.is_closed() {
            actual
        } else {
            return Ok(expr);
        };
        let effect_ty = effect_type(effect)?;
        let value_ty = runtime_type(&value)?;
        Ok(Expr::typed(
            ExprKind::Thunk {
                effect: effect_ty.clone(),
                value: value_ty.clone(),
                expr: Box::new(expr),
            },
            RuntimeType::thunk(effect_ty, value_ty),
        ))
    }
}

fn role_impl_call_compatible(candidate: &DemandSignature, call: &DemandSignature) -> bool {
    signatures_compatible_for_call(call, candidate)
        || signatures_compatible_for_call(candidate, call)
}

fn missing_signature_with_runtime_return(
    signature: DemandSignature,
    expr_ty: &RuntimeType,
) -> DemandSignature {
    let runtime_ret = DemandSignature::from_runtime_type(expr_ty);
    if !matches!(runtime_ret, DemandSignature::Thunk { .. }) {
        return signature;
    }
    let (args, ret) = uncurried_emit_signatures(signature);
    if matches!(ret, DemandSignature::Thunk { .. }) {
        return curried_signatures(&args, ret);
    }
    let DemandSignature::Thunk { effect, .. } = runtime_ret else {
        return curried_signatures(&args, ret);
    };
    curried_signatures(
        &args,
        DemandSignature::Thunk {
            effect,
            value: Box::new(ret),
        },
    )
}

fn resume_signature_from_context(ty: &RuntimeType, handled_body: &Expr) -> DemandSignature {
    let handled_body = DemandSignature::from_runtime_type(&handled_body.ty);
    match ty {
        RuntimeType::Fun { param, .. } => DemandSignature::Fun {
            param: Box::new(DemandSignature::from_runtime_type(param)),
            ret: Box::new(handled_body),
        },
        RuntimeType::Core(core_ir::Type::Fun {
            param,
            param_effect,
            ..
        }) => {
            let param = signature_core_value(&DemandSignature::from_runtime_type(
                &RuntimeType::core(*param.clone()),
            ));
            let effect = DemandEffect::from_core_type(param_effect);
            DemandSignature::Fun {
                param: Box::new(effected_core_signature(param, effect)),
                ret: Box::new(handled_body),
            }
        }
        _ => DemandSignature::from_runtime_type(ty),
    }
}

fn applied_call_with_head(expr: &Expr) -> Option<(&core_ir::Path, &Expr, Vec<&Expr>)> {
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
            ExprKind::Var(target) => {
                args.reverse();
                return Some((target, callee, args));
            }
            _ => return None,
        }
    }
}

fn applied_call_arg_evidence_signatures(expr: &Expr) -> Vec<Option<DemandSignature>> {
    let mut callee = expr;
    let mut hints = Vec::new();
    loop {
        callee = transparent_call_head(callee);
        let ExprKind::Apply {
            callee: next,
            evidence,
            ..
        } = &callee.kind
        else {
            break;
        };
        hints.push(evidence.as_ref().and_then(apply_evidence_arg_signature));
        callee = next;
    }
    hints.reverse();
    hints
}

fn applied_call_principal_signature_hints(
    expr: &Expr,
    arity: usize,
) -> Option<(Vec<Option<DemandSignature>>, DemandSignature)> {
    let mut callee = expr;
    let mut principal = None;
    loop {
        callee = transparent_call_head(callee);
        let ExprKind::Apply {
            callee: next,
            evidence,
            ..
        } = &callee.kind
        else {
            break;
        };
        if let Some(signature) = evidence
            .as_ref()
            .and_then(apply_evidence_substituted_callee_signature)
        {
            principal = Some(signature);
        }
        callee = next;
    }

    let (params, ret) = uncurried_emit_signatures(principal?);
    if params.len() < arity {
        return None;
    }
    let ret = if params.len() == arity {
        ret
    } else {
        curried_signatures(&params[arity..], ret)
    };
    let params = params.into_iter().take(arity).map(Some).collect();
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

fn uncurried_emit_signatures(
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

fn curried_param_signatures_from_type(
    ty: &RuntimeType,
    arity: usize,
) -> Vec<Option<DemandSignature>> {
    let mut out = Vec::with_capacity(arity);
    let mut current = DemandSignature::from_runtime_type(ty);
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

fn most_specific_specialization<'a>(
    expected: &DemandSignature,
    candidates: &[&'a DemandSpecialization],
) -> Option<&'a DemandSpecialization> {
    let min = candidates
        .iter()
        .map(|candidate| signature_hole_count(&candidate.solved))
        .min()?;
    let hole_filtered = candidates
        .iter()
        .copied()
        .filter(|candidate| signature_hole_count(&candidate.solved) == min)
        .collect::<Vec<_>>();
    let min_never = hole_filtered
        .iter()
        .map(|candidate| signature_never_count(&candidate.solved))
        .min()?;
    let never_filtered = hole_filtered
        .into_iter()
        .filter(|candidate| signature_never_count(&candidate.solved) == min_never)
        .collect::<Vec<_>>();
    let max_effect_score = never_filtered
        .iter()
        .map(|candidate| signature_effect_match_score(expected, &candidate.solved))
        .max()?;
    never_filtered.into_iter().find(|candidate| {
        signature_effect_match_score(expected, &candidate.solved) == max_effect_score
    })
}

fn sort_specialization_candidates(candidates: &mut [&DemandSpecialization]) {
    candidates.sort_by(|left, right| {
        specialization_path_key(left)
            .cmp(&specialization_path_key(right))
            .then_with(|| specialization_target_key(left).cmp(&specialization_target_key(right)))
    });
}

fn specialization_path_key(specialization: &DemandSpecialization) -> String {
    path_key(&specialization.path)
}

fn specialization_target_key(specialization: &DemandSpecialization) -> String {
    path_key(&specialization.target)
}

fn path_key(path: &core_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn signature_effect_match_score(expected: &DemandSignature, candidate: &DemandSignature) -> usize {
    match (expected, candidate) {
        (
            DemandSignature::Fun {
                param: expected_param,
                ret: expected_ret,
            },
            DemandSignature::Fun {
                param: candidate_param,
                ret: candidate_ret,
            },
        ) => {
            signature_effect_match_score(expected_param, candidate_param)
                + signature_effect_match_score(expected_ret, candidate_ret)
        }
        (
            DemandSignature::Thunk {
                effect: expected_effect,
                value: expected_value,
            },
            DemandSignature::Thunk {
                effect: candidate_effect,
                value: candidate_value,
            },
        ) => {
            effect_match_score(expected_effect, candidate_effect)
                + signature_effect_match_score(expected_value, candidate_value)
        }
        (DemandSignature::Core(expected), DemandSignature::Core(candidate)) => {
            core_effect_match_score(expected, candidate)
        }
        (
            DemandSignature::Thunk {
                value: expected, ..
            },
            candidate,
        ) => signature_effect_match_score(expected, candidate),
        (
            expected,
            DemandSignature::Thunk {
                value: candidate, ..
            },
        ) => signature_effect_match_score(expected, candidate),
        _ => 0,
    }
}

fn core_effect_match_score(expected: &DemandCoreType, candidate: &DemandCoreType) -> usize {
    match (expected, candidate) {
        (
            DemandCoreType::Fun {
                param: expected_param,
                param_effect: expected_param_effect,
                ret_effect: expected_ret_effect,
                ret: expected_ret,
            },
            DemandCoreType::Fun {
                param: candidate_param,
                param_effect: candidate_param_effect,
                ret_effect: candidate_ret_effect,
                ret: candidate_ret,
            },
        ) => {
            core_effect_match_score(expected_param, candidate_param)
                + effect_match_score(expected_param_effect, candidate_param_effect)
                + effect_match_score(expected_ret_effect, candidate_ret_effect)
                + core_effect_match_score(expected_ret, candidate_ret)
        }
        (
            DemandCoreType::Named {
                args: expected_args,
                ..
            },
            DemandCoreType::Named {
                args: candidate_args,
                ..
            },
        ) => expected_args
            .iter()
            .zip(candidate_args)
            .map(|(expected, candidate)| type_arg_effect_match_score(expected, candidate))
            .sum(),
        _ => 0,
    }
}

fn type_arg_effect_match_score(expected: &DemandTypeArg, candidate: &DemandTypeArg) -> usize {
    match (expected, candidate) {
        (DemandTypeArg::Type(expected), DemandTypeArg::Type(candidate)) => {
            core_effect_match_score(expected, candidate)
        }
        (
            DemandTypeArg::Bounds {
                lower: expected_lower,
                upper: expected_upper,
            },
            DemandTypeArg::Bounds {
                lower: candidate_lower,
                upper: candidate_upper,
            },
        ) => {
            optional_core_effect_match_score(expected_lower, candidate_lower)
                + optional_core_effect_match_score(expected_upper, candidate_upper)
        }
        _ => 0,
    }
}

fn optional_core_effect_match_score(
    expected: &Option<DemandCoreType>,
    candidate: &Option<DemandCoreType>,
) -> usize {
    match (expected, candidate) {
        (Some(expected), Some(candidate)) => core_effect_match_score(expected, candidate),
        _ => 0,
    }
}

fn effect_match_score(expected: &DemandEffect, candidate: &DemandEffect) -> usize {
    let mut expected_paths = Vec::new();
    collect_effect_paths(expected, &mut expected_paths);
    if expected_paths.is_empty() {
        return 0;
    }
    expected_paths
        .iter()
        .filter(|path| effect_contains_path(candidate, path))
        .count()
}

fn collect_effect_paths<'a>(effect: &'a DemandEffect, out: &mut Vec<&'a core_ir::Path>) {
    match effect {
        DemandEffect::Atom(DemandCoreType::Named { path, .. }) => out.push(path),
        DemandEffect::Row(items) => {
            for item in items {
                collect_effect_paths(item, out);
            }
        }
        DemandEffect::Empty | DemandEffect::Hole(_) | DemandEffect::Atom(_) => {}
    }
}

fn effect_contains_path(effect: &DemandEffect, needle: &core_ir::Path) -> bool {
    match effect {
        DemandEffect::Atom(DemandCoreType::Named { path, .. }) => path == needle,
        DemandEffect::Row(items) => items.iter().any(|item| effect_contains_path(item, needle)),
        DemandEffect::Empty | DemandEffect::Hole(_) | DemandEffect::Atom(_) => false,
    }
}

fn signature_hole_count(signature: &DemandSignature) -> usize {
    match signature {
        DemandSignature::Ignored => 0,
        DemandSignature::Hole(_) => 1,
        DemandSignature::Core(ty) => core_hole_count(ty),
        DemandSignature::Fun { param, ret } => {
            signature_hole_count(param) + signature_hole_count(ret)
        }
        DemandSignature::Thunk { effect, value } => {
            effect_hole_count(effect) + signature_hole_count(value)
        }
    }
}

fn signature_never_count(signature: &DemandSignature) -> usize {
    match signature {
        DemandSignature::Ignored | DemandSignature::Hole(_) => 0,
        DemandSignature::Core(ty) => core_never_count(ty),
        DemandSignature::Fun { param, ret } => {
            signature_never_count(param) + signature_never_count(ret)
        }
        DemandSignature::Thunk { effect, value } => {
            effect_never_count(effect) + signature_never_count(value)
        }
    }
}

fn signature_arity(signature: &DemandSignature) -> usize {
    let mut arity = 0;
    let mut current = signature;
    loop {
        match current {
            DemandSignature::Fun { ret, .. } => {
                arity += 1;
                current = ret;
            }
            DemandSignature::Thunk { effect, value } if demand_effect_is_empty(effect) => {
                current = value;
            }
            _ => break,
        }
    }
    arity
}

fn effect_hole_count(effect: &DemandEffect) -> usize {
    match effect {
        DemandEffect::Empty => 0,
        DemandEffect::Hole(_) => 1,
        DemandEffect::Atom(ty) => core_hole_count(ty),
        DemandEffect::Row(items) => items.iter().map(effect_hole_count).sum(),
    }
}

fn core_hole_count(ty: &DemandCoreType) -> usize {
    match ty {
        DemandCoreType::Any => 0,
        DemandCoreType::Never => 0,
        DemandCoreType::Hole(_) => 1,
        DemandCoreType::Named { args, .. } => args.iter().map(type_arg_hole_count).sum(),
        DemandCoreType::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_hole_count(param)
                + effect_hole_count(param_effect)
                + effect_hole_count(ret_effect)
                + core_hole_count(ret)
        }
        DemandCoreType::Tuple(items)
        | DemandCoreType::Union(items)
        | DemandCoreType::Inter(items) => items.iter().map(core_hole_count).sum(),
        DemandCoreType::Record(fields) => fields
            .iter()
            .map(|field| core_hole_count(&field.value))
            .sum(),
        DemandCoreType::Variant(cases) => cases
            .iter()
            .flat_map(|case| &case.payloads)
            .map(core_hole_count)
            .sum(),
        DemandCoreType::RowAsValue(items) => items.iter().map(effect_hole_count).sum(),
        DemandCoreType::Recursive { body, .. } => core_hole_count(body),
    }
}

fn type_arg_hole_count(arg: &DemandTypeArg) -> usize {
    match arg {
        DemandTypeArg::Type(ty) => core_hole_count(ty),
        DemandTypeArg::Bounds { lower, upper } => lower
            .iter()
            .chain(upper)
            .map(|ty| core_hole_count(ty))
            .sum(),
    }
}

fn effect_never_count(effect: &DemandEffect) -> usize {
    match effect {
        DemandEffect::Empty | DemandEffect::Hole(_) => 0,
        DemandEffect::Atom(ty) => core_never_count(ty),
        DemandEffect::Row(items) => items.iter().map(effect_never_count).sum(),
    }
}

fn core_never_count(ty: &DemandCoreType) -> usize {
    match ty {
        DemandCoreType::Never => 1,
        DemandCoreType::Any | DemandCoreType::Hole(_) => 0,
        DemandCoreType::Named { args, .. } => args.iter().map(type_arg_never_count).sum(),
        DemandCoreType::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_never_count(param)
                + effect_never_count(param_effect)
                + effect_never_count(ret_effect)
                + core_never_count(ret)
        }
        DemandCoreType::Tuple(items)
        | DemandCoreType::Union(items)
        | DemandCoreType::Inter(items) => items.iter().map(core_never_count).sum(),
        DemandCoreType::Record(fields) => fields
            .iter()
            .map(|field| core_never_count(&field.value))
            .sum(),
        DemandCoreType::Variant(cases) => cases
            .iter()
            .flat_map(|case| &case.payloads)
            .map(core_never_count)
            .sum(),
        DemandCoreType::RowAsValue(items) => items.iter().map(effect_never_count).sum(),
        DemandCoreType::Recursive { body, .. } => core_never_count(body),
    }
}

fn type_arg_never_count(arg: &DemandTypeArg) -> usize {
    match arg {
        DemandTypeArg::Type(ty) => core_never_count(ty),
        DemandTypeArg::Bounds { lower, upper } => lower
            .iter()
            .chain(upper)
            .map(|ty| core_never_count(ty))
            .sum(),
    }
}

fn variant_payload_signature(
    tag: &core_ir::Name,
    expected: Option<&DemandSignature>,
) -> Option<DemandSignature> {
    match expected {
        Some(DemandSignature::Core(DemandCoreType::Variant(cases))) => cases
            .iter()
            .find(|case| case.name == *tag)
            .and_then(|case| case.payloads.first())
            .cloned()
            .map(DemandSignature::Core),
        Some(DemandSignature::Core(DemandCoreType::Named { args, .. })) => {
            single_payload_arg(args).map(DemandSignature::Core)
        }
        _ => None,
    }
}

fn tuple_item_signature(
    expected: Option<&DemandSignature>,
    index: usize,
    len: usize,
) -> Option<DemandSignature> {
    let Some(DemandSignature::Core(DemandCoreType::Tuple(items))) = expected else {
        return None;
    };
    if items.len() != len {
        return None;
    }
    items.get(index).cloned().map(DemandSignature::Core)
}

fn record_field_signature(
    expected: Option<&DemandSignature>,
    name: &core_ir::Name,
) -> Option<DemandSignature> {
    let Some(DemandSignature::Core(DemandCoreType::Record(fields))) = expected else {
        return None;
    };
    fields
        .iter()
        .find(|field| field.name == *name)
        .map(|field| DemandSignature::Core(field.value.clone()))
}

fn coerce_from_type(
    from: &core_ir::Type,
    expected: Option<&DemandSignature>,
) -> Result<core_ir::Type, DemandEmitError> {
    let Some(DemandSignature::Core(DemandCoreType::Named { args, .. })) = expected else {
        return Ok(from.clone());
    };
    let Some(payload) = single_payload_arg(args) else {
        return Ok(from.clone());
    };
    let core_ir::Type::Variant(variant) = from else {
        return Ok(from.clone());
    };
    let [case] = variant.cases.as_slice() else {
        return Ok(from.clone());
    };
    if case.payloads.len() != 1 {
        return Ok(from.clone());
    }
    Ok(core_ir::Type::Variant(core_ir::VariantType {
        cases: vec![core_ir::VariantCase {
            name: case.name.clone(),
            payloads: vec![core_type(&payload)?],
        }],
        tail: variant.tail.clone(),
    }))
}

fn coerce_to_type(
    to: &core_ir::Type,
    expected: Option<&DemandSignature>,
) -> Result<core_ir::Type, DemandEmitError> {
    match expected {
        Some(DemandSignature::Core(ty)) => core_type(ty),
        _ => Ok(to.clone()),
    }
}

fn single_payload_arg(args: &[DemandTypeArg]) -> Option<DemandCoreType> {
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

fn thunk_effect_signature(ty: &RuntimeType) -> Option<DemandEffect> {
    match ty {
        RuntimeType::Thunk { effect, .. } => Some(DemandEffect::from_core_type(effect)),
        _ => None,
    }
}

fn demand_effect_is_empty(effect: &DemandEffect) -> bool {
    match effect {
        DemandEffect::Empty => true,
        DemandEffect::Row(items) => items.iter().all(demand_effect_is_empty),
        DemandEffect::Hole(_) | DemandEffect::Atom(_) => false,
    }
}

fn debug_missing_specialization(target: &core_ir::Path, signature: &DemandSignature) {
    if std::env::var_os("YULANG_DEBUG_DEMAND_EMIT").is_none() {
        return;
    }
    eprintln!("missing specialization for {target:?}: {signature:?}");
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

fn signatures_compatible_for_call(expected: &DemandSignature, candidate: &DemandSignature) -> bool {
    if expected_requires_empty_thunk_not_present_in_candidate(expected, candidate) {
        return false;
    }
    DemandUnifier::new()
        .unify_signature(expected, candidate)
        .is_ok()
        || DemandUnifier::new()
            .unify_signature(expected, &erase_empty_thunks(candidate))
            .is_ok()
        || DemandUnifier::new()
            .unify_signature(&erase_empty_thunks(expected), candidate)
            .is_ok()
        || DemandUnifier::new()
            .unify_signature(
                &erase_empty_thunks(expected),
                &erase_empty_thunks(candidate),
            )
            .is_ok()
        || signatures_structurally_compatible_for_call(expected, candidate)
}

fn signatures_compatible_for_target_call(
    target: &core_ir::Path,
    expected: &DemandSignature,
    candidate: &DemandSignature,
) -> bool {
    if signatures_compatible_for_call(expected, candidate) {
        return true;
    }
    let consumed = known_consumed_effects_for_target(target);
    if consumed.is_empty() {
        return false;
    }
    let expected = erase_consumed_return_thunks(expected, &consumed);
    signatures_compatible_for_call(&expected, candidate)
}

fn signatures_structurally_compatible_for_call(
    expected: &DemandSignature,
    candidate: &DemandSignature,
) -> bool {
    match (expected, candidate) {
        (
            DemandSignature::Fun {
                param: expected_param,
                ret: expected_ret,
            },
            DemandSignature::Fun {
                param: candidate_param,
                ret: candidate_ret,
            },
        ) => {
            signatures_structurally_compatible_for_call(expected_param, candidate_param)
                && signatures_structurally_compatible_for_call(expected_ret, candidate_ret)
        }
        (
            DemandSignature::Thunk {
                value: expected_value,
                ..
            },
            DemandSignature::Thunk {
                value: candidate_value,
                ..
            },
        ) => signatures_structurally_compatible_for_call(expected_value, candidate_value),
        (DemandSignature::Core(expected), DemandSignature::Core(candidate)) => {
            core_types_structurally_compatible_for_call(expected, candidate)
        }
        _ => false,
    }
}

fn core_types_structurally_compatible_for_call(
    expected: &DemandCoreType,
    candidate: &DemandCoreType,
) -> bool {
    match (expected, candidate) {
        (DemandCoreType::Record(expected), DemandCoreType::Record(candidate)) => {
            record_types_structurally_compatible_for_call(expected, candidate)
        }
        (
            DemandCoreType::Named {
                path: expected_path,
                args: expected_args,
            },
            DemandCoreType::Named {
                path: candidate_path,
                args: candidate_args,
            },
        ) => {
            expected_path == candidate_path
                && expected_args.len() == candidate_args.len()
                && expected_args
                    .iter()
                    .zip(candidate_args)
                    .all(|(expected, candidate)| {
                        type_args_structurally_compatible_for_call(expected, candidate)
                    })
        }
        (DemandCoreType::Any | DemandCoreType::Hole(_), _)
        | (_, DemandCoreType::Any | DemandCoreType::Hole(_)) => true,
        _ => expected == candidate,
    }
}

fn record_types_structurally_compatible_for_call(
    expected: &[DemandRecordField],
    candidate: &[DemandRecordField],
) -> bool {
    expected.iter().all(|expected_field| {
        candidate
            .iter()
            .find(|field| field.name == expected_field.name)
            .is_some_and(|candidate_field| {
                core_types_structurally_compatible_for_call(
                    &expected_field.value,
                    &candidate_field.value,
                )
            })
    }) && candidate
        .iter()
        .filter(|candidate_field| {
            !expected
                .iter()
                .any(|field| field.name == candidate_field.name)
        })
        .all(|candidate_field| candidate_field.optional)
}

fn type_args_structurally_compatible_for_call(
    expected: &DemandTypeArg,
    candidate: &DemandTypeArg,
) -> bool {
    match (expected, candidate) {
        (DemandTypeArg::Type(expected), DemandTypeArg::Type(candidate)) => {
            core_types_structurally_compatible_for_call(expected, candidate)
        }
        (
            DemandTypeArg::Bounds {
                lower: expected_lower,
                upper: expected_upper,
            },
            DemandTypeArg::Bounds {
                lower: candidate_lower,
                upper: candidate_upper,
            },
        ) => {
            optional_core_types_structurally_compatible_for_call(expected_lower, candidate_lower)
                && optional_core_types_structurally_compatible_for_call(
                    expected_upper,
                    candidate_upper,
                )
        }
        (DemandTypeArg::Type(expected), DemandTypeArg::Bounds { lower, upper })
        | (DemandTypeArg::Bounds { lower, upper }, DemandTypeArg::Type(expected)) => {
            lower.as_ref().or(upper.as_ref()).is_some_and(|candidate| {
                core_types_structurally_compatible_for_call(expected, candidate)
            })
        }
    }
}

fn optional_core_types_structurally_compatible_for_call(
    expected: &Option<DemandCoreType>,
    candidate: &Option<DemandCoreType>,
) -> bool {
    match (expected, candidate) {
        (Some(expected), Some(candidate)) => {
            core_types_structurally_compatible_for_call(expected, candidate)
        }
        (None, _) | (_, None) => true,
    }
}

fn role_impl_receiver_compatible(candidate: &DemandSignature, call: &DemandSignature) -> bool {
    let (candidate_args, _) = uncurried_emit_signatures(candidate.clone());
    let (call_args, _) = uncurried_emit_signatures(call.clone());
    let Some((candidate_receiver, call_receiver)) = candidate_args.first().zip(call_args.first())
    else {
        return false;
    };
    let candidate_receiver = signature_value(candidate_receiver);
    let call_receiver = signature_value(call_receiver);
    signatures_compatible_for_call(&call_receiver, &candidate_receiver)
        || signatures_compatible_for_call(&candidate_receiver, &call_receiver)
}

fn strengthen_handler_arg_signatures(
    target: &core_ir::Path,
    mut args: Vec<DemandSignature>,
    hints: &[Option<DemandSignature>],
    ret: &DemandSignature,
) -> Vec<DemandSignature> {
    if known_consumed_effects_for_target(target).is_empty() {
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

fn expected_requires_empty_thunk_not_present_in_candidate(
    expected: &DemandSignature,
    candidate: &DemandSignature,
) -> bool {
    match (expected, candidate) {
        (
            DemandSignature::Fun {
                ret: expected_ret, ..
            },
            DemandSignature::Fun {
                ret: candidate_ret, ..
            },
        ) => expected_requires_empty_thunk_not_present_in_candidate(expected_ret, candidate_ret),
        (
            DemandSignature::Thunk {
                effect: expected_effect,
                value: expected_value,
            },
            DemandSignature::Thunk {
                effect: candidate_effect,
                value: candidate_value,
            },
        ) if demand_effect_is_empty(expected_effect)
            && demand_effect_is_empty(candidate_effect) =>
        {
            expected_requires_empty_thunk_not_present_in_candidate(expected_value, candidate_value)
        }
        (DemandSignature::Thunk { effect, .. }, candidate)
            if demand_effect_is_empty(effect)
                && !matches!(candidate, DemandSignature::Thunk { .. }) =>
        {
            true
        }
        _ => false,
    }
}

fn erase_empty_thunks(signature: &DemandSignature) -> DemandSignature {
    match signature {
        DemandSignature::Fun { param, ret } => DemandSignature::Fun {
            param: Box::new(erase_empty_thunks(param)),
            ret: Box::new(erase_empty_thunks(ret)),
        },
        DemandSignature::Thunk { effect, value } if demand_effect_is_empty(effect) => {
            erase_empty_thunks(value)
        }
        DemandSignature::Thunk { effect, value } => DemandSignature::Thunk {
            effect: effect.clone(),
            value: Box::new(erase_empty_thunks(value)),
        },
        other => other.clone(),
    }
}

fn erase_consumed_return_thunks(
    signature: &DemandSignature,
    consumed: &[core_ir::Path],
) -> DemandSignature {
    match signature {
        DemandSignature::Fun { param, ret } => DemandSignature::Fun {
            param: param.clone(),
            ret: Box::new(erase_consumed_return_thunks(ret, consumed)),
        },
        DemandSignature::Thunk { effect, value }
            if demand_effect_is_consumed_by(effect, consumed) =>
        {
            erase_consumed_return_thunks(value, consumed)
        }
        DemandSignature::Thunk { effect, value } => DemandSignature::Thunk {
            effect: effect.clone(),
            value: Box::new(erase_consumed_return_thunks(value, consumed)),
        },
        other => other.clone(),
    }
}

fn known_consumed_effects_for_target(target: &core_ir::Path) -> Vec<core_ir::Path> {
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

fn core_effect_is_unknown(effect: &core_ir::Type) -> bool {
    matches!(effect, core_ir::Type::Any | core_ir::Type::Var(_))
}

fn remove_core_effects(effect: core_ir::Type, consumed: &[core_ir::Path]) -> core_ir::Type {
    match effect {
        core_ir::Type::Named { path, args: _ }
            if consumed
                .iter()
                .any(|consumed| effect_paths_match(consumed, &path)) =>
        {
            core_ir::Type::Never
        }
        core_ir::Type::Row { items, tail } => {
            let items = items
                .into_iter()
                .map(|item| remove_core_effects(item, consumed))
                .filter(|item| !matches!(item, core_ir::Type::Never))
                .collect::<Vec<_>>();
            let tail = Box::new(remove_core_effects(*tail, consumed));
            if items.is_empty() && matches!(tail.as_ref(), core_ir::Type::Never) {
                core_ir::Type::Never
            } else {
                core_ir::Type::Row { items, tail }
            }
        }
        other => other,
    }
}

fn demand_effect_is_consumed_by(effect: &DemandEffect, consumed: &[core_ir::Path]) -> bool {
    match effect {
        DemandEffect::Empty | DemandEffect::Hole(_) => false,
        DemandEffect::Atom(ty) => demand_effect_path(ty).is_some_and(|path| {
            consumed
                .iter()
                .any(|effect| effect_paths_match(effect, path))
        }),
        DemandEffect::Row(items) => items
            .iter()
            .any(|item| demand_effect_is_consumed_by(item, consumed)),
    }
}

fn demand_effect_path(ty: &DemandCoreType) -> Option<&core_ir::Path> {
    match ty {
        DemandCoreType::Named { path, .. } => Some(path),
        _ => None,
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

fn path_segments(segments: &[&str]) -> core_ir::Path {
    core_ir::Path {
        segments: segments
            .iter()
            .map(|segment| core_ir::Name((*segment).to_string()))
            .collect(),
    }
}

fn bind_here_result_type(
    original: &Expr,
    inner: &Expr,
    expected: Option<&DemandSignature>,
) -> Result<RuntimeType, DemandEmitError> {
    if let Some(expected) = expected.filter(|signature| signature.is_closed()) {
        return runtime_type(expected);
    }
    match &inner.ty {
        RuntimeType::Thunk { value, .. } => Ok(*value.clone()),
        _ => Ok(original.ty.clone()),
    }
}

fn force_thunk_callee_to_function(mut callee: Expr) -> Result<Expr, DemandEmitError> {
    loop {
        let RuntimeType::Thunk { value, .. } = &callee.ty else {
            return Ok(callee);
        };
        if !runtime_type_is_function(value) {
            return Ok(callee);
        }
        let value_ty = value.as_ref().clone();
        callee = Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(callee),
            },
            value_ty,
        );
    }
}

fn runtime_type_is_function(ty: &RuntimeType) -> bool {
    matches!(
        ty,
        RuntimeType::Fun { .. } | RuntimeType::Core(core_ir::Type::Fun { .. })
    )
}

fn signature_returns_function(signature: &DemandSignature) -> bool {
    match signature {
        DemandSignature::Fun { .. } => true,
        DemandSignature::Thunk { value, .. } => signature_returns_function(value),
        DemandSignature::Core(DemandCoreType::Fun { .. }) => true,
        DemandSignature::Ignored | DemandSignature::Hole(_) | DemandSignature::Core(_) => false,
    }
}

fn apply_param_signature(ty: &RuntimeType) -> Option<DemandSignature> {
    match ty {
        RuntimeType::Fun { param, .. } => Some(DemandSignature::from_runtime_type(param)),
        RuntimeType::Core(core_ir::Type::Fun {
            param,
            param_effect,
            ..
        }) => {
            let param =
                DemandSignature::from_runtime_type(&RuntimeType::core(param.as_ref().clone()));
            Some(effected_core_signature(
                signature_core_value(&param),
                DemandEffect::from_core_type(param_effect),
            ))
        }
        _ => None,
    }
}

fn apply_result_runtime_type(callee: &Expr) -> Option<RuntimeType> {
    match &callee.ty {
        RuntimeType::Fun { ret, .. } => Some(*ret.clone()),
        RuntimeType::Core(core_ir::Type::Fun {
            ret, ret_effect, ..
        }) => Some(effected_runtime_type(*ret.clone(), *ret_effect.clone())),
        _ => None,
    }
}

fn effected_runtime_type(value: core_ir::Type, effect: core_ir::Type) -> RuntimeType {
    if matches!(effect, core_ir::Type::Never) {
        RuntimeType::core(value)
    } else {
        RuntimeType::thunk(effect, RuntimeType::core(value))
    }
}

fn force_arg_to_expected_value(
    arg: Expr,
    expected: &DemandSignature,
) -> Result<Expr, DemandEmitError> {
    if !expected.is_closed() {
        return Ok(arg);
    }
    if let DemandSignature::Thunk { effect, value } = expected {
        return wrap_arg_in_empty_thunk(arg, effect, value);
    }
    let RuntimeType::Thunk { value, .. } = &arg.ty else {
        return Ok(arg);
    };
    let actual_value = DemandSignature::from_runtime_type(value);
    if DemandUnifier::new()
        .unify_signature(expected, &actual_value)
        .is_err()
    {
        return Ok(arg);
    }
    Ok(Expr::typed(
        ExprKind::BindHere {
            expr: Box::new(arg),
        },
        runtime_type(expected)?,
    ))
}

fn wrap_arg_in_empty_thunk(
    arg: Expr,
    effect: &DemandEffect,
    expected_value: &DemandSignature,
) -> Result<Expr, DemandEmitError> {
    if !matches!(effect, DemandEffect::Empty) || matches!(arg.ty, RuntimeType::Thunk { .. }) {
        return Ok(arg);
    }
    let actual = DemandSignature::from_runtime_type(&arg.ty);
    if DemandUnifier::new()
        .unify_signature(expected_value, &actual)
        .is_err()
    {
        return Ok(arg);
    }
    let value_ty = runtime_type(expected_value)?;
    Ok(Expr::typed(
        ExprKind::Thunk {
            effect: core_ir::Type::Never,
            value: value_ty.clone(),
            expr: Box::new(arg),
        },
        RuntimeType::thunk(core_ir::Type::Never, value_ty),
    ))
}

fn runtime_type(signature: &DemandSignature) -> Result<RuntimeType, DemandEmitError> {
    Ok(match signature {
        DemandSignature::Ignored => RuntimeType::core(core_ir::Type::Any),
        DemandSignature::Hole(id) => return Err(DemandEmitError::UnresolvedValueHole(*id)),
        DemandSignature::Core(ty) => RuntimeType::core(core_type(ty)?),
        DemandSignature::Fun { param, ret } => {
            RuntimeType::fun(runtime_type(param)?, runtime_type(ret)?)
        }
        DemandSignature::Thunk { effect, value } => {
            RuntimeType::thunk(effect_type(effect)?, runtime_type(value)?)
        }
    })
}

fn runtime_shape_type(signature: &DemandSignature) -> Result<RuntimeType, DemandEmitError> {
    Ok(match signature {
        DemandSignature::Ignored | DemandSignature::Hole(_) => {
            RuntimeType::core(core_ir::Type::Any)
        }
        DemandSignature::Core(ty) => RuntimeType::core(core_shape_type(ty)?),
        DemandSignature::Fun { param, ret } => {
            RuntimeType::fun(runtime_shape_type(param)?, runtime_shape_type(ret)?)
        }
        DemandSignature::Thunk { effect, value } => {
            RuntimeType::thunk(effect_shape_type(effect)?, runtime_shape_type(value)?)
        }
    })
}

fn core_type(ty: &DemandCoreType) -> Result<core_ir::Type, DemandEmitError> {
    Ok(match ty {
        DemandCoreType::Any => core_ir::Type::Any,
        DemandCoreType::Never => core_ir::Type::Never,
        DemandCoreType::Hole(id) => return Err(DemandEmitError::UnresolvedCoreHole(*id)),
        DemandCoreType::Named { path, args } => core_ir::Type::Named {
            path: path.clone(),
            args: args
                .iter()
                .map(type_arg)
                .collect::<Result<Vec<_>, DemandEmitError>>()?,
        },
        DemandCoreType::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => core_ir::Type::Fun {
            param: Box::new(core_type(param)?),
            param_effect: Box::new(effect_type(param_effect)?),
            ret_effect: Box::new(effect_type(ret_effect)?),
            ret: Box::new(core_type(ret)?),
        },
        DemandCoreType::Tuple(items) => core_ir::Type::Tuple(
            items
                .iter()
                .map(core_type)
                .collect::<Result<Vec<_>, DemandEmitError>>()?,
        ),
        DemandCoreType::Record(fields) => core_ir::Type::Record(core_ir::RecordType {
            fields: fields
                .iter()
                .map(|field| {
                    Ok(core_ir::RecordField {
                        name: field.name.clone(),
                        value: core_type(&field.value)?,
                        optional: field.optional,
                    })
                })
                .collect::<Result<Vec<_>, DemandEmitError>>()?,
            spread: None,
        }),
        DemandCoreType::Variant(cases) => core_ir::Type::Variant(core_ir::VariantType {
            cases: cases
                .iter()
                .map(|case| {
                    Ok(core_ir::VariantCase {
                        name: case.name.clone(),
                        payloads: case.payloads.iter().map(core_type).collect::<Result<
                            Vec<_>,
                            DemandEmitError,
                        >>(
                        )?,
                    })
                })
                .collect::<Result<Vec<_>, DemandEmitError>>()?,
            tail: None,
        }),
        DemandCoreType::RowAsValue(items) => row_type(items)?,
        DemandCoreType::Union(items) => core_ir::Type::Union(
            items
                .iter()
                .map(core_type)
                .collect::<Result<Vec<_>, DemandEmitError>>()?,
        ),
        DemandCoreType::Inter(items) => core_ir::Type::Inter(
            items
                .iter()
                .map(core_type)
                .collect::<Result<Vec<_>, DemandEmitError>>()?,
        ),
        DemandCoreType::Recursive { var, body } => core_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(core_type(body)?),
        },
    })
}

fn core_shape_type(ty: &DemandCoreType) -> Result<core_ir::Type, DemandEmitError> {
    Ok(match ty {
        DemandCoreType::Any | DemandCoreType::Hole(_) => core_ir::Type::Any,
        DemandCoreType::Never => core_ir::Type::Never,
        DemandCoreType::Named { path, args } => core_ir::Type::Named {
            path: path.clone(),
            args: args
                .iter()
                .map(type_arg_shape)
                .collect::<Result<Vec<_>, DemandEmitError>>()?,
        },
        DemandCoreType::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => core_ir::Type::Fun {
            param: Box::new(core_shape_type(param)?),
            param_effect: Box::new(effect_shape_type(param_effect)?),
            ret_effect: Box::new(effect_shape_type(ret_effect)?),
            ret: Box::new(core_shape_type(ret)?),
        },
        DemandCoreType::Tuple(items) => core_ir::Type::Tuple(
            items
                .iter()
                .map(core_shape_type)
                .collect::<Result<Vec<_>, DemandEmitError>>()?,
        ),
        DemandCoreType::Record(fields) => core_ir::Type::Record(core_ir::RecordType {
            fields: fields
                .iter()
                .map(|field| {
                    Ok(core_ir::RecordField {
                        name: field.name.clone(),
                        value: core_shape_type(&field.value)?,
                        optional: field.optional,
                    })
                })
                .collect::<Result<Vec<_>, DemandEmitError>>()?,
            spread: None,
        }),
        DemandCoreType::Variant(cases) => core_ir::Type::Variant(core_ir::VariantType {
            cases: cases
                .iter()
                .map(|case| {
                    Ok(core_ir::VariantCase {
                        name: case.name.clone(),
                        payloads: case.payloads.iter().map(core_shape_type).collect::<Result<
                            Vec<_>,
                            DemandEmitError,
                        >>(
                        )?,
                    })
                })
                .collect::<Result<Vec<_>, DemandEmitError>>()?,
            tail: None,
        }),
        DemandCoreType::RowAsValue(items) => row_shape_type(items)?,
        DemandCoreType::Union(items) => core_ir::Type::Union(
            items
                .iter()
                .map(core_shape_type)
                .collect::<Result<Vec<_>, DemandEmitError>>()?,
        ),
        DemandCoreType::Inter(items) => core_ir::Type::Inter(
            items
                .iter()
                .map(core_shape_type)
                .collect::<Result<Vec<_>, DemandEmitError>>()?,
        ),
        DemandCoreType::Recursive { var, body } => core_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(core_shape_type(body)?),
        },
    })
}

fn effect_type(effect: &DemandEffect) -> Result<core_ir::Type, DemandEmitError> {
    match effect {
        DemandEffect::Empty => Ok(core_ir::Type::Never),
        DemandEffect::Hole(id) => Err(DemandEmitError::UnresolvedEffectHole(*id)),
        DemandEffect::Atom(ty) => core_type(ty),
        DemandEffect::Row(items) => row_type(items),
    }
}

fn effect_shape_type(effect: &DemandEffect) -> Result<core_ir::Type, DemandEmitError> {
    match effect {
        DemandEffect::Empty => Ok(core_ir::Type::Never),
        DemandEffect::Hole(_) => Ok(core_ir::Type::Any),
        DemandEffect::Atom(ty) => core_shape_type(ty),
        DemandEffect::Row(items) => row_shape_type(items),
    }
}

fn row_type(items: &[DemandEffect]) -> Result<core_ir::Type, DemandEmitError> {
    let mut flat = Vec::new();
    for item in items {
        push_effect_items(item, &mut flat)?;
    }
    Ok(match flat.as_slice() {
        [] => core_ir::Type::Never,
        [single] => single.clone(),
        _ => core_ir::Type::Row {
            items: flat,
            tail: Box::new(core_ir::Type::Never),
        },
    })
}

fn row_shape_type(items: &[DemandEffect]) -> Result<core_ir::Type, DemandEmitError> {
    let mut flat = Vec::new();
    for item in items {
        push_effect_shape_items(item, &mut flat)?;
    }
    Ok(match flat.as_slice() {
        [] => core_ir::Type::Never,
        [single] => single.clone(),
        _ => core_ir::Type::Row {
            items: flat,
            tail: Box::new(core_ir::Type::Never),
        },
    })
}

fn push_effect_items(
    effect: &DemandEffect,
    out: &mut Vec<core_ir::Type>,
) -> Result<(), DemandEmitError> {
    match effect {
        DemandEffect::Empty => Ok(()),
        DemandEffect::Hole(id) => Err(DemandEmitError::UnresolvedEffectHole(*id)),
        DemandEffect::Atom(ty) => {
            out.push(core_type(ty)?);
            Ok(())
        }
        DemandEffect::Row(items) => {
            for item in items {
                push_effect_items(item, out)?;
            }
            Ok(())
        }
    }
}

fn push_effect_shape_items(
    effect: &DemandEffect,
    out: &mut Vec<core_ir::Type>,
) -> Result<(), DemandEmitError> {
    match effect {
        DemandEffect::Empty => Ok(()),
        DemandEffect::Hole(_) => {
            out.push(core_ir::Type::Any);
            Ok(())
        }
        DemandEffect::Atom(ty) => {
            out.push(core_shape_type(ty)?);
            Ok(())
        }
        DemandEffect::Row(items) => {
            for item in items {
                push_effect_shape_items(item, out)?;
            }
            Ok(())
        }
    }
}

fn type_arg(arg: &DemandTypeArg) -> Result<core_ir::TypeArg, DemandEmitError> {
    Ok(match arg {
        DemandTypeArg::Type(ty) => core_ir::TypeArg::Type(core_type(ty)?),
        DemandTypeArg::Bounds { lower, upper } => core_ir::TypeArg::Bounds(core_ir::TypeBounds {
            lower: lower.as_ref().map(core_type).transpose()?.map(Box::new),
            upper: upper.as_ref().map(core_type).transpose()?.map(Box::new),
        }),
    })
}

fn type_arg_shape(arg: &DemandTypeArg) -> Result<core_ir::TypeArg, DemandEmitError> {
    Ok(match arg {
        DemandTypeArg::Type(ty) => core_ir::TypeArg::Type(core_shape_type(ty)?),
        DemandTypeArg::Bounds { lower, upper } => core_ir::TypeArg::Bounds(core_ir::TypeBounds {
            lower: lower
                .as_ref()
                .map(core_shape_type)
                .transpose()?
                .map(Box::new),
            upper: upper
                .as_ref()
                .map(core_shape_type)
                .transpose()?
                .map(Box::new),
        }),
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

fn single_binding_signature<'a>(
    pattern: &Pattern,
    bindings: &'a [(core_ir::Path, DemandSignature)],
) -> Option<&'a DemandSignature> {
    if !matches!(pattern, Pattern::Bind { .. }) {
        return None;
    }
    bindings.first().map(|(_, signature)| signature)
}

fn collect_pattern_bind_paths(pattern: &Pattern, out: &mut Vec<core_ir::Path>) {
    match pattern {
        Pattern::Bind { name, .. } => {
            out.push(core_ir::Path::from_name(name.clone()));
        }
        Pattern::Tuple { items, .. } => {
            for item in items {
                collect_pattern_bind_paths(item, out);
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                collect_pattern_bind_paths(item, out);
            }
            if let Some(spread) = spread {
                collect_pattern_bind_paths(spread, out);
            }
            for item in suffix {
                collect_pattern_bind_paths(item, out);
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                collect_pattern_bind_paths(&field.pattern, out);
            }
            if let Some(spread) = spread {
                match spread {
                    crate::ir::RecordSpreadPattern::Head(pattern)
                    | crate::ir::RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_bind_paths(pattern, out);
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                collect_pattern_bind_paths(value, out);
            }
        }
        Pattern::Or { left, right, .. } => {
            collect_pattern_bind_paths(left, out);
            collect_pattern_bind_paths(right, out);
        }
        Pattern::As { pattern, name, .. } => {
            collect_pattern_bind_paths(pattern, out);
            out.push(core_ir::Path::from_name(name.clone()));
        }
        Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
    }
}

fn next_effect_id_after_expr(expr: &Expr) -> usize {
    max_effect_id_expr(expr).map_or(0, |id| id + 1)
}

fn max_effect_id_expr(expr: &Expr) -> Option<usize> {
    let mut max = None;
    match &expr.kind {
        ExprKind::Lambda { body, .. } => update_max(&mut max, max_effect_id_expr(body)),
        ExprKind::Apply { callee, arg, .. } => {
            update_max(&mut max, max_effect_id_expr(callee));
            update_max(&mut max, max_effect_id_expr(arg));
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            update_max(&mut max, max_effect_id_expr(cond));
            update_max(&mut max, max_effect_id_expr(then_branch));
            update_max(&mut max, max_effect_id_expr(else_branch));
        }
        ExprKind::Tuple(items) => {
            for item in items {
                update_max(&mut max, max_effect_id_expr(item));
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                update_max(&mut max, max_effect_id_expr(&field.value));
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        update_max(&mut max, max_effect_id_expr(expr));
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                update_max(&mut max, max_effect_id_expr(value));
            }
        }
        ExprKind::Select { base, .. } => update_max(&mut max, max_effect_id_expr(base)),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            update_max(&mut max, max_effect_id_expr(scrutinee));
            for arm in arms {
                update_max(&mut max, max_effect_id_pattern(&arm.pattern));
                if let Some(guard) = &arm.guard {
                    update_max(&mut max, max_effect_id_expr(guard));
                }
                update_max(&mut max, max_effect_id_expr(&arm.body));
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                update_max(&mut max, max_effect_id_stmt(stmt));
            }
            if let Some(tail) = tail {
                update_max(&mut max, max_effect_id_expr(tail));
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            update_max(&mut max, max_effect_id_expr(body));
            for arm in arms {
                update_max(&mut max, max_effect_id_pattern(&arm.payload));
                if let Some(guard) = &arm.guard {
                    update_max(&mut max, max_effect_id_expr(guard));
                }
                update_max(&mut max, max_effect_id_expr(&arm.body));
            }
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => update_max(&mut max, max_effect_id_expr(expr)),
        ExprKind::LocalPushId { id, body } => {
            update_max(&mut max, Some(id.0));
            update_max(&mut max, max_effect_id_expr(body));
        }
        ExprKind::FindId { id } => update_max(&mut max, max_effect_id_ref(*id)),
        ExprKind::AddId { id, thunk, .. } => {
            update_max(&mut max, max_effect_id_ref(*id));
            update_max(&mut max, max_effect_id_expr(thunk));
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId => {}
    }
    max
}

fn max_effect_id_stmt(stmt: &Stmt) -> Option<usize> {
    let mut max = None;
    match stmt {
        Stmt::Let { pattern, value } => {
            update_max(&mut max, max_effect_id_pattern(pattern));
            update_max(&mut max, max_effect_id_expr(value));
        }
        Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => {
            update_max(&mut max, max_effect_id_expr(expr));
        }
    }
    max
}

fn max_effect_id_pattern(pattern: &Pattern) -> Option<usize> {
    let mut max = None;
    match pattern {
        Pattern::Tuple { items, .. } => {
            for item in items {
                update_max(&mut max, max_effect_id_pattern(item));
            }
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                update_max(&mut max, max_effect_id_pattern(item));
            }
            if let Some(spread) = spread {
                update_max(&mut max, max_effect_id_pattern(spread));
            }
            for item in suffix {
                update_max(&mut max, max_effect_id_pattern(item));
            }
        }
        Pattern::Record { fields, spread, .. } => {
            for field in fields {
                update_max(&mut max, max_effect_id_pattern(&field.pattern));
                if let Some(default) = &field.default {
                    update_max(&mut max, max_effect_id_expr(default));
                }
            }
            if let Some(spread) = spread {
                match spread {
                    crate::ir::RecordSpreadPattern::Head(pattern)
                    | crate::ir::RecordSpreadPattern::Tail(pattern) => {
                        update_max(&mut max, max_effect_id_pattern(pattern));
                    }
                }
            }
        }
        Pattern::Variant { value, .. } => {
            if let Some(value) = value {
                update_max(&mut max, max_effect_id_pattern(value));
            }
        }
        Pattern::Or { left, right, .. } => {
            update_max(&mut max, max_effect_id_pattern(left));
            update_max(&mut max, max_effect_id_pattern(right));
        }
        Pattern::As { pattern, .. } => update_max(&mut max, max_effect_id_pattern(pattern)),
        Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => {}
    }
    max
}

fn max_effect_id_ref(id: EffectIdRef) -> Option<usize> {
    match id {
        EffectIdRef::Var(id) => Some(id.0),
        EffectIdRef::Peek => None,
    }
}

fn update_max(max: &mut Option<usize>, value: Option<usize>) {
    if let Some(value) = value {
        *max = Some(max.map_or(value, |current| current.max(value)));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{EffectIdRef, Root};

    #[test]
    fn emitter_creates_monomorphic_binding_with_solved_type() {
        let id = path("id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![generic_identity(id.clone())],
            root_exprs: Vec::new(),
            roots: Vec::new(),
        };
        let specialization = specialization(&id, "id__ddmono0", fun(core("int"), core("int")));
        let emitter = DemandEmitter::from_module(&module, std::slice::from_ref(&specialization));

        let emitted = emitter.emit(&specialization).expect("emitted binding");

        assert_eq!(emitted.name, path("id__ddmono0"));
        assert!(emitted.type_params.is_empty());
        assert_eq!(emitted.body.ty, rt_fun("int", "int"));
        let ExprKind::Lambda { body, .. } = &emitted.body.kind else {
            panic!("expected lambda");
        };
        assert_eq!(body.ty, RuntimeType::core(named("int")));
        assert_eq!(
            emitted.scheme.body,
            runtime_core_type(&rt_fun("int", "int"))
        );
    }

    #[test]
    fn emitter_rewrites_generic_child_call_to_specialization() {
        let id = path("id");
        let use_id = path("use_id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![
                generic_identity(id.clone()),
                generic_use_id(use_id.clone(), id.clone()),
            ],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(use_id.clone())],
        };
        let id_spec = specialization(&id, "id__ddmono0", fun(core("int"), core("int")));
        let use_id_spec = specialization(&use_id, "use_id__ddmono1", fun(core("int"), core("int")));
        let specializations = vec![id_spec.clone(), use_id_spec.clone()];
        let emitter = DemandEmitter::from_module(&module, &specializations);

        let emitted = emitter.emit(&use_id_spec).expect("emitted binding");

        let ExprKind::Lambda { body, .. } = &emitted.body.kind else {
            panic!("expected lambda");
        };
        let ExprKind::Apply { callee, arg, .. } = &body.kind else {
            panic!("expected apply");
        };
        assert_eq!(arg.ty, RuntimeType::core(named("int")));
        let ExprKind::Var(callee_path) = &callee.kind else {
            panic!("expected specialized callee");
        };
        assert_eq!(callee_path, &path("id__ddmono0"));
        assert_eq!(callee.ty, rt_fun("int", "int"));
    }

    #[test]
    fn emitter_uses_known_specializations_when_emitting_fresh_binding() {
        let id = path("id");
        let use_id = path("use_id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![
                generic_identity(id.clone()),
                generic_use_id(use_id.clone(), id.clone()),
            ],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(use_id.clone())],
        };
        let id_spec = specialization(&id, "id__ddmono0", fun(core("int"), core("int")));
        let use_id_spec = specialization(&use_id, "use_id__ddmono1", fun(core("int"), core("int")));
        let known = vec![id_spec, use_id_spec.clone()];
        let emit = vec![use_id_spec.clone()];
        let emitter = DemandEmitter::from_module_with_known(&module, &emit, &known);

        let emitted = emitter.emit(&use_id_spec).expect("emitted binding");

        let ExprKind::Lambda { body, .. } = &emitted.body.kind else {
            panic!("expected lambda");
        };
        let ExprKind::Apply { callee, .. } = &body.kind else {
            panic!("expected apply");
        };
        let ExprKind::Var(callee_path) = &callee.kind else {
            panic!("expected specialized callee");
        };
        assert_eq!(callee_path, &path("id__ddmono0"));
    }

    #[test]
    fn emitter_rewrites_legacy_mono_call_to_demand_specialization() {
        let id = path("id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(path("id__mono3")),
                        rt_fun("int", "int"),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                        RuntimeType::core(named("int")),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::core(named("int")),
            )],
            roots: Vec::new(),
        };
        let specialization = specialization(&id, "id__ddmono0", fun(core("int"), core("int")));

        let rewrite = DemandEmitter::rewrite_module_uses_with_specializations_report(
            module,
            std::slice::from_ref(&specialization),
        )
        .expect("rewritten module");

        assert_eq!(rewrite.changed_roots, 1);
        let ExprKind::Apply { callee, .. } = &rewrite.module.root_exprs[0].kind else {
            panic!("expected apply");
        };
        let ExprKind::Var(callee_path) = &callee.kind else {
            panic!("expected specialized callee");
        };
        assert_eq!(callee_path, &path("id__ddmono0"));
    }

    #[test]
    fn emitter_rewrites_calls_inside_closed_legacy_mono_binding() {
        let id = path("id");
        let use_id = path("use_id__mono3");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![Binding {
                name: use_id.clone(),
                type_params: Vec::new(),
                scheme: core_ir::Scheme {
                    requirements: Vec::new(),
                    body: runtime_core_type(&rt_fun("int", "int")),
                },
                body: Expr::typed(
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Apply {
                                callee: Box::new(Expr::typed(
                                    ExprKind::Var(id.clone()),
                                    rt_fun("int", "int"),
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
                    rt_fun("int", "int"),
                ),
            }],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(use_id.clone())],
        };
        let specialization = specialization(&id, "id__ddmono0", fun(core("int"), core("int")));

        let rewrite = DemandEmitter::rewrite_module_uses_with_specializations_report(
            module,
            std::slice::from_ref(&specialization),
        )
        .expect("rewritten module");

        assert_eq!(rewrite.changed_bindings, 1);
        let ExprKind::Lambda { body, .. } = &rewrite.module.bindings[0].body.kind else {
            panic!("expected lambda");
        };
        let ExprKind::Apply { callee, .. } = &body.kind else {
            panic!("expected apply");
        };
        let ExprKind::Var(callee_path) = &callee.kind else {
            panic!("expected specialized callee");
        };
        assert_eq!(callee_path, &path("id__ddmono0"));
    }

    #[test]
    fn emitter_leaves_legacy_mono_binding_when_rewrite_has_unresolved_holes() {
        let id = path("id");
        let use_id = path("use_id__mono3");
        let open_opt = DemandCoreType::Named {
            path: path("opt"),
            args: vec![DemandTypeArg::Type(DemandCoreType::Hole(0))],
        };
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![Binding {
                name: use_id.clone(),
                type_params: Vec::new(),
                scheme: core_ir::Scheme {
                    requirements: Vec::new(),
                    body: runtime_core_type(&RuntimeType::fun(
                        RuntimeType::core(named("int")),
                        RuntimeType::core(core_ir::Type::Any),
                    )),
                },
                body: Expr::typed(
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Apply {
                                callee: Box::new(Expr::typed(
                                    ExprKind::Var(id.clone()),
                                    RuntimeType::fun(
                                        RuntimeType::core(named("int")),
                                        RuntimeType::core(core_ir::Type::Any),
                                    ),
                                )),
                                arg: Box::new(Expr::typed(
                                    ExprKind::Var(path("x")),
                                    RuntimeType::core(named("int")),
                                )),
                                evidence: None,
                                instantiation: None,
                            },
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                    },
                    RuntimeType::fun(
                        RuntimeType::core(named("int")),
                        RuntimeType::core(core_ir::Type::Any),
                    ),
                ),
            }],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(use_id.clone())],
        };
        let specialization = specialization(
            &id,
            "id__ddmono0",
            fun(core("int"), DemandSignature::Core(open_opt)),
        );

        let rewrite = DemandEmitter::rewrite_module_uses_with_specializations_report(
            module,
            std::slice::from_ref(&specialization),
        )
        .expect("legacy rewrite should be recoverable");

        assert_eq!(rewrite.changed_bindings, 0);
        let ExprKind::Lambda { body, .. } = &rewrite.module.bindings[0].body.kind else {
            panic!("expected lambda");
        };
        let ExprKind::Apply { callee, .. } = &body.kind else {
            panic!("expected apply");
        };
        let ExprKind::Var(callee_path) = &callee.kind else {
            panic!("expected original callee");
        };
        assert_eq!(callee_path, &id);
    }

    #[test]
    fn emitter_matches_specialization_by_solved_signature() {
        let id = path("id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(path("id__mono3")),
                        rt_fun("int", "int"),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                        RuntimeType::core(named("int")),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::core(named("int")),
            )],
            roots: Vec::new(),
        };
        let specialization = DemandSpecialization {
            target: id.clone(),
            path: path("id__ddmono0"),
            key: DemandKey::from_signature(id, fun(core("str"), core("str"))),
            solved: fun(core("int"), core("int")),
        };

        let rewrite = DemandEmitter::rewrite_module_uses_with_specializations_report(
            module,
            std::slice::from_ref(&specialization),
        )
        .expect("rewritten module");

        assert_eq!(rewrite.changed_roots, 1);
        let ExprKind::Apply { callee, .. } = &rewrite.module.root_exprs[0].kind else {
            panic!("expected apply");
        };
        let ExprKind::Var(callee_path) = &callee.kind else {
            panic!("expected specialized callee");
        };
        assert_eq!(callee_path, &path("id__ddmono0"));
    }

    #[test]
    fn emitter_matches_specialization_with_empty_thunk_argument() {
        let id = path("id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(path("id__mono3")),
                        RuntimeType::fun(
                            RuntimeType::thunk(
                                core_ir::Type::Never,
                                RuntimeType::core(named("int")),
                            ),
                            RuntimeType::core(named("int")),
                        ),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Thunk {
                            effect: core_ir::Type::Never,
                            value: RuntimeType::core(named("int")),
                            expr: Box::new(Expr::typed(
                                ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                                RuntimeType::core(named("int")),
                            )),
                        },
                        RuntimeType::thunk(core_ir::Type::Never, RuntimeType::core(named("int"))),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::core(named("int")),
            )],
            roots: Vec::new(),
        };
        let specialization = specialization(&id, "id__ddmono0", fun(core("int"), core("int")));

        let rewrite = DemandEmitter::rewrite_module_uses_with_specializations_report(
            module,
            std::slice::from_ref(&specialization),
        )
        .expect("rewritten module");

        let ExprKind::Apply { callee, arg, .. } = &rewrite.module.root_exprs[0].kind else {
            panic!("expected apply");
        };
        let ExprKind::Var(callee_path) = &callee.kind else {
            panic!("expected specialized callee");
        };
        assert_eq!(callee_path, &path("id__ddmono0"));
        assert!(matches!(arg.kind, ExprKind::BindHere { .. }));
    }

    #[test]
    fn emitter_deduplicates_candidates_by_solved_signature() {
        let id = path("id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(path("id__mono3")),
                        rt_fun("int", "int"),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                        RuntimeType::core(named("int")),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::core(named("int")),
            )],
            roots: Vec::new(),
        };
        let first = DemandSpecialization {
            target: id.clone(),
            path: path("id__ddmono0"),
            key: DemandKey::from_signature(id.clone(), fun(core("str"), core("str"))),
            solved: fun(core("int"), core("int")),
        };
        let second = DemandSpecialization {
            target: id.clone(),
            path: path("id__ddmono1"),
            key: DemandKey::from_signature(id, fun(core("bool"), core("bool"))),
            solved: fun(core("int"), core("int")),
        };

        let rewrite = DemandEmitter::rewrite_module_uses_with_specializations_report(
            module,
            &[first, second],
        )
        .expect("rewritten module");

        assert_eq!(rewrite.changed_roots, 1);
        let ExprKind::Apply { callee, .. } = &rewrite.module.root_exprs[0].kind else {
            panic!("expected apply");
        };
        let ExprKind::Var(callee_path) = &callee.kind else {
            panic!("expected specialized callee");
        };
        assert!([path("id__ddmono0"), path("id__ddmono1")].contains(callee_path));
    }

    #[test]
    fn emitter_prefers_non_never_specialization_when_expected_is_concrete() {
        let id = path("id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(path("id__mono3")),
                        rt_fun("int", "int"),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                        RuntimeType::core(named("int")),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::core(named("int")),
            )],
            roots: Vec::new(),
        };
        let bottom = DemandSpecialization {
            target: id.clone(),
            path: path("id__ddmono0"),
            key: DemandKey::from_signature(id.clone(), fun(core("never"), core("never"))),
            solved: DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(DemandCoreType::Never)),
                ret: Box::new(DemandSignature::Core(DemandCoreType::Never)),
            },
        };
        let concrete = DemandSpecialization {
            target: id.clone(),
            path: path("id__ddmono1"),
            key: DemandKey::from_signature(id, fun(core("int"), core("int"))),
            solved: fun(core("int"), core("int")),
        };

        let rewrite = DemandEmitter::rewrite_module_uses_with_specializations_report(
            module,
            &[bottom, concrete],
        )
        .expect("rewritten module");

        let ExprKind::Apply { callee, .. } = &rewrite.module.root_exprs[0].kind else {
            panic!("expected apply");
        };
        let ExprKind::Var(callee_path) = &callee.kind else {
            panic!("expected specialized callee");
        };
        assert_eq!(callee_path, &path("id__ddmono1"));
    }

    #[test]
    fn emitter_matches_specialization_with_empty_thunk_return() {
        let f = path("f");
        let call = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Apply {
                        callee: Box::new(Expr::typed(
                            ExprKind::Var(path("f__mono2")),
                            RuntimeType::fun(
                                RuntimeType::core(named("int")),
                                RuntimeType::fun(
                                    RuntimeType::core(named("int")),
                                    RuntimeType::core(named("int")),
                                ),
                            ),
                        )),
                        arg: Box::new(Expr::typed(
                            ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                            RuntimeType::core(named("int")),
                        )),
                        evidence: None,
                        instantiation: None,
                    },
                    RuntimeType::fun(
                        RuntimeType::core(named("int")),
                        RuntimeType::core(named("int")),
                    ),
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(core_ir::Lit::Int("2".to_string())),
                    RuntimeType::core(named("int")),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::core(named("int")),
        );
        let module = Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![call],
            roots: Vec::new(),
        };
        let spec = specialization(
            &f,
            "f__ddmono0",
            fun(
                core("int"),
                thunk(DemandEffect::Empty, fun(core("int"), core("int"))),
            ),
        );

        let rewrite =
            DemandEmitter::rewrite_module_uses_with_specializations_report(module, &[spec])
                .expect("rewritten module");

        let ExprKind::Apply { callee, .. } = &rewrite.module.root_exprs[0].kind else {
            panic!("expected outer apply");
        };
        let ExprKind::BindHere { expr: forced } = &callee.kind else {
            panic!("expected empty thunk result to be forced before next argument");
        };
        let Some((target, _, _)) = applied_call_with_head(forced) else {
            panic!("expected specialized inner call");
        };
        assert_eq!(target, &path("f__ddmono0"));
    }

    #[test]
    fn bind_here_result_type_ignores_open_expected_signature() {
        let original = Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(Expr::typed(
                    ExprKind::Var(path("action")),
                    RuntimeType::thunk(core_ir::Type::Never, RuntimeType::core(named("int"))),
                )),
            },
            RuntimeType::core(core_ir::Type::Any),
        );
        let inner = Expr::typed(
            ExprKind::Var(path("action")),
            RuntimeType::thunk(core_ir::Type::Never, RuntimeType::core(named("int"))),
        );

        let ty = bind_here_result_type(&original, &inner, Some(&DemandSignature::Hole(0)))
            .expect("bind_here type");

        assert_eq!(ty, RuntimeType::core(named("int")));
    }

    #[test]
    fn emitter_removes_bind_here_when_inner_is_already_a_value() {
        let specializations = HashMap::new();
        let mut rewriter = BodyEmitter::new(&specializations);
        let expr = Expr::typed(
            ExprKind::BindHere {
                expr: Box::new(Expr::typed(ExprKind::Var(path("f")), rt_fun("int", "int"))),
            },
            rt_fun("int", "int"),
        );

        let rewritten = rewriter.rewrite_expr(&expr, None).expect("rewritten bind");

        assert!(matches!(rewritten.kind, ExprKind::Var(_)));
        assert_eq!(rewritten.ty, rt_fun("int", "int"));
    }

    #[test]
    fn emitter_propagates_expected_thunk_through_add_id() {
        let undet = named_path(&["std", "undet", "undet"]);
        let expected = thunk(
            DemandEffect::Atom(DemandCoreType::Named {
                path: path_segments(&["std", "undet", "undet"]),
                args: Vec::new(),
            }),
            core("int"),
        );
        let original_ty =
            RuntimeType::thunk(undet.clone(), RuntimeType::core(core_ir::Type::Never));
        let expr = Expr::typed(
            ExprKind::AddId {
                id: EffectIdRef::Peek,
                allowed: undet.clone(),
                thunk: Box::new(Expr::typed(
                    ExprKind::Thunk {
                        effect: undet.clone(),
                        value: RuntimeType::core(core_ir::Type::Never),
                        expr: Box::new(Expr::typed(
                            ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                            RuntimeType::core(named("int")),
                        )),
                    },
                    original_ty,
                )),
            },
            RuntimeType::thunk(undet.clone(), RuntimeType::core(core_ir::Type::Never)),
        );
        let specializations = HashMap::new();
        let mut rewriter = BodyEmitter::new(&specializations);

        let rewritten = rewriter
            .rewrite_expr(&expr, Some(&expected))
            .expect("rewritten add_id");

        assert_eq!(
            rewritten.ty,
            RuntimeType::thunk(undet.clone(), RuntimeType::core(named("int")))
        );
        let ExprKind::AddId { thunk, .. } = &rewritten.kind else {
            panic!("expected add_id");
        };
        let ExprKind::Thunk { value, .. } = &thunk.kind else {
            panic!("expected protected thunk");
        };
        assert_eq!(value, &RuntimeType::core(named("int")));
        assert_eq!(
            thunk.ty,
            RuntimeType::thunk(undet, RuntimeType::core(named("int")))
        );
    }

    #[test]
    fn emitter_does_not_use_full_specialization_for_partial_call() {
        let f = path("f");
        let root = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Var(f.clone()),
                    RuntimeType::fun(
                        RuntimeType::core(named("int")),
                        RuntimeType::thunk(
                            core_ir::Type::Never,
                            RuntimeType::fun(
                                RuntimeType::core(named("int")),
                                RuntimeType::core(named("int")),
                            ),
                        ),
                    ),
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                    RuntimeType::core(named("int")),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::thunk(
                core_ir::Type::Never,
                RuntimeType::fun(
                    RuntimeType::core(named("int")),
                    RuntimeType::core(named("int")),
                ),
            ),
        );
        let module = Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![root],
            roots: vec![Root::Expr(0)],
        };
        let spec = specialization(
            &f,
            "f__ddmono0",
            fun(core("int"), fun(core("int"), core("int"))),
        );

        let rewrite =
            DemandEmitter::rewrite_module_uses_with_specializations_report(module, &[spec])
                .expect("rewritten module");
        let ExprKind::Apply { callee, .. } = &rewrite.module.root_exprs[0].kind else {
            panic!("expected apply");
        };
        let ExprKind::Var(callee_path) = &callee.kind else {
            panic!("expected original callee");
        };

        assert_eq!(callee_path, &f);
    }

    #[test]
    fn emitter_can_use_full_specialization_for_plain_partial_call() {
        let f = path("f");
        let root = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Var(f.clone()),
                    RuntimeType::fun(
                        RuntimeType::core(named("int")),
                        RuntimeType::fun(
                            RuntimeType::core(named("int")),
                            RuntimeType::core(named("int")),
                        ),
                    ),
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                    RuntimeType::core(named("int")),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::fun(
                RuntimeType::core(named("int")),
                RuntimeType::core(named("int")),
            ),
        );
        let module = Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![root],
            roots: vec![Root::Expr(0)],
        };
        let spec = specialization(
            &f,
            "f__ddmono0",
            fun(core("int"), fun(core("int"), core("int"))),
        );

        let rewrite =
            DemandEmitter::rewrite_module_uses_with_specializations_report(module, &[spec])
                .expect("rewritten module");
        let ExprKind::Apply { callee, .. } = &rewrite.module.root_exprs[0].kind else {
            panic!("expected apply");
        };
        let ExprKind::Var(callee_path) = &callee.kind else {
            panic!("expected original callee");
        };

        assert_eq!(callee_path, &path("f__ddmono0"));
    }

    #[test]
    fn emitter_wraps_value_arg_for_empty_thunk_parameter() {
        let id = path("id");
        let use_id = path("use_id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![Binding {
                name: use_id.clone(),
                type_params: vec![core_ir::TypeVar("a".to_string())],
                scheme: core_ir::Scheme {
                    requirements: Vec::new(),
                    body: core_ir::Type::Any,
                },
                body: Expr::typed(
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
                                    RuntimeType::core(named("int")),
                                )),
                                evidence: None,
                                instantiation: None,
                            },
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                    },
                    RuntimeType::fun(
                        RuntimeType::core(named("int")),
                        RuntimeType::core(named("int")),
                    ),
                ),
            }],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(use_id.clone())],
        };
        let id_spec = specialization(
            &id,
            "id__ddmono0",
            fun(thunk(DemandEffect::Empty, core("int")), core("int")),
        );
        let use_id_spec = specialization(&use_id, "use_id__ddmono1", fun(core("int"), core("int")));
        let specializations = vec![id_spec, use_id_spec.clone()];
        let emitter = DemandEmitter::from_module(&module, &specializations);

        let emitted = emitter.emit(&use_id_spec).expect("emitted binding");

        let ExprKind::Lambda { body, .. } = &emitted.body.kind else {
            panic!("expected lambda");
        };
        let ExprKind::Apply { arg, .. } = &body.kind else {
            panic!("expected apply");
        };
        assert!(matches!(arg.kind, ExprKind::Thunk { .. }));
        assert_eq!(
            arg.ty,
            RuntimeType::thunk(core_ir::Type::Never, RuntimeType::core(named("int")))
        );
    }

    #[test]
    fn emitter_lifts_pure_branch_to_expected_thunk() {
        let io = named("io");
        let root = Expr::typed(
            ExprKind::If {
                cond: Box::new(Expr::typed(
                    ExprKind::Lit(core_ir::Lit::Bool(true)),
                    RuntimeType::core(named("bool")),
                )),
                then_branch: Box::new(Expr::typed(
                    ExprKind::Thunk {
                        effect: io.clone(),
                        value: RuntimeType::core(named("unit")),
                        expr: Box::new(Expr::typed(
                            ExprKind::Lit(core_ir::Lit::Unit),
                            RuntimeType::core(named("unit")),
                        )),
                    },
                    RuntimeType::thunk(io.clone(), RuntimeType::core(named("unit"))),
                )),
                else_branch: Box::new(Expr::typed(
                    ExprKind::Lit(core_ir::Lit::Unit),
                    RuntimeType::core(named("unit")),
                )),
                evidence: None,
            },
            RuntimeType::thunk(io.clone(), RuntimeType::core(named("unit"))),
        );
        let module = Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![root],
            roots: vec![Root::Expr(0)],
        };

        let rewrite = DemandEmitter::rewrite_module_uses_with_specializations_report(module, &[])
            .expect("rewritten module");

        let ExprKind::If { else_branch, .. } = &rewrite.module.root_exprs[0].kind else {
            panic!("expected if");
        };
        assert!(matches!(else_branch.kind, ExprKind::Thunk { .. }));
        assert_eq!(
            else_branch.ty,
            RuntimeType::thunk(io, RuntimeType::core(named("unit")))
        );
    }

    #[test]
    fn emitter_forces_thunk_function_callee() {
        let f = path("f");
        let thunked_fun = RuntimeType::thunk(
            core_ir::Type::Never,
            RuntimeType::fun(
                RuntimeType::core(named("unit")),
                RuntimeType::core(named("int")),
            ),
        );
        let root = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(ExprKind::Var(f), thunked_fun)),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(core_ir::Lit::Unit),
                    RuntimeType::core(named("unit")),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::core(named("int")),
        );
        let module = Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![root],
            roots: vec![Root::Expr(0)],
        };

        let rewrite = DemandEmitter::rewrite_module_uses_with_specializations_report(module, &[])
            .expect("rewritten module");

        let ExprKind::Apply { callee, .. } = &rewrite.module.root_exprs[0].kind else {
            panic!("expected apply");
        };
        assert!(matches!(callee.kind, ExprKind::BindHere { .. }));
    }

    #[test]
    fn emitter_rewrites_range_fold_from_with_thunked_callback_parameter() {
        let fold_from = path_segments(&["std", "range", "fold_from"]);
        let last = named_path(&["std", "flow", "loop", "last"]);
        let callback_sig = fun(
            core("unit"),
            thunk(
                DemandEffect::Atom(DemandCoreType::Named {
                    path: path_segments(&["std", "flow", "loop", "last"]),
                    args: Vec::new(),
                }),
                fun(
                    core("int"),
                    thunk(
                        DemandEffect::Atom(DemandCoreType::Named {
                            path: path_segments(&["std", "flow", "loop", "last"]),
                            args: Vec::new(),
                        }),
                        core("unit"),
                    ),
                ),
            ),
        );
        let root = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Apply {
                        callee: Box::new(Expr::typed(
                            ExprKind::Apply {
                                callee: Box::new(Expr::typed(
                                    ExprKind::Var(fold_from.clone()),
                                    RuntimeType::fun(
                                        RuntimeType::core(core_ir::Type::Any),
                                        RuntimeType::fun(
                                            RuntimeType::core(named("int")),
                                            RuntimeType::fun(
                                                RuntimeType::core(named("unit")),
                                                RuntimeType::thunk(
                                                    last.clone(),
                                                    RuntimeType::core(named("unit")),
                                                ),
                                            ),
                                        ),
                                    ),
                                )),
                                arg: Box::new(Expr::typed(
                                    ExprKind::Var(path("f")),
                                    runtime_type(&callback_sig).expect("callback type"),
                                )),
                                evidence: None,
                                instantiation: None,
                            },
                            RuntimeType::fun(
                                RuntimeType::core(named("int")),
                                RuntimeType::fun(
                                    RuntimeType::core(named("unit")),
                                    RuntimeType::thunk(
                                        last.clone(),
                                        RuntimeType::core(named("unit")),
                                    ),
                                ),
                            ),
                        )),
                        arg: Box::new(Expr::typed(
                            ExprKind::Lit(core_ir::Lit::Int("0".to_string())),
                            RuntimeType::core(named("int")),
                        )),
                        evidence: None,
                        instantiation: None,
                    },
                    RuntimeType::fun(
                        RuntimeType::core(named("unit")),
                        RuntimeType::thunk(last.clone(), RuntimeType::core(named("unit"))),
                    ),
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(core_ir::Lit::Unit),
                    RuntimeType::core(named("unit")),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::thunk(last, RuntimeType::core(named("unit"))),
        );
        let module = Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![root],
            roots: vec![Root::Expr(0)],
        };
        let spec = specialization(
            &fold_from,
            "fold_from__ddmono0",
            fun(
                thunk(DemandEffect::Empty, callback_sig),
                fun(
                    core("int"),
                    fun(
                        core("unit"),
                        thunk(
                            DemandEffect::Atom(DemandCoreType::Named {
                                path: path_segments(&["std", "flow", "loop", "last"]),
                                args: Vec::new(),
                            }),
                            core("unit"),
                        ),
                    ),
                ),
            ),
        );

        let rewrite =
            DemandEmitter::rewrite_module_uses_with_specializations_report(module, &[spec])
                .expect("rewritten module");
        let Some((target, _, args)) = applied_call_with_head(&rewrite.module.root_exprs[0]) else {
            panic!("expected specialized call");
        };

        assert_eq!(target, &path("fold_from__ddmono0"));
        assert!(matches!(args[0].kind, ExprKind::Thunk { .. }));
    }

    #[test]
    fn emitter_forces_enclosed_effectful_specialized_call() {
        let fold_from = path_segments(&["std", "range", "fold_from"]);
        let last = named_path(&["std", "flow", "loop", "last"]);
        let last_effect = DemandEffect::Atom(DemandCoreType::Named {
            path: path_segments(&["std", "flow", "loop", "last"]),
            args: Vec::new(),
        });
        let callback_sig = fun(
            core("unit"),
            thunk(
                last_effect.clone(),
                fun(core("int"), thunk(last_effect.clone(), core("unit"))),
            ),
        );
        let call = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::Apply {
                        callee: Box::new(Expr::typed(
                            ExprKind::Apply {
                                callee: Box::new(Expr::typed(
                                    ExprKind::Var(fold_from.clone()),
                                    RuntimeType::fun(
                                        RuntimeType::core(core_ir::Type::Any),
                                        RuntimeType::fun(
                                            RuntimeType::core(named("int")),
                                            RuntimeType::fun(
                                                RuntimeType::core(named("unit")),
                                                RuntimeType::thunk(
                                                    core_ir::Type::Never,
                                                    RuntimeType::core(named("unit")),
                                                ),
                                            ),
                                        ),
                                    ),
                                )),
                                arg: Box::new(Expr::typed(
                                    ExprKind::Var(path("f")),
                                    runtime_type(&callback_sig).expect("callback type"),
                                )),
                                evidence: None,
                                instantiation: None,
                            },
                            RuntimeType::fun(
                                RuntimeType::core(named("int")),
                                RuntimeType::fun(
                                    RuntimeType::core(named("unit")),
                                    RuntimeType::thunk(
                                        core_ir::Type::Never,
                                        RuntimeType::core(named("unit")),
                                    ),
                                ),
                            ),
                        )),
                        arg: Box::new(Expr::typed(
                            ExprKind::Lit(core_ir::Lit::Int("0".to_string())),
                            RuntimeType::core(named("int")),
                        )),
                        evidence: None,
                        instantiation: None,
                    },
                    RuntimeType::fun(
                        RuntimeType::core(named("unit")),
                        RuntimeType::thunk(core_ir::Type::Never, RuntimeType::core(named("unit"))),
                    ),
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(core_ir::Lit::Unit),
                    RuntimeType::core(named("unit")),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::thunk(core_ir::Type::Never, RuntimeType::core(named("unit"))),
        );
        let root = Expr::typed(
            ExprKind::Thunk {
                effect: last.clone(),
                value: RuntimeType::core(named("unit")),
                expr: Box::new(call),
            },
            RuntimeType::thunk(last.clone(), RuntimeType::core(named("unit"))),
        );
        let module = Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![root],
            roots: vec![Root::Expr(0)],
        };
        let spec = specialization(
            &fold_from,
            "fold_from__ddmono0",
            fun(
                thunk(DemandEffect::Empty, callback_sig),
                fun(
                    core("int"),
                    fun(core("unit"), thunk(last_effect, core("unit"))),
                ),
            ),
        );

        let rewrite =
            DemandEmitter::rewrite_module_uses_with_specializations_report(module, &[spec])
                .expect("rewritten module");
        let ExprKind::Thunk { expr: body, .. } = &rewrite.module.root_exprs[0].kind else {
            panic!("expected thunk root");
        };
        let ExprKind::BindHere { expr: inner } = &body.kind else {
            panic!("expected enclosed call to be forced");
        };
        let Some((target, _, args)) = applied_call_with_head(inner) else {
            panic!("expected specialized call");
        };

        assert_eq!(target, &path("fold_from__ddmono0"));
        assert!(matches!(args[0].kind, ExprKind::Thunk { .. }));
    }

    #[test]
    fn emitter_reads_call_spine_through_forced_partial_application() {
        let f = path("f");
        let root = Expr::typed(
            ExprKind::Apply {
                callee: Box::new(Expr::typed(
                    ExprKind::BindHere {
                        expr: Box::new(Expr::typed(
                            ExprKind::Apply {
                                callee: Box::new(Expr::typed(
                                    ExprKind::Var(f.clone()),
                                    RuntimeType::fun(
                                        RuntimeType::core(core_ir::Type::Any),
                                        RuntimeType::thunk(
                                            core_ir::Type::Never,
                                            RuntimeType::fun(
                                                RuntimeType::core(core_ir::Type::Any),
                                                RuntimeType::core(core_ir::Type::Any),
                                            ),
                                        ),
                                    ),
                                )),
                                arg: Box::new(Expr::typed(
                                    ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                                    RuntimeType::core(named("int")),
                                )),
                                evidence: None,
                                instantiation: None,
                            },
                            RuntimeType::thunk(
                                core_ir::Type::Never,
                                RuntimeType::fun(
                                    RuntimeType::core(named("int")),
                                    RuntimeType::core(named("int")),
                                ),
                            ),
                        )),
                    },
                    RuntimeType::fun(
                        RuntimeType::core(named("int")),
                        RuntimeType::core(named("int")),
                    ),
                )),
                arg: Box::new(Expr::typed(
                    ExprKind::Lit(core_ir::Lit::Int("2".to_string())),
                    RuntimeType::core(named("int")),
                )),
                evidence: None,
                instantiation: None,
            },
            RuntimeType::core(named("int")),
        );
        let module = Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![root],
            roots: vec![Root::Expr(0)],
        };
        let spec = specialization(
            &f,
            "f__ddmono0",
            fun(core("int"), fun(core("int"), core("int"))),
        );

        let rewrite =
            DemandEmitter::rewrite_module_uses_with_specializations_report(module, &[spec])
                .expect("rewritten module");
        let Some((target, _, args)) = applied_call_with_head(&rewrite.module.root_exprs[0]) else {
            panic!("expected specialized call");
        };

        assert_eq!(target, &path("f__ddmono0"));
        assert_eq!(args.len(), 2);
    }

    #[test]
    fn emitter_rejects_unresolved_value_holes() {
        let id = path("id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![generic_identity(id.clone())],
            root_exprs: Vec::new(),
            roots: Vec::new(),
        };
        let specialization = specialization(&id, "id__ddmono0", DemandSignature::Hole(3));
        let emitter = DemandEmitter::from_module(&module, std::slice::from_ref(&specialization));

        let error = emitter.emit(&specialization).expect_err("unresolved hole");

        assert_eq!(
            error,
            DemandEmitError::Specialization {
                target: id,
                path: path("id__ddmono0"),
                source: Box::new(DemandEmitError::UnresolvedValueHole(3)),
            }
        );
    }

    #[test]
    fn emitter_preserves_coerce_inner_from_type() {
        let make = path("make");
        let enum_ty = core_ir::Type::Variant(core_ir::VariantType {
            cases: vec![core_ir::VariantCase {
                name: core_ir::Name("included".to_string()),
                payloads: vec![named("int")],
            }],
            tail: None,
        });
        let bound_ty = named("bound");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![Binding {
                name: make.clone(),
                type_params: vec![core_ir::TypeVar("a".to_string())],
                scheme: core_ir::Scheme {
                    requirements: Vec::new(),
                    body: core_ir::Type::Any,
                },
                body: Expr::typed(
                    ExprKind::Lambda {
                        param: core_ir::Name("value".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Coerce {
                                from: enum_ty.clone(),
                                to: bound_ty.clone(),
                                expr: Box::new(Expr::typed(
                                    ExprKind::Variant {
                                        tag: core_ir::Name("included".to_string()),
                                        value: Some(Box::new(Expr::typed(
                                            ExprKind::Var(path("value")),
                                            RuntimeType::core(core_ir::Type::Any),
                                        ))),
                                    },
                                    RuntimeType::core(enum_ty.clone()),
                                )),
                            },
                            RuntimeType::core(bound_ty.clone()),
                        )),
                    },
                    RuntimeType::fun(
                        RuntimeType::core(core_ir::Type::Any),
                        RuntimeType::core(core_ir::Type::Any),
                    ),
                ),
            }],
            root_exprs: Vec::new(),
            roots: Vec::new(),
        };
        let specialization = specialization(
            &make,
            "make__ddmono0",
            fun(
                core("int"),
                DemandSignature::Core(DemandCoreType::Named {
                    path: path("bound"),
                    args: Vec::new(),
                }),
            ),
        );
        let emitter = DemandEmitter::from_module(&module, std::slice::from_ref(&specialization));

        let emitted = emitter.emit(&specialization).expect("emitted binding");
        let ExprKind::Lambda { body, .. } = &emitted.body.kind else {
            panic!("expected lambda");
        };
        let ExprKind::Coerce { expr: inner, .. } = &body.kind else {
            panic!("expected coerce");
        };

        assert_eq!(inner.ty, RuntimeType::core(enum_ty));
    }

    #[test]
    fn emitter_specializes_coerce_variant_payload_from_nominal_result() {
        let make = path("make");
        let original_enum_ty = core_ir::Type::Variant(core_ir::VariantType {
            cases: vec![core_ir::VariantCase {
                name: core_ir::Name("just".to_string()),
                payloads: vec![core_ir::Type::Any],
            }],
            tail: None,
        });
        let original_opt_ty = core_ir::Type::Named {
            path: path("opt"),
            args: vec![core_ir::TypeArg::Type(core_ir::Type::Any)],
        };
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![Binding {
                name: make.clone(),
                type_params: vec![core_ir::TypeVar("a".to_string())],
                scheme: core_ir::Scheme {
                    requirements: Vec::new(),
                    body: core_ir::Type::Any,
                },
                body: Expr::typed(
                    ExprKind::Lambda {
                        param: core_ir::Name("value".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Coerce {
                                from: original_enum_ty,
                                to: original_opt_ty,
                                expr: Box::new(Expr::typed(
                                    ExprKind::Variant {
                                        tag: core_ir::Name("just".to_string()),
                                        value: Some(Box::new(Expr::typed(
                                            ExprKind::Var(path("value")),
                                            RuntimeType::core(core_ir::Type::Any),
                                        ))),
                                    },
                                    RuntimeType::core(core_ir::Type::Any),
                                )),
                            },
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                    },
                    RuntimeType::fun(
                        RuntimeType::core(core_ir::Type::Any),
                        RuntimeType::core(core_ir::Type::Any),
                    ),
                ),
            }],
            root_exprs: Vec::new(),
            roots: Vec::new(),
        };
        let opt_int = DemandCoreType::Named {
            path: path("opt"),
            args: vec![DemandTypeArg::Type(DemandCoreType::Named {
                path: path("int"),
                args: Vec::new(),
            })],
        };
        let specialization = specialization(
            &make,
            "make__ddmono0",
            fun(core("int"), DemandSignature::Core(opt_int)),
        );
        let emitter = DemandEmitter::from_module(&module, std::slice::from_ref(&specialization));

        let emitted = emitter.emit(&specialization).expect("emitted binding");
        let ExprKind::Lambda { body, .. } = &emitted.body.kind else {
            panic!("expected lambda");
        };
        let ExprKind::Coerce {
            from,
            to,
            expr: inner,
        } = &body.kind
        else {
            panic!("expected coerce");
        };
        let ExprKind::Variant { value, .. } = &inner.kind else {
            panic!("expected variant");
        };

        assert_eq!(
            from,
            &core_ir::Type::Variant(core_ir::VariantType {
                cases: vec![core_ir::VariantCase {
                    name: core_ir::Name("just".to_string()),
                    payloads: vec![named("int")],
                }],
                tail: None,
            })
        );
        assert_eq!(
            to,
            &core_ir::Type::Named {
                path: path("opt"),
                args: vec![core_ir::TypeArg::Type(named("int"))],
            }
        );
        assert_eq!(inner.ty, RuntimeType::core(from.clone()));
        assert_eq!(
            value.as_ref().expect("payload").ty,
            RuntimeType::core(named("int"))
        );
    }

    fn generic_identity(name: core_ir::Path) -> Binding {
        Binding {
            name,
            type_params: vec![core_ir::TypeVar("a".to_string())],
            scheme: core_ir::Scheme {
                requirements: Vec::new(),
                body: core_ir::Type::Any,
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: core_ir::Name("x".to_string()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Var(path("x")),
                        RuntimeType::core(core_ir::Type::Any),
                    )),
                },
                RuntimeType::fun(
                    RuntimeType::core(core_ir::Type::Any),
                    RuntimeType::core(core_ir::Type::Any),
                ),
            ),
        }
    }

    fn generic_use_id(name: core_ir::Path, id: core_ir::Path) -> Binding {
        Binding {
            name,
            type_params: vec![core_ir::TypeVar("a".to_string())],
            scheme: core_ir::Scheme {
                requirements: Vec::new(),
                body: core_ir::Type::Any,
            },
            body: Expr::typed(
                ExprKind::Lambda {
                    param: core_ir::Name("x".to_string()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Apply {
                            callee: Box::new(Expr::typed(
                                ExprKind::Var(id),
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
                RuntimeType::fun(
                    RuntimeType::core(core_ir::Type::Any),
                    RuntimeType::core(core_ir::Type::Any),
                ),
            ),
        }
    }

    fn specialization(
        target: &core_ir::Path,
        name: &str,
        solved: DemandSignature,
    ) -> DemandSpecialization {
        DemandSpecialization {
            target: target.clone(),
            path: path(name),
            key: DemandKey::from_signature(target.clone(), solved.clone()),
            solved,
        }
    }

    fn fun(param: DemandSignature, ret: DemandSignature) -> DemandSignature {
        DemandSignature::Fun {
            param: Box::new(param),
            ret: Box::new(ret),
        }
    }

    fn core(name: &str) -> DemandSignature {
        DemandSignature::Core(DemandCoreType::Named {
            path: path(name),
            args: Vec::new(),
        })
    }

    fn thunk(effect: DemandEffect, value: DemandSignature) -> DemandSignature {
        DemandSignature::Thunk {
            effect,
            value: Box::new(value),
        }
    }

    fn rt_fun(param: &str, ret: &str) -> RuntimeType {
        RuntimeType::fun(
            RuntimeType::core(named(param)),
            RuntimeType::core(named(ret)),
        )
    }

    fn named(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: path(name),
            args: Vec::new(),
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

    fn named_path(segments: &[&str]) -> core_ir::Type {
        core_ir::Type::Named {
            path: path_segments(segments),
            args: Vec::new(),
        }
    }
}
