use std::collections::HashMap;

use super::*;
use crate::ir::{
    Binding, Expr, ExprKind, MatchArm, Module, RecordExprField, RecordSpreadExpr, Stmt,
    Type as RuntimeType,
};
use crate::types::runtime_core_type;

pub struct DemandEmitter<'a> {
    bindings: HashMap<core_ir::Path, &'a Binding>,
    ordered_specializations: &'a [DemandSpecialization],
    specializations: HashMap<DemandKey, &'a DemandSpecialization>,
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
        }
    }

    pub fn emit_all(&self) -> Result<Vec<Binding>, DemandEmitError> {
        self.ordered_specializations
            .iter()
            .map(|specialization| self.emit(specialization))
            .collect()
    }

    pub fn rewrite_module_uses(&self, module: Module) -> Result<Module, DemandEmitError> {
        rewrite_module_uses_with_map(module, &self.specializations).map(|output| output.module)
    }

    pub fn rewrite_module_uses_with_specializations(
        module: Module,
        specializations: &'a [DemandSpecialization],
    ) -> Result<Module, DemandEmitError> {
        let specializations = specializations
            .iter()
            .map(|specialization| (specialization.key.clone(), specialization))
            .collect::<HashMap<_, _>>();
        rewrite_module_uses_with_map(module, &specializations).map(|output| output.module)
    }

    pub fn rewrite_module_uses_with_specializations_report(
        module: Module,
        specializations: &'a [DemandSpecialization],
    ) -> Result<DemandRewriteOutput, DemandEmitError> {
        let specializations = specializations
            .iter()
            .map(|specialization| (specialization.key.clone(), specialization))
            .collect::<HashMap<_, _>>();
        rewrite_module_uses_with_map(module, &specializations)
    }

    pub fn emit(&self, specialization: &DemandSpecialization) -> Result<Binding, DemandEmitError> {
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
    ) -> Result<Binding, DemandEmitError> {
        let original = self
            .bindings
            .get(&specialization.target)
            .copied()
            .ok_or_else(|| DemandEmitError::MissingBinding(specialization.target.clone()))?;
        let solved_ty = runtime_type(&specialization.solved)?;
        let mut rewriter =
            BodyEmitter::new(&self.specializations).with_current_specialization(specialization);
        let mut body = rewriter.rewrite_expr(&original.body, Some(&specialization.solved))?;
        body.ty = solved_ty;
        Ok(Binding {
            name: specialization.path.clone(),
            type_params: Vec::new(),
            scheme: core_ir::Scheme {
                requirements: Vec::new(),
                body: runtime_core_type(&body.ty),
            },
            body,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DemandRewriteOutput {
    pub module: Module,
    pub changed_roots: usize,
    pub changed_bindings: usize,
}

fn rewrite_module_uses_with_map(
    module: Module,
    specializations: &HashMap<DemandKey, &DemandSpecialization>,
) -> Result<DemandRewriteOutput, DemandEmitError> {
    let mut changed_roots = 0;
    let mut root_exprs = Vec::with_capacity(module.root_exprs.len());
    for (index, expr) in module.root_exprs.into_iter().enumerate() {
        let rewritten = rewrite_root_expr(expr.clone(), specializations).map_err(|source| {
            DemandEmitError::RootRewrite {
                index,
                source: Box::new(source),
            }
        })?;
        if rewritten != expr {
            changed_roots += 1;
        }
        root_exprs.push(rewritten);
    }

    let mut changed_bindings = 0;
    let mut bindings = Vec::with_capacity(module.bindings.len());
    for binding in module.bindings.into_iter() {
        let path = binding.name.clone();
        let rewritten =
            rewrite_binding_uses(binding.clone(), specializations).map_err(|source| {
                DemandEmitError::BindingRewrite {
                    path,
                    source: Box::new(source),
                }
            })?;
        if rewritten != binding {
            changed_bindings += 1;
        }
        bindings.push(rewritten);
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
    })
}

fn rewrite_root_expr(
    expr: Expr,
    specializations: &HashMap<DemandKey, &DemandSpecialization>,
) -> Result<Expr, DemandEmitError> {
    let expected = DemandSignature::from_runtime_type(&expr.ty);
    if !expected.is_closed() {
        return Ok(expr);
    }
    let mut rewriter = BodyEmitter::new(specializations);
    rewriter.rewrite_expr(&expr, Some(&expected))
}

fn rewrite_binding_uses(
    binding: Binding,
    specializations: &HashMap<DemandKey, &DemandSpecialization>,
) -> Result<Binding, DemandEmitError> {
    if !binding.type_params.is_empty() {
        return Ok(binding);
    }
    let expected = DemandSignature::from_runtime_type(&binding.body.ty);
    let expected = expected.is_closed().then_some(expected);
    let mut rewriter = BodyEmitter::new(specializations);
    let body = rewriter.rewrite_expr(&binding.body, expected.as_ref())?;
    Ok(Binding { body, ..binding })
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
}

impl<'a> BodyEmitter<'a> {
    fn new(specializations: &'a HashMap<DemandKey, &'a DemandSpecialization>) -> Self {
        Self {
            specializations,
            current_specialization: None,
            enclosing_thunk_effects: Vec::new(),
            locals: HashMap::new(),
        }
    }

    fn with_current_specialization(mut self, specialization: &'a DemandSpecialization) -> Self {
        self.current_specialization = Some(specialization);
        self
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
                } else if let Some(call) = self.rewrite_specialized_call(expr, expected)? {
                    Ok(call)
                } else {
                    self.rewrite_apply(expr)
                }
            }
            ExprKind::Var(path) => {
                let ty = self
                    .locals
                    .get(path)
                    .filter(|signature| signature.is_closed())
                    .map(runtime_type)
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
                        .map(|item| self.rewrite_expr(item, None))
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                self.value_expr_type(expr, expected)?,
            )),
            ExprKind::Record { fields, spread } => Ok(Expr::typed(
                ExprKind::Record {
                    fields: fields
                        .iter()
                        .map(|field| {
                            Ok(RecordExprField {
                                name: field.name.clone(),
                                value: self.rewrite_expr(&field.value, None)?,
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
                            Ok(MatchArm {
                                pattern: arm.pattern.clone(),
                                guard: arm
                                    .guard
                                    .as_ref()
                                    .map(|guard| self.rewrite_expr(guard, None))
                                    .transpose()?,
                                body: self.rewrite_expr(&arm.body, expected)?,
                            })
                        })
                        .collect::<Result<Vec<_>, DemandEmitError>>()?,
                    evidence: evidence.clone(),
                },
                self.expr_type(expr, expected)?,
            )),
            ExprKind::Block { stmts, tail } => Ok(Expr::typed(
                ExprKind::Block {
                    stmts: stmts
                        .iter()
                        .map(|stmt| self.rewrite_stmt(stmt))
                        .collect::<Result<Vec<_>, _>>()?,
                    tail: tail
                        .as_ref()
                        .map(|tail| self.rewrite_expr(tail, expected).map(Box::new))
                        .transpose()?,
                },
                self.expr_type(expr, expected)?,
            )),
            ExprKind::Handle {
                body,
                arms,
                evidence,
                handler,
            } => Ok(Expr::typed(
                ExprKind::Handle {
                    body: Box::new(self.rewrite_expr(body, None)?),
                    arms: arms
                        .iter()
                        .map(|arm| {
                            Ok(crate::ir::HandleArm {
                                effect: arm.effect.clone(),
                                payload: arm.payload.clone(),
                                resume: arm.resume.clone(),
                                guard: arm
                                    .guard
                                    .as_ref()
                                    .map(|guard| self.rewrite_expr(guard, None))
                                    .transpose()?,
                                body: self.rewrite_expr(&arm.body, expected)?,
                            })
                        })
                        .collect::<Result<Vec<_>, DemandEmitError>>()?,
                    evidence: evidence.clone(),
                    handler: handler.clone(),
                },
                self.expr_type(expr, expected)?,
            )),
            ExprKind::BindHere { expr: inner } => {
                let inner_expected = self.bind_here_inner_expected(inner, expected);
                let inner = self.rewrite_expr(inner, inner_expected.as_ref())?;
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
                        effect,
                        value,
                        expr: Box::new(inner),
                    },
                    self.expr_type(expr, expected)?,
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
                    thunk: Box::new(self.rewrite_expr(thunk, None)?),
                },
                self.expr_type(expr, expected)?,
            )),
            ExprKind::Coerce {
                from,
                to,
                expr: inner,
            } => {
                let from = coerce_from_type(from, expected)?;
                let to = coerce_to_type(to, expected)?;
                let from_signature =
                    DemandSignature::from_runtime_type(&RuntimeType::core(from.clone()));
                Ok(Expr::typed(
                    ExprKind::Coerce {
                        from,
                        to,
                        expr: Box::new(self.rewrite_expr(inner, Some(&from_signature))?),
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
            if expected.is_closed() {
                runtime_type(expected)?
            } else {
                expr.ty.clone()
            },
        ))
    }

    fn rewrite_specialized_call(
        &mut self,
        expr: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<Option<Expr>, DemandEmitError> {
        let Some((target, head, args)) = applied_call_with_head(expr) else {
            return Ok(None);
        };
        let ret = expected
            .cloned()
            .unwrap_or_else(|| DemandSignature::from_runtime_type(&expr.ty));
        let param_hints = self.closed_call_param_hints(target, head, &args, ret.clone());
        let arg_signatures = args
            .iter()
            .zip(param_hints)
            .map(|(arg, hint)| {
                let signature = self.expr_signature(arg);
                hint.map(|hint| merge_signature_hint(hint, signature.clone()))
                    .unwrap_or(signature)
            })
            .collect::<Vec<_>>();
        let signature = curried_signatures(&arg_signatures, ret);
        let key = DemandKey::from_signature(target.clone(), signature);
        let Some(specialization) = self
            .find_specialization(&key)
            .or_else(|| self.find_role_impl_specialization(target, &key.signature))
        else {
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
        let Some(call) = self.rewrite_specialized_call(expr, Some(&expected_thunk))? else {
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

    fn closed_call_param_hints(
        &self,
        target: &core_ir::Path,
        head: &Expr,
        args: &[&Expr],
        ret: DemandSignature,
    ) -> Vec<Option<DemandSignature>> {
        let param_hints = curried_param_signatures_from_type(&head.ty, args.len());
        let provisional_args = param_hints
            .iter()
            .zip(args)
            .map(|(hint, arg)| hint.clone().unwrap_or_else(|| self.expr_signature(arg)))
            .collect::<Vec<_>>();
        let closed = close_known_associated_type_signature(
            target,
            curried_signatures(&provisional_args, ret),
        );
        let (closed_args, _) = uncurried_emit_signatures(closed);
        if closed_args.len() == args.len() {
            return closed_args.into_iter().map(Some).collect();
        }
        param_hints
    }

    fn find_specialization(&self, key: &DemandKey) -> Option<&'a DemandSpecialization> {
        if let Some(specialization) = self.current_specialization
            && specialization.target == key.target
            && signature_arity(&key.signature) == signature_arity(&specialization.key.signature)
        {
            return Some(specialization);
        }
        if let Some(specialization) = self.specializations.get(key) {
            return Some(*specialization);
        }
        let matches = self
            .specializations
            .values()
            .copied()
            .filter(|specialization| {
                specialization.target == key.target
                    && signature_arity(&key.signature)
                        == signature_arity(&specialization.key.signature)
                    && DemandUnifier::new()
                        .unify_signature(&key.signature, &specialization.key.signature)
                        .is_ok()
            })
            .collect::<Vec<_>>();
        match matches.as_slice() {
            [] => None,
            [specialization] => Some(*specialization),
            [first, rest @ ..]
                if rest
                    .iter()
                    .all(|specialization| specialization.key.signature == first.key.signature) =>
            {
                Some(*first)
            }
            _ => most_specific_specialization(&matches),
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
        let matches = self
            .specializations
            .values()
            .copied()
            .filter(|specialization| {
                specialization.target.segments.last() == Some(method)
                    && is_impl_method_path(&specialization.target)
                    && signature_arity(signature) == signature_arity(&specialization.key.signature)
                    && DemandUnifier::new()
                        .unify_signature(signature, &specialization.key.signature)
                        .is_ok()
            })
            .collect::<Vec<_>>();
        match matches.as_slice() {
            [] => None,
            [specialization] => Some(*specialization),
            [first, rest @ ..]
                if rest
                    .iter()
                    .all(|specialization| specialization.key.signature == first.key.signature) =>
            {
                Some(*first)
            }
            _ => most_specific_specialization(&matches),
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

    fn rewrite_stmt(&mut self, stmt: &Stmt) -> Result<Stmt, DemandEmitError> {
        Ok(match stmt {
            Stmt::Let { pattern, value } => Stmt::Let {
                pattern: pattern.clone(),
                value: self.rewrite_expr(value, None)?,
            },
            Stmt::Expr(expr) => Stmt::Expr(self.rewrite_expr(expr, None)?),
            Stmt::Module { def, body } => Stmt::Module {
                def: def.clone(),
                body: self.rewrite_expr(body, None)?,
            },
        })
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
        inner: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Option<DemandSignature> {
        let expected = expected?;
        let effect = self.bind_here_effect(inner);
        Some(DemandSignature::Thunk {
            effect,
            value: Box::new(expected.clone()),
        })
    }

    fn bind_here_effect(&self, inner: &Expr) -> DemandEffect {
        if let Some(effect) = thunk_effect_signature(&inner.ty)
            && !demand_effect_is_empty(&effect)
        {
            return effect;
        }
        self.enclosing_thunk_effects
            .last()
            .cloned()
            .unwrap_or(DemandEffect::Empty)
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

fn applied_call_with_head(expr: &Expr) -> Option<(&core_ir::Path, &Expr, Vec<&Expr>)> {
    let mut callee = expr;
    let mut args = Vec::new();
    loop {
        match &callee.kind {
            ExprKind::Apply {
                callee: next, arg, ..
            } => {
                args.push(arg.as_ref());
                callee = next;
            }
            ExprKind::BindHere { expr } => {
                callee = expr;
            }
            ExprKind::Var(target) => {
                args.reverse();
                return Some((target, callee, args));
            }
            _ => return None,
        }
    }
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
    candidates: &[&'a DemandSpecialization],
) -> Option<&'a DemandSpecialization> {
    let min = candidates
        .iter()
        .map(|candidate| signature_hole_count(&candidate.key.signature))
        .min()?;
    let mut best = candidates
        .iter()
        .copied()
        .filter(|candidate| signature_hole_count(&candidate.key.signature) == min);
    let first = best.next()?;
    best.next().is_none().then_some(first)
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

fn signature_arity(signature: &DemandSignature) -> usize {
    let mut arity = 0;
    let mut current = signature;
    while let DemandSignature::Fun { ret, .. } = current {
        arity += 1;
        current = ret;
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

fn bind_here_result_type(
    original: &Expr,
    inner: &Expr,
    expected: Option<&DemandSignature>,
) -> Result<RuntimeType, DemandEmitError> {
    if let Some(expected) = expected {
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

fn effect_type(effect: &DemandEffect) -> Result<core_ir::Type, DemandEmitError> {
    match effect {
        DemandEffect::Empty => Ok(core_ir::Type::Never),
        DemandEffect::Hole(id) => Err(DemandEmitError::UnresolvedEffectHole(*id)),
        DemandEffect::Atom(ty) => core_type(ty),
        DemandEffect::Row(items) => row_type(items),
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

fn type_arg(arg: &DemandTypeArg) -> Result<core_ir::TypeArg, DemandEmitError> {
    Ok(match arg {
        DemandTypeArg::Type(ty) => core_ir::TypeArg::Type(core_type(ty)?),
        DemandTypeArg::Bounds { lower, upper } => core_ir::TypeArg::Bounds(core_ir::TypeBounds {
            lower: lower.as_ref().map(core_type).transpose()?.map(Box::new),
            upper: upper.as_ref().map(core_type).transpose()?.map(Box::new),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Root;

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
