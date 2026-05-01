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
        Self {
            bindings: module
                .bindings
                .iter()
                .map(|binding| (binding.name.clone(), binding))
                .collect(),
            ordered_specializations: specializations,
            specializations: specializations
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

    pub fn emit(&self, specialization: &DemandSpecialization) -> Result<Binding, DemandEmitError> {
        let original = self
            .bindings
            .get(&specialization.target)
            .copied()
            .ok_or_else(|| DemandEmitError::MissingBinding(specialization.target.clone()))?;
        let solved_ty = runtime_type(&specialization.solved)?;
        let mut rewriter = BodyEmitter::new(&self.specializations);
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
pub enum DemandEmitError {
    MissingBinding(core_ir::Path),
    UnresolvedValueHole(u32),
    UnresolvedCoreHole(u32),
    UnresolvedEffectHole(u32),
    NonFunctionCall(DemandSignature),
}

struct BodyEmitter<'a> {
    specializations: &'a HashMap<DemandKey, &'a DemandSpecialization>,
    locals: HashMap<core_ir::Path, DemandSignature>,
}

impl<'a> BodyEmitter<'a> {
    fn new(specializations: &'a HashMap<DemandKey, &'a DemandSpecialization>) -> Self {
        Self {
            specializations,
            locals: HashMap::new(),
        }
    }

    fn rewrite_expr(
        &mut self,
        expr: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<Expr, DemandEmitError> {
        match &expr.kind {
            ExprKind::Lambda { param, body, .. } => {
                self.rewrite_lambda(expr, param, body, expected)
            }
            ExprKind::Apply { .. } => {
                if let Some(call) = self.rewrite_specialized_call(expr, expected)? {
                    return Ok(call);
                }
                self.rewrite_apply(expr)
            }
            ExprKind::Var(path) => {
                let ty = self
                    .locals
                    .get(path)
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
                self.expr_type(expr, expected)?,
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
                self.expr_type(expr, expected)?,
            )),
            ExprKind::Variant { tag, value } => Ok(Expr::typed(
                ExprKind::Variant {
                    tag: tag.clone(),
                    value: value
                        .as_ref()
                        .map(|value| self.rewrite_expr(value, None).map(Box::new))
                        .transpose()?,
                },
                self.expr_type(expr, expected)?,
            )),
            ExprKind::Select { base, field } => Ok(Expr::typed(
                ExprKind::Select {
                    base: Box::new(self.rewrite_expr(base, None)?),
                    field: field.clone(),
                },
                self.expr_type(expr, expected)?,
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
            ExprKind::BindHere { expr: inner } => Ok(Expr::typed(
                ExprKind::BindHere {
                    expr: Box::new(self.rewrite_expr(inner, None)?),
                },
                self.expr_type(expr, expected)?,
            )),
            ExprKind::Thunk {
                effect,
                value,
                expr: inner,
            } => Ok(Expr::typed(
                ExprKind::Thunk {
                    effect: effect.clone(),
                    value: value.clone(),
                    expr: Box::new(self.rewrite_expr(inner, None)?),
                },
                self.expr_type(expr, expected)?,
            )),
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
            } => Ok(Expr::typed(
                ExprKind::Coerce {
                    from: from.clone(),
                    to: to.clone(),
                    expr: Box::new(self.rewrite_expr(inner, expected)?),
                },
                self.expr_type(expr, expected)?,
            )),
            ExprKind::Pack { var, expr: inner } => Ok(Expr::typed(
                ExprKind::Pack {
                    var: var.clone(),
                    expr: Box::new(self.rewrite_expr(inner, expected)?),
                },
                self.expr_type(expr, expected)?,
            )),
            ExprKind::EffectOp(path) => Ok(Expr::typed(
                ExprKind::EffectOp(path.clone()),
                self.expr_type(expr, expected)?,
            )),
            ExprKind::PrimitiveOp(op) => Ok(Expr::typed(
                ExprKind::PrimitiveOp(op.clone()),
                self.expr_type(expr, expected)?,
            )),
            ExprKind::Lit(lit) => Ok(Expr::typed(
                ExprKind::Lit(lit.clone()),
                self.expr_type(expr, expected)?,
            )),
            ExprKind::PeekId => Ok(Expr::typed(
                ExprKind::PeekId,
                self.expr_type(expr, expected)?,
            )),
            ExprKind::FindId { id } => Ok(Expr::typed(
                ExprKind::FindId { id: *id },
                self.expr_type(expr, expected)?,
            )),
        }
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
            return self.clone_with_type(expr, None);
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
            runtime_type(expected)?,
        ))
    }

    fn rewrite_specialized_call(
        &mut self,
        expr: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<Option<Expr>, DemandEmitError> {
        let Some((target, args)) = applied_call(expr) else {
            return Ok(None);
        };
        let ret = expected
            .cloned()
            .unwrap_or_else(|| DemandSignature::from_runtime_type(&expr.ty));
        let arg_signatures = args
            .iter()
            .map(|arg| self.expr_signature(arg))
            .collect::<Vec<_>>();
        let key =
            DemandKey::from_signature(target.clone(), curried_signatures(&arg_signatures, ret));
        let Some(specialization) = self.specializations.get(&key) else {
            return Ok(None);
        };
        let mut callee_signature = specialization.solved.clone();
        let mut call = Expr::typed(
            ExprKind::Var(specialization.path.clone()),
            runtime_type(&callee_signature)?,
        );
        for arg in args {
            let DemandSignature::Fun { param, ret } = callee_signature else {
                return Err(DemandEmitError::NonFunctionCall(callee_signature));
            };
            let arg = self.rewrite_expr(arg, Some(&param))?;
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
        Ok(Expr::typed(
            ExprKind::Apply {
                callee: Box::new(self.rewrite_expr(callee, None)?),
                arg: Box::new(self.rewrite_expr(arg, None)?),
                evidence: evidence.clone(),
                instantiation: instantiation.clone(),
            },
            expr.ty.clone(),
        ))
    }

    fn expr_signature(&self, expr: &Expr) -> DemandSignature {
        match &expr.kind {
            ExprKind::Var(path) => self
                .locals
                .get(path)
                .cloned()
                .unwrap_or_else(|| DemandSignature::from_runtime_type(&expr.ty)),
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

    fn clone_with_type(
        &mut self,
        expr: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<Expr, DemandEmitError> {
        let mut cloned = expr.clone();
        cloned.ty = self.expr_type(expr, expected)?;
        Ok(cloned)
    }

    fn expr_type(
        &self,
        expr: &Expr,
        expected: Option<&DemandSignature>,
    ) -> Result<RuntimeType, DemandEmitError> {
        expected
            .map(runtime_type)
            .transpose()
            .map(|ty| ty.unwrap_or_else(|| expr.ty.clone()))
    }
}

fn runtime_type(signature: &DemandSignature) -> Result<RuntimeType, DemandEmitError> {
    Ok(match signature {
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

        assert_eq!(error, DemandEmitError::UnresolvedValueHole(3));
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
}
