//! Lower elaborated monomorphic IR directly into finalized runtime IR.
//!
//! This entrypoint is the new post-inference path: references must already be
//! resolved to `MonoInstanceId`, and runtime effect/thunk boundaries must be
//! explicit in the elaborated tree. This module only performs name/type shape
//! conversion; it does not rediscover apply evidence or monomorphize again.

use std::collections::BTreeMap;

use yulang_elaborated_ir as elaborated;
use yulang_erased_ir as erased;
use yulang_runtime_ir::{
    EffectIdRef, EffectIdVar, FinalizedBinding, FinalizedExpr, FinalizedExprKind,
    FinalizedHandleArm, FinalizedMatchArm, FinalizedModule, FinalizedPattern,
    FinalizedRecordExprField, FinalizedRecordPatternField, FinalizedRecordSpreadExpr,
    FinalizedRecordSpreadPattern, FinalizedResumeBinding, FinalizedStmt, HandleEffect,
    JoinEvidence, Root, RuntimeType,
};
use yulang_runtime_types::diagnostic::{RuntimeError, RuntimeResult};
use yulang_typed_ir as typed_ir;

pub fn lower_elaborated_program(
    program: elaborated::ElaboratedProgram,
) -> RuntimeResult<FinalizedModule> {
    ElaboratedRuntimeLower::new(&program.module).lower_module(program.module)
}

struct ElaboratedRuntimeLower {
    instance_names: BTreeMap<elaborated::MonoInstanceId, typed_ir::Path>,
    instance_sources: BTreeMap<elaborated::MonoInstanceId, elaborated::DemandSource>,
    next_adapter_param: u32,
}

impl ElaboratedRuntimeLower {
    fn new(module: &elaborated::ElaboratedModule) -> Self {
        Self {
            instance_names: module
                .instances
                .iter()
                .map(|instance| (instance.id, convert_path(&instance.name)))
                .collect(),
            instance_sources: module
                .instances
                .iter()
                .map(|instance| (instance.id, instance.source.clone()))
                .collect(),
            next_adapter_param: 0,
        }
    }

    fn lower_module(
        mut self,
        module: elaborated::ElaboratedModule,
    ) -> RuntimeResult<FinalizedModule> {
        let bindings = module
            .instances
            .into_iter()
            .map(|instance| self.lower_instance(instance))
            .collect::<RuntimeResult<Vec<_>>>()?;
        let root_exprs = module
            .root_exprs
            .into_iter()
            .map(|expr| self.lower_expr(expr))
            .collect::<RuntimeResult<Vec<_>>>()?;
        let roots = module
            .roots
            .into_iter()
            .map(|root| self.lower_root(root))
            .collect::<RuntimeResult<Vec<_>>>()?;
        Ok(FinalizedModule {
            path: convert_path(&module.path),
            bindings,
            root_exprs,
            roots,
            role_impls: Vec::new(),
        })
    }

    fn lower_instance(
        &mut self,
        instance: elaborated::MonoInstance,
    ) -> RuntimeResult<FinalizedBinding> {
        let name = self
            .instance_names
            .get(&instance.id)
            .cloned()
            .ok_or_else(|| invariant("missing elaborated instance name"))?;
        let scheme_body = core_value_type_from_mono_type(&instance.signature.value);
        Ok(FinalizedBinding {
            name,
            type_params: Vec::new(),
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: scheme_body,
            },
            body: self.lower_expr(instance.body)?,
        })
    }

    fn lower_root(&self, root: elaborated::ElaboratedRoot) -> RuntimeResult<Root> {
        match root {
            elaborated::ElaboratedRoot::Expr(index) => Ok(Root::Expr(index)),
            elaborated::ElaboratedRoot::Instance(instance) => {
                if let Some(elaborated::DemandSource::RootExpr(index)) =
                    self.instance_sources.get(&instance)
                {
                    return Ok(Root::Expr(*index));
                }
                let name = self
                    .instance_names
                    .get(&instance)
                    .cloned()
                    .ok_or_else(|| invariant("missing elaborated root instance name"))?;
                Ok(Root::Binding(name))
            }
        }
    }

    fn lower_expr(&mut self, expr: elaborated::ElaboratedExpr) -> RuntimeResult<FinalizedExpr> {
        let ty = runtime_type_from_computation(&expr.comp);
        let kind = match expr.kind {
            elaborated::ElaboratedExprKind::Def(def) => {
                FinalizedExprKind::Var(path_from_name(local_name(def)))
            }
            elaborated::ElaboratedExprKind::Ref(_) => {
                return Err(invariant(
                    "elaborated runtime lower received unresolved RefId",
                ));
            }
            elaborated::ElaboratedExprKind::InstanceRef(instance) => {
                let name = self
                    .instance_names
                    .get(&instance)
                    .cloned()
                    .ok_or_else(|| invariant("missing elaborated referenced instance name"))?;
                FinalizedExprKind::Var(name)
            }
            elaborated::ElaboratedExprKind::EffectOp(path) => {
                FinalizedExprKind::EffectOp(convert_path(&path))
            }
            elaborated::ElaboratedExprKind::PrimitiveOp(op) => {
                FinalizedExprKind::PrimitiveOp(convert_primitive_op(op))
            }
            elaborated::ElaboratedExprKind::Lit(lit) => FinalizedExprKind::Lit(convert_lit(lit)),
            elaborated::ElaboratedExprKind::Lambda {
                param,
                param_type: _,
                body,
            } => FinalizedExprKind::Lambda {
                param: local_name(param),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(self.lower_expr(*body)?),
            },
            elaborated::ElaboratedExprKind::Apply { callee, arg } => FinalizedExprKind::Apply {
                callee: Box::new(self.lower_expr(*callee)?),
                arg: Box::new(self.lower_expr(*arg)?),
                evidence: None,
                instantiation: None,
            },
            elaborated::ElaboratedExprKind::RefSet { .. } => {
                return Err(invariant(
                    "elaborated RefSet cannot be represented in runtime IR",
                ));
            }
            elaborated::ElaboratedExprKind::Tuple(items) => FinalizedExprKind::Tuple(
                items
                    .into_iter()
                    .map(|item| self.lower_expr(item))
                    .collect::<RuntimeResult<Vec<_>>>()?,
            ),
            elaborated::ElaboratedExprKind::Record { fields, spread } => {
                FinalizedExprKind::Record {
                    fields: fields
                        .into_iter()
                        .map(|field| {
                            Ok(FinalizedRecordExprField {
                                name: convert_name(field.name),
                                value: self.lower_expr(field.value)?,
                            })
                        })
                        .collect::<RuntimeResult<Vec<_>>>()?,
                    spread: spread
                        .map(|spread| self.lower_record_spread_expr(spread))
                        .transpose()?,
                }
            }
            elaborated::ElaboratedExprKind::Variant { tag, value } => FinalizedExprKind::Variant {
                tag: convert_name(tag),
                value: value
                    .map(|value| self.lower_expr(*value).map(Box::new))
                    .transpose()?,
            },
            elaborated::ElaboratedExprKind::Select { base, field } => FinalizedExprKind::Select {
                base: Box::new(self.lower_expr(*base)?),
                field: convert_name(field),
            },
            elaborated::ElaboratedExprKind::Match { scrutinee, arms } => FinalizedExprKind::Match {
                scrutinee: Box::new(self.lower_expr(*scrutinee)?),
                arms: arms
                    .into_iter()
                    .map(|arm| self.lower_match_arm(arm))
                    .collect::<RuntimeResult<Vec<_>>>()?,
                evidence: JoinEvidence {
                    result: core_value_type_from_computation(&expr.comp),
                },
            },
            elaborated::ElaboratedExprKind::Handle { body, arms } => {
                let lowered_arms = arms
                    .into_iter()
                    .map(|arm| self.lower_handle_arm(arm))
                    .collect::<RuntimeResult<Vec<_>>>()?;
                FinalizedExprKind::Handle {
                    body: Box::new(self.lower_expr(*body)?),
                    handler: HandleEffect {
                        consumes: lowered_arms
                            .iter()
                            .map(|arm| arm.effect.clone())
                            .collect::<Vec<_>>(),
                        residual_before: None,
                        residual_after: None,
                    },
                    arms: lowered_arms,
                    evidence: JoinEvidence {
                        result: core_value_type_from_computation(&expr.comp),
                    },
                }
            }
            elaborated::ElaboratedExprKind::Block(block) => FinalizedExprKind::Block {
                stmts: block
                    .stmts
                    .into_iter()
                    .map(|stmt| self.lower_stmt(stmt))
                    .collect::<RuntimeResult<Vec<_>>>()?,
                tail: block
                    .tail
                    .map(|tail| self.lower_expr(*tail).map(Box::new))
                    .transpose()?,
            },
            elaborated::ElaboratedExprKind::MakeThunk { body, thunk } => FinalizedExprKind::Thunk {
                effect: convert_type(thunk.effect.row().as_type()),
                value: runtime_type_from_mono_type(thunk.value.as_ref()),
                expr: Box::new(self.lower_expr(*body)?),
            },
            elaborated::ElaboratedExprKind::LocalPushId { id, body } => {
                FinalizedExprKind::LocalPushId {
                    id: convert_effect_id_var(id),
                    body: Box::new(self.lower_expr(*body)?),
                }
            }
            elaborated::ElaboratedExprKind::PeekId => FinalizedExprKind::PeekId,
            elaborated::ElaboratedExprKind::FindId { id } => FinalizedExprKind::FindId {
                id: convert_effect_id_ref(id),
            },
            elaborated::ElaboratedExprKind::AddId {
                id,
                allowed,
                active,
                thunk,
            } => FinalizedExprKind::AddId {
                id: convert_effect_id_ref(id),
                allowed: convert_type(allowed.row().as_type()),
                active,
                thunk: Box::new(self.lower_expr(*thunk)?),
            },
            elaborated::ElaboratedExprKind::ForceThunk { thunk, target, .. } => {
                return self.lower_force_thunk(*thunk, target);
            }
            elaborated::ElaboratedExprKind::Cast {
                expr,
                source,
                target,
            } => {
                return self.lower_cast(*expr, source, target);
            }
            elaborated::ElaboratedExprKind::FunctionAdapter { function, adapter } => {
                return self.lower_function_adapter(*function, adapter);
            }
            elaborated::ElaboratedExprKind::Pack { var, expr } => FinalizedExprKind::Pack {
                var: convert_type_var(var),
                expr: Box::new(self.lower_expr(*expr)?),
            },
        };
        Ok(FinalizedExpr { ty, kind })
    }

    fn lower_force_thunk(
        &mut self,
        thunk: elaborated::ElaboratedExpr,
        target: elaborated::MonoComputation,
    ) -> RuntimeResult<FinalizedExpr> {
        Ok(FinalizedExpr {
            ty: runtime_type_from_computation(&target),
            kind: FinalizedExprKind::BindHere {
                expr: Box::new(self.lower_expr(thunk)?),
            },
        })
    }

    fn lower_cast(
        &mut self,
        expr: elaborated::ElaboratedExpr,
        source: elaborated::MonoType,
        target: elaborated::MonoType,
    ) -> RuntimeResult<FinalizedExpr> {
        let lowered = self.lower_expr(expr)?;
        Ok(adapt_mono_value_expr(lowered, &source, &target))
    }

    fn lower_function_adapter(
        &mut self,
        function: elaborated::ElaboratedExpr,
        adapter: elaborated::FunctionAdapter,
    ) -> RuntimeResult<FinalizedExpr> {
        let function = self.lower_expr(function)?;
        Ok(self.lower_function_adapter_expr(function, adapter))
    }

    fn lower_function_adapter_expr(
        &mut self,
        function: FinalizedExpr,
        adapter: elaborated::FunctionAdapter,
    ) -> FinalizedExpr {
        let param_name = self.next_adapter_param_name();
        let param_expr = FinalizedExpr {
            ty: runtime_type_from_mono_value_and_effect(
                &adapter.target.param,
                &adapter.target.param_effect,
            ),
            kind: FinalizedExprKind::Var(path_from_name(param_name.clone())),
        };
        let arg = adapt_mono_boundary_expr(
            param_expr,
            &adapter.target.param,
            &adapter.target.param_effect,
            &adapter.source.param,
            &adapter.source.param_effect,
        );
        let call_ty = runtime_type_from_mono_value_and_effect(
            &adapter.source.ret,
            &adapter.source.ret_effect,
        );
        let mut body = FinalizedExpr {
            ty: call_ty,
            kind: FinalizedExprKind::Apply {
                callee: Box::new(function),
                arg: Box::new(arg),
                evidence: None,
                instantiation: None,
            },
        };
        body = adapt_mono_boundary_expr(
            body,
            &adapter.source.ret,
            &adapter.source.ret_effect,
            &adapter.target.ret,
            &adapter.target.ret_effect,
        );
        for boundary in adapter.call.result_boundaries.into_iter().rev() {
            body = self.lower_function_result_boundary(body, boundary);
        }
        if let Some(local_scope) = adapter.call.local_scope {
            body = FinalizedExpr {
                ty: body.ty.clone(),
                kind: FinalizedExprKind::LocalPushId {
                    id: convert_effect_id_var(local_scope),
                    body: Box::new(body),
                },
            };
        }
        let target_ty = runtime_type_from_function_boundary(&adapter.target);
        FinalizedExpr {
            ty: target_ty,
            kind: FinalizedExprKind::Lambda {
                param: param_name,
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(body),
            },
        }
    }

    fn lower_function_result_boundary(
        &mut self,
        body: FinalizedExpr,
        boundary: elaborated::FunctionResultBoundary,
    ) -> FinalizedExpr {
        match boundary {
            elaborated::FunctionResultBoundary::AddId {
                id,
                allowed,
                active,
            } => FinalizedExpr {
                ty: body.ty.clone(),
                kind: FinalizedExprKind::AddId {
                    id: convert_effect_id_ref(id),
                    allowed: convert_type(allowed.row().as_type()),
                    active,
                    thunk: Box::new(body),
                },
            },
            elaborated::FunctionResultBoundary::FunctionAdapter(adapter) => {
                self.lower_function_adapter_expr(body, *adapter)
            }
        }
    }

    fn next_adapter_param_name(&mut self) -> typed_ir::Name {
        let index = self.next_adapter_param;
        self.next_adapter_param += 1;
        typed_ir::Name(format!("adapter_arg_{index}"))
    }

    fn lower_stmt(&mut self, stmt: elaborated::ElaboratedStmt) -> RuntimeResult<FinalizedStmt> {
        match stmt {
            elaborated::ElaboratedStmt::Let { pattern, value } => Ok(FinalizedStmt::Let {
                pattern: self.lower_pattern(pattern)?,
                value: self.lower_expr(value)?,
            }),
            elaborated::ElaboratedStmt::Expr(expr) => {
                Ok(FinalizedStmt::Expr(self.lower_expr(expr)?))
            }
            elaborated::ElaboratedStmt::Module { def, body } => Ok(FinalizedStmt::Module {
                def: path_from_name(local_name(def)),
                body: FinalizedExpr {
                    ty: block_runtime_type(&body),
                    kind: FinalizedExprKind::Block {
                        stmts: body
                            .stmts
                            .into_iter()
                            .map(|stmt| self.lower_stmt(stmt))
                            .collect::<RuntimeResult<Vec<_>>>()?,
                        tail: body
                            .tail
                            .map(|tail| self.lower_expr(*tail).map(Box::new))
                            .transpose()?,
                    },
                },
            }),
        }
    }

    fn lower_match_arm(&mut self, arm: elaborated::MatchArm) -> RuntimeResult<FinalizedMatchArm> {
        Ok(FinalizedMatchArm {
            pattern: self.lower_pattern(arm.pattern)?,
            guard: arm.guard.map(|guard| self.lower_expr(guard)).transpose()?,
            body: self.lower_expr(arm.body)?,
        })
    }

    fn lower_handle_arm(
        &mut self,
        arm: elaborated::HandleArm,
    ) -> RuntimeResult<FinalizedHandleArm> {
        Ok(FinalizedHandleArm {
            effect: convert_path(&arm.effect),
            payload: self.lower_pattern(arm.payload)?,
            resume: arm.resume.map(|resume| FinalizedResumeBinding {
                name: local_name(resume.def),
                ty: runtime_type_from_mono_type(&resume.typ),
            }),
            guard: arm.guard.map(|guard| self.lower_expr(guard)).transpose()?,
            body: self.lower_expr(arm.body)?,
        })
    }

    fn lower_record_spread_expr(
        &mut self,
        spread: elaborated::RecordSpreadExpr,
    ) -> RuntimeResult<FinalizedRecordSpreadExpr> {
        Ok(match spread {
            elaborated::RecordSpreadExpr::Head(expr) => {
                FinalizedRecordSpreadExpr::Head(Box::new(self.lower_expr(*expr)?))
            }
            elaborated::RecordSpreadExpr::Tail(expr) => {
                FinalizedRecordSpreadExpr::Tail(Box::new(self.lower_expr(*expr)?))
            }
        })
    }

    fn lower_pattern(&mut self, pattern: elaborated::Pattern) -> RuntimeResult<FinalizedPattern> {
        Ok(match pattern {
            elaborated::Pattern::Wildcard { typ } => FinalizedPattern::Wildcard {
                ty: runtime_type_from_mono_type(&typ),
            },
            elaborated::Pattern::Bind { def, typ } => FinalizedPattern::Bind {
                name: local_name(def),
                ty: runtime_type_from_mono_type(&typ),
            },
            elaborated::Pattern::Lit { lit, typ } => FinalizedPattern::Lit {
                lit: convert_lit(lit),
                ty: runtime_type_from_mono_type(&typ),
            },
            elaborated::Pattern::Tuple { items, typ } => FinalizedPattern::Tuple {
                items: items
                    .into_iter()
                    .map(|item| self.lower_pattern(item))
                    .collect::<RuntimeResult<Vec<_>>>()?,
                ty: runtime_type_from_mono_type(&typ),
            },
            elaborated::Pattern::List {
                prefix,
                spread,
                suffix,
                typ,
            } => FinalizedPattern::List {
                prefix: prefix
                    .into_iter()
                    .map(|item| self.lower_pattern(item))
                    .collect::<RuntimeResult<Vec<_>>>()?,
                spread: spread
                    .map(|spread| self.lower_pattern(*spread).map(Box::new))
                    .transpose()?,
                suffix: suffix
                    .into_iter()
                    .map(|item| self.lower_pattern(item))
                    .collect::<RuntimeResult<Vec<_>>>()?,
                ty: runtime_type_from_mono_type(&typ),
            },
            elaborated::Pattern::Record {
                fields,
                spread,
                typ,
            } => FinalizedPattern::Record {
                fields: fields
                    .into_iter()
                    .map(|field| {
                        Ok(FinalizedRecordPatternField {
                            name: convert_name(field.name),
                            pattern: self.lower_pattern(field.pattern)?,
                            default: field
                                .default
                                .map(|default| self.lower_expr(default))
                                .transpose()?,
                        })
                    })
                    .collect::<RuntimeResult<Vec<_>>>()?,
                spread: spread
                    .map(|spread| self.lower_record_spread_pattern(spread))
                    .transpose()?,
                ty: runtime_type_from_mono_type(&typ),
            },
            elaborated::Pattern::Variant { tag, value, typ } => FinalizedPattern::Variant {
                tag: convert_name(tag),
                value: value
                    .map(|value| self.lower_pattern(*value).map(Box::new))
                    .transpose()?,
                ty: runtime_type_from_mono_type(&typ),
            },
            elaborated::Pattern::Or { left, right, typ } => FinalizedPattern::Or {
                left: Box::new(self.lower_pattern(*left)?),
                right: Box::new(self.lower_pattern(*right)?),
                ty: runtime_type_from_mono_type(&typ),
            },
            elaborated::Pattern::As { pattern, def, typ } => FinalizedPattern::As {
                pattern: Box::new(self.lower_pattern(*pattern)?),
                name: local_name(def),
                ty: runtime_type_from_mono_type(&typ),
            },
        })
    }

    fn lower_record_spread_pattern(
        &mut self,
        spread: elaborated::RecordSpreadPattern,
    ) -> RuntimeResult<FinalizedRecordSpreadPattern> {
        Ok(match spread {
            elaborated::RecordSpreadPattern::Head(pattern) => {
                FinalizedRecordSpreadPattern::Head(Box::new(self.lower_pattern(*pattern)?))
            }
            elaborated::RecordSpreadPattern::Tail(pattern) => {
                FinalizedRecordSpreadPattern::Tail(Box::new(self.lower_pattern(*pattern)?))
            }
        })
    }
}

fn block_runtime_type(block: &elaborated::ElaboratedBlock) -> RuntimeType {
    block
        .tail
        .as_ref()
        .map(|tail| runtime_type_from_computation(&tail.comp))
        .unwrap_or_else(|| RuntimeType::Value(unit_type()))
}

fn adapt_mono_boundary_expr(
    expr: FinalizedExpr,
    source_value: &elaborated::MonoType,
    source_effect: &elaborated::MonoEffect,
    target_value: &elaborated::MonoType,
    target_effect: &elaborated::MonoEffect,
) -> FinalizedExpr {
    let source = computation_type_from_parts(source_value, source_effect);
    let target = computation_type_from_parts(target_value, target_effect);
    adapt_mono_value_expr(expr, &source, &target)
}

fn computation_type_from_parts(
    value: &elaborated::MonoType,
    effect: &elaborated::MonoEffect,
) -> elaborated::MonoType {
    if effect.is_pure() {
        value.clone()
    } else {
        elaborated::MonoType::effective_thunk(effect.clone(), value.clone())
    }
}

fn adapt_mono_value_expr(
    expr: FinalizedExpr,
    source: &elaborated::MonoType,
    target: &elaborated::MonoType,
) -> FinalizedExpr {
    if source == target {
        return expr;
    }
    match (source, target) {
        (_, elaborated::MonoType::EffectiveThunk(target_thunk)) => {
            let body = adapt_mono_value_expr(expr, source, target_thunk.value.as_ref());
            let ty = runtime_type_from_mono_type(target);
            FinalizedExpr {
                ty,
                kind: FinalizedExprKind::Thunk {
                    effect: convert_type(target_thunk.effect.row().as_type()),
                    value: runtime_type_from_mono_type(target_thunk.value.as_ref()),
                    expr: Box::new(body),
                },
            }
        }
        (elaborated::MonoType::EffectiveThunk(source_thunk), _) => {
            let forced = FinalizedExpr {
                ty: runtime_type_from_mono_type(source_thunk.value.as_ref()),
                kind: FinalizedExprKind::BindHere {
                    expr: Box::new(expr),
                },
            };
            adapt_mono_value_expr(forced, source_thunk.value.as_ref(), target)
        }
        (
            elaborated::MonoType::Function(source_boundary),
            elaborated::MonoType::Function(target_boundary),
        ) => FinalizedExpr {
            ty: runtime_type_from_mono_type(target),
            kind: FinalizedExprKind::Coerce {
                from: core_function_type_from_boundary(source_boundary),
                to: core_function_type_from_boundary(target_boundary),
                expr: Box::new(expr),
            },
        },
        _ => FinalizedExpr {
            ty: runtime_type_from_mono_type(target),
            kind: FinalizedExprKind::Coerce {
                from: core_value_type_from_mono_type(source),
                to: core_value_type_from_mono_type(target),
                expr: Box::new(expr),
            },
        },
    }
}

fn runtime_type_from_computation(comp: &elaborated::MonoComputation) -> RuntimeType {
    runtime_type_from_mono_value_and_effect(&comp.value, &comp.effect)
}

fn runtime_type_from_mono_value_and_effect(
    value: &elaborated::MonoType,
    effect: &elaborated::MonoEffect,
) -> RuntimeType {
    let value = runtime_type_from_mono_type(value);
    let effect = convert_type(effect.row().as_type());
    if effect_is_empty(&effect) {
        value
    } else {
        RuntimeType::Thunk {
            effect,
            value: Box::new(value),
        }
    }
}

fn runtime_type_from_mono_type(typ: &elaborated::MonoType) -> RuntimeType {
    match typ {
        elaborated::MonoType::Value(value) => {
            runtime_type_from_core_value(convert_type(value.as_type()))
        }
        elaborated::MonoType::Function(boundary) => runtime_type_from_function_boundary(boundary),
        elaborated::MonoType::EffectiveThunk(thunk) => RuntimeType::Thunk {
            effect: convert_type(thunk.effect.row().as_type()),
            value: Box::new(runtime_type_from_mono_type(thunk.value.as_ref())),
        },
    }
}

fn runtime_type_from_function_boundary(boundary: &elaborated::FunctionBoundary) -> RuntimeType {
    RuntimeType::Fun {
        param: Box::new(runtime_type_from_mono_value_and_effect(
            &boundary.param,
            &boundary.param_effect,
        )),
        ret: Box::new(runtime_type_from_mono_value_and_effect(
            &boundary.ret,
            &boundary.ret_effect,
        )),
    }
}

fn runtime_type_from_core_value(ty: typed_ir::Type) -> RuntimeType {
    match ty {
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => RuntimeType::Fun {
            param: Box::new(runtime_type_from_core_value_and_effect(
                *param,
                *param_effect,
            )),
            ret: Box::new(runtime_type_from_core_value_and_effect(*ret, *ret_effect)),
        },
        ty => RuntimeType::Value(ty),
    }
}

fn runtime_type_from_core_value_and_effect(
    value: typed_ir::Type,
    effect: typed_ir::Type,
) -> RuntimeType {
    let value = runtime_type_from_core_value(value);
    if effect_is_empty(&effect) {
        value
    } else {
        RuntimeType::Thunk {
            effect,
            value: Box::new(value),
        }
    }
}

fn core_value_type_from_computation(comp: &elaborated::MonoComputation) -> typed_ir::Type {
    core_value_type_from_mono_type(&comp.value)
}

fn core_value_type_from_mono_type(typ: &elaborated::MonoType) -> typed_ir::Type {
    match typ {
        elaborated::MonoType::Value(value) => convert_type(value.as_type()),
        elaborated::MonoType::Function(boundary) => core_function_type_from_boundary(boundary),
        elaborated::MonoType::EffectiveThunk(thunk) => {
            core_value_type_from_mono_type(thunk.value.as_ref())
        }
    }
}

fn core_function_type_from_boundary(boundary: &elaborated::FunctionBoundary) -> typed_ir::Type {
    let (param, param_effect) =
        core_value_and_effect_from_boundary(&boundary.param, &boundary.param_effect);
    let (ret, ret_effect) =
        core_value_and_effect_from_boundary(&boundary.ret, &boundary.ret_effect);
    typed_ir::Type::Fun {
        param: Box::new(param),
        param_effect: Box::new(param_effect),
        ret_effect: Box::new(ret_effect),
        ret: Box::new(ret),
    }
}

fn core_value_and_effect_from_boundary(
    value: &elaborated::MonoType,
    effect: &elaborated::MonoEffect,
) -> (typed_ir::Type, typed_ir::Type) {
    match value {
        elaborated::MonoType::EffectiveThunk(thunk) => (
            core_value_type_from_mono_type(thunk.value.as_ref()),
            convert_type(thunk.effect.row().as_type()),
        ),
        value => (
            core_value_type_from_mono_type(value),
            convert_type(effect.row().as_type()),
        ),
    }
}

fn effect_is_empty(effect: &typed_ir::Type) -> bool {
    match effect {
        typed_ir::Type::Never => true,
        typed_ir::Type::Row { items, tail } => items.is_empty() && effect_is_empty(tail),
        typed_ir::Type::Recursive { body, .. } => effect_is_empty(body),
        _ => false,
    }
}

fn convert_type(typ: &erased::Type) -> typed_ir::Type {
    match typ {
        erased::Type::Unknown => typed_ir::Type::Unknown,
        erased::Type::Never => typed_ir::Type::Never,
        erased::Type::Any => typed_ir::Type::Any,
        erased::Type::Var(var) => typed_ir::Type::Var(convert_type_var(var.clone())),
        erased::Type::Named { path, args } => typed_ir::Type::Named {
            path: convert_path(path),
            args: args.iter().map(convert_type_arg).collect(),
        },
        erased::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(convert_type(param)),
            param_effect: Box::new(convert_type(param_effect)),
            ret_effect: Box::new(convert_type(ret_effect)),
            ret: Box::new(convert_type(ret)),
        },
        erased::Type::Tuple(items) => {
            typed_ir::Type::Tuple(items.iter().map(convert_type).collect())
        }
        erased::Type::Record(record) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: record
                .fields
                .iter()
                .map(|field| typed_ir::RecordField {
                    name: convert_name(field.name.clone()),
                    value: convert_type(&field.value),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.as_ref().map(convert_record_spread),
        }),
        erased::Type::Variant(variant) => typed_ir::Type::Variant(typed_ir::VariantType {
            cases: variant
                .cases
                .iter()
                .map(|case| typed_ir::VariantCase {
                    name: convert_name(case.name.clone()),
                    payloads: case.payloads.iter().map(convert_type).collect(),
                })
                .collect(),
            tail: variant
                .tail
                .as_ref()
                .map(|tail| Box::new(convert_type(tail))),
        }),
        erased::Type::Row { items, tail } => typed_ir::Type::Row {
            items: items.iter().map(convert_type).collect(),
            tail: Box::new(convert_type(tail)),
        },
        erased::Type::Union(items) => {
            typed_ir::Type::Union(items.iter().map(convert_type).collect())
        }
        erased::Type::Inter(items) => {
            typed_ir::Type::Inter(items.iter().map(convert_type).collect())
        }
        erased::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var: convert_type_var(var.clone()),
            body: Box::new(convert_type(body)),
        },
    }
}

fn convert_type_arg(arg: &erased::TypeArg) -> typed_ir::TypeArg {
    match arg {
        erased::TypeArg::Type(typ) => typed_ir::TypeArg::Type(convert_type(typ)),
        erased::TypeArg::Bounds(bounds) => typed_ir::TypeArg::Bounds(convert_type_bounds(bounds)),
    }
}

fn convert_type_bounds(bounds: &erased::TypeBounds) -> typed_ir::TypeBounds {
    typed_ir::TypeBounds {
        lower: bounds.lower.as_ref().map(|typ| Box::new(convert_type(typ))),
        upper: bounds.upper.as_ref().map(|typ| Box::new(convert_type(typ))),
    }
}

fn convert_record_spread(spread: &erased::RecordSpread) -> typed_ir::RecordSpread {
    match spread {
        erased::RecordSpread::Head(typ) => {
            typed_ir::RecordSpread::Head(Box::new(convert_type(typ)))
        }
        erased::RecordSpread::Tail(typ) => {
            typed_ir::RecordSpread::Tail(Box::new(convert_type(typ)))
        }
    }
}

fn convert_primitive_op(op: erased::PrimitiveOp) -> typed_ir::PrimitiveOp {
    macro_rules! convert {
        ($($variant:ident),* $(,)?) => {
            match op {
                $(erased::PrimitiveOp::$variant => typed_ir::PrimitiveOp::$variant,)*
            }
        };
    }
    convert!(
        YadaYada,
        BoolNot,
        BoolEq,
        ListEmpty,
        ListSingleton,
        ListLen,
        ListMerge,
        ListIndex,
        ListIndexRange,
        ListSplice,
        ListIndexRangeRaw,
        ListSpliceRaw,
        ListViewRaw,
        StringLen,
        StringIndex,
        StringIndexRange,
        StringSplice,
        StringIndexRangeRaw,
        StringSpliceRaw,
        StringLineCount,
        StringLineRange,
        IntAdd,
        IntSub,
        IntMul,
        IntDiv,
        IntMod,
        IntEq,
        IntLt,
        IntLe,
        IntGt,
        IntGe,
        FloatAdd,
        FloatSub,
        FloatMul,
        FloatDiv,
        FloatEq,
        FloatLt,
        FloatLe,
        FloatGt,
        FloatGe,
        StringEq,
        StringConcat,
        StringToBytes,
        CharEq,
        CharToString,
        CharIsWhitespace,
        CharIsPunctuation,
        CharIsWord,
        BytesLen,
        BytesEq,
        BytesConcat,
        BytesIndex,
        BytesIndexRange,
        BytesToUtf8Raw,
        BytesToPath,
        PathToBytes,
        IntToString,
        IntToHex,
        IntToUpperHex,
        FloatToString,
        BoolToString,
    )
}

fn convert_lit(lit: erased::Lit) -> typed_ir::Lit {
    match lit {
        erased::Lit::Int(value) => typed_ir::Lit::Int(value),
        erased::Lit::Float(value) => typed_ir::Lit::Float(value),
        erased::Lit::String(value) => typed_ir::Lit::String(value),
        erased::Lit::Bool(value) => typed_ir::Lit::Bool(value),
        erased::Lit::Unit => typed_ir::Lit::Unit,
    }
}

fn convert_effect_id_var(id: elaborated::EffectIdVar) -> EffectIdVar {
    EffectIdVar(id.0 as usize)
}

fn convert_effect_id_ref(id: elaborated::EffectIdRef) -> EffectIdRef {
    match id {
        elaborated::EffectIdRef::Var(id) => EffectIdRef::Var(convert_effect_id_var(id)),
        elaborated::EffectIdRef::Peek => EffectIdRef::Peek,
    }
}

fn convert_type_var(var: erased::TypeVar) -> typed_ir::TypeVar {
    typed_ir::TypeVar(var.0)
}

fn convert_path(path: &erased::Path) -> typed_ir::Path {
    typed_ir::Path::new(path.segments.iter().cloned().map(convert_name).collect())
}

fn convert_name(name: erased::Name) -> typed_ir::Name {
    typed_ir::Name(name.0)
}

fn path_from_name(name: typed_ir::Name) -> typed_ir::Path {
    typed_ir::Path::from_name(name)
}

fn local_name(def: erased::DefId) -> typed_ir::Name {
    typed_ir::Name(format!("local_{}", def.0))
}

fn unit_type() -> typed_ir::Type {
    typed_ir::Type::Tuple(Vec::new())
}

fn invariant(message: &'static str) -> RuntimeError {
    RuntimeError::InvariantViolation {
        stage: "elaborated-runtime-lower",
        context: String::new(),
        message,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lower_elaborated_program_rewrites_instance_ref_to_runtime_path() {
        let int = concrete_named_type("int");
        let comp = elaborated::MonoComputation {
            value: elaborated::MonoType::Value(int),
            effect: elaborated::MonoEffect::pure(),
        };
        let target = elaborated::MonoInstanceId(1);
        let program = elaborated::ElaboratedProgram {
            module: elaborated::ElaboratedModule {
                path: erased::Path::default(),
                instances: vec![
                    elaborated::MonoInstance {
                        id: elaborated::MonoInstanceId(0),
                        name: erased::Path::from_name(erased::Name("root_expr_0".to_string())),
                        source: elaborated::DemandSource::RootExpr(0),
                        signature: comp.clone(),
                        body: elaborated::ElaboratedExpr::new(
                            elaborated::ElaboratedExprKind::InstanceRef(target),
                            comp.clone(),
                        ),
                    },
                    elaborated::MonoInstance {
                        id: target,
                        name: erased::Path::from_name(erased::Name("one".to_string())),
                        source: elaborated::DemandSource::Def(erased::DefId(1)),
                        signature: comp.clone(),
                        body: elaborated::ElaboratedExpr::new(
                            elaborated::ElaboratedExprKind::Lit(erased::Lit::Int("1".to_string())),
                            comp.clone(),
                        ),
                    },
                ],
                root_exprs: vec![elaborated::ElaboratedExpr::new(
                    elaborated::ElaboratedExprKind::InstanceRef(target),
                    comp,
                )],
                roots: vec![elaborated::ElaboratedRoot::Instance(
                    elaborated::MonoInstanceId(0),
                )],
            },
            refs: elaborated::ResolvedRefTable::default(),
        };

        let module = lower_elaborated_program(program).expect("runtime module");
        assert_eq!(module.bindings.len(), 2);
        assert_eq!(module.root_exprs.len(), 1);
        assert!(matches!(
            &module.root_exprs[0].kind,
            FinalizedExprKind::Var(path) if path.segments == vec![typed_ir::Name("one".to_string())]
        ));
        assert_eq!(module.roots, vec![Root::Expr(0)]);
    }

    #[test]
    fn lower_elaborated_program_lowers_function_adapter_hygiene_plan() {
        let int = elaborated::MonoType::Value(concrete_named_type("int"));
        let io = elaborated::MonoEffect::new(concrete_named_type("io"));
        let function = elaborated::FunctionBoundary {
            param: int.clone(),
            param_effect: elaborated::MonoEffect::pure(),
            ret_effect: elaborated::MonoEffect::pure(),
            ret: int.clone(),
        };
        let function_comp = elaborated::MonoComputation {
            value: elaborated::MonoType::Function(Box::new(function.clone())),
            effect: elaborated::MonoEffect::pure(),
        };
        let target = elaborated::MonoInstanceId(1);
        let program = elaborated::ElaboratedProgram {
            module: elaborated::ElaboratedModule {
                path: erased::Path::default(),
                instances: vec![elaborated::MonoInstance {
                    id: target,
                    name: erased::Path::from_name(erased::Name("f".to_string())),
                    source: elaborated::DemandSource::Def(erased::DefId(1)),
                    signature: function_comp.clone(),
                    body: elaborated::ElaboratedExpr::new(
                        elaborated::ElaboratedExprKind::Lambda {
                            param: erased::DefId(10),
                            param_type: int.clone(),
                            body: Box::new(elaborated::ElaboratedExpr::new(
                                elaborated::ElaboratedExprKind::Def(erased::DefId(10)),
                                elaborated::MonoComputation {
                                    value: int,
                                    effect: elaborated::MonoEffect::pure(),
                                },
                            )),
                        },
                        function_comp.clone(),
                    ),
                }],
                root_exprs: vec![elaborated::ElaboratedExpr::new(
                    elaborated::ElaboratedExprKind::FunctionAdapter {
                        function: Box::new(elaborated::ElaboratedExpr::new(
                            elaborated::ElaboratedExprKind::InstanceRef(target),
                            function_comp.clone(),
                        )),
                        adapter: elaborated::FunctionAdapter {
                            source: function.clone(),
                            target: function,
                            call: elaborated::FunctionAdapterCall {
                                local_scope: Some(elaborated::EffectIdVar(9)),
                                result_boundaries: vec![
                                    elaborated::FunctionResultBoundary::AddId {
                                        id: elaborated::EffectIdRef::Peek,
                                        allowed: io,
                                        active: true,
                                    },
                                ],
                            },
                        },
                    },
                    function_comp,
                )],
                roots: vec![elaborated::ElaboratedRoot::Expr(0)],
            },
            refs: elaborated::ResolvedRefTable::default(),
        };

        let module = lower_elaborated_program(program).expect("runtime module");
        let FinalizedExprKind::Lambda { body, .. } = &module.root_exprs[0].kind else {
            panic!("function adapter should lower to a runtime lambda");
        };
        let FinalizedExprKind::LocalPushId { id, body } = &body.kind else {
            panic!("adapter local_scope should lower to LocalPushId");
        };
        assert_eq!(*id, EffectIdVar(9));
        let FinalizedExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } = &body.kind
        else {
            panic!("adapter result boundary should lower to AddId");
        };
        assert_eq!(*id, EffectIdRef::Peek);
        assert_eq!(*active, true);
        assert_eq!(
            allowed,
            &typed_ir::Type::Named {
                path: typed_ir::Path::from_name(typed_ir::Name("io".to_string())),
                args: Vec::new(),
            }
        );
        assert!(matches!(thunk.kind, FinalizedExprKind::Apply { .. }));
    }

    fn concrete_named_type(name: &str) -> elaborated::ConcreteType {
        elaborated::ConcreteType::try_from_type(erased::Type::Named {
            path: erased::Path::from_name(erased::Name(name.to_string())),
            args: Vec::new(),
        })
        .expect("concrete named type")
    }
}
