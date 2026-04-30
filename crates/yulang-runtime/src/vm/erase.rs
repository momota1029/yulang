use super::*;

pub(super) fn erase_module(
    module: Module,
    effects: &EffectPathResolver,
) -> Result<Module, VmError> {
    let bindings = module
        .bindings
        .into_iter()
        .map(|binding| erase_binding(binding, effects))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Module {
        path: module.path,
        bindings,
        root_exprs: module
            .root_exprs
            .into_iter()
            .map(|expr| erase_expr(expr, effects))
            .collect::<Result<Vec<_>, _>>()?,
        roots: module.roots,
    })
}

pub(super) fn erase_binding(
    binding: Binding,
    effects: &EffectPathResolver,
) -> Result<Binding, VmError> {
    if !binding.type_params.is_empty() {
        return Err(VmError::ResidualPolymorphicBinding {
            path: binding.name,
            vars: binding.type_params,
        });
    }
    Ok(Binding {
        name: binding.name,
        type_params: Vec::new(),
        scheme: binding.scheme,
        body: erase_expr(binding.body, effects)?,
    })
}

pub(super) fn erase_expr(expr: Expr, effects: &EffectPathResolver) -> Result<Expr, VmError> {
    let Expr { ty, kind } = expr;
    match kind {
        ExprKind::Thunk { effect, expr, .. } if effect_is_empty(&effect) => {
            erase_expr(*expr, effects)
        }
        ExprKind::BindHere { expr } if is_erased_thunk_type(&expr.ty) => erase_expr(*expr, effects),
        ExprKind::AddId { thunk, .. } if is_erased_thunk_type(&thunk.ty) => {
            erase_expr(*thunk, effects)
        }
        kind => Ok(Expr {
            ty: erase_type(ty, effects),
            kind: erase_kind(kind, effects)?,
        }),
    }
}

pub(super) fn erase_kind(
    kind: ExprKind,
    effects: &EffectPathResolver,
) -> Result<ExprKind, VmError> {
    Ok(match kind {
        ExprKind::EffectOp(path) => ExprKind::EffectOp(effects.resolve_op_path(path)),
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body: Box::new(erase_expr(*body, effects)?),
        },
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => ExprKind::Apply {
            callee: Box::new(erase_expr(*callee, effects)?),
            arg: Box::new(erase_expr(*arg, effects)?),
            evidence,
            instantiation,
        },
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => ExprKind::If {
            cond: Box::new(erase_expr(*cond, effects)?),
            then_branch: Box::new(erase_expr(*then_branch, effects)?),
            else_branch: Box::new(erase_expr(*else_branch, effects)?),
            evidence,
        },
        ExprKind::Tuple(items) => ExprKind::Tuple(
            items
                .into_iter()
                .map(|expr| erase_expr(expr, effects))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| {
                    Ok(RecordExprField {
                        name: field.name,
                        value: erase_expr(field.value, effects)?,
                    })
                })
                .collect::<Result<Vec<_>, VmError>>()?,
            spread: spread
                .map(|spread| erase_record_spread_expr(spread, effects))
                .transpose()?,
        },
        ExprKind::Variant { tag, value } => ExprKind::Variant {
            tag,
            value: value
                .map(|value| erase_expr(*value, effects).map(Box::new))
                .transpose()?,
        },
        ExprKind::Select { base, field } => ExprKind::Select {
            base: Box::new(erase_expr(*base, effects)?),
            field,
        },
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => ExprKind::Match {
            scrutinee: Box::new(erase_expr(*scrutinee, effects)?),
            arms: arms
                .into_iter()
                .map(|arm| erase_match_arm(arm, effects))
                .collect::<Result<Vec<_>, _>>()?,
            evidence,
        },
        ExprKind::Block { stmts, tail } => ExprKind::Block {
            stmts: stmts
                .into_iter()
                .map(|stmt| erase_stmt(stmt, effects))
                .collect::<Result<Vec<_>, _>>()?,
            tail: tail
                .map(|tail| erase_expr(*tail, effects).map(Box::new))
                .transpose()?,
        },
        ExprKind::Handle {
            body,
            arms,
            evidence,
            mut handler,
        } => {
            handler.consumes = handler
                .consumes
                .into_iter()
                .map(|path| effects.resolve_namespace_path(path))
                .collect();
            handler.residual_before = handler
                .residual_before
                .map(|ty| effects.resolve_effect_type(ty));
            handler.residual_after = handler
                .residual_after
                .map(|ty| effects.resolve_effect_type(ty));
            let consumes = handler.consumes.clone();
            ExprKind::Handle {
                body: Box::new(erase_expr(*body, effects)?),
                arms: arms
                    .into_iter()
                    .map(|arm| erase_handle_arm(arm, effects, &consumes))
                    .collect::<Result<Vec<_>, _>>()?,
                evidence,
                handler,
            }
        }
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => ExprKind::Thunk {
            effect: effects.resolve_effect_type(effect),
            value: erase_type(value, effects),
            expr: Box::new(erase_expr(*expr, effects)?),
        },
        ExprKind::BindHere { expr } => ExprKind::BindHere {
            expr: Box::new(erase_expr(*expr, effects)?),
        },
        ExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
            id,
            body: Box::new(erase_expr(*body, effects)?),
        },
        ExprKind::AddId { id, allowed, thunk } => ExprKind::AddId {
            id,
            allowed: effects.resolve_effect_type(allowed),
            thunk: Box::new(erase_expr(*thunk, effects)?),
        },
        ExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
            from,
            to,
            expr: Box::new(erase_expr(*expr, effects)?),
        },
        ExprKind::Pack { var, expr } => ExprKind::Pack {
            var,
            expr: Box::new(erase_expr(*expr, effects)?),
        },
        other @ (ExprKind::Var(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. }) => other,
    })
}

pub(super) fn erase_stmt(stmt: Stmt, effects: &EffectPathResolver) -> Result<Stmt, VmError> {
    Ok(match stmt {
        Stmt::Let { pattern, value } => Stmt::Let {
            pattern,
            value: erase_expr(value, effects)?,
        },
        Stmt::Expr(expr) => Stmt::Expr(erase_expr(expr, effects)?),
        Stmt::Module { def, body } => Stmt::Module {
            def,
            body: erase_expr(body, effects)?,
        },
    })
}

pub(super) fn erase_match_arm(
    arm: MatchArm,
    effects: &EffectPathResolver,
) -> Result<MatchArm, VmError> {
    Ok(MatchArm {
        pattern: arm.pattern,
        guard: arm
            .guard
            .map(|guard| erase_expr(guard, effects))
            .transpose()?,
        body: erase_expr(arm.body, effects)?,
    })
}

pub(super) fn erase_handle_arm(
    arm: HandleArm,
    effects: &EffectPathResolver,
    consumes: &[core_ir::Path],
) -> Result<HandleArm, VmError> {
    Ok(HandleArm {
        effect: effects.resolve_handle_arm_path(arm.effect, consumes),
        payload: arm.payload,
        resume: arm.resume,
        guard: arm
            .guard
            .map(|guard| erase_expr(guard, effects))
            .transpose()?,
        body: erase_expr(arm.body, effects)?,
    })
}

pub(super) fn erase_record_spread_expr(
    spread: RecordSpreadExpr,
    effects: &EffectPathResolver,
) -> Result<RecordSpreadExpr, VmError> {
    Ok(match spread {
        RecordSpreadExpr::Head(expr) => {
            RecordSpreadExpr::Head(Box::new(erase_expr(*expr, effects)?))
        }
        RecordSpreadExpr::Tail(expr) => {
            RecordSpreadExpr::Tail(Box::new(erase_expr(*expr, effects)?))
        }
    })
}

pub(super) fn erase_type(ty: Type, effects: &EffectPathResolver) -> Type {
    match ty {
        Type::Core(ty) => Type::Core(ty),
        Type::Fun { param, ret } => {
            Type::fun(erase_type(*param, effects), erase_type(*ret, effects))
        }
        Type::Thunk { effect, value } if effect_is_empty(&effect) => erase_type(*value, effects),
        Type::Thunk { effect, value } => Type::thunk(
            effects.resolve_effect_type(effect),
            erase_type(*value, effects),
        ),
    }
}

pub(super) fn is_erased_thunk_type(ty: &Type) -> bool {
    matches!(ty, Type::Thunk { effect, .. } if effect_is_empty(effect))
}

#[derive(Default)]
pub(super) struct EffectPathResolver {
    ops_by_last: HashMap<core_ir::Name, core_ir::Path>,
    namespaces_by_last: HashMap<core_ir::Name, core_ir::Path>,
}

impl EffectPathResolver {
    pub(super) fn collect(module: &Module) -> Self {
        let mut resolver = Self::default();
        for binding in &module.bindings {
            resolver.collect_expr(&binding.body);
        }
        for expr in &module.root_exprs {
            resolver.collect_expr(expr);
        }
        resolver
    }

    pub(super) fn resolve_op_path(&self, path: core_ir::Path) -> core_ir::Path {
        let path = strip_synthetic_with_segments(path);
        if path.segments.len() == 1 {
            if let Some(resolved) = self.ops_by_last.get(&path.segments[0]) {
                return resolved.clone();
            }
        }
        path
    }

    pub(super) fn resolve_handle_arm_path(
        &self,
        path: core_ir::Path,
        consumes: &[core_ir::Path],
    ) -> core_ir::Path {
        let path = strip_synthetic_with_segments(path);
        if path.segments.is_empty() {
            return path;
        }
        if path.segments.len() == 1 {
            let op = path.segments[0].clone();
            let mut direct_candidates = Vec::new();
            for namespace in consumes {
                let namespace = strip_synthetic_with_segments(namespace.clone());
                if namespace.segments.last() == Some(&op) && !direct_candidates.contains(&namespace)
                {
                    direct_candidates.push(namespace);
                }
            }
            if direct_candidates.len() == 1 {
                return direct_candidates.remove(0);
            }

            let mut candidates = Vec::new();
            for namespace in consumes {
                let namespace = strip_synthetic_with_segments(namespace.clone());
                if namespace.segments.is_empty() {
                    continue;
                }
                let mut segments = namespace.segments;
                segments.push(op.clone());
                let candidate = core_ir::Path { segments };
                if !candidates.contains(&candidate) {
                    candidates.push(candidate);
                }
            }
            if candidates.len() == 1 {
                return candidates.remove(0);
            }
        }
        if path.segments.len() > 1 {
            let op = path.segments.last().cloned().expect("non-empty path");
            let namespace = core_ir::Path {
                segments: path.segments[..path.segments.len() - 1].to_vec(),
            };
            let resolved_namespace = self.resolve_namespace_path(namespace.clone());
            if resolved_namespace != namespace {
                let mut segments = resolved_namespace.segments;
                segments.push(op);
                return core_ir::Path { segments };
            }
        }
        self.resolve_op_path(path)
    }

    pub(super) fn resolve_effect_type(&self, ty: core_ir::Type) -> core_ir::Type {
        match ty {
            core_ir::Type::Named { path, args } => core_ir::Type::Named {
                path: self.resolve_namespace_path(path),
                args,
            },
            core_ir::Type::Row { items, tail } => core_ir::Type::Row {
                items: items
                    .into_iter()
                    .map(|item| self.resolve_effect_type(item))
                    .collect(),
                tail: Box::new(self.resolve_effect_type(*tail)),
            },
            other => other,
        }
    }

    pub(super) fn resolve_namespace_path(&self, path: core_ir::Path) -> core_ir::Path {
        if path.segments.len() == 1 {
            if let Some(resolved) = self.namespaces_by_last.get(&path.segments[0]) {
                return resolved.clone();
            }
        }
        path
    }

    pub(super) fn collect_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::EffectOp(path) => self.insert_effect_op(path),
            ExprKind::Lambda { body, .. }
            | ExprKind::BindHere { expr: body }
            | ExprKind::Thunk { expr: body, .. }
            | ExprKind::LocalPushId { body, .. }
            | ExprKind::Coerce { expr: body, .. }
            | ExprKind::Pack { expr: body, .. } => self.collect_expr(body),
            ExprKind::Apply { callee, arg, .. } => {
                self.collect_expr(callee);
                self.collect_expr(arg);
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.collect_expr(cond);
                self.collect_expr(then_branch);
                self.collect_expr(else_branch);
            }
            ExprKind::Tuple(items) => items.iter().for_each(|item| self.collect_expr(item)),
            ExprKind::Record { fields, spread } => {
                fields
                    .iter()
                    .for_each(|field| self.collect_expr(&field.value));
                if let Some(spread) = spread {
                    match spread {
                        RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                            self.collect_expr(expr)
                        }
                    }
                }
            }
            ExprKind::Variant {
                value: Some(value), ..
            }
            | ExprKind::Select { base: value, .. } => self.collect_expr(value),
            ExprKind::Match {
                scrutinee, arms, ..
            } => {
                self.collect_expr(scrutinee);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        self.collect_expr(guard);
                    }
                    self.collect_expr(&arm.body);
                }
            }
            ExprKind::Block { stmts, tail } => {
                for stmt in stmts {
                    match stmt {
                        Stmt::Let { value, .. }
                        | Stmt::Expr(value)
                        | Stmt::Module { body: value, .. } => self.collect_expr(value),
                    }
                }
                if let Some(tail) = tail {
                    self.collect_expr(tail);
                }
            }
            ExprKind::Handle { body, arms, .. } => {
                self.collect_expr(body);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        self.collect_expr(guard);
                    }
                    self.collect_expr(&arm.body);
                }
            }
            ExprKind::AddId { thunk, .. } => self.collect_expr(thunk),
            ExprKind::Var(_)
            | ExprKind::PrimitiveOp(_)
            | ExprKind::Lit(_)
            | ExprKind::Variant { value: None, .. }
            | ExprKind::PeekId
            | ExprKind::FindId { .. } => {}
        }
    }

    pub(super) fn insert_effect_op(&mut self, path: &core_ir::Path) {
        let path = strip_synthetic_with_segments(path.clone());
        let Some(op) = path.segments.last().cloned() else {
            return;
        };
        self.ops_by_last.entry(op).or_insert_with(|| path.clone());
        if path.segments.len() > 1 {
            let namespace = core_ir::Path {
                segments: path.segments[..path.segments.len() - 1].to_vec(),
            };
            if let Some(name) = namespace.segments.last().cloned() {
                self.namespaces_by_last.entry(name).or_insert(namespace);
            }
        }
    }
}

pub(super) fn strip_synthetic_with_segments(path: core_ir::Path) -> core_ir::Path {
    core_ir::Path {
        segments: path
            .segments
            .into_iter()
            .filter(|segment| !segment.0.starts_with("#with"))
            .collect(),
    }
}
