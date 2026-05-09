use std::collections::{HashMap, HashSet};
use std::fmt;

use yulang_core_ir as core_ir;
use yulang_runtime as runtime;

use crate::cps_capture::infer_cps_captures;
use crate::cps_ir::{
    CpsContinuation, CpsContinuationId, CpsFunction, CpsHandler, CpsHandlerArm, CpsHandlerId,
    CpsLiteral, CpsModule, CpsShotKind, CpsStmt, CpsTerminator, CpsValueId,
};

pub type CpsLowerResult<T> = Result<T, CpsLowerError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CpsLowerError {
    UnsupportedRoot {
        root: runtime::Root,
    },
    MissingRootExpr {
        index: usize,
    },
    UnsupportedExpr {
        kind: &'static str,
    },
    UnsupportedPattern {
        kind: &'static str,
    },
    UnsupportedBinding {
        path: core_ir::Path,
        reason: &'static str,
    },
    PrimitiveArityMismatch {
        op: core_ir::PrimitiveOp,
        expected: usize,
        actual: usize,
    },
    CallArityMismatch {
        target: String,
        expected: usize,
        actual: usize,
    },
}

impl fmt::Display for CpsLowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CpsLowerError::UnsupportedRoot { root } => {
                write!(f, "CPS lowering does not support root {root:?} yet")
            }
            CpsLowerError::MissingRootExpr { index } => {
                write!(f, "runtime module has no root expression at index {index}")
            }
            CpsLowerError::UnsupportedExpr { kind } => {
                write!(f, "CPS lowering does not support {kind} expressions yet")
            }
            CpsLowerError::UnsupportedPattern { kind } => {
                write!(f, "CPS lowering does not support {kind} patterns yet")
            }
            CpsLowerError::UnsupportedBinding { path, reason } => {
                write!(
                    f,
                    "CPS lowering does not support binding {} yet: {reason}",
                    path_name(path)
                )
            }
            CpsLowerError::PrimitiveArityMismatch {
                op,
                expected,
                actual,
            } => write!(
                f,
                "CPS lowering expected {expected} arguments for primitive {op:?}, got {actual}"
            ),
            CpsLowerError::CallArityMismatch {
                target,
                expected,
                actual,
            } => write!(
                f,
                "CPS lowering expected {expected} arguments for call to {target}, got {actual}"
            ),
        }
    }
}

impl std::error::Error for CpsLowerError {}

pub fn lower_cps_module(module: &runtime::Module) -> CpsLowerResult<CpsModule> {
    let binding_table = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    let function_table = module
        .bindings
        .iter()
        .filter_map(binding_function_info)
        .collect::<HashMap<_, _>>();
    let reachable = reachable_binding_paths(module, &function_table, &binding_table);
    let functions = module
        .bindings
        .iter()
        .filter(|binding| reachable.contains(&binding.name))
        .map(|binding| lower_binding(binding, &function_table, &binding_table))
        .collect::<CpsLowerResult<Vec<_>>>()?;

    let mut roots = Vec::new();
    for root in &module.roots {
        match root {
            runtime::Root::Expr(index) => {
                let expr = module
                    .root_exprs
                    .get(*index)
                    .ok_or(CpsLowerError::MissingRootExpr { index: *index })?;
                roots.push(
                    FunctionLowerer::new(
                        format!("root_{index}"),
                        &function_table,
                        &binding_table,
                        Vec::new(),
                    )
                    .lower_root(expr)?,
                );
            }
            runtime::Root::Binding(_) => {
                return Err(CpsLowerError::UnsupportedRoot { root: root.clone() });
            }
        }
    }
    let mut module = CpsModule { functions, roots };
    infer_cps_captures(&mut module);
    Ok(module)
}

fn reachable_binding_paths(
    module: &runtime::Module,
    functions: &HashMap<core_ir::Path, FunctionInfo>,
    bindings: &HashMap<core_ir::Path, &runtime::Binding>,
) -> HashSet<core_ir::Path> {
    let binding_bodies = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), &binding.body))
        .collect::<HashMap<_, _>>();
    let mut reachable = HashSet::new();
    let mut stack = Vec::new();
    for root in &module.roots {
        match root {
            runtime::Root::Expr(index) => {
                if let Some(expr) = module.root_exprs.get(*index) {
                    collect_expr_direct_calls(expr, functions, bindings, &mut stack);
                }
            }
            runtime::Root::Binding(path) => stack.push(path.clone()),
        }
    }

    while let Some(path) = stack.pop() {
        if !reachable.insert(path.clone()) {
            continue;
        }
        let Some(body) = binding_bodies.get(&path) else {
            continue;
        };
        collect_expr_direct_calls(body, functions, bindings, &mut stack);
    }
    reachable
}

fn collect_expr_direct_calls(
    expr: &runtime::Expr,
    functions: &HashMap<core_ir::Path, FunctionInfo>,
    bindings: &HashMap<core_ir::Path, &runtime::Binding>,
    out: &mut Vec<core_ir::Path>,
) {
    if let Some((body, arms)) = inline_thunk_handler_apply(expr, functions, bindings) {
        collect_expr_direct_calls(&body, functions, bindings, out);
        let used_effects = collect_expr_performed_effects(&body);
        for arm in &arms {
            if !used_effects
                .iter()
                .any(|effect| effect_matches(&arm.effect, effect))
            {
                continue;
            }
            collect_pattern_direct_calls(&arm.payload, functions, bindings, out);
            if let Some(guard) = &arm.guard {
                collect_expr_direct_calls(guard, functions, bindings, out);
            }
            collect_expr_direct_calls(&arm.body, functions, bindings, out);
        }
        return;
    }
    if let Some((target, args)) = direct_apply_target(expr, functions) {
        if !args.iter().any(|arg| is_inline_argument(arg)) {
            out.push(target);
        }
    }
    match &expr.kind {
        runtime::ExprKind::Lambda { body, .. } => {
            collect_expr_direct_calls(body, functions, bindings, out);
        }
        runtime::ExprKind::Apply { callee, arg, .. } => {
            collect_expr_direct_calls(callee, functions, bindings, out);
            collect_expr_direct_calls(arg, functions, bindings, out);
        }
        runtime::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_direct_calls(cond, functions, bindings, out);
            collect_expr_direct_calls(then_branch, functions, bindings, out);
            collect_expr_direct_calls(else_branch, functions, bindings, out);
        }
        runtime::ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_direct_calls(item, functions, bindings, out);
            }
        }
        runtime::ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_direct_calls(&field.value, functions, bindings, out);
            }
            if let Some(spread) = spread {
                match spread {
                    runtime::RecordSpreadExpr::Head(expr)
                    | runtime::RecordSpreadExpr::Tail(expr) => {
                        collect_expr_direct_calls(expr, functions, bindings, out);
                    }
                }
            }
        }
        runtime::ExprKind::Variant {
            value: Some(value), ..
        } => collect_expr_direct_calls(value, functions, bindings, out),
        runtime::ExprKind::Select { base, .. } => {
            collect_expr_direct_calls(base, functions, bindings, out);
        }
        runtime::ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_direct_calls(scrutinee, functions, bindings, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_direct_calls(guard, functions, bindings, out);
                }
                collect_expr_direct_calls(&arm.body, functions, bindings, out);
                collect_pattern_direct_calls(&arm.pattern, functions, bindings, out);
            }
        }
        runtime::ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                match stmt {
                    runtime::Stmt::Let { pattern, value } => {
                        collect_pattern_direct_calls(pattern, functions, bindings, out);
                        collect_expr_direct_calls(value, functions, bindings, out);
                    }
                    runtime::Stmt::Expr(expr) => {
                        collect_expr_direct_calls(expr, functions, bindings, out);
                    }
                    runtime::Stmt::Module { body, .. } => {
                        collect_expr_direct_calls(body, functions, bindings, out);
                    }
                }
            }
            if let Some(tail) = tail {
                collect_expr_direct_calls(tail, functions, bindings, out);
            }
        }
        runtime::ExprKind::Handle { body, arms, .. } => {
            collect_expr_direct_calls(body, functions, bindings, out);
            for arm in arms {
                collect_pattern_direct_calls(&arm.payload, functions, bindings, out);
                if let Some(guard) = &arm.guard {
                    collect_expr_direct_calls(guard, functions, bindings, out);
                }
                collect_expr_direct_calls(&arm.body, functions, bindings, out);
            }
        }
        runtime::ExprKind::BindHere { expr }
        | runtime::ExprKind::Thunk { expr, .. }
        | runtime::ExprKind::LocalPushId { body: expr, .. }
        | runtime::ExprKind::AddId { thunk: expr, .. }
        | runtime::ExprKind::Coerce { expr, .. }
        | runtime::ExprKind::Pack { expr, .. } => {
            collect_expr_direct_calls(expr, functions, bindings, out);
        }
        runtime::ExprKind::Var(_)
        | runtime::ExprKind::EffectOp(_)
        | runtime::ExprKind::PrimitiveOp(_)
        | runtime::ExprKind::Lit(_)
        | runtime::ExprKind::Variant { value: None, .. }
        | runtime::ExprKind::PeekId
        | runtime::ExprKind::FindId { .. } => {}
    }
}

fn collect_expr_performed_effects(expr: &runtime::Expr) -> Vec<core_ir::Path> {
    let mut effects = Vec::new();
    collect_expr_performed_effects_into(expr, &mut effects);
    effects
}

fn collect_expr_performed_effects_into(expr: &runtime::Expr, out: &mut Vec<core_ir::Path>) {
    if let Some((effect, _)) = effect_apply_nested(expr)
        && !out.iter().any(|seen| seen == &effect)
    {
        out.push(effect);
    }
    match &expr.kind {
        runtime::ExprKind::Lambda { body, .. }
        | runtime::ExprKind::Thunk { expr: body, .. }
        | runtime::ExprKind::LocalPushId { body, .. }
        | runtime::ExprKind::BindHere { expr: body }
        | runtime::ExprKind::AddId { thunk: body, .. }
        | runtime::ExprKind::Coerce { expr: body, .. }
        | runtime::ExprKind::Pack { expr: body, .. } => {
            collect_expr_performed_effects_into(body, out);
        }
        runtime::ExprKind::Apply { callee, arg, .. } => {
            collect_expr_performed_effects_into(callee, out);
            collect_expr_performed_effects_into(arg, out);
        }
        runtime::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_performed_effects_into(cond, out);
            collect_expr_performed_effects_into(then_branch, out);
            collect_expr_performed_effects_into(else_branch, out);
        }
        runtime::ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_performed_effects_into(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_performed_effects_into(guard, out);
                }
                collect_expr_performed_effects_into(&arm.body, out);
            }
        }
        runtime::ExprKind::Handle { body, arms, .. } => {
            collect_expr_performed_effects_into(body, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_performed_effects_into(guard, out);
                }
                collect_expr_performed_effects_into(&arm.body, out);
            }
        }
        runtime::ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                match stmt {
                    runtime::Stmt::Let { value, .. } | runtime::Stmt::Expr(value) => {
                        collect_expr_performed_effects_into(value, out);
                    }
                    runtime::Stmt::Module { body, .. } => {
                        collect_expr_performed_effects_into(body, out);
                    }
                }
            }
            if let Some(tail) = tail {
                collect_expr_performed_effects_into(tail, out);
            }
        }
        runtime::ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_performed_effects_into(item, out);
            }
        }
        runtime::ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_performed_effects_into(&field.value, out);
            }
            if let Some(spread) = spread {
                match spread {
                    runtime::RecordSpreadExpr::Head(expr)
                    | runtime::RecordSpreadExpr::Tail(expr) => {
                        collect_expr_performed_effects_into(expr, out);
                    }
                }
            }
        }
        runtime::ExprKind::Variant {
            value: Some(value), ..
        }
        | runtime::ExprKind::Select { base: value, .. } => {
            collect_expr_performed_effects_into(value, out);
        }
        runtime::ExprKind::Var(_)
        | runtime::ExprKind::EffectOp(_)
        | runtime::ExprKind::PrimitiveOp(_)
        | runtime::ExprKind::Lit(_)
        | runtime::ExprKind::Variant { value: None, .. }
        | runtime::ExprKind::PeekId
        | runtime::ExprKind::FindId { .. } => {}
    }
}

fn collect_pattern_direct_calls(
    pattern: &runtime::Pattern,
    functions: &HashMap<core_ir::Path, FunctionInfo>,
    bindings: &HashMap<core_ir::Path, &runtime::Binding>,
    out: &mut Vec<core_ir::Path>,
) {
    match pattern {
        runtime::Pattern::Tuple { items, .. } => {
            for item in items {
                collect_pattern_direct_calls(item, functions, bindings, out);
            }
        }
        runtime::Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            for item in prefix {
                collect_pattern_direct_calls(item, functions, bindings, out);
            }
            if let Some(spread) = spread {
                collect_pattern_direct_calls(spread, functions, bindings, out);
            }
            for item in suffix {
                collect_pattern_direct_calls(item, functions, bindings, out);
            }
        }
        runtime::Pattern::Record { fields, spread, .. } => {
            for field in fields {
                collect_pattern_direct_calls(&field.pattern, functions, bindings, out);
                if let Some(default) = &field.default {
                    collect_expr_direct_calls(default, functions, bindings, out);
                }
            }
            if let Some(spread) = spread {
                match spread {
                    runtime::RecordSpreadPattern::Head(pattern)
                    | runtime::RecordSpreadPattern::Tail(pattern) => {
                        collect_pattern_direct_calls(pattern, functions, bindings, out);
                    }
                }
            }
        }
        runtime::Pattern::Variant {
            value: Some(value), ..
        }
        | runtime::Pattern::As { pattern: value, .. } => {
            collect_pattern_direct_calls(value, functions, bindings, out);
        }
        runtime::Pattern::Or { left, right, .. } => {
            collect_pattern_direct_calls(left, functions, bindings, out);
            collect_pattern_direct_calls(right, functions, bindings, out);
        }
        runtime::Pattern::Wildcard { .. }
        | runtime::Pattern::Bind { .. }
        | runtime::Pattern::Lit { .. }
        | runtime::Pattern::Variant { value: None, .. } => {}
    }
}

fn direct_apply_target<'expr>(
    expr: &'expr runtime::Expr,
    functions: &HashMap<core_ir::Path, FunctionInfo>,
) -> Option<(core_ir::Path, Vec<&'expr runtime::Expr>)> {
    direct_apply_path(expr, functions)
        .ok()
        .flatten()
        .map(|(path, _, args)| (path.clone(), args))
}

fn inline_thunk_handler_apply(
    expr: &runtime::Expr,
    functions: &HashMap<core_ir::Path, FunctionInfo>,
    bindings: &HashMap<core_ir::Path, &runtime::Binding>,
) -> Option<(runtime::Expr, Vec<runtime::HandleArm>)> {
    let (target, _, args) = direct_apply_path(expr, functions).ok()??;
    if args.len() != 1 {
        return None;
    }
    let binding = bindings.get(target)?;
    let (params, body) = collect_lambda_params(&binding.body);
    if params.len() != 1 {
        return None;
    }
    let body = handle_body_execution_inner(body).unwrap_or(body);
    let runtime::ExprKind::Handle {
        body: handled_body,
        arms,
        ..
    } = &body.kind
    else {
        return None;
    };
    let handled_body = handle_body_execution_inner(handled_body).unwrap_or(handled_body);
    let handled_body = transparent_expr(handled_body);
    let runtime::ExprKind::Var(body_var) = &handled_body.kind else {
        return None;
    };
    if body_var != &core_ir::Path::from_name(params[0].clone()) {
        return None;
    }
    Some((args[0].clone(), arms.clone()))
}

fn transparent_expr(expr: &runtime::Expr) -> &runtime::Expr {
    let mut current = expr;
    loop {
        match &current.kind {
            runtime::ExprKind::Coerce { expr, .. }
            | runtime::ExprKind::Pack { expr, .. }
            | runtime::ExprKind::AddId { thunk: expr, .. } => current = expr,
            _ => return current,
        }
    }
}

fn lower_binding(
    binding: &runtime::Binding,
    functions: &HashMap<core_ir::Path, FunctionInfo>,
    bindings: &HashMap<core_ir::Path, &runtime::Binding>,
) -> CpsLowerResult<CpsFunction> {
    if !binding.type_params.is_empty() {
        return Err(CpsLowerError::UnsupportedBinding {
            path: binding.name.clone(),
            reason: "residual type parameters",
        });
    }
    if let runtime::ExprKind::PrimitiveOp(op) = binding.body.kind {
        return Ok(lower_primitive_binding(&binding.name, op));
    }
    let (params, body) = collect_lambda_params(&binding.body);
    if params.is_empty() {
        return Err(CpsLowerError::UnsupportedBinding {
            path: binding.name.clone(),
            reason: "non-function body",
        });
    }
    FunctionLowerer::new(path_name(&binding.name), functions, bindings, params).lower_root(body)
}

fn binding_function_info(binding: &runtime::Binding) -> Option<(core_ir::Path, FunctionInfo)> {
    if let runtime::ExprKind::PrimitiveOp(op) = binding.body.kind {
        return Some((
            binding.name.clone(),
            FunctionInfo {
                name: path_name(&binding.name),
                arity: primitive_arity(op),
            },
        ));
    }
    let (params, _) = collect_lambda_params(&binding.body);
    (!params.is_empty()).then(|| {
        (
            binding.name.clone(),
            FunctionInfo {
                name: path_name(&binding.name),
                arity: params.len(),
            },
        )
    })
}

fn lower_primitive_binding(path: &core_ir::Path, op: core_ir::PrimitiveOp) -> CpsFunction {
    let arity = primitive_arity(op);
    let params = (0..arity).map(CpsValueId).collect::<Vec<_>>();
    let dest = CpsValueId(arity);
    CpsFunction {
        name: path_name(path),
        params: params.clone(),
        entry: CpsContinuationId(0),
        continuations: vec![CpsContinuation {
            id: CpsContinuationId(0),
            params: params.clone(),
            captures: Vec::new(),
            shot_kind: CpsShotKind::MultiShot,
            stmts: vec![CpsStmt::Primitive {
                dest,
                op,
                args: params,
            }],
            terminator: CpsTerminator::Return(dest),
        }],
        handlers: Vec::new(),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FunctionInfo {
    name: String,
    arity: usize,
}

struct FunctionLowerer<'a> {
    name: String,
    functions: &'a HashMap<core_ir::Path, FunctionInfo>,
    bindings: &'a HashMap<core_ir::Path, &'a runtime::Binding>,
    next_value: usize,
    next_continuation: usize,
    next_handler: usize,
    continuations: Vec<CpsContinuation>,
    handlers: Vec<CpsHandler>,
    current: ContinuationBuilder,
    locals: HashMap<core_ir::Path, CpsValueId>,
    local_exprs: HashMap<core_ir::Path, runtime::Expr>,
    resumptions: HashSet<core_ir::Path>,
    params: Vec<CpsValueId>,
}

impl<'a> FunctionLowerer<'a> {
    fn new(
        name: String,
        functions: &'a HashMap<core_ir::Path, FunctionInfo>,
        bindings: &'a HashMap<core_ir::Path, &'a runtime::Binding>,
        params: Vec<core_ir::Name>,
    ) -> Self {
        let mut next_value = 0;
        let mut param_values = Vec::with_capacity(params.len());
        let mut locals = HashMap::new();
        for param in params {
            let value = CpsValueId(next_value);
            next_value += 1;
            locals.insert(core_ir::Path::from_name(param), value);
            param_values.push(value);
        }
        Self {
            name,
            functions,
            bindings,
            next_value,
            next_continuation: 1,
            next_handler: 0,
            continuations: Vec::new(),
            handlers: Vec::new(),
            current: ContinuationBuilder::new(CpsContinuationId(0), param_values.clone()),
            locals,
            local_exprs: HashMap::new(),
            resumptions: HashSet::new(),
            params: param_values,
        }
    }

    fn lower_root(mut self, expr: &runtime::Expr) -> CpsLowerResult<CpsFunction> {
        let value = self.lower_expr(expr)?;
        self.terminate(CpsTerminator::Return(value));
        self.finish_current();
        Ok(CpsFunction {
            name: self.name,
            params: self.params,
            entry: CpsContinuationId(0),
            continuations: self.continuations,
            handlers: self.handlers,
        })
    }

    fn lower_expr(&mut self, expr: &runtime::Expr) -> CpsLowerResult<CpsValueId> {
        if let Some((body, arms)) = inline_thunk_handler_apply(expr, self.functions, self.bindings)
        {
            return self.lower_handle(&body, &arms);
        }

        if let Some(value) = self.lower_local_expr_apply(expr)? {
            return Ok(value);
        }

        if let Some((op, args)) = primitive_apply(expr) {
            let expected = primitive_arity(op);
            if args.len() != expected {
                return Err(CpsLowerError::PrimitiveArityMismatch {
                    op,
                    expected,
                    actual: args.len(),
                });
            }
            let args = args
                .into_iter()
                .map(|arg| self.lower_expr(arg))
                .collect::<CpsLowerResult<Vec<_>>>()?;
            let dest = self.fresh_value();
            self.current
                .stmts
                .push(CpsStmt::Primitive { dest, op, args });
            return Ok(dest);
        }

        if let Some((target, args)) = direct_apply(expr, self.functions)? {
            if args.iter().any(|arg| is_inline_argument(arg))
                && let Some(value) = self.lower_inline_direct_apply(expr)?
            {
                return Ok(value);
            }
            let args = args
                .into_iter()
                .map(|arg| self.lower_expr(arg))
                .collect::<CpsLowerResult<Vec<_>>>()?;
            let dest = self.fresh_value();
            self.current
                .stmts
                .push(CpsStmt::DirectCall { dest, target, args });
            return Ok(dest);
        }

        if let Some((resumption, arg)) = self.resume_apply(expr) {
            let arg = self.lower_expr(arg)?;
            let dest = self.fresh_value();
            self.current.stmts.push(CpsStmt::Resume {
                dest,
                resumption,
                arg,
            });
            return Ok(dest);
        }

        match &expr.kind {
            runtime::ExprKind::Lit(lit) => {
                let dest = self.fresh_value();
                self.current.stmts.push(CpsStmt::Literal {
                    dest,
                    literal: lower_literal(lit),
                });
                Ok(dest)
            }
            runtime::ExprKind::PrimitiveOp(_) => Err(CpsLowerError::UnsupportedExpr {
                kind: "bare primitive",
            }),
            runtime::ExprKind::Var(path) => self
                .locals
                .get(path)
                .copied()
                .ok_or(CpsLowerError::UnsupportedExpr { kind: "free var" }),
            runtime::ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => self.lower_if(cond, then_branch, else_branch),
            runtime::ExprKind::Block { stmts, tail } => self.lower_block(stmts, tail.as_deref()),
            runtime::ExprKind::EffectOp(_) => Err(CpsLowerError::UnsupportedExpr {
                kind: "bare effect operation",
            }),
            runtime::ExprKind::Lambda { .. } => {
                Err(CpsLowerError::UnsupportedExpr { kind: "lambda" })
            }
            runtime::ExprKind::Apply { .. } => {
                Err(CpsLowerError::UnsupportedExpr { kind: "apply" })
            }
            runtime::ExprKind::Tuple(_) => Err(CpsLowerError::UnsupportedExpr { kind: "tuple" }),
            runtime::ExprKind::Record { .. } => {
                Err(CpsLowerError::UnsupportedExpr { kind: "record" })
            }
            runtime::ExprKind::Variant { .. } => {
                Err(CpsLowerError::UnsupportedExpr { kind: "variant" })
            }
            runtime::ExprKind::Select { .. } => {
                Err(CpsLowerError::UnsupportedExpr { kind: "select" })
            }
            runtime::ExprKind::Match { .. } => {
                if let Some((cond, then_branch, else_branch)) = bool_match(expr) {
                    self.lower_if(cond, then_branch, else_branch)
                } else {
                    Err(CpsLowerError::UnsupportedExpr { kind: "match" })
                }
            }
            runtime::ExprKind::Handle { body, arms, .. } => self.lower_handle(body, arms),
            runtime::ExprKind::BindHere { expr } => self.lower_expr(expr),
            runtime::ExprKind::Thunk { expr, .. } => self.lower_expr(expr),
            runtime::ExprKind::LocalPushId { body, .. } => self.lower_expr(body),
            runtime::ExprKind::AddId { thunk, .. } => self.lower_expr(thunk),
            runtime::ExprKind::Coerce { expr, .. } | runtime::ExprKind::Pack { expr, .. } => {
                self.lower_expr(expr)
            }
            runtime::ExprKind::PeekId => Err(CpsLowerError::UnsupportedExpr { kind: "peek_id" }),
            runtime::ExprKind::FindId { .. } => {
                Err(CpsLowerError::UnsupportedExpr { kind: "find_id" })
            }
        }
    }

    fn lower_if(
        &mut self,
        cond: &runtime::Expr,
        then_branch: &runtime::Expr,
        else_branch: &runtime::Expr,
    ) -> CpsLowerResult<CpsValueId> {
        let cond = self.lower_expr(cond)?;
        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let then_cont = self.fresh_continuation();
        let else_cont = self.fresh_continuation();
        let merge_cont = self.fresh_continuation();
        let result = self.fresh_value();

        self.terminate(CpsTerminator::Branch {
            cond,
            then_cont,
            else_cont,
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(then_cont, Vec::new());
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        let then_value = self.lower_expr(then_branch)?;
        self.terminate(CpsTerminator::Continue {
            target: merge_cont,
            args: vec![then_value],
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(else_cont, Vec::new());
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        let else_value = self.lower_expr(else_branch)?;
        self.terminate(CpsTerminator::Continue {
            target: merge_cont,
            args: vec![else_value],
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(merge_cont, vec![result]);
        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        Ok(result)
    }

    fn lower_block(
        &mut self,
        stmts: &[runtime::Stmt],
        tail: Option<&runtime::Expr>,
    ) -> CpsLowerResult<CpsValueId> {
        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        for stmt in stmts {
            match stmt {
                runtime::Stmt::Let { pattern, value } => {
                    let value = self.lower_expr(value)?;
                    self.bind_pattern(pattern, value)?;
                }
                runtime::Stmt::Expr(expr) => {
                    self.lower_expr(expr)?;
                }
                runtime::Stmt::Module { .. } => {
                    self.locals = saved_locals;
                    return Err(CpsLowerError::UnsupportedExpr {
                        kind: "module statement",
                    });
                }
            }
        }
        let value = match tail {
            Some(tail) => self.lower_expr(tail)?,
            None => {
                let value = self.fresh_value();
                self.current.stmts.push(CpsStmt::Literal {
                    dest: value,
                    literal: CpsLiteral::Unit,
                });
                value
            }
        };
        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        Ok(value)
    }

    fn lower_handle(
        &mut self,
        body: &runtime::Expr,
        arms: &[runtime::HandleArm],
    ) -> CpsLowerResult<CpsValueId> {
        let mut value_arms = arms
            .iter()
            .filter(|arm| arm.resume.is_none() && arm.effect.segments.is_empty());
        let value_arm = value_arms.next();
        if value_arms.next().is_some() {
            return Err(CpsLowerError::UnsupportedExpr {
                kind: "multi-value handler",
            });
        }
        if value_arm.is_some_and(|arm| arm.guard.is_some()) {
            return Err(CpsLowerError::UnsupportedExpr {
                kind: "handler guard",
            });
        }

        let effect_arms = arms
            .iter()
            .filter(|arm| arm.resume.is_some())
            .collect::<Vec<_>>();
        if effect_arms.is_empty() {
            let value = self.lower_expr(body)?;
            return self.lower_handle_value(value, value_arm);
        };
        if arms
            .iter()
            .any(|candidate| candidate.resume.is_none() && !candidate.effect.segments.is_empty())
        {
            return Err(CpsLowerError::UnsupportedExpr {
                kind: "handler without resume",
            });
        }
        if effect_arms.iter().any(|arm| arm.guard.is_some()) {
            return Err(CpsLowerError::UnsupportedExpr {
                kind: "handler guard",
            });
        }
        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let saved_resumptions = self.resumptions.clone();

        let value_cont = self.fresh_continuation();
        let merge_cont = self.fresh_continuation();
        let handler = self.fresh_handler();
        let result = self.fresh_value();
        let effects = effect_arms
            .iter()
            .map(|arm| arm.effect.clone())
            .collect::<Vec<_>>();

        self.lower_handled_body(body, &effects, handler, Some(value_cont))?;
        let used_effects = self.performed_effects_for_handler(handler);
        let mut handler_entries = Vec::with_capacity(effect_arms.len());
        for arm in &effect_arms {
            if used_effects
                .iter()
                .any(|effect| effect_matches(&arm.effect, effect))
            {
                handler_entries.push((arm.effect.clone(), self.fresh_continuation()));
            }
        }
        if !handler_entries.is_empty() {
            self.handlers.push(CpsHandler {
                id: handler,
                arms: handler_entries
                    .iter()
                    .map(|(effect, entry)| CpsHandlerArm {
                        effect: effect.clone(),
                        entry: *entry,
                    })
                    .collect(),
            });
        }

        let handled_value = self.fresh_value();
        self.current = ContinuationBuilder::new(value_cont, vec![handled_value]);
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        self.resumptions = saved_resumptions.clone();
        let handled = self.lower_handle_value(handled_value, value_arm)?;
        self.terminate(CpsTerminator::Continue {
            target: merge_cont,
            args: vec![handled],
        });
        self.finish_current();

        for (effect, handler_cont) in handler_entries {
            let Some(arm) = effect_arms
                .iter()
                .find(|arm| effect_matches(&arm.effect, &effect))
            else {
                return Err(CpsLowerError::UnsupportedExpr {
                    kind: "handler effect mismatch",
                });
            };
            let Some(resume) = &arm.resume else {
                return Err(CpsLowerError::UnsupportedExpr {
                    kind: "handler without resume",
                });
            };
            let handler_payload = self.fresh_value();
            let handler_resume = self.fresh_value();
            self.current =
                ContinuationBuilder::new(handler_cont, vec![handler_payload, handler_resume]);
            self.locals = saved_locals.clone();
            self.local_exprs = saved_local_exprs.clone();
            self.resumptions = saved_resumptions.clone();
            self.bind_pattern(&arm.payload, handler_payload)?;
            let resume_path = core_ir::Path::from_name(resume.name.clone());
            self.locals.insert(resume_path.clone(), handler_resume);
            self.resumptions.insert(resume_path);
            let handled = self.lower_expr(&arm.body)?;
            self.terminate(CpsTerminator::Continue {
                target: merge_cont,
                args: vec![handled],
            });
            self.finish_current();
        }

        self.current = ContinuationBuilder::new(merge_cont, vec![result]);
        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        self.resumptions = saved_resumptions;
        Ok(result)
    }

    fn lower_handle_value(
        &mut self,
        value: CpsValueId,
        value_arm: Option<&runtime::HandleArm>,
    ) -> CpsLowerResult<CpsValueId> {
        let Some(arm) = value_arm else {
            return Ok(value);
        };
        self.bind_pattern(&arm.payload, value)?;
        self.lower_expr(&arm.body)
    }

    fn lower_handled_body(
        &mut self,
        body: &runtime::Expr,
        expected_effects: &[core_ir::Path],
        handler: CpsHandlerId,
        value_cont: Option<CpsContinuationId>,
    ) -> CpsLowerResult<core_ir::Path> {
        if let Some(expr) = handle_body_execution_inner(body) {
            return self.lower_handled_body(expr, expected_effects, handler, value_cont);
        }

        if let Some((effect, payload)) = effect_apply(body) {
            let (effect, resumed_value) =
                self.begin_resume_after_perform(effect, payload, expected_effects, handler)?;
            self.terminate(CpsTerminator::Return(resumed_value));
            self.finish_current();
            return Ok(effect);
        }

        if let Some((op, args)) = primitive_apply(body) {
            let expected = primitive_arity(op);
            if args.len() != expected {
                return Err(CpsLowerError::PrimitiveArityMismatch {
                    op,
                    expected,
                    actual: args.len(),
                });
            }
            let effect_arg = args
                .iter()
                .enumerate()
                .find_map(|(index, arg)| effect_apply_nested(arg).map(|effect| (index, effect)));
            let Some((effect_index, (effect, payload))) = effect_arg else {
                let value = self.lower_expr(body)?;
                self.finish_handled_value(value, value_cont);
                return Ok(default_expected_effect(expected_effects));
            };
            let (effect, resumed_value) =
                self.begin_resume_after_perform(effect, payload, expected_effects, handler)?;
            let mut lowered_args = Vec::with_capacity(args.len());
            for (index, arg) in args.into_iter().enumerate() {
                if index == effect_index {
                    lowered_args.push(resumed_value);
                } else {
                    lowered_args.push(self.lower_expr(arg)?);
                }
            }
            let dest = self.fresh_value();
            self.current.stmts.push(CpsStmt::Primitive {
                dest,
                op,
                args: lowered_args,
            });
            self.terminate(CpsTerminator::Return(dest));
            self.finish_current();
            return Ok(effect);
        }

        if let Some((target, args)) = direct_apply(body, self.functions)? {
            let effect_arg = args
                .iter()
                .enumerate()
                .find_map(|(index, arg)| effect_apply_nested(arg).map(|effect| (index, effect)));
            let Some((effect_index, (effect, payload))) = effect_arg else {
                let value = self.lower_expr(body)?;
                self.finish_handled_value(value, value_cont);
                return Ok(default_expected_effect(expected_effects));
            };
            let (effect, resumed_value) =
                self.begin_resume_after_perform(effect, payload, expected_effects, handler)?;
            let mut lowered_args = Vec::with_capacity(args.len());
            for (index, arg) in args.into_iter().enumerate() {
                if index == effect_index {
                    lowered_args.push(resumed_value);
                } else {
                    lowered_args.push(self.lower_expr(arg)?);
                }
            }
            let dest = self.fresh_value();
            self.current.stmts.push(CpsStmt::DirectCall {
                dest,
                target,
                args: lowered_args,
            });
            self.terminate(CpsTerminator::Return(dest));
            self.finish_current();
            return Ok(effect);
        }

        if let runtime::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } = &body.kind
        {
            return self.lower_handled_if(
                cond,
                then_branch,
                else_branch,
                expected_effects,
                handler,
                value_cont,
            );
        }

        if let Some((cond, then_branch, else_branch)) = bool_match(body) {
            return self.lower_handled_if(
                cond,
                then_branch,
                else_branch,
                expected_effects,
                handler,
                value_cont,
            );
        }

        if let runtime::ExprKind::Block { stmts, tail } = &body.kind {
            return self.lower_handled_block(
                stmts,
                tail.as_deref(),
                expected_effects,
                handler,
                value_cont,
            );
        }

        let value = match self.lower_expr(body) {
            Ok(value) => value,
            Err(CpsLowerError::UnsupportedExpr { .. }) => {
                return Err(CpsLowerError::UnsupportedExpr {
                    kind: "handler body continuation",
                });
            }
            Err(error) => return Err(error),
        };
        self.finish_handled_value(value, value_cont);
        Ok(default_expected_effect(expected_effects))
    }

    fn finish_handled_value(&mut self, value: CpsValueId, value_cont: Option<CpsContinuationId>) {
        match value_cont {
            Some(value_cont) => self.terminate(CpsTerminator::Continue {
                target: value_cont,
                args: vec![value],
            }),
            None => self.terminate(CpsTerminator::Return(value)),
        }
        self.finish_current();
    }

    fn lower_handled_if(
        &mut self,
        cond: &runtime::Expr,
        then_branch: &runtime::Expr,
        else_branch: &runtime::Expr,
        expected_effects: &[core_ir::Path],
        handler: CpsHandlerId,
        value_cont: Option<CpsContinuationId>,
    ) -> CpsLowerResult<core_ir::Path> {
        let cond = self.lower_expr(cond)?;
        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let saved_resumptions = self.resumptions.clone();
        let then_cont = self.fresh_continuation();
        let else_cont = self.fresh_continuation();

        self.terminate(CpsTerminator::Branch {
            cond,
            then_cont,
            else_cont,
        });
        self.finish_current();

        self.current = ContinuationBuilder::new(then_cont, Vec::new());
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        self.resumptions = saved_resumptions.clone();
        let then_effect =
            self.lower_handled_body(then_branch, expected_effects, handler, value_cont)?;

        self.current = ContinuationBuilder::new(else_cont, Vec::new());
        self.locals = saved_locals.clone();
        self.local_exprs = saved_local_exprs.clone();
        self.resumptions = saved_resumptions.clone();
        let else_effect =
            self.lower_handled_body(else_branch, expected_effects, handler, value_cont)?;
        if !handled_effects_compatible(expected_effects, &then_effect, &else_effect) {
            return Err(CpsLowerError::UnsupportedExpr {
                kind: "handler effect mismatch",
            });
        }

        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        self.resumptions = saved_resumptions;
        Ok(then_effect)
    }

    fn lower_handled_block(
        &mut self,
        stmts: &[runtime::Stmt],
        tail: Option<&runtime::Expr>,
        expected_effects: &[core_ir::Path],
        handler: CpsHandlerId,
        value_cont: Option<CpsContinuationId>,
    ) -> CpsLowerResult<core_ir::Path> {
        for (index, stmt) in stmts.iter().enumerate() {
            match stmt {
                runtime::Stmt::Let { pattern, value } => {
                    if let Some((effect, payload)) = effect_apply_nested(value) {
                        let (effect, resumed_value) = self.begin_resume_after_perform(
                            effect,
                            payload,
                            expected_effects,
                            handler,
                        )?;
                        self.bind_pattern(pattern, resumed_value)?;
                        let rest_effect = self.lower_handled_block(
                            &stmts[index + 1..],
                            tail,
                            expected_effects,
                            handler,
                            None,
                        )?;
                        if !handled_effects_compatible(expected_effects, &rest_effect, &effect) {
                            return Err(CpsLowerError::UnsupportedExpr {
                                kind: "handler effect mismatch",
                            });
                        }
                        return Ok(effect);
                    }

                    let value = self.lower_expr(value)?;
                    self.bind_pattern(pattern, value)?;
                }
                runtime::Stmt::Expr(expr) => {
                    if let Some((effect, payload)) = effect_apply_nested(expr) {
                        let (effect, _) = self.begin_resume_after_perform(
                            effect,
                            payload,
                            expected_effects,
                            handler,
                        )?;
                        let rest_effect = self.lower_handled_block(
                            &stmts[index + 1..],
                            tail,
                            expected_effects,
                            handler,
                            None,
                        )?;
                        if !handled_effects_compatible(expected_effects, &rest_effect, &effect) {
                            return Err(CpsLowerError::UnsupportedExpr {
                                kind: "handler effect mismatch",
                            });
                        }
                        return Ok(effect);
                    }

                    self.lower_expr(expr)?;
                }
                runtime::Stmt::Module { .. } => {
                    return Err(CpsLowerError::UnsupportedExpr {
                        kind: "module statement",
                    });
                }
            }
        }

        match tail {
            Some(tail) => self.lower_handled_body(tail, expected_effects, handler, value_cont),
            None => Err(CpsLowerError::UnsupportedExpr {
                kind: "handler body continuation",
            }),
        }
    }

    fn begin_resume_after_perform(
        &mut self,
        effect: core_ir::Path,
        payload: &runtime::Expr,
        expected_effects: &[core_ir::Path],
        handler: CpsHandlerId,
    ) -> CpsLowerResult<(core_ir::Path, CpsValueId)> {
        if !matches_any_effect(expected_effects, &effect) {
            return Err(CpsLowerError::UnsupportedExpr {
                kind: "handler effect mismatch",
            });
        }
        let payload = self.lower_expr(payload)?;
        let resume_cont = self.fresh_continuation();
        self.terminate(CpsTerminator::Perform {
            effect: effect.clone(),
            payload,
            resume: resume_cont,
            handler,
        });
        self.finish_current();

        let resumed_value = self.fresh_value();
        self.current = ContinuationBuilder::new(resume_cont, vec![resumed_value]);
        Ok((effect, resumed_value))
    }

    fn bind_pattern(
        &mut self,
        pattern: &runtime::Pattern,
        value: CpsValueId,
    ) -> CpsLowerResult<()> {
        match pattern {
            runtime::Pattern::Wildcard { .. } => Ok(()),
            runtime::Pattern::Bind { name, .. } => {
                let path = core_ir::Path::from_name(name.clone());
                self.local_exprs.remove(&path);
                self.locals.insert(path, value);
                Ok(())
            }
            runtime::Pattern::Lit { .. } => {
                Err(CpsLowerError::UnsupportedPattern { kind: "literal" })
            }
            runtime::Pattern::Tuple { .. } => {
                Err(CpsLowerError::UnsupportedPattern { kind: "tuple" })
            }
            runtime::Pattern::List { .. } => {
                Err(CpsLowerError::UnsupportedPattern { kind: "list" })
            }
            runtime::Pattern::Record { .. } => {
                Err(CpsLowerError::UnsupportedPattern { kind: "record" })
            }
            runtime::Pattern::Variant { .. } => {
                Err(CpsLowerError::UnsupportedPattern { kind: "variant" })
            }
            runtime::Pattern::Or { .. } => Err(CpsLowerError::UnsupportedPattern { kind: "or" }),
            runtime::Pattern::As { .. } => Err(CpsLowerError::UnsupportedPattern { kind: "as" }),
        }
    }

    fn fresh_value(&mut self) -> CpsValueId {
        let value = CpsValueId(self.next_value);
        self.next_value += 1;
        value
    }

    fn fresh_continuation(&mut self) -> CpsContinuationId {
        let continuation = CpsContinuationId(self.next_continuation);
        self.next_continuation += 1;
        continuation
    }

    fn fresh_handler(&mut self) -> CpsHandlerId {
        let handler = CpsHandlerId(self.next_handler);
        self.next_handler += 1;
        handler
    }

    fn performed_effects_for_handler(&self, handler: CpsHandlerId) -> Vec<core_ir::Path> {
        let mut effects = Vec::new();
        for continuation in &self.continuations {
            if let CpsTerminator::Perform {
                effect,
                handler: used,
                ..
            } = &continuation.terminator
                && *used == handler
                && !effects.iter().any(|seen| seen == effect)
            {
                effects.push(effect.clone());
            }
        }
        effects
    }

    fn lower_inline_direct_apply(
        &mut self,
        expr: &runtime::Expr,
    ) -> CpsLowerResult<Option<CpsValueId>> {
        let Some((target, _, args)) = direct_apply_path(expr, self.functions)? else {
            return Ok(None);
        };
        let Some(binding) = self.bindings.get(target) else {
            return Ok(None);
        };
        let (params, body) = collect_lambda_params(&binding.body);
        if params.len() != args.len() {
            return Ok(None);
        }

        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let saved_resumptions = self.resumptions.clone();
        for (param, arg) in params.into_iter().zip(args) {
            let path = core_ir::Path::from_name(param);
            if is_inline_argument(arg) {
                self.local_exprs.insert(path, arg.clone());
            } else {
                let value = self.lower_expr(arg)?;
                self.locals.insert(path, value);
            }
        }
        let value = self.lower_expr(body);
        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        self.resumptions = saved_resumptions;
        value.map(Some)
    }

    fn lower_local_expr_apply(
        &mut self,
        expr: &runtime::Expr,
    ) -> CpsLowerResult<Option<CpsValueId>> {
        let runtime::ExprKind::Apply { callee, arg, .. } = &expr.kind else {
            return Ok(None);
        };
        let callee = transparent_effect_expr(callee);
        let runtime::ExprKind::Var(path) = &callee.kind else {
            return Ok(None);
        };
        let Some(callee) = self.local_exprs.get(path).cloned() else {
            return Ok(None);
        };
        let callee = inline_callable_expr(&callee);
        let (params, body) = collect_lambda_params(&callee);
        if params.len() != 1 {
            return Ok(None);
        }
        let saved_locals = self.locals.clone();
        let saved_local_exprs = self.local_exprs.clone();
        let saved_resumptions = self.resumptions.clone();
        let value = self.lower_expr(arg)?;
        self.locals
            .insert(core_ir::Path::from_name(params[0].clone()), value);
        let value = self.lower_expr(body);
        self.locals = saved_locals;
        self.local_exprs = saved_local_exprs;
        self.resumptions = saved_resumptions;
        value.map(Some)
    }

    fn resume_apply<'expr>(
        &self,
        expr: &'expr runtime::Expr,
    ) -> Option<(CpsValueId, &'expr runtime::Expr)> {
        let runtime::ExprKind::Apply { callee, arg, .. } = &expr.kind else {
            return None;
        };
        let runtime::ExprKind::Var(path) = &callee.kind else {
            return None;
        };
        if !self.resumptions.contains(path) {
            return None;
        }
        let resumption = *self.locals.get(path)?;
        Some((resumption, arg.as_ref()))
    }

    fn terminate(&mut self, terminator: CpsTerminator) {
        self.current.terminator = Some(terminator);
    }

    fn finish_current(&mut self) {
        let terminator = self
            .current
            .terminator
            .take()
            .expect("CPS lowerer finished an unterminated continuation");
        self.continuations.push(CpsContinuation {
            id: self.current.id,
            params: std::mem::take(&mut self.current.params),
            captures: std::mem::take(&mut self.current.captures),
            shot_kind: CpsShotKind::MultiShot,
            stmts: std::mem::take(&mut self.current.stmts),
            terminator,
        });
    }
}

fn effect_matches(expected: &core_ir::Path, actual: &core_ir::Path) -> bool {
    actual == expected
        || (!expected.segments.is_empty()
            && actual.segments.len() == expected.segments.len() + 1
            && actual.segments.starts_with(&expected.segments))
        || (expected.segments.len() == 1 && actual.segments.last() == expected.segments.first())
}

fn is_inline_argument(expr: &runtime::Expr) -> bool {
    matches!(
        &expr.kind,
        runtime::ExprKind::Lambda { .. }
            | runtime::ExprKind::Thunk { .. }
            | runtime::ExprKind::LocalPushId { .. }
    )
}

fn inline_callable_expr(expr: &runtime::Expr) -> runtime::Expr {
    match &expr.kind {
        runtime::ExprKind::Thunk { expr, .. }
        | runtime::ExprKind::LocalPushId { body: expr, .. }
        | runtime::ExprKind::BindHere { expr }
        | runtime::ExprKind::AddId { thunk: expr, .. }
        | runtime::ExprKind::Coerce { expr, .. }
        | runtime::ExprKind::Pack { expr, .. } => inline_callable_expr(expr),
        _ => expr.clone(),
    }
}

fn matches_any_effect(expected: &[core_ir::Path], actual: &core_ir::Path) -> bool {
    expected
        .iter()
        .any(|expected| effect_matches(expected, actual))
}

fn handled_effects_compatible(
    expected: &[core_ir::Path],
    left: &core_ir::Path,
    right: &core_ir::Path,
) -> bool {
    left == right || (matches_any_effect(expected, left) && matches_any_effect(expected, right))
}

fn default_expected_effect(expected: &[core_ir::Path]) -> core_ir::Path {
    expected.first().cloned().unwrap_or_default()
}

struct ContinuationBuilder {
    id: CpsContinuationId,
    params: Vec<CpsValueId>,
    captures: Vec<CpsValueId>,
    stmts: Vec<CpsStmt>,
    terminator: Option<CpsTerminator>,
}

impl ContinuationBuilder {
    fn new(id: CpsContinuationId, params: Vec<CpsValueId>) -> Self {
        Self {
            id,
            params,
            captures: Vec::new(),
            stmts: Vec::new(),
            terminator: None,
        }
    }
}

fn collect_lambda_params(expr: &runtime::Expr) -> (Vec<core_ir::Name>, &runtime::Expr) {
    let mut params = Vec::new();
    let mut current = expr;
    while let runtime::ExprKind::Lambda { param, body, .. } = &current.kind {
        params.push(param.clone());
        current = body;
    }
    (params, current)
}

fn lower_literal(lit: &core_ir::Lit) -> CpsLiteral {
    match lit {
        core_ir::Lit::Int(value) => CpsLiteral::Int(value.clone()),
        core_ir::Lit::Float(value) => CpsLiteral::Float(value.clone()),
        core_ir::Lit::String(value) => CpsLiteral::String(value.clone()),
        core_ir::Lit::Bool(value) => CpsLiteral::Bool(*value),
        core_ir::Lit::Unit => CpsLiteral::Unit,
    }
}

fn primitive_apply(expr: &runtime::Expr) -> Option<(core_ir::PrimitiveOp, Vec<&runtime::Expr>)> {
    let mut args = Vec::new();
    let mut current = expr;
    loop {
        current = transparent_effect_expr(current);
        match &current.kind {
            runtime::ExprKind::Apply { callee, arg, .. } => {
                args.push(arg.as_ref());
                current = callee;
            }
            _ => break,
        }
    }
    let runtime::ExprKind::PrimitiveOp(op) = &current.kind else {
        return None;
    };
    args.reverse();
    Some((*op, args))
}

fn effect_apply(expr: &runtime::Expr) -> Option<(core_ir::Path, &runtime::Expr)> {
    let runtime::ExprKind::Apply { callee, arg, .. } = &expr.kind else {
        return None;
    };
    let callee = transparent_effect_expr(callee);
    let runtime::ExprKind::EffectOp(effect) = &callee.kind else {
        return None;
    };
    Some((effect.clone(), arg.as_ref()))
}

fn effect_apply_nested(expr: &runtime::Expr) -> Option<(core_ir::Path, &runtime::Expr)> {
    effect_apply(transparent_effect_expr(expr))
}

fn transparent_effect_expr(expr: &runtime::Expr) -> &runtime::Expr {
    let mut current = expr;
    loop {
        match &current.kind {
            runtime::ExprKind::BindHere { expr }
            | runtime::ExprKind::Coerce { expr, .. }
            | runtime::ExprKind::Pack { expr, .. }
            | runtime::ExprKind::AddId { thunk: expr, .. } => current = expr,
            _ => return current,
        }
    }
}

fn handle_body_execution_inner(expr: &runtime::Expr) -> Option<&runtime::Expr> {
    // VM handle evaluation runs a thunk-valued body inside the handler boundary.
    // Treat only the whole BindHere* -> Thunk wrapper as that execution marker.
    let mut current = expr;
    while let runtime::ExprKind::BindHere { expr } = &current.kind {
        current = expr;
    }
    let runtime::ExprKind::Thunk { expr, .. } = &current.kind else {
        return None;
    };
    let mut inner = expr.as_ref();
    while let runtime::ExprKind::BindHere { expr } = &inner.kind {
        inner = expr;
    }
    Some(inner)
}

fn direct_apply<'expr>(
    expr: &'expr runtime::Expr,
    functions: &HashMap<core_ir::Path, FunctionInfo>,
) -> CpsLowerResult<Option<(String, Vec<&'expr runtime::Expr>)>> {
    let Some((_, target, args)) = direct_apply_path(expr, functions)? else {
        return Ok(None);
    };
    Ok(Some((target.name.clone(), args)))
}

fn bool_match(expr: &runtime::Expr) -> Option<(&runtime::Expr, &runtime::Expr, &runtime::Expr)> {
    let runtime::ExprKind::Match {
        scrutinee, arms, ..
    } = &expr.kind
    else {
        return None;
    };
    if arms.len() != 2 || arms.iter().any(|arm| arm.guard.is_some()) {
        return None;
    }
    let mut then_branch = None;
    let mut else_branch = None;
    for arm in arms {
        match &arm.pattern {
            runtime::Pattern::Lit {
                lit: core_ir::Lit::Bool(true),
                ..
            } => then_branch = Some(&arm.body),
            runtime::Pattern::Lit {
                lit: core_ir::Lit::Bool(false),
                ..
            } => else_branch = Some(&arm.body),
            _ => return None,
        }
    }
    Some((scrutinee, then_branch?, else_branch?))
}

fn direct_apply_path<'expr, 'functions>(
    expr: &'expr runtime::Expr,
    functions: &'functions HashMap<core_ir::Path, FunctionInfo>,
) -> CpsLowerResult<
    Option<(
        &'expr core_ir::Path,
        &'functions FunctionInfo,
        Vec<&'expr runtime::Expr>,
    )>,
> {
    let mut args = Vec::new();
    let mut current = expr;
    loop {
        current = transparent_effect_expr(current);
        match &current.kind {
            runtime::ExprKind::Apply { callee, arg, .. } => {
                args.push(arg.as_ref());
                current = callee;
            }
            _ => break,
        }
    }
    let runtime::ExprKind::Var(path) = &current.kind else {
        return Ok(None);
    };
    let Some(target) = functions.get(path) else {
        return Ok(None);
    };
    if args.len() != target.arity {
        return Err(CpsLowerError::CallArityMismatch {
            target: target.name.clone(),
            expected: target.arity,
            actual: args.len(),
        });
    }
    args.reverse();
    Ok(Some((path, target, args)))
}

fn primitive_arity(op: core_ir::PrimitiveOp) -> usize {
    use core_ir::PrimitiveOp;
    match op {
        PrimitiveOp::BoolNot
        | PrimitiveOp::ListEmpty
        | PrimitiveOp::ListSingleton
        | PrimitiveOp::ListLen
        | PrimitiveOp::ListViewRaw
        | PrimitiveOp::StringLen
        | PrimitiveOp::IntToString
        | PrimitiveOp::IntToHex
        | PrimitiveOp::IntToUpperHex
        | PrimitiveOp::FloatToString
        | PrimitiveOp::BoolToString => 1,
        PrimitiveOp::BoolEq
        | PrimitiveOp::ListMerge
        | PrimitiveOp::ListIndex
        | PrimitiveOp::ListIndexRange
        | PrimitiveOp::StringIndex
        | PrimitiveOp::StringIndexRange
        | PrimitiveOp::IntAdd
        | PrimitiveOp::IntSub
        | PrimitiveOp::IntMul
        | PrimitiveOp::IntDiv
        | PrimitiveOp::IntEq
        | PrimitiveOp::IntLt
        | PrimitiveOp::IntLe
        | PrimitiveOp::IntGt
        | PrimitiveOp::IntGe
        | PrimitiveOp::FloatAdd
        | PrimitiveOp::FloatSub
        | PrimitiveOp::FloatMul
        | PrimitiveOp::FloatDiv
        | PrimitiveOp::FloatEq
        | PrimitiveOp::FloatLt
        | PrimitiveOp::FloatLe
        | PrimitiveOp::FloatGt
        | PrimitiveOp::FloatGe
        | PrimitiveOp::StringConcat => 2,
        PrimitiveOp::ListSplice
        | PrimitiveOp::ListIndexRangeRaw
        | PrimitiveOp::StringSplice
        | PrimitiveOp::StringIndexRangeRaw => 3,
        PrimitiveOp::ListSpliceRaw | PrimitiveOp::StringSpliceRaw => 4,
    }
}

fn path_name(path: &core_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

#[cfg(test)]
mod tests {
    use crate::cps_eval::eval_cps_module;
    use crate::cps_validate::validate_cps_module;

    use super::*;

    fn unknown_lit(lit: core_ir::Lit) -> runtime::Expr {
        runtime::Expr::typed(runtime::ExprKind::Lit(lit), runtime::Type::unknown())
    }

    fn primitive(op: core_ir::PrimitiveOp) -> runtime::Expr {
        runtime::Expr::typed(runtime::ExprKind::PrimitiveOp(op), runtime::Type::unknown())
    }

    fn apply(callee: runtime::Expr, arg: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Apply {
                callee: Box::new(callee),
                arg: Box::new(arg),
                evidence: None,
                instantiation: None,
            },
            runtime::Type::unknown(),
        )
    }

    fn if_expr(
        cond: runtime::Expr,
        then_branch: runtime::Expr,
        else_branch: runtime::Expr,
    ) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::If {
                cond: Box::new(cond),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
                evidence: None,
            },
            runtime::Type::unknown(),
        )
    }

    fn var(name: &str) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Var(core_ir::Path::from_name(core_ir::Name(name.to_string()))),
            runtime::Type::unknown(),
        )
    }

    fn effect_op(name: &str) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::EffectOp(core_ir::Path::from_name(core_ir::Name(name.to_string()))),
            runtime::Type::unknown(),
        )
    }

    fn effect_op_path(path: core_ir::Path) -> runtime::Expr {
        runtime::Expr::typed(runtime::ExprKind::EffectOp(path), runtime::Type::unknown())
    }

    fn bind_pattern(name: &str) -> runtime::Pattern {
        runtime::Pattern::Bind {
            name: core_ir::Name(name.to_string()),
            ty: runtime::Type::unknown(),
        }
    }

    fn handle_once(
        effect: &str,
        payload: &str,
        resume: &str,
        body: runtime::Expr,
        arm_body: runtime::Expr,
    ) -> runtime::Expr {
        let effect = core_ir::Path::from_name(core_ir::Name(effect.to_string()));
        runtime::Expr::typed(
            runtime::ExprKind::Handle {
                body: Box::new(body),
                arms: vec![runtime::HandleArm {
                    effect: effect.clone(),
                    payload: bind_pattern(payload),
                    resume: Some(runtime::ResumeBinding {
                        name: core_ir::Name(resume.to_string()),
                        ty: runtime::Type::unknown(),
                    }),
                    guard: None,
                    body: arm_body,
                }],
                evidence: runtime::JoinEvidence {
                    result: core_ir::Type::Unknown,
                },
                handler: runtime::HandleEffect {
                    consumes: vec![effect],
                    residual_before: None,
                    residual_after: None,
                },
            },
            runtime::Type::unknown(),
        )
    }

    fn handle_once_with_value(
        effect: &str,
        payload: &str,
        resume: &str,
        body: runtime::Expr,
        arm_body: runtime::Expr,
        value_payload: &str,
        value_body: runtime::Expr,
    ) -> runtime::Expr {
        let effect = core_ir::Path::from_name(core_ir::Name(effect.to_string()));
        runtime::Expr::typed(
            runtime::ExprKind::Handle {
                body: Box::new(body),
                arms: vec![
                    runtime::HandleArm {
                        effect: effect.clone(),
                        payload: bind_pattern(payload),
                        resume: Some(runtime::ResumeBinding {
                            name: core_ir::Name(resume.to_string()),
                            ty: runtime::Type::unknown(),
                        }),
                        guard: None,
                        body: arm_body,
                    },
                    runtime::HandleArm {
                        effect: core_ir::Path::default(),
                        payload: bind_pattern(value_payload),
                        resume: None,
                        guard: None,
                        body: value_body,
                    },
                ],
                evidence: runtime::JoinEvidence {
                    result: core_ir::Type::Unknown,
                },
                handler: runtime::HandleEffect {
                    consumes: vec![effect],
                    residual_before: None,
                    residual_after: None,
                },
            },
            runtime::Type::unknown(),
        )
    }

    fn handle_value(
        body: runtime::Expr,
        value_payload: &str,
        value_body: runtime::Expr,
    ) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Handle {
                body: Box::new(body),
                arms: vec![runtime::HandleArm {
                    effect: core_ir::Path::default(),
                    payload: bind_pattern(value_payload),
                    resume: None,
                    guard: None,
                    body: value_body,
                }],
                evidence: runtime::JoinEvidence {
                    result: core_ir::Type::Unknown,
                },
                handler: runtime::HandleEffect {
                    consumes: Vec::new(),
                    residual_before: None,
                    residual_after: None,
                },
            },
            runtime::Type::unknown(),
        )
    }

    fn handle_once_expr(
        effect: core_ir::Path,
        payload: &str,
        resume: &str,
        body: runtime::Expr,
        arm_body: runtime::Expr,
    ) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Handle {
                body: Box::new(body),
                arms: vec![runtime::HandleArm {
                    effect: effect.clone(),
                    payload: bind_pattern(payload),
                    resume: Some(runtime::ResumeBinding {
                        name: core_ir::Name(resume.to_string()),
                        ty: runtime::Type::unknown(),
                    }),
                    guard: None,
                    body: arm_body,
                }],
                evidence: runtime::JoinEvidence {
                    result: core_ir::Type::Unknown,
                },
                handler: runtime::HandleEffect {
                    consumes: vec![effect],
                    residual_before: None,
                    residual_after: None,
                },
            },
            runtime::Type::unknown(),
        )
    }

    fn block(stmts: Vec<runtime::Stmt>, tail: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Block {
                stmts,
                tail: Some(Box::new(tail)),
            },
            runtime::Type::unknown(),
        )
    }

    fn thunk(expr: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Thunk {
                effect: core_ir::Type::Unknown,
                value: runtime::Type::unknown(),
                expr: Box::new(expr),
            },
            runtime::Type::unknown(),
        )
    }

    fn bind_here(expr: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::BindHere {
                expr: Box::new(expr),
            },
            runtime::Type::unknown(),
        )
    }

    fn lambda(param: &str, body: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Lambda {
                param: core_ir::Name(param.to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(body),
            },
            runtime::Type::unknown(),
        )
    }

    fn binding(name: &str, body: runtime::Expr) -> runtime::Binding {
        runtime::Binding {
            name: core_ir::Path::from_name(core_ir::Name(name.to_string())),
            type_params: Vec::new(),
            scheme: core_ir::Scheme {
                requirements: Vec::new(),
                body: core_ir::Type::Unknown,
            },
            body,
        }
    }

    fn effect_path(effect: &str, op: &str) -> core_ir::Path {
        core_ir::Path {
            segments: vec![
                core_ir::Name(effect.to_string()),
                core_ir::Name(op.to_string()),
            ],
        }
    }

    fn module_with_root(expr: runtime::Expr) -> runtime::Module {
        module_with_bindings_and_root(Vec::new(), expr)
    }

    fn module_with_bindings_and_root(
        bindings: Vec<runtime::Binding>,
        expr: runtime::Expr,
    ) -> runtime::Module {
        runtime::Module {
            path: core_ir::Path::default(),
            bindings,
            root_exprs: vec![expr],
            roots: vec![runtime::Root::Expr(0)],
            role_impls: Vec::new(),
        }
    }

    #[test]
    fn lowers_pure_int_add_to_multishot_cps() {
        let expr = apply(
            apply(
                primitive(core_ir::PrimitiveOp::IntAdd),
                unknown_lit(core_ir::Lit::Int("20".to_string())),
            ),
            unknown_lit(core_ir::Lit::Int("22".to_string())),
        );
        let module = module_with_root(expr);
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(lowered.roots.len(), 1);
        assert_eq!(lowered.roots[0].continuations.len(), 1);
        assert_eq!(
            lowered.roots[0].continuations[0].shot_kind,
            CpsShotKind::MultiShot
        );
        assert_eq!(
            lowered.roots[0].continuations[0].stmts,
            vec![
                CpsStmt::Literal {
                    dest: CpsValueId(0),
                    literal: CpsLiteral::Int("20".to_string()),
                },
                CpsStmt::Literal {
                    dest: CpsValueId(1),
                    literal: CpsLiteral::Int("22".to_string()),
                },
                CpsStmt::Primitive {
                    dest: CpsValueId(2),
                    op: core_ir::PrimitiveOp::IntAdd,
                    args: vec![CpsValueId(0), CpsValueId(1)],
                },
            ]
        );
        assert_eq!(
            lowered.roots[0].continuations[0].terminator,
            CpsTerminator::Return(CpsValueId(2))
        );
    }

    #[test]
    fn skips_unreachable_non_function_binding() {
        let module = runtime::Module {
            path: core_ir::Path::default(),
            bindings: vec![runtime::Binding {
                name: core_ir::Path::from_name(core_ir::Name("unused".to_string())),
                type_params: Vec::new(),
                scheme: core_ir::Scheme {
                    requirements: Vec::new(),
                    body: core_ir::Type::Unknown,
                },
                body: unknown_lit(core_ir::Lit::Int("0".to_string())),
            }],
            root_exprs: vec![unknown_lit(core_ir::Lit::Int("41".to_string()))],
            roots: vec![runtime::Root::Expr(0)],
            role_impls: Vec::new(),
        };
        let lowered = lower_cps_module(&module).expect("lowered");

        assert!(lowered.functions.is_empty());
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("41".to_string())]
        );
    }

    #[test]
    fn inlines_thunk_handler_wrapper_call() {
        let effect = effect_path("sub", "return");
        let handler = binding(
            "run",
            lambda(
                "x",
                handle_once_expr(effect.clone(), "a", "_k", var("x"), thunk(var("a"))),
            ),
        );
        let root = apply(
            var("run"),
            thunk(apply(
                effect_op_path(effect),
                unknown_lit(core_ir::Lit::Int("41".to_string())),
            )),
        );
        let module = module_with_bindings_and_root(vec![handler], root);
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert!(lowered.functions.is_empty());
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("41".to_string())]
        );
    }

    #[test]
    fn lowers_if_to_multishot_continuation_graph() {
        let module = module_with_root(if_expr(
            unknown_lit(core_ir::Lit::Bool(true)),
            unknown_lit(core_ir::Lit::Int("1".to_string())),
            unknown_lit(core_ir::Lit::Int("2".to_string())),
        ));
        let lowered = lower_cps_module(&module).expect("lowered");
        let root = &lowered.roots[0];

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(root.continuations.len(), 4);
        assert!(
            root.continuations
                .iter()
                .all(|continuation| continuation.shot_kind == CpsShotKind::MultiShot)
        );
        assert_eq!(
            root.continuations[0].terminator,
            CpsTerminator::Branch {
                cond: CpsValueId(0),
                then_cont: CpsContinuationId(1),
                else_cont: CpsContinuationId(2),
            }
        );
        assert_eq!(root.continuations[3].params, vec![CpsValueId(1)]);
        assert_eq!(
            root.continuations[3].terminator,
            CpsTerminator::Return(CpsValueId(1))
        );
    }

    #[test]
    fn lowers_direct_call_to_cps() {
        let inc = binding(
            "inc",
            lambda(
                "x",
                apply(
                    apply(primitive(core_ir::PrimitiveOp::IntAdd), var("x")),
                    unknown_lit(core_ir::Lit::Int("1".to_string())),
                ),
            ),
        );
        let root = apply(var("inc"), unknown_lit(core_ir::Lit::Int("41".to_string())));
        let module = module_with_bindings_and_root(vec![inc], root);
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(lowered.functions.len(), 1);
        assert_eq!(lowered.functions[0].name, "inc");
        assert_eq!(lowered.functions[0].params, vec![CpsValueId(0)]);
        assert_eq!(
            lowered.roots[0].continuations[0].stmts,
            vec![
                CpsStmt::Literal {
                    dest: CpsValueId(0),
                    literal: CpsLiteral::Int("41".to_string()),
                },
                CpsStmt::DirectCall {
                    dest: CpsValueId(1),
                    target: "inc".to_string(),
                    args: vec![CpsValueId(0)],
                },
            ]
        );
    }

    #[test]
    fn lowers_single_effect_handler_with_resumption() {
        let body = apply(
            effect_op("choose"),
            unknown_lit(core_ir::Lit::Int("1".to_string())),
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(core_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(core_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));
        let lowered = lower_cps_module(&module).expect("lowered");
        let root = &lowered.roots[0];

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(root.handlers.len(), 1);
        assert!(
            root.continuations.iter().any(|continuation| matches!(
                continuation.terminator,
                CpsTerminator::Perform { .. }
            ))
        );
        assert!(
            root.continuations
                .iter()
                .flat_map(|continuation| &continuation.stmts)
                .any(|stmt| matches!(stmt, CpsStmt::Resume { .. }))
        );
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("3".to_string())]
        );
    }

    #[test]
    fn lowers_value_handler_arm() {
        let body = unknown_lit(core_ir::Lit::Int("1".to_string()));
        let value_body = apply(
            apply(primitive(core_ir::PrimitiveOp::IntAdd), var("value")),
            unknown_lit(core_ir::Lit::Int("10".to_string())),
        );
        let module = module_with_root(handle_value(body, "value", value_body));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("11".to_string())]
        );
    }

    #[test]
    fn leaves_resume_result_outside_value_arm() {
        let body = apply(
            effect_op("choose"),
            unknown_lit(core_ir::Lit::Int("1".to_string())),
        );
        let arm_body = apply(var("k"), var("x"));
        let value_body = apply(
            apply(primitive(core_ir::PrimitiveOp::IntAdd), var("value")),
            unknown_lit(core_ir::Lit::Int("10".to_string())),
        );
        let module = module_with_root(handle_once_with_value(
            "choose", "x", "k", body, arm_body, "value", value_body,
        ));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("1".to_string())]
        );
    }

    #[test]
    fn leaves_multishot_resume_results_outside_value_arm() {
        let body = apply(
            effect_op("choose"),
            unknown_lit(core_ir::Lit::Int("1".to_string())),
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(core_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(core_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );
        let value_body = apply(
            apply(primitive(core_ir::PrimitiveOp::IntAdd), var("value")),
            unknown_lit(core_ir::Lit::Int("10".to_string())),
        );
        let module = module_with_root(handle_once_with_value(
            "choose", "x", "k", body, arm_body, "value", value_body,
        ));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("3".to_string())]
        );
    }

    #[test]
    fn lowers_effect_handler_body_rest_into_resumption_continuation() {
        let choose_one = apply(
            effect_op("choose"),
            unknown_lit(core_ir::Lit::Int("1".to_string())),
        );
        let body = apply(
            apply(primitive(core_ir::PrimitiveOp::IntAdd), choose_one),
            unknown_lit(core_ir::Lit::Int("10".to_string())),
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(core_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(core_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("23".to_string())]
        );
    }

    #[test]
    fn lowers_direct_call_rest_into_resumption_continuation() {
        let inc = binding(
            "inc",
            lambda(
                "x",
                apply(
                    apply(primitive(core_ir::PrimitiveOp::IntAdd), var("x")),
                    unknown_lit(core_ir::Lit::Int("10".to_string())),
                ),
            ),
        );
        let body = apply(
            var("inc"),
            apply(
                effect_op("choose"),
                unknown_lit(core_ir::Lit::Int("1".to_string())),
            ),
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(core_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(core_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );
        let module = module_with_bindings_and_root(
            vec![inc],
            handle_once("choose", "x", "k", body, arm_body),
        );
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("23".to_string())]
        );
    }

    #[test]
    fn lowers_block_rest_into_resumption_continuation() {
        let body = block(
            vec![runtime::Stmt::Let {
                pattern: bind_pattern("y"),
                value: apply(
                    effect_op("choose"),
                    unknown_lit(core_ir::Lit::Int("1".to_string())),
                ),
            }],
            apply(
                apply(primitive(core_ir::PrimitiveOp::IntAdd), var("y")),
                unknown_lit(core_ir::Lit::Int("10".to_string())),
            ),
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(core_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(core_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("23".to_string())]
        );
    }

    #[test]
    fn lowers_multiple_block_effects_into_nested_resumption_continuations() {
        let body = block(
            vec![
                runtime::Stmt::Let {
                    pattern: bind_pattern("a"),
                    value: apply(
                        effect_op("choose"),
                        unknown_lit(core_ir::Lit::Int("1".to_string())),
                    ),
                },
                runtime::Stmt::Let {
                    pattern: bind_pattern("b"),
                    value: apply(
                        effect_op("choose"),
                        unknown_lit(core_ir::Lit::Int("2".to_string())),
                    ),
                },
            ],
            apply(
                apply(primitive(core_ir::PrimitiveOp::IntAdd), var("a")),
                var("b"),
            ),
        );
        let arm_body = apply(var("k"), var("x"));
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert!(
            lowered.roots[0]
                .continuations
                .iter()
                .filter(|continuation| matches!(
                    continuation.terminator,
                    CpsTerminator::Perform { .. }
                ))
                .count()
                >= 2
        );
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("3".to_string())]
        );
    }

    #[test]
    fn lowers_block_expr_statement_rest_into_resumption_continuation() {
        let body = block(
            vec![runtime::Stmt::Expr(apply(
                effect_op("choose"),
                unknown_lit(core_ir::Lit::Int("1".to_string())),
            ))],
            apply(
                apply(
                    primitive(core_ir::PrimitiveOp::IntAdd),
                    unknown_lit(core_ir::Lit::Int("10".to_string())),
                ),
                unknown_lit(core_ir::Lit::Int("20".to_string())),
            ),
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(core_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(core_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("60".to_string())]
        );
    }

    #[test]
    fn unwraps_thunked_handle_body_before_cps_effect_lowering() {
        let body = bind_here(thunk(block(
            vec![runtime::Stmt::Let {
                pattern: bind_pattern("y"),
                value: apply(
                    effect_op("choose"),
                    unknown_lit(core_ir::Lit::Int("1".to_string())),
                ),
            }],
            apply(
                apply(primitive(core_ir::PrimitiveOp::IntAdd), var("y")),
                unknown_lit(core_ir::Lit::Int("10".to_string())),
            ),
        )));
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(core_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(core_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("23".to_string())]
        );
    }

    #[test]
    fn infers_capture_for_block_value_used_after_effect() {
        let body = block(
            vec![
                runtime::Stmt::Let {
                    pattern: bind_pattern("z"),
                    value: unknown_lit(core_ir::Lit::Int("10".to_string())),
                },
                runtime::Stmt::Let {
                    pattern: bind_pattern("y"),
                    value: apply(
                        effect_op("choose"),
                        unknown_lit(core_ir::Lit::Int("1".to_string())),
                    ),
                },
            ],
            apply(
                apply(primitive(core_ir::PrimitiveOp::IntAdd), var("y")),
                var("z"),
            ),
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_two = apply(var("k"), unknown_lit(core_ir::Lit::Int("2".to_string())));
        let arm_body = apply(
            apply(primitive(core_ir::PrimitiveOp::IntAdd), resume_x),
            resume_two,
        );
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert!(
            lowered.roots[0]
                .continuations
                .iter()
                .any(|continuation| !continuation.captures.is_empty())
        );
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("23".to_string())]
        );
    }

    #[test]
    fn does_not_unwrap_bind_here_without_thunked_handle_body() {
        let body = bind_here(apply(
            effect_op("choose"),
            unknown_lit(core_ir::Lit::Int("1".to_string())),
        ));
        let arm_body = apply(var("k"), var("x"));
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));

        assert_eq!(
            lower_cps_module(&module).expect_err("bind-here alone is not a handle body wrapper"),
            CpsLowerError::UnsupportedExpr {
                kind: "handler body continuation",
            }
        );
    }

    #[test]
    fn lowers_if_branches_with_distinct_resume_continuations() {
        let then_branch = apply(
            apply(
                primitive(core_ir::PrimitiveOp::IntAdd),
                apply(
                    effect_op("choose"),
                    unknown_lit(core_ir::Lit::Int("1".to_string())),
                ),
            ),
            unknown_lit(core_ir::Lit::Int("10".to_string())),
        );
        let else_branch = apply(
            apply(
                primitive(core_ir::PrimitiveOp::IntAdd),
                apply(
                    effect_op("choose"),
                    unknown_lit(core_ir::Lit::Int("2".to_string())),
                ),
            ),
            unknown_lit(core_ir::Lit::Int("20".to_string())),
        );
        let body = if_expr(
            unknown_lit(core_ir::Lit::Bool(true)),
            then_branch,
            else_branch,
        );
        let resume_x = apply(var("k"), var("x"));
        let resume_three = apply(var("k"), unknown_lit(core_ir::Lit::Int("3".to_string())));
        let arm_body = apply(
            apply(primitive(core_ir::PrimitiveOp::IntAdd), resume_x),
            resume_three,
        );
        let module = module_with_root(handle_once("choose", "x", "k", body, arm_body));
        let lowered = lower_cps_module(&module).expect("lowered");

        validate_cps_module(&lowered).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("24".to_string())]
        );
    }

    #[test]
    fn rejects_direct_call_arity_mismatch() {
        let inc = binding("inc", lambda("x", var("x")));
        let root = apply(
            apply(var("inc"), unknown_lit(core_ir::Lit::Int("1".to_string()))),
            unknown_lit(core_ir::Lit::Int("2".to_string())),
        );
        let module = module_with_bindings_and_root(vec![inc], root);

        assert_eq!(
            lower_cps_module(&module).expect_err("arity mismatch"),
            CpsLowerError::CallArityMismatch {
                target: "inc".to_string(),
                expected: 1,
                actual: 2,
            }
        );
    }
}
