use std::collections::{HashMap, HashSet};
use std::fmt;

use yulang_core_ir as core_ir;
use yulang_runtime as runtime;

use crate::control_ir::{
    BlockId, NativeBlock, NativeFunction, NativeLiteral, NativeModule, NativeStmt,
    NativeTerminator, ValueId,
};

pub type NativeLowerResult<T> = Result<T, NativeLowerError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeLowerError {
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

impl fmt::Display for NativeLowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeLowerError::UnsupportedRoot { root } => {
                write!(f, "native backend does not support root {root:?} yet")
            }
            NativeLowerError::MissingRootExpr { index } => {
                write!(f, "runtime module has no root expression at index {index}")
            }
            NativeLowerError::UnsupportedExpr { kind } => {
                write!(f, "native backend does not support {kind} expressions yet")
            }
            NativeLowerError::UnsupportedPattern { kind } => {
                write!(f, "native backend does not support {kind} patterns yet")
            }
            NativeLowerError::UnsupportedBinding { path, reason } => {
                write!(
                    f,
                    "native backend does not support binding {} yet: {reason}",
                    path_name(path)
                )
            }
            NativeLowerError::PrimitiveArityMismatch {
                op,
                expected,
                actual,
            } => write!(
                f,
                "native backend expected {expected} arguments for primitive {op:?}, got {actual}"
            ),
            NativeLowerError::CallArityMismatch {
                target,
                expected,
                actual,
            } => write!(
                f,
                "native backend expected {expected} arguments for call to {target}, got {actual}"
            ),
        }
    }
}

impl std::error::Error for NativeLowerError {}

pub fn lower_module(module: &runtime::Module) -> NativeLowerResult<NativeModule> {
    let function_table = module
        .bindings
        .iter()
        .map(|binding| {
            let (params, _) = collect_lambda_params(&binding.body);
            (
                binding.name.clone(),
                FunctionInfo {
                    name: path_name(&binding.name),
                    arity: params.len(),
                },
            )
        })
        .collect::<HashMap<_, _>>();
    let mut functions = Vec::new();
    for binding in &module.bindings {
        let lowered = lower_binding(binding, &function_table)?;
        functions.push(lowered.function);
        functions.extend(lowered.generated);
    }

    let mut roots = Vec::new();
    for root in &module.roots {
        match root {
            runtime::Root::Expr(index) => {
                let expr = module
                    .root_exprs
                    .get(*index)
                    .ok_or(NativeLowerError::MissingRootExpr { index: *index })?;
                let lowered =
                    FunctionLowerer::new(format!("root_{index}"), &function_table, Vec::new())
                        .lower_root(expr)?;
                roots.push(lowered.function);
                functions.extend(lowered.generated);
            }
            runtime::Root::Binding(_) => {
                return Err(NativeLowerError::UnsupportedRoot { root: root.clone() });
            }
        }
    }
    Ok(NativeModule { functions, roots })
}

fn lower_binding(
    binding: &runtime::Binding,
    functions: &HashMap<core_ir::Path, FunctionInfo>,
) -> NativeLowerResult<LoweredFunction> {
    if !binding.type_params.is_empty() {
        return Err(NativeLowerError::UnsupportedBinding {
            path: binding.name.clone(),
            reason: "residual type parameters",
        });
    }
    let (params, body) = collect_lambda_params(&binding.body);
    if params.is_empty() {
        return Err(NativeLowerError::UnsupportedBinding {
            path: binding.name.clone(),
            reason: "non-function body",
        });
    }
    FunctionLowerer::new(path_name(&binding.name), functions, params).lower_root(body)
}

struct LoweredFunction {
    function: NativeFunction,
    generated: Vec<NativeFunction>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct FunctionInfo {
    name: String,
    arity: usize,
}

struct FunctionLowerer<'a> {
    name: String,
    functions: &'a HashMap<core_ir::Path, FunctionInfo>,
    next_value: usize,
    next_block: usize,
    blocks: Vec<NativeBlock>,
    current: BlockBuilder,
    locals: HashMap<core_ir::Path, ValueId>,
    params: Vec<ValueId>,
    captures: Vec<ValueId>,
    generated: Vec<NativeFunction>,
    next_lambda: usize,
}

impl<'a> FunctionLowerer<'a> {
    fn new(
        name: String,
        functions: &'a HashMap<core_ir::Path, FunctionInfo>,
        params: Vec<core_ir::Name>,
    ) -> Self {
        let mut next_value = 0;
        let mut param_values = Vec::with_capacity(params.len());
        let mut locals = HashMap::new();
        for param in params {
            let value = ValueId(next_value);
            next_value += 1;
            locals.insert(core_ir::Path::from_name(param), value);
            param_values.push(value);
        }
        Self {
            name,
            functions,
            next_value,
            next_block: 1,
            blocks: Vec::new(),
            current: BlockBuilder::new(BlockId(0), param_values.clone()),
            locals,
            params: param_values,
            captures: Vec::new(),
            generated: Vec::new(),
            next_lambda: 0,
        }
    }

    fn new_closure(
        name: String,
        functions: &'a HashMap<core_ir::Path, FunctionInfo>,
        captures: Vec<core_ir::Path>,
        param: core_ir::Name,
    ) -> Self {
        let mut next_value = 0;
        let mut params = Vec::with_capacity(captures.len() + 1);
        let mut locals = HashMap::new();
        for capture in captures {
            let value = ValueId(next_value);
            next_value += 1;
            locals.insert(capture, value);
            params.push(value);
        }
        let captures = params.clone();
        let param_value = ValueId(next_value);
        next_value += 1;
        locals.insert(core_ir::Path::from_name(param), param_value);
        params.push(param_value);
        Self {
            name,
            functions,
            next_value,
            next_block: 1,
            blocks: Vec::new(),
            current: BlockBuilder::new(BlockId(0), params.clone()),
            locals,
            params,
            captures,
            generated: Vec::new(),
            next_lambda: 0,
        }
    }

    fn lower_root(mut self, expr: &runtime::Expr) -> NativeLowerResult<LoweredFunction> {
        let value = self.lower_expr(expr)?;
        self.terminate(NativeTerminator::Return(value));
        self.finish_current();
        Ok(LoweredFunction {
            function: NativeFunction {
                name: self.name,
                captures: self.captures,
                params: self.params,
                blocks: self.blocks,
            },
            generated: self.generated,
        })
    }

    fn lower_expr(&mut self, expr: &runtime::Expr) -> NativeLowerResult<ValueId> {
        if let Some((op, args)) = primitive_apply(expr) {
            let expected = primitive_arity(op);
            if args.len() != expected {
                return Err(NativeLowerError::PrimitiveArityMismatch {
                    op,
                    expected,
                    actual: args.len(),
                });
            }
            let args = args
                .into_iter()
                .map(|arg| self.lower_expr(arg))
                .collect::<NativeLowerResult<Vec<_>>>()?;
            let dest = self.fresh_value();
            self.current
                .stmts
                .push(NativeStmt::Primitive { dest, op, args });
            return Ok(dest);
        }

        if let Some((target, args)) = direct_apply(expr, self.functions)? {
            let args = args
                .into_iter()
                .map(|arg| self.lower_expr(arg))
                .collect::<NativeLowerResult<Vec<_>>>()?;
            let dest = self.fresh_value();
            self.current
                .stmts
                .push(NativeStmt::DirectCall { dest, target, args });
            return Ok(dest);
        }

        if let runtime::ExprKind::Apply { callee, arg, .. } = &expr.kind {
            let callee = self.lower_expr(callee)?;
            let arg = self.lower_expr(arg)?;
            let dest = self.fresh_value();
            self.current.stmts.push(NativeStmt::ClosureCall {
                dest,
                callee,
                args: vec![arg],
            });
            return Ok(dest);
        }

        match &expr.kind {
            runtime::ExprKind::Lit(lit) => {
                let dest = self.fresh_value();
                self.current.stmts.push(NativeStmt::Literal {
                    dest,
                    literal: lower_literal(lit),
                });
                Ok(dest)
            }
            runtime::ExprKind::PrimitiveOp(_) => Err(NativeLowerError::UnsupportedExpr {
                kind: "bare primitive",
            }),
            runtime::ExprKind::Var(path) => self
                .locals
                .get(path)
                .copied()
                .ok_or(NativeLowerError::UnsupportedExpr { kind: "free var" }),
            runtime::ExprKind::EffectOp(_) => Err(NativeLowerError::UnsupportedExpr {
                kind: "effect operation",
            }),
            runtime::ExprKind::Lambda { param, body, .. } => self.lower_lambda(param, body),
            runtime::ExprKind::Apply { .. } => {
                Err(NativeLowerError::UnsupportedExpr { kind: "apply" })
            }
            runtime::ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => self.lower_if(cond, then_branch, else_branch),
            runtime::ExprKind::Tuple(_) => Err(NativeLowerError::UnsupportedExpr { kind: "tuple" }),
            runtime::ExprKind::Record { .. } => {
                Err(NativeLowerError::UnsupportedExpr { kind: "record" })
            }
            runtime::ExprKind::Variant { .. } => {
                Err(NativeLowerError::UnsupportedExpr { kind: "variant" })
            }
            runtime::ExprKind::Select { .. } => {
                Err(NativeLowerError::UnsupportedExpr { kind: "select" })
            }
            runtime::ExprKind::Match { .. } => {
                Err(NativeLowerError::UnsupportedExpr { kind: "match" })
            }
            runtime::ExprKind::Block { stmts, tail } => self.lower_block(stmts, tail.as_deref()),
            runtime::ExprKind::Handle { .. } => {
                Err(NativeLowerError::UnsupportedExpr { kind: "handler" })
            }
            runtime::ExprKind::BindHere { .. } => {
                Err(NativeLowerError::UnsupportedExpr { kind: "bind_here" })
            }
            runtime::ExprKind::Thunk { .. } => {
                Err(NativeLowerError::UnsupportedExpr { kind: "thunk" })
            }
            runtime::ExprKind::LocalPushId { .. } => Err(NativeLowerError::UnsupportedExpr {
                kind: "local effect id scope",
            }),
            runtime::ExprKind::PeekId => Err(NativeLowerError::UnsupportedExpr { kind: "peek_id" }),
            runtime::ExprKind::FindId { .. } => {
                Err(NativeLowerError::UnsupportedExpr { kind: "find_id" })
            }
            runtime::ExprKind::AddId { .. } => {
                Err(NativeLowerError::UnsupportedExpr { kind: "add_id" })
            }
            runtime::ExprKind::Coerce { expr, .. } => self.lower_expr(expr),
            runtime::ExprKind::Pack { .. } => {
                Err(NativeLowerError::UnsupportedExpr { kind: "pack" })
            }
        }
    }

    fn fresh_value(&mut self) -> ValueId {
        let value = ValueId(self.next_value);
        self.next_value += 1;
        value
    }

    fn fresh_block(&mut self) -> BlockId {
        let block = BlockId(self.next_block);
        self.next_block += 1;
        block
    }

    fn lower_if(
        &mut self,
        cond: &runtime::Expr,
        then_branch: &runtime::Expr,
        else_branch: &runtime::Expr,
    ) -> NativeLowerResult<ValueId> {
        let cond = self.lower_expr(cond)?;
        let saved_locals = self.locals.clone();
        let then_block = self.fresh_block();
        let else_block = self.fresh_block();
        let merge_block = self.fresh_block();
        let result = self.fresh_value();

        self.terminate(NativeTerminator::Branch {
            cond,
            then_block,
            else_block,
        });
        self.finish_current();

        self.current = BlockBuilder::new(then_block, Vec::new());
        self.locals = saved_locals.clone();
        let then_value = self.lower_expr(then_branch)?;
        self.terminate(NativeTerminator::Jump {
            target: merge_block,
            args: vec![then_value],
        });
        self.finish_current();

        self.current = BlockBuilder::new(else_block, Vec::new());
        self.locals = saved_locals.clone();
        let else_value = self.lower_expr(else_branch)?;
        self.terminate(NativeTerminator::Jump {
            target: merge_block,
            args: vec![else_value],
        });
        self.finish_current();

        self.current = BlockBuilder::new(merge_block, vec![result]);
        self.locals = saved_locals;
        Ok(result)
    }

    fn lower_block(
        &mut self,
        stmts: &[runtime::Stmt],
        tail: Option<&runtime::Expr>,
    ) -> NativeLowerResult<ValueId> {
        let saved_locals = self.locals.clone();
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
                    return Err(NativeLowerError::UnsupportedExpr {
                        kind: "module statement",
                    });
                }
            }
        }
        let value = match tail {
            Some(tail) => self.lower_expr(tail)?,
            None => {
                let value = self.fresh_value();
                self.current.stmts.push(NativeStmt::Literal {
                    dest: value,
                    literal: NativeLiteral::Unit,
                });
                value
            }
        };
        self.locals = saved_locals;
        Ok(value)
    }

    fn lower_lambda(
        &mut self,
        param: &core_ir::Name,
        body: &runtime::Expr,
    ) -> NativeLowerResult<ValueId> {
        let mut bound = HashSet::new();
        bound.insert(core_ir::Path::from_name(param.clone()));
        let mut capture_paths = free_vars(body, &mut bound)
            .into_iter()
            .filter(|path| self.locals.contains_key(path))
            .collect::<Vec<_>>();
        capture_paths.sort_by_key(path_name);
        let captures = capture_paths
            .iter()
            .map(|path| {
                self.locals
                    .get(path)
                    .copied()
                    .ok_or(NativeLowerError::UnsupportedExpr {
                        kind: "lambda capture",
                    })
            })
            .collect::<NativeLowerResult<Vec<_>>>()?;

        let target = format!("{}#lambda{}", self.name, self.next_lambda);
        self.next_lambda += 1;
        let lowered = FunctionLowerer::new_closure(
            target.clone(),
            self.functions,
            capture_paths,
            param.clone(),
        )
        .lower_root(body)?;
        self.generated.push(lowered.function);
        self.generated.extend(lowered.generated);

        let dest = self.fresh_value();
        self.current.stmts.push(NativeStmt::MakeClosure {
            dest,
            target,
            captures,
        });
        Ok(dest)
    }

    fn bind_pattern(
        &mut self,
        pattern: &runtime::Pattern,
        value: ValueId,
    ) -> NativeLowerResult<()> {
        match pattern {
            runtime::Pattern::Wildcard { .. } => Ok(()),
            runtime::Pattern::Bind { name, .. } => {
                self.locals
                    .insert(core_ir::Path::from_name(name.clone()), value);
                Ok(())
            }
            runtime::Pattern::Lit { .. } => {
                Err(NativeLowerError::UnsupportedPattern { kind: "literal" })
            }
            runtime::Pattern::Tuple { .. } => {
                Err(NativeLowerError::UnsupportedPattern { kind: "tuple" })
            }
            runtime::Pattern::List { .. } => {
                Err(NativeLowerError::UnsupportedPattern { kind: "list" })
            }
            runtime::Pattern::Record { .. } => {
                Err(NativeLowerError::UnsupportedPattern { kind: "record" })
            }
            runtime::Pattern::Variant { .. } => {
                Err(NativeLowerError::UnsupportedPattern { kind: "variant" })
            }
            runtime::Pattern::Or { .. } => Err(NativeLowerError::UnsupportedPattern { kind: "or" }),
            runtime::Pattern::As { .. } => Err(NativeLowerError::UnsupportedPattern { kind: "as" }),
        }
    }

    fn terminate(&mut self, terminator: NativeTerminator) {
        self.current.terminator = Some(terminator);
    }

    fn finish_current(&mut self) {
        let terminator = self
            .current
            .terminator
            .take()
            .expect("native lowerer finished an unterminated block");
        self.blocks.push(NativeBlock {
            id: self.current.id,
            params: std::mem::take(&mut self.current.params),
            stmts: std::mem::take(&mut self.current.stmts),
            terminator,
        });
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

fn free_vars(expr: &runtime::Expr, bound: &mut HashSet<core_ir::Path>) -> HashSet<core_ir::Path> {
    match &expr.kind {
        runtime::ExprKind::Var(path) => {
            if bound.contains(path) {
                HashSet::new()
            } else {
                {
                    let mut set = HashSet::new();
                    set.insert(path.clone());
                    set
                }
            }
        }
        runtime::ExprKind::Lambda { param, body, .. } => {
            let path = core_ir::Path::from_name(param.clone());
            let inserted = bound.insert(path.clone());
            let vars = free_vars(body, bound);
            if inserted {
                bound.remove(&path);
            }
            vars
        }
        runtime::ExprKind::Apply { callee, arg, .. } => {
            let mut vars = free_vars(callee, bound);
            vars.extend(free_vars(arg, bound));
            vars
        }
        runtime::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            let mut vars = free_vars(cond, bound);
            vars.extend(free_vars(then_branch, bound));
            vars.extend(free_vars(else_branch, bound));
            vars
        }
        runtime::ExprKind::Block { stmts, tail } => {
            let mut vars = HashSet::new();
            let mut inserted = Vec::new();
            for stmt in stmts {
                match stmt {
                    runtime::Stmt::Let { pattern, value } => {
                        vars.extend(free_vars(value, bound));
                        for name in pattern_bind_names(pattern) {
                            let path = core_ir::Path::from_name(name);
                            if bound.insert(path.clone()) {
                                inserted.push(path);
                            }
                        }
                    }
                    runtime::Stmt::Expr(expr) => vars.extend(free_vars(expr, bound)),
                    runtime::Stmt::Module { body, .. } => vars.extend(free_vars(body, bound)),
                }
            }
            if let Some(tail) = tail {
                vars.extend(free_vars(tail, bound));
            }
            for path in inserted {
                bound.remove(&path);
            }
            vars
        }
        runtime::ExprKind::Tuple(items) => {
            let mut vars = HashSet::new();
            for item in items {
                vars.extend(free_vars(item, bound));
            }
            vars
        }
        runtime::ExprKind::Record { fields, spread } => {
            let mut vars = HashSet::new();
            for field in fields {
                vars.extend(free_vars(&field.value, bound));
            }
            if let Some(spread) = spread {
                match spread {
                    runtime::RecordSpreadExpr::Head(expr)
                    | runtime::RecordSpreadExpr::Tail(expr) => vars.extend(free_vars(expr, bound)),
                }
            }
            vars
        }
        runtime::ExprKind::Variant { value, .. } => value
            .as_deref()
            .map(|value| free_vars(value, bound))
            .unwrap_or_default(),
        runtime::ExprKind::Select { base, .. } => free_vars(base, bound),
        runtime::ExprKind::Match {
            scrutinee, arms, ..
        } => {
            let mut vars = free_vars(scrutinee, bound);
            for arm in arms {
                let mut arm_bound = bound.clone();
                for name in pattern_bind_names(&arm.pattern) {
                    arm_bound.insert(core_ir::Path::from_name(name));
                }
                if let Some(guard) = &arm.guard {
                    vars.extend(free_vars(guard, &mut arm_bound));
                }
                vars.extend(free_vars(&arm.body, &mut arm_bound));
            }
            vars
        }
        runtime::ExprKind::Handle { body, arms, .. } => {
            let mut vars = free_vars(body, bound);
            for arm in arms {
                let mut arm_bound = bound.clone();
                for name in pattern_bind_names(&arm.payload) {
                    arm_bound.insert(core_ir::Path::from_name(name));
                }
                if let Some(resume) = &arm.resume {
                    arm_bound.insert(core_ir::Path::from_name(resume.name.clone()));
                }
                if let Some(guard) = &arm.guard {
                    vars.extend(free_vars(guard, &mut arm_bound));
                }
                vars.extend(free_vars(&arm.body, &mut arm_bound));
            }
            vars
        }
        runtime::ExprKind::BindHere { expr }
        | runtime::ExprKind::Thunk { expr, .. }
        | runtime::ExprKind::Coerce { expr, .. }
        | runtime::ExprKind::Pack { expr, .. } => free_vars(expr, bound),
        runtime::ExprKind::LocalPushId { body, .. } => free_vars(body, bound),
        runtime::ExprKind::AddId { thunk, .. } => free_vars(thunk, bound),
        runtime::ExprKind::PrimitiveOp(_)
        | runtime::ExprKind::EffectOp(_)
        | runtime::ExprKind::Lit(_)
        | runtime::ExprKind::PeekId
        | runtime::ExprKind::FindId { .. } => HashSet::new(),
    }
}

fn pattern_bind_names(pattern: &runtime::Pattern) -> Vec<core_ir::Name> {
    match pattern {
        runtime::Pattern::Bind { name, .. } => vec![name.clone()],
        runtime::Pattern::Tuple { items, .. } => {
            items.iter().flat_map(pattern_bind_names).collect()
        }
        runtime::Pattern::List {
            prefix,
            spread,
            suffix,
            ..
        } => {
            let mut names = prefix
                .iter()
                .flat_map(pattern_bind_names)
                .collect::<Vec<_>>();
            if let Some(spread) = spread {
                names.extend(pattern_bind_names(spread));
            }
            names.extend(suffix.iter().flat_map(pattern_bind_names));
            names
        }
        runtime::Pattern::Record { fields, spread, .. } => {
            let mut names = fields
                .iter()
                .flat_map(|field| pattern_bind_names(&field.pattern))
                .collect::<Vec<_>>();
            if let Some(spread) = spread {
                match spread {
                    runtime::RecordSpreadPattern::Head(pattern)
                    | runtime::RecordSpreadPattern::Tail(pattern) => {
                        names.extend(pattern_bind_names(pattern));
                    }
                }
            }
            names
        }
        runtime::Pattern::Variant { value, .. } => {
            value.as_deref().map(pattern_bind_names).unwrap_or_default()
        }
        runtime::Pattern::Or { left, right, .. } => {
            let mut names = pattern_bind_names(left);
            names.extend(pattern_bind_names(right));
            names
        }
        runtime::Pattern::As { pattern, name, .. } => {
            let mut names = pattern_bind_names(pattern);
            names.push(name.clone());
            names
        }
        runtime::Pattern::Wildcard { .. } | runtime::Pattern::Lit { .. } => Vec::new(),
    }
}

struct BlockBuilder {
    id: BlockId,
    params: Vec<ValueId>,
    stmts: Vec<NativeStmt>,
    terminator: Option<NativeTerminator>,
}

impl BlockBuilder {
    fn new(id: BlockId, params: Vec<ValueId>) -> Self {
        Self {
            id,
            params,
            stmts: Vec::new(),
            terminator: None,
        }
    }
}

fn lower_literal(lit: &core_ir::Lit) -> NativeLiteral {
    match lit {
        core_ir::Lit::Int(value) => NativeLiteral::Int(value.clone()),
        core_ir::Lit::Float(value) => NativeLiteral::Float(value.clone()),
        core_ir::Lit::String(value) => NativeLiteral::String(value.clone()),
        core_ir::Lit::Bool(value) => NativeLiteral::Bool(*value),
        core_ir::Lit::Unit => NativeLiteral::Unit,
    }
}

fn primitive_apply(expr: &runtime::Expr) -> Option<(core_ir::PrimitiveOp, Vec<&runtime::Expr>)> {
    let mut args = Vec::new();
    let mut current = expr;
    while let runtime::ExprKind::Apply { callee, arg, .. } = &current.kind {
        args.push(arg.as_ref());
        current = callee;
    }
    let runtime::ExprKind::PrimitiveOp(op) = &current.kind else {
        return None;
    };
    args.reverse();
    Some((*op, args))
}

fn direct_apply<'expr>(
    expr: &'expr runtime::Expr,
    functions: &HashMap<core_ir::Path, FunctionInfo>,
) -> NativeLowerResult<Option<(String, Vec<&'expr runtime::Expr>)>> {
    let mut args = Vec::new();
    let mut current = expr;
    while let runtime::ExprKind::Apply { callee, arg, .. } = &current.kind {
        args.push(arg.as_ref());
        current = callee;
    }
    let runtime::ExprKind::Var(path) = &current.kind else {
        return Ok(None);
    };
    let Some(target) = functions.get(path) else {
        return Ok(None);
    };
    if args.len() != target.arity {
        return Err(NativeLowerError::CallArityMismatch {
            target: target.name.clone(),
            expected: target.arity,
            actual: args.len(),
        });
    }
    args.reverse();
    Ok(Some((target.name.clone(), args)))
}

fn path_name(path: &core_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
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

#[cfg(test)]
mod tests {
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

    fn bind_pattern(name: &str) -> runtime::Pattern {
        runtime::Pattern::Bind {
            name: core_ir::Name(name.to_string()),
            ty: runtime::Type::unknown(),
        }
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

    fn module_with_binding_and_root(
        binding: runtime::Binding,
        expr: runtime::Expr,
    ) -> runtime::Module {
        module_with_bindings_and_root(vec![binding], expr)
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

    fn module_with_root(expr: runtime::Expr) -> runtime::Module {
        runtime::Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![expr],
            roots: vec![runtime::Root::Expr(0)],
            role_impls: Vec::new(),
        }
    }

    #[test]
    fn lowers_literal_root() {
        let module = module_with_root(unknown_lit(core_ir::Lit::Int("42".to_string())));
        let lowered = lower_module(&module).expect("lowered");

        assert_eq!(lowered.roots.len(), 1);
        assert_eq!(
            lowered.roots[0].blocks[0].stmts,
            vec![NativeStmt::Literal {
                dest: ValueId(0),
                literal: NativeLiteral::Int("42".to_string()),
            }]
        );
        assert_eq!(
            lowered.roots[0].blocks[0].terminator,
            NativeTerminator::Return(ValueId(0))
        );
    }

    #[test]
    fn lowers_primitive_apply_root() {
        let expr = apply(
            apply(
                primitive(core_ir::PrimitiveOp::IntAdd),
                unknown_lit(core_ir::Lit::Int("1".to_string())),
            ),
            unknown_lit(core_ir::Lit::Int("2".to_string())),
        );
        let module = module_with_root(expr);
        let lowered = lower_module(&module).expect("lowered");

        assert_eq!(
            lowered.roots[0].blocks[0].stmts,
            vec![
                NativeStmt::Literal {
                    dest: ValueId(0),
                    literal: NativeLiteral::Int("1".to_string()),
                },
                NativeStmt::Literal {
                    dest: ValueId(1),
                    literal: NativeLiteral::Int("2".to_string()),
                },
                NativeStmt::Primitive {
                    dest: ValueId(2),
                    op: core_ir::PrimitiveOp::IntAdd,
                    args: vec![ValueId(0), ValueId(1)],
                },
            ]
        );
    }

    #[test]
    fn rejects_effect_operation_root() {
        let expr = runtime::Expr::typed(
            runtime::ExprKind::EffectOp(core_ir::Path::from_name(core_ir::Name(
                "read".to_string(),
            ))),
            runtime::Type::unknown(),
        );
        let module = module_with_root(expr);

        assert_eq!(
            lower_module(&module).expect_err("unsupported"),
            NativeLowerError::UnsupportedExpr {
                kind: "effect operation",
            }
        );
    }

    #[test]
    fn lowers_if_with_branch_and_merge_blocks() {
        let module = module_with_root(if_expr(
            unknown_lit(core_ir::Lit::Bool(true)),
            unknown_lit(core_ir::Lit::Int("1".to_string())),
            unknown_lit(core_ir::Lit::Int("2".to_string())),
        ));
        let lowered = lower_module(&module).expect("lowered");
        let blocks = &lowered.roots[0].blocks;

        assert_eq!(blocks.len(), 4);
        assert_eq!(
            blocks[0].terminator,
            NativeTerminator::Branch {
                cond: ValueId(0),
                then_block: BlockId(1),
                else_block: BlockId(2),
            }
        );
        assert_eq!(
            blocks[1].terminator,
            NativeTerminator::Jump {
                target: BlockId(3),
                args: vec![ValueId(2)],
            }
        );
        assert_eq!(
            blocks[2].terminator,
            NativeTerminator::Jump {
                target: BlockId(3),
                args: vec![ValueId(3)],
            }
        );
        assert_eq!(blocks[3].params, vec![ValueId(1)]);
        assert_eq!(blocks[3].terminator, NativeTerminator::Return(ValueId(1)));
    }

    #[test]
    fn lowers_simple_block_binding() {
        let module = module_with_root(block(
            vec![runtime::Stmt::Let {
                pattern: bind_pattern("x"),
                value: unknown_lit(core_ir::Lit::Int("42".to_string())),
            }],
            var("x"),
        ));
        let lowered = lower_module(&module).expect("lowered");

        assert_eq!(
            lowered.roots[0].blocks[0].stmts,
            vec![NativeStmt::Literal {
                dest: ValueId(0),
                literal: NativeLiteral::Int("42".to_string()),
            }]
        );
        assert_eq!(
            lowered.roots[0].blocks[0].terminator,
            NativeTerminator::Return(ValueId(0))
        );
    }

    #[test]
    fn lowers_direct_monomorphic_call() {
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
        let module = module_with_binding_and_root(inc, root);
        let lowered = lower_module(&module).expect("lowered");

        assert_eq!(lowered.functions.len(), 1);
        assert_eq!(lowered.functions[0].name, "inc");
        assert_eq!(lowered.functions[0].params, vec![ValueId(0)]);
        assert_eq!(
            lowered.roots[0].blocks[0].stmts,
            vec![
                NativeStmt::Literal {
                    dest: ValueId(0),
                    literal: NativeLiteral::Int("41".to_string()),
                },
                NativeStmt::DirectCall {
                    dest: ValueId(1),
                    target: "inc".to_string(),
                    args: vec![ValueId(0)],
                },
            ]
        );
        assert_eq!(
            lowered.roots[0].blocks[0].terminator,
            NativeTerminator::Return(ValueId(1))
        );
    }

    #[test]
    fn rejects_direct_call_arity_mismatch() {
        let inc = binding("inc", lambda("x", var("x")));
        let root = apply(
            apply(var("inc"), unknown_lit(core_ir::Lit::Int("1".to_string()))),
            unknown_lit(core_ir::Lit::Int("2".to_string())),
        );
        let module = module_with_binding_and_root(inc, root);

        assert_eq!(
            lower_module(&module).expect_err("arity mismatch"),
            NativeLowerError::CallArityMismatch {
                target: "inc".to_string(),
                expected: 1,
                actual: 2,
            }
        );
    }

    #[test]
    fn lowers_multiple_bindings() {
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
        let twice = binding(
            "twice",
            lambda("x", apply(var("inc"), apply(var("inc"), var("x")))),
        );
        let root = apply(
            var("twice"),
            unknown_lit(core_ir::Lit::Int("40".to_string())),
        );
        let module = module_with_bindings_and_root(vec![inc, twice], root);
        let lowered = lower_module(&module).expect("lowered");

        assert_eq!(lowered.functions.len(), 2);
        assert_eq!(lowered.functions[0].name, "inc");
        assert_eq!(lowered.functions[1].name, "twice");
    }
}
