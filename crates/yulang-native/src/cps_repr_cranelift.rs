use std::collections::HashMap;
use std::fmt;

use cranelift_codegen::ir::{self, AbiParam, InstBuilder, types};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use yulang_core_ir as core_ir;
use yulang_runtime as runtime;

use crate::cps_ir::{CpsContinuationId, CpsLiteral, CpsStmt, CpsTerminator, CpsValueId};
use crate::cps_lower::{CpsLowerError, lower_cps_module};
use crate::cps_repr::CpsReprAbiLane;
use crate::cps_repr_abi::{
    CpsReprAbiContinuation, CpsReprAbiFunction, CpsReprAbiModule, CpsReprAbiValue,
    lower_cps_repr_abi_module,
};
use crate::cps_validate::{CpsValidateError, validate_cps_module};

pub type CpsReprCraneliftResult<T> = Result<T, CpsReprCraneliftError>;

#[derive(Debug, Clone, PartialEq)]
pub enum CpsReprCraneliftError {
    Lower(CpsLowerError),
    Validate(CpsValidateError),
    UnsupportedFunction {
        function: String,
        reason: &'static str,
    },
    UnsupportedLane {
        function: String,
        value: CpsValueId,
        lane: CpsReprAbiLane,
    },
    UnsupportedReturnLane {
        function: String,
        continuation: CpsContinuationId,
        lane: CpsReprAbiLane,
    },
    UnsupportedLiteral {
        function: String,
        literal: CpsLiteral,
    },
    UnsupportedPrimitive {
        function: String,
        op: core_ir::PrimitiveOp,
    },
    UnsupportedStmt {
        function: String,
        kind: &'static str,
    },
    UnsupportedTerminator {
        function: String,
        kind: &'static str,
    },
    MissingFunction {
        name: String,
    },
    MissingContinuation {
        function: String,
        continuation: CpsContinuationId,
    },
    MissingValue {
        function: String,
        value: CpsValueId,
    },
    InvalidReturnArity {
        function: String,
        arity: usize,
    },
    Cranelift(String),
}

impl fmt::Display for CpsReprCraneliftError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CpsReprCraneliftError::Lower(error) => write!(f, "{error}"),
            CpsReprCraneliftError::Validate(error) => write!(f, "{error}"),
            CpsReprCraneliftError::UnsupportedFunction { function, reason } => write!(
                f,
                "CPS repr Cranelift prototype does not support `{function}` yet: {reason}"
            ),
            CpsReprCraneliftError::UnsupportedLane {
                function,
                value,
                lane,
            } => write!(
                f,
                "CPS repr Cranelift prototype cannot lower value {value:?} with lane {lane:?} in `{function}`"
            ),
            CpsReprCraneliftError::UnsupportedReturnLane {
                function,
                continuation,
                lane,
            } => write!(
                f,
                "CPS repr Cranelift prototype cannot lower continuation {function}::{continuation:?} with return lane {lane:?}"
            ),
            CpsReprCraneliftError::UnsupportedLiteral { function, literal } => write!(
                f,
                "CPS repr Cranelift prototype does not support literal {literal:?} in `{function}` yet"
            ),
            CpsReprCraneliftError::UnsupportedPrimitive { function, op } => write!(
                f,
                "CPS repr Cranelift prototype does not support primitive {op:?} in `{function}` yet"
            ),
            CpsReprCraneliftError::UnsupportedStmt { function, kind } => write!(
                f,
                "CPS repr Cranelift prototype does not support {kind} statements in `{function}` yet"
            ),
            CpsReprCraneliftError::UnsupportedTerminator { function, kind } => write!(
                f,
                "CPS repr Cranelift prototype does not support {kind} terminators in `{function}` yet"
            ),
            CpsReprCraneliftError::MissingFunction { name } => {
                write!(f, "CPS repr Cranelift function `{name}` is missing")
            }
            CpsReprCraneliftError::MissingContinuation {
                function,
                continuation,
            } => write!(
                f,
                "CPS repr Cranelift continuation {continuation:?} is missing in `{function}`"
            ),
            CpsReprCraneliftError::MissingValue { function, value } => write!(
                f,
                "CPS repr Cranelift value {value:?} is missing in `{function}`"
            ),
            CpsReprCraneliftError::InvalidReturnArity { function, arity } => write!(
                f,
                "CPS repr Cranelift function `{function}` has {arity} return values"
            ),
            CpsReprCraneliftError::Cranelift(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for CpsReprCraneliftError {}

impl From<CpsLowerError> for CpsReprCraneliftError {
    fn from(error: CpsLowerError) -> Self {
        Self::Lower(error)
    }
}

impl From<CpsValidateError> for CpsReprCraneliftError {
    fn from(error: CpsValidateError) -> Self {
        Self::Validate(error)
    }
}

pub struct CpsReprJitModule {
    module: JITModule,
    roots: Vec<FuncId>,
}

impl CpsReprJitModule {
    pub fn run_roots_i64(&mut self) -> CpsReprCraneliftResult<Vec<i64>> {
        self.module
            .finalize_definitions()
            .map_err(cranelift_error)?;
        self.roots
            .iter()
            .map(|root| {
                let ptr = self.module.get_finalized_function(*root);
                let call = unsafe { std::mem::transmute::<_, extern "C" fn() -> i64>(ptr) };
                Ok(call())
            })
            .collect()
    }
}

pub fn compile_cps_repr_abi_module(
    module: &CpsReprAbiModule,
) -> CpsReprCraneliftResult<CpsReprJitModule> {
    validate_scalar_subset(module)?;

    let mut builder =
        JITBuilder::new(cranelift_module::default_libcall_names()).map_err(cranelift_error)?;
    builder.symbol(
        "yulang_cps_make_resumption_i64_0",
        yulang_cps_make_resumption_i64_0 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_resumption_i64_1",
        yulang_cps_make_resumption_i64_1 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_resumption_i64_2",
        yulang_cps_make_resumption_i64_2 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_resumption_i64_3",
        yulang_cps_make_resumption_i64_3 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_resumption_i64_4",
        yulang_cps_make_resumption_i64_4 as *const u8,
    );
    builder.symbol("yulang_cps_resume_i64", yulang_cps_resume_i64 as *const u8);
    let mut jit = JITModule::new(builder);
    let functions = declare_functions(&mut jit, module)?;
    define_functions(&mut jit, module, &functions)?;
    let roots = module
        .roots
        .iter()
        .map(|root| {
            functions.functions.get(&root.name).copied().ok_or_else(|| {
                CpsReprCraneliftError::MissingFunction {
                    name: root.name.clone(),
                }
            })
        })
        .collect::<CpsReprCraneliftResult<Vec<_>>>()?;
    Ok(CpsReprJitModule { module: jit, roots })
}

pub fn compile_runtime_module_to_cps_repr_jit(
    module: &runtime::Module,
) -> CpsReprCraneliftResult<CpsReprJitModule> {
    let cps = lower_cps_module(module)?;
    validate_cps_module(&cps)?;
    let repr = crate::cps_repr::lower_cps_repr_module(&cps);
    let abi = lower_cps_repr_abi_module(&repr);
    compile_cps_repr_abi_module(&abi)
}

fn declare_functions(
    jit: &mut JITModule,
    module: &CpsReprAbiModule,
) -> CpsReprCraneliftResult<DeclaredFunctions> {
    let mut functions = HashMap::new();
    let mut continuations = HashMap::new();
    for function in module.functions.iter().chain(&module.roots) {
        let sig = function_signature(jit, function);
        let id = jit
            .declare_function(&function.name, Linkage::Export, &sig)
            .map_err(cranelift_error)?;
        functions.insert(function.name.clone(), id);
        if function_has_effect_flow(function) {
            for continuation in &function.continuations {
                let name = continuation_symbol(function, continuation.id);
                let sig = continuation_signature(jit, continuation);
                let id = jit
                    .declare_function(&name, Linkage::Local, &sig)
                    .map_err(cranelift_error)?;
                continuations.insert((function.name.clone(), continuation.id), id);
            }
        }
    }
    Ok(DeclaredFunctions {
        functions,
        continuations,
    })
}

fn define_functions(
    jit: &mut JITModule,
    module: &CpsReprAbiModule,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    for function in module.functions.iter().chain(&module.roots) {
        let id = functions
            .functions
            .get(&function.name)
            .copied()
            .ok_or_else(|| CpsReprCraneliftError::MissingFunction {
                name: function.name.clone(),
            })?;
        if function_has_effect_flow(function) {
            define_effectful_function(jit, function, functions)?;
        }
        let mut ctx = jit.make_context();
        ctx.func.signature = function_signature(jit, function);
        if function_has_effect_flow(function) {
            lower_effectful_function_wrapper(jit, &mut ctx, function, functions)?;
        } else {
            lower_function(jit, &mut ctx, function, functions)?;
        }
        jit.define_function(id, &mut ctx).map_err(cranelift_error)?;
        jit.clear_context(&mut ctx);
    }
    Ok(())
}

#[derive(Debug, Default)]
struct DeclaredFunctions {
    functions: HashMap<String, FuncId>,
    continuations: HashMap<(String, CpsContinuationId), FuncId>,
}

fn define_effectful_function(
    jit: &mut JITModule,
    function: &CpsReprAbiFunction,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    for continuation in &function.continuations {
        let id = functions
            .continuations
            .get(&(function.name.clone(), continuation.id))
            .copied()
            .ok_or_else(|| CpsReprCraneliftError::MissingContinuation {
                function: function.name.clone(),
                continuation: continuation.id,
            })?;
        let mut ctx = jit.make_context();
        ctx.func.signature = continuation_signature(jit, continuation);
        lower_continuation_function(jit, &mut ctx, function, continuation, functions)?;
        jit.define_function(id, &mut ctx).map_err(cranelift_error)?;
        jit.clear_context(&mut ctx);
    }
    Ok(())
}

fn lower_effectful_function_wrapper(
    jit: &mut JITModule,
    ctx: &mut cranelift_codegen::Context,
    function: &CpsReprAbiFunction,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    let mut builder_context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_context);
    let block = builder.create_block();
    builder.append_block_params_for_function_params(block);
    builder.switch_to_block(block);

    let entry = continuation_func_ref(jit, &mut builder, function, function.entry, functions)?;
    let null_env = builder.ins().iconst(types::I64, 0);
    let mut args = vec![null_env];
    args.extend(builder.block_params(block).iter().copied());
    let call = builder.ins().call(entry, &args);
    let results = builder.inst_results(call);
    if results.len() != 1 {
        return Err(CpsReprCraneliftError::InvalidReturnArity {
            function: function.name.clone(),
            arity: results.len(),
        });
    }
    let result = results[0];
    builder.ins().return_(&[result]);
    builder.seal_all_blocks();
    builder.finalize();
    Ok(())
}

fn function_has_effect_flow(function: &CpsReprAbiFunction) -> bool {
    !function.handlers.is_empty()
        || function.continuations.iter().any(|continuation| {
            matches!(continuation.terminator, CpsTerminator::Perform { .. })
                || continuation
                    .stmts
                    .iter()
                    .any(|stmt| matches!(stmt, CpsStmt::Resume { .. }))
        })
}

fn continuation_signature(jit: &JITModule, continuation: &CpsReprAbiContinuation) -> ir::Signature {
    let mut sig = jit.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.extend(
        continuation
            .params
            .iter()
            .map(|_| AbiParam::new(types::I64)),
    );
    sig.returns.push(AbiParam::new(types::I64));
    sig
}

fn continuation_symbol(function: &CpsReprAbiFunction, id: CpsContinuationId) -> String {
    format!("{}$k{}", function.name, id.0)
}

fn continuation_func_ref(
    jit: &mut JITModule,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    id: CpsContinuationId,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<ir::FuncRef> {
    let id = functions
        .continuations
        .get(&(function.name.clone(), id))
        .copied()
        .ok_or_else(|| CpsReprCraneliftError::MissingContinuation {
            function: function.name.clone(),
            continuation: id,
        })?;
    Ok(jit.declare_func_in_func(id, builder.func))
}

fn lower_continuation_function(
    jit: &mut JITModule,
    ctx: &mut cranelift_codegen::Context,
    function: &CpsReprAbiFunction,
    continuation: &CpsReprAbiContinuation,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    let mut builder_context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_context);
    let block = builder.create_block();
    builder.append_block_params_for_function_params(block);
    builder.switch_to_block(block);
    declare_variables(&mut builder, function);

    let params = builder.block_params(block).to_vec();
    let Some(env_ptr) = params.first().copied() else {
        return Err(CpsReprCraneliftError::UnsupportedFunction {
            function: function.name.clone(),
            reason: "continuation function without environment pointer",
        });
    };
    bind_environment_slots(&mut builder, function, continuation, env_ptr)?;
    for (param, value) in continuation.params.iter().zip(params.iter().skip(1)) {
        builder.def_var(variable(param.value), *value);
    }

    for stmt in &continuation.stmts {
        lower_effect_stmt(jit, &mut builder, function, stmt, functions)?;
    }
    lower_effect_terminator(jit, &mut builder, function, continuation, functions)?;
    builder.seal_all_blocks();
    builder.finalize();
    Ok(())
}

fn bind_environment_slots(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    continuation: &CpsReprAbiContinuation,
    env_ptr: ir::Value,
) -> CpsReprCraneliftResult<()> {
    for slot in &continuation.environment {
        validate_environment_lane(function, slot.value, slot.lane)?;
        let offset = i32::try_from(slot.index * 8).map_err(|_| {
            CpsReprCraneliftError::UnsupportedFunction {
                function: function.name.clone(),
                reason: "continuation environment offset",
            }
        })?;
        let value = builder
            .ins()
            .load(types::I64, ir::MemFlags::new(), env_ptr, offset);
        builder.def_var(variable(slot.value), value);
    }
    Ok(())
}

fn lower_effect_stmt(
    jit: &mut JITModule,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    stmt: &CpsStmt,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    match stmt {
        CpsStmt::Literal { dest, literal } => {
            let value = lower_literal(builder, function, literal)?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::Primitive { dest, op, args } => {
            let args = read_values(builder, function, args)?;
            let value = lower_primitive(builder, function, *op, &args)?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::DirectCall { dest, target, args } => {
            let id = functions.functions.get(target).copied().ok_or_else(|| {
                CpsReprCraneliftError::MissingFunction {
                    name: target.clone(),
                }
            })?;
            let callee = jit.declare_func_in_func(id, builder.func);
            let args = read_values(builder, function, args)?;
            let call = builder.ins().call(callee, &args);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(CpsReprCraneliftError::InvalidReturnArity {
                    function: target.clone(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
        }
        CpsStmt::CloneContinuation { .. } => {
            return Err(CpsReprCraneliftError::UnsupportedStmt {
                function: function.name.clone(),
                kind: "clone continuation",
            });
        }
        CpsStmt::Resume {
            dest,
            resumption,
            arg,
        } => {
            let helper = declare_import(
                jit,
                builder,
                "yulang_cps_resume_i64",
                &[types::I64, types::I64],
                types::I64,
            )?;
            let resumption = read_value(builder, function, *resumption)?;
            let arg = read_value(builder, function, *arg)?;
            let call = builder.ins().call(helper, &[resumption, arg]);
            let results = builder.inst_results(call);
            builder.def_var(variable(*dest), results[0]);
        }
    }
    Ok(())
}

fn lower_effect_terminator(
    jit: &mut JITModule,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    continuation: &CpsReprAbiContinuation,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    match &continuation.terminator {
        CpsTerminator::Return(value) => {
            let value = read_value(builder, function, *value)?;
            builder.ins().return_(&[value]);
        }
        CpsTerminator::Continue { target, args } => {
            let value = call_continuation(jit, builder, function, *target, args, functions)?;
            builder.ins().return_(&[value]);
        }
        CpsTerminator::Branch {
            cond,
            then_cont,
            else_cont,
        } => {
            lower_effect_branch(
                jit, builder, function, *cond, *then_cont, *else_cont, functions,
            )?;
        }
        CpsTerminator::Perform {
            payload,
            resume,
            handler,
            ..
        } => {
            let handler_entry = function
                .handlers
                .iter()
                .find(|candidate| candidate.id == *handler)
                .map(|candidate| candidate.entry)
                .ok_or_else(|| CpsReprCraneliftError::UnsupportedTerminator {
                    function: function.name.clone(),
                    kind: "perform without handler entry",
                })?;
            let resumption = make_resumption(jit, builder, function, *resume, functions)?;
            let payload = read_value(builder, function, *payload)?;
            let callee = continuation_func_ref(jit, builder, function, handler_entry, functions)?;
            let null_env = builder.ins().iconst(types::I64, 0);
            let call = builder.ins().call(callee, &[null_env, payload, resumption]);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(CpsReprCraneliftError::InvalidReturnArity {
                    function: function.name.clone(),
                    arity: results.len(),
                });
            }
            let result = results[0];
            builder.ins().return_(&[result]);
        }
    }
    Ok(())
}

fn lower_effect_branch(
    jit: &mut JITModule,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    cond: CpsValueId,
    then_cont: CpsContinuationId,
    else_cont: CpsContinuationId,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    let then_block = builder.create_block();
    let else_block = builder.create_block();
    let merge_block = builder.create_block();
    builder.append_block_param(merge_block, types::I64);

    let cond = read_value(builder, function, cond)?;
    let cond = builder
        .ins()
        .icmp_imm(ir::condcodes::IntCC::NotEqual, cond, 0);
    builder.ins().brif(cond, then_block, &[], else_block, &[]);

    builder.switch_to_block(then_block);
    let then_value = call_continuation(jit, builder, function, then_cont, &[], functions)?;
    builder
        .ins()
        .jump(merge_block, &[ir::BlockArg::Value(then_value)]);

    builder.switch_to_block(else_block);
    let else_value = call_continuation(jit, builder, function, else_cont, &[], functions)?;
    builder
        .ins()
        .jump(merge_block, &[ir::BlockArg::Value(else_value)]);

    builder.switch_to_block(merge_block);
    let result = builder.block_params(merge_block)[0];
    builder.ins().return_(&[result]);
    Ok(())
}

fn call_continuation(
    jit: &mut JITModule,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    target: CpsContinuationId,
    args: &[CpsValueId],
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<ir::Value> {
    let callee = continuation_func_ref(jit, builder, function, target, functions)?;
    let env = continuation_environment_argument(builder, function, target)?;
    let mut call_args = vec![env];
    call_args.extend(read_values(builder, function, args)?);
    let call = builder.ins().call(callee, &call_args);
    let results = builder.inst_results(call);
    if results.len() != 1 {
        return Err(CpsReprCraneliftError::InvalidReturnArity {
            function: function.name.clone(),
            arity: results.len(),
        });
    }
    Ok(results[0])
}

fn continuation_environment_argument(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    target: CpsContinuationId,
) -> CpsReprCraneliftResult<ir::Value> {
    let target = continuation(function, target)?;
    if target.environment.is_empty() {
        return Ok(builder.ins().iconst(types::I64, 0));
    }
    Err(CpsReprCraneliftError::UnsupportedTerminator {
        function: function.name.clone(),
        kind: "continue to captured continuation",
    })
}

fn make_resumption(
    jit: &mut JITModule,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    resume: CpsContinuationId,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<ir::Value> {
    let resume_continuation = continuation(function, resume)?;
    if resume_continuation.params.len() != 1 {
        return Err(CpsReprCraneliftError::UnsupportedTerminator {
            function: function.name.clone(),
            kind: "resume continuation arity",
        });
    }
    if resume_continuation.environment.len() > 4 {
        return Err(CpsReprCraneliftError::UnsupportedTerminator {
            function: function.name.clone(),
            kind: "resume continuation environment larger than four slots",
        });
    }

    let func_ref = continuation_func_ref(jit, builder, function, resume, functions)?;
    let code = builder.ins().func_addr(types::I64, func_ref);
    let mut args = vec![code];
    for slot in &resume_continuation.environment {
        validate_environment_lane(function, slot.value, slot.lane)?;
        args.push(read_value(builder, function, slot.value)?);
    }
    let helper_name = match resume_continuation.environment.len() {
        0 => "yulang_cps_make_resumption_i64_0",
        1 => "yulang_cps_make_resumption_i64_1",
        2 => "yulang_cps_make_resumption_i64_2",
        3 => "yulang_cps_make_resumption_i64_3",
        4 => "yulang_cps_make_resumption_i64_4",
        _ => unreachable!("environment length checked above"),
    };
    let params = vec![types::I64; args.len()];
    let helper = declare_import(jit, builder, helper_name, &params, types::I64)?;
    let call = builder.ins().call(helper, &args);
    let results = builder.inst_results(call);
    Ok(results[0])
}

fn continuation(
    function: &CpsReprAbiFunction,
    id: CpsContinuationId,
) -> CpsReprCraneliftResult<&CpsReprAbiContinuation> {
    function
        .continuations
        .iter()
        .find(|continuation| continuation.id == id)
        .ok_or_else(|| CpsReprCraneliftError::MissingContinuation {
            function: function.name.clone(),
            continuation: id,
        })
}

fn declare_import(
    jit: &mut JITModule,
    builder: &mut FunctionBuilder<'_>,
    name: &str,
    params: &[ir::Type],
    ret: ir::Type,
) -> CpsReprCraneliftResult<ir::FuncRef> {
    let mut sig = jit.make_signature();
    sig.params.extend(params.iter().copied().map(AbiParam::new));
    sig.returns.push(AbiParam::new(ret));
    let id = jit
        .declare_function(name, Linkage::Import, &sig)
        .map_err(cranelift_error)?;
    Ok(jit.declare_func_in_func(id, builder.func))
}

fn function_signature(jit: &JITModule, function: &CpsReprAbiFunction) -> ir::Signature {
    let mut sig = jit.make_signature();
    sig.params
        .extend(function.params.iter().map(|_| AbiParam::new(types::I64)));
    sig.returns.push(AbiParam::new(types::I64));
    sig
}

fn lower_function(
    jit: &mut JITModule,
    ctx: &mut cranelift_codegen::Context,
    function: &CpsReprAbiFunction,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    let mut builder_context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_context);
    let blocks = create_blocks(&mut builder, function);
    declare_variables(&mut builder, function);
    bind_function_params(&mut builder, function, &blocks)?;

    for continuation in &function.continuations {
        let block = continuation_block(function, &blocks, continuation.id)?;
        builder.switch_to_block(block);
        bind_continuation_params(&mut builder, function, continuation, block)?;
        for stmt in &continuation.stmts {
            lower_stmt(jit, &mut builder, function, stmt, functions)?;
        }
        lower_terminator(&mut builder, function, &blocks, &continuation.terminator)?;
    }
    builder.seal_all_blocks();
    builder.finalize();
    Ok(())
}

fn create_blocks(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
) -> HashMap<CpsContinuationId, ir::Block> {
    function
        .continuations
        .iter()
        .map(|continuation| {
            let block = builder.create_block();
            if continuation.id != function.entry {
                for _ in &continuation.params {
                    builder.append_block_param(block, types::I64);
                }
            }
            (continuation.id, block)
        })
        .collect()
}

fn declare_variables(builder: &mut FunctionBuilder<'_>, function: &CpsReprAbiFunction) {
    for value in function_value_ids(function) {
        builder.declare_var(variable(value), types::I64);
    }
}

fn bind_function_params(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    blocks: &HashMap<CpsContinuationId, ir::Block>,
) -> CpsReprCraneliftResult<()> {
    let entry = continuation_block(function, blocks, function.entry)?;
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    let params = builder.block_params(entry).to_vec();
    if function
        .continuations
        .iter()
        .find(|continuation| continuation.id == function.entry)
        .is_some_and(|continuation| !continuation.params.is_empty())
    {
        return Err(CpsReprCraneliftError::UnsupportedFunction {
            function: function.name.clone(),
            reason: "entry continuation parameters",
        });
    }
    for (param, value) in function.params.iter().zip(params) {
        builder.def_var(variable(param.value), value);
    }
    Ok(())
}

fn bind_continuation_params(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    continuation: &CpsReprAbiContinuation,
    block: ir::Block,
) -> CpsReprCraneliftResult<()> {
    if continuation.id == function.entry {
        return Ok(());
    }
    let params = builder.block_params(block).to_vec();
    for (param, value) in continuation.params.iter().zip(params) {
        builder.def_var(variable(param.value), value);
    }
    Ok(())
}

fn lower_stmt(
    jit: &mut JITModule,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    stmt: &CpsStmt,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    match stmt {
        CpsStmt::Literal { dest, literal } => {
            let value = lower_literal(builder, function, literal)?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::Primitive { dest, op, args } => {
            let args = read_values(builder, function, args)?;
            let value = lower_primitive(builder, function, *op, &args)?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::DirectCall { dest, target, args } => {
            let id = functions.functions.get(target).copied().ok_or_else(|| {
                CpsReprCraneliftError::MissingFunction {
                    name: target.clone(),
                }
            })?;
            let callee = jit.declare_func_in_func(id, builder.func);
            let args = read_values(builder, function, args)?;
            let call = builder.ins().call(callee, &args);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(CpsReprCraneliftError::InvalidReturnArity {
                    function: target.clone(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
        }
        CpsStmt::CloneContinuation { .. } => {
            return Err(CpsReprCraneliftError::UnsupportedStmt {
                function: function.name.clone(),
                kind: "clone continuation",
            });
        }
        CpsStmt::Resume { .. } => {
            return Err(CpsReprCraneliftError::UnsupportedStmt {
                function: function.name.clone(),
                kind: "resume",
            });
        }
    }
    Ok(())
}

fn lower_terminator(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    blocks: &HashMap<CpsContinuationId, ir::Block>,
    terminator: &CpsTerminator,
) -> CpsReprCraneliftResult<()> {
    match terminator {
        CpsTerminator::Return(value) => {
            let value = read_value(builder, function, *value)?;
            builder.ins().return_(&[value]);
        }
        CpsTerminator::Continue { target, args } => {
            let target = continuation_block(function, blocks, *target)?;
            let args = read_block_args(builder, function, args)?;
            builder.ins().jump(target, &args);
        }
        CpsTerminator::Branch {
            cond,
            then_cont,
            else_cont,
        } => {
            let cond = read_value(builder, function, *cond)?;
            let cond = builder
                .ins()
                .icmp_imm(ir::condcodes::IntCC::NotEqual, cond, 0);
            let then_cont = continuation_block(function, blocks, *then_cont)?;
            let else_cont = continuation_block(function, blocks, *else_cont)?;
            builder.ins().brif(cond, then_cont, &[], else_cont, &[]);
        }
        CpsTerminator::Perform { .. } => {
            return Err(CpsReprCraneliftError::UnsupportedTerminator {
                function: function.name.clone(),
                kind: "perform",
            });
        }
    }
    Ok(())
}

fn lower_literal(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    literal: &CpsLiteral,
) -> CpsReprCraneliftResult<ir::Value> {
    match literal {
        CpsLiteral::Int(value) => {
            let value =
                value
                    .parse::<i64>()
                    .map_err(|_| CpsReprCraneliftError::UnsupportedLiteral {
                        function: function.name.clone(),
                        literal: literal.clone(),
                    })?;
            Ok(builder.ins().iconst(types::I64, value))
        }
        CpsLiteral::Bool(value) => Ok(builder.ins().iconst(types::I64, i64::from(*value))),
        CpsLiteral::Unit => Ok(builder.ins().iconst(types::I64, 0)),
        CpsLiteral::Float(_) | CpsLiteral::String(_) => {
            Err(CpsReprCraneliftError::UnsupportedLiteral {
                function: function.name.clone(),
                literal: literal.clone(),
            })
        }
    }
}

fn lower_primitive(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    op: core_ir::PrimitiveOp,
    args: &[ir::Value],
) -> CpsReprCraneliftResult<ir::Value> {
    let value = match op {
        core_ir::PrimitiveOp::BoolNot => {
            let zero = builder.ins().iconst(types::I64, 0);
            let is_zero = builder
                .ins()
                .icmp(ir::condcodes::IntCC::Equal, args[0], zero);
            builder.ins().uextend(types::I64, is_zero)
        }
        core_ir::PrimitiveOp::BoolEq | core_ir::PrimitiveOp::IntEq => {
            let eq = builder
                .ins()
                .icmp(ir::condcodes::IntCC::Equal, args[0], args[1]);
            builder.ins().uextend(types::I64, eq)
        }
        core_ir::PrimitiveOp::IntAdd => builder.ins().iadd(args[0], args[1]),
        core_ir::PrimitiveOp::IntSub => builder.ins().isub(args[0], args[1]),
        core_ir::PrimitiveOp::IntMul => builder.ins().imul(args[0], args[1]),
        core_ir::PrimitiveOp::IntDiv => builder.ins().sdiv(args[0], args[1]),
        core_ir::PrimitiveOp::IntLt => int_cmp(builder, ir::condcodes::IntCC::SignedLessThan, args),
        core_ir::PrimitiveOp::IntLe => {
            int_cmp(builder, ir::condcodes::IntCC::SignedLessThanOrEqual, args)
        }
        core_ir::PrimitiveOp::IntGt => {
            int_cmp(builder, ir::condcodes::IntCC::SignedGreaterThan, args)
        }
        core_ir::PrimitiveOp::IntGe => int_cmp(
            builder,
            ir::condcodes::IntCC::SignedGreaterThanOrEqual,
            args,
        ),
        _ => {
            return Err(CpsReprCraneliftError::UnsupportedPrimitive {
                function: function.name.clone(),
                op,
            });
        }
    };
    Ok(value)
}

fn int_cmp(
    builder: &mut FunctionBuilder<'_>,
    code: ir::condcodes::IntCC,
    args: &[ir::Value],
) -> ir::Value {
    let cmp = builder.ins().icmp(code, args[0], args[1]);
    builder.ins().uextend(types::I64, cmp)
}

fn validate_scalar_subset(module: &CpsReprAbiModule) -> CpsReprCraneliftResult<()> {
    for function in module.functions.iter().chain(&module.roots) {
        let has_effect_flow = function_has_effect_flow(function);
        for param in &function.params {
            validate_value_lane(function, param)?;
        }
        for continuation in &function.continuations {
            if !has_effect_flow && !continuation.environment.is_empty() {
                return Err(CpsReprCraneliftError::UnsupportedFunction {
                    function: function.name.clone(),
                    reason: "continuation environment",
                });
            }
            if has_effect_flow && continuation.environment.len() > 4 {
                return Err(CpsReprCraneliftError::UnsupportedFunction {
                    function: function.name.clone(),
                    reason: "continuation environment larger than four slots",
                });
            }
            for slot in &continuation.environment {
                validate_environment_lane(function, slot.value, slot.lane)?;
            }
            for param in &continuation.params {
                validate_value_lane(function, param)?;
            }
            for stmt in &continuation.stmts {
                match stmt {
                    CpsStmt::Literal { literal, .. } => match literal {
                        CpsLiteral::Int(_) | CpsLiteral::Bool(_) | CpsLiteral::Unit => {}
                        CpsLiteral::Float(_) | CpsLiteral::String(_) => {
                            return Err(CpsReprCraneliftError::UnsupportedLiteral {
                                function: function.name.clone(),
                                literal: literal.clone(),
                            });
                        }
                    },
                    CpsStmt::Primitive { op, .. } => validate_primitive(function, *op)?,
                    CpsStmt::DirectCall { .. } => {}
                    CpsStmt::CloneContinuation { .. } => {
                        return Err(CpsReprCraneliftError::UnsupportedStmt {
                            function: function.name.clone(),
                            kind: "clone continuation",
                        });
                    }
                    CpsStmt::Resume { .. } if has_effect_flow => {}
                    CpsStmt::Resume { .. } => {
                        return Err(CpsReprCraneliftError::UnsupportedStmt {
                            function: function.name.clone(),
                            kind: "resume",
                        });
                    }
                }
            }
            if continuation.return_lane != CpsReprAbiLane::ScalarI64 {
                return Err(CpsReprCraneliftError::UnsupportedReturnLane {
                    function: function.name.clone(),
                    continuation: continuation.id,
                    lane: continuation.return_lane,
                });
            }
        }
    }
    Ok(())
}

fn validate_value_lane(
    function: &CpsReprAbiFunction,
    value: &CpsReprAbiValue,
) -> CpsReprCraneliftResult<()> {
    match value.lane {
        CpsReprAbiLane::ScalarI64 | CpsReprAbiLane::ResumptionPtr | CpsReprAbiLane::Unknown => {
            Ok(())
        }
        lane => Err(CpsReprCraneliftError::UnsupportedLane {
            function: function.name.clone(),
            value: value.value,
            lane,
        }),
    }
}

fn validate_environment_lane(
    function: &CpsReprAbiFunction,
    value: CpsValueId,
    lane: CpsReprAbiLane,
) -> CpsReprCraneliftResult<()> {
    match lane {
        CpsReprAbiLane::ScalarI64 | CpsReprAbiLane::Unknown => Ok(()),
        lane => Err(CpsReprCraneliftError::UnsupportedLane {
            function: function.name.clone(),
            value,
            lane,
        }),
    }
}

fn validate_primitive(
    function: &CpsReprAbiFunction,
    op: core_ir::PrimitiveOp,
) -> CpsReprCraneliftResult<()> {
    match op {
        core_ir::PrimitiveOp::BoolNot
        | core_ir::PrimitiveOp::BoolEq
        | core_ir::PrimitiveOp::IntAdd
        | core_ir::PrimitiveOp::IntSub
        | core_ir::PrimitiveOp::IntMul
        | core_ir::PrimitiveOp::IntDiv
        | core_ir::PrimitiveOp::IntEq
        | core_ir::PrimitiveOp::IntLt
        | core_ir::PrimitiveOp::IntLe
        | core_ir::PrimitiveOp::IntGt
        | core_ir::PrimitiveOp::IntGe => Ok(()),
        _ => Err(CpsReprCraneliftError::UnsupportedPrimitive {
            function: function.name.clone(),
            op,
        }),
    }
}

fn read_values(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    values: &[CpsValueId],
) -> CpsReprCraneliftResult<Vec<ir::Value>> {
    values
        .iter()
        .map(|value| read_value(builder, function, *value))
        .collect()
}

fn read_value(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    value: CpsValueId,
) -> CpsReprCraneliftResult<ir::Value> {
    if !function_value_ids(function).contains(&value) {
        return Err(CpsReprCraneliftError::MissingValue {
            function: function.name.clone(),
            value,
        });
    }
    Ok(builder.use_var(variable(value)))
}

fn read_block_args(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    values: &[CpsValueId],
) -> CpsReprCraneliftResult<Vec<ir::BlockArg>> {
    Ok(read_values(builder, function, values)?
        .into_iter()
        .map(ir::BlockArg::Value)
        .collect())
}

fn continuation_block(
    function: &CpsReprAbiFunction,
    blocks: &HashMap<CpsContinuationId, ir::Block>,
    id: CpsContinuationId,
) -> CpsReprCraneliftResult<ir::Block> {
    blocks
        .get(&id)
        .copied()
        .ok_or_else(|| CpsReprCraneliftError::MissingContinuation {
            function: function.name.clone(),
            continuation: id,
        })
}

fn function_value_ids(function: &CpsReprAbiFunction) -> Vec<CpsValueId> {
    let mut values = function
        .params
        .iter()
        .map(|value| value.value)
        .collect::<Vec<_>>();
    for continuation in &function.continuations {
        values.extend(continuation.params.iter().map(|value| value.value));
        values.extend(continuation.environment.iter().map(|slot| slot.value));
        for stmt in &continuation.stmts {
            match stmt {
                CpsStmt::Literal { dest, .. }
                | CpsStmt::Primitive { dest, .. }
                | CpsStmt::DirectCall { dest, .. }
                | CpsStmt::CloneContinuation { dest, .. }
                | CpsStmt::Resume { dest, .. } => values.push(*dest),
            }
        }
    }
    values.sort();
    values.dedup();
    values
}

fn variable(value: CpsValueId) -> Variable {
    Variable::from_u32(value.0 as u32)
}

fn cranelift_error(error: impl fmt::Display) -> CpsReprCraneliftError {
    CpsReprCraneliftError::Cranelift(error.to_string())
}

type NativeCpsI64Continuation = extern "C" fn(*const i64, i64) -> i64;

#[repr(C)]
struct NativeCpsI64Resumption {
    code: NativeCpsI64Continuation,
    env: Box<[i64]>,
}

fn make_native_i64_resumption(code: usize, env: Vec<i64>) -> *mut NativeCpsI64Resumption {
    let code = unsafe { std::mem::transmute::<usize, NativeCpsI64Continuation>(code) };
    Box::into_raw(Box::new(NativeCpsI64Resumption {
        code,
        env: env.into_boxed_slice(),
    }))
}

extern "C" fn yulang_cps_make_resumption_i64_0(code: usize) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, Vec::new())
}

extern "C" fn yulang_cps_make_resumption_i64_1(code: usize, a: i64) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, vec![a])
}

extern "C" fn yulang_cps_make_resumption_i64_2(
    code: usize,
    a: i64,
    b: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, vec![a, b])
}

extern "C" fn yulang_cps_make_resumption_i64_3(
    code: usize,
    a: i64,
    b: i64,
    c: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, vec![a, b, c])
}

extern "C" fn yulang_cps_make_resumption_i64_4(
    code: usize,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, vec![a, b, c, d])
}

extern "C" fn yulang_cps_resume_i64(resumption: *const NativeCpsI64Resumption, arg: i64) -> i64 {
    let resumption = unsafe { &*resumption };
    (resumption.code)(resumption.env.as_ptr(), arg)
}

#[cfg(test)]
mod tests {
    use crate::cps_ir::{CpsContinuation, CpsFunction, CpsModule, CpsShotKind};
    use crate::cps_repr::lower_cps_repr_module;
    use crate::cps_repr_abi::lower_cps_repr_abi_module;

    use super::*;

    #[test]
    fn jit_runs_pure_continuation_flow() {
        let abi = pure_add_abi();
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![42]);
    }

    #[test]
    fn jit_runs_perform_with_tail_resume_handler() {
        let abi = tail_resume_effect_abi();
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![42]);
    }

    #[test]
    fn jit_runs_multishot_resumption_calls() {
        let abi = multishot_resume_effect_abi();
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![22]);
    }

    #[test]
    fn rejects_perform_until_effect_codegen_exists() {
        let effect = core_ir::Path::from_name(core_ir::Name("choose".to_string()));
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![CpsStmt::Literal {
                        dest: CpsValueId(0),
                        literal: CpsLiteral::Int("1".to_string()),
                    }],
                    terminator: CpsTerminator::Perform {
                        effect,
                        payload: CpsValueId(0),
                        resume: CpsContinuationId(0),
                        handler: crate::cps_ir::CpsHandlerId(0),
                    },
                }],
            }],
        }));

        let error = match compile_cps_repr_abi_module(&abi) {
            Ok(_) => panic!("expected unsupported perform"),
            Err(error) => error,
        };

        assert!(matches!(
            error,
            CpsReprCraneliftError::UnsupportedReturnLane {
                lane: CpsReprAbiLane::Unknown,
                ..
            }
        ));
    }

    #[test]
    fn jit_runs_runtime_module_through_cps_pipeline() {
        let expr = apply(
            apply(
                primitive(core_ir::PrimitiveOp::IntAdd),
                unknown_lit(core_ir::Lit::Int("20".to_string())),
            ),
            unknown_lit(core_ir::Lit::Int("22".to_string())),
        );
        let mut jit = compile_runtime_module_to_cps_repr_jit(&module_with_root(expr))
            .expect("compiled runtime module through CPS repr");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![42]);
    }

    fn pure_add_abi() -> CpsReprAbiModule {
        lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(0),
                                literal: CpsLiteral::Int("40".to_string()),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(1),
                                literal: CpsLiteral::Int("2".to_string()),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(2),
                                op: core_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(0), CpsValueId(1)],
                            },
                        ],
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(1),
                            args: vec![CpsValueId(2)],
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(3)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                ],
            }],
        }))
    }

    fn tail_resume_effect_abi() -> CpsReprAbiModule {
        let effect = core_ir::Path::from_name(core_ir::Name("choose".to_string()));
        lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: vec![crate::cps_ir::CpsHandler {
                    id: crate::cps_ir::CpsHandlerId(0),
                    effect: effect.clone(),
                    entry: CpsContinuationId(2),
                }],
                continuations: vec![
                    CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(0),
                                literal: CpsLiteral::Int("1".to_string()),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(2),
                                literal: CpsLiteral::Int("10".to_string()),
                            },
                        ],
                        terminator: CpsTerminator::Perform {
                            effect,
                            payload: CpsValueId(0),
                            resume: CpsContinuationId(1),
                            handler: crate::cps_ir::CpsHandlerId(0),
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(1)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(2),
                                literal: CpsLiteral::Int("41".to_string()),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(3),
                                op: core_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(1), CpsValueId(2)],
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(2),
                        params: vec![CpsValueId(4), CpsValueId(5)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Resume {
                            dest: CpsValueId(6),
                            resumption: CpsValueId(5),
                            arg: CpsValueId(4),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(6)),
                    },
                ],
            }],
        }))
    }

    fn multishot_resume_effect_abi() -> CpsReprAbiModule {
        let effect = core_ir::Path::from_name(core_ir::Name("choose".to_string()));
        lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: vec![crate::cps_ir::CpsHandler {
                    id: crate::cps_ir::CpsHandlerId(0),
                    effect: effect.clone(),
                    entry: CpsContinuationId(2),
                }],
                continuations: vec![
                    CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(0),
                                literal: CpsLiteral::Int("1".to_string()),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(2),
                                literal: CpsLiteral::Int("10".to_string()),
                            },
                        ],
                        terminator: CpsTerminator::Perform {
                            effect,
                            payload: CpsValueId(0),
                            resume: CpsContinuationId(1),
                            handler: crate::cps_ir::CpsHandlerId(0),
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(1)],
                        captures: vec![CpsValueId(2)],
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Primitive {
                            dest: CpsValueId(3),
                            op: core_ir::PrimitiveOp::IntAdd,
                            args: vec![CpsValueId(1), CpsValueId(2)],
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(2),
                        params: vec![CpsValueId(4), CpsValueId(5)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![
                            CpsStmt::Resume {
                                dest: CpsValueId(6),
                                resumption: CpsValueId(5),
                                arg: CpsValueId(4),
                            },
                            CpsStmt::Resume {
                                dest: CpsValueId(7),
                                resumption: CpsValueId(5),
                                arg: CpsValueId(4),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(8),
                                op: core_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(6), CpsValueId(7)],
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(8)),
                    },
                ],
            }],
        }))
    }

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

    fn module_with_root(expr: runtime::Expr) -> runtime::Module {
        runtime::Module {
            path: core_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![expr],
            roots: vec![runtime::Root::Expr(0)],
            role_impls: Vec::new(),
        }
    }
}
