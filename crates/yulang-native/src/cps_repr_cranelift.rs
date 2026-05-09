use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt;

use cranelift_codegen::ir::{self, AbiParam, InstBuilder, types};
use cranelift_codegen::settings;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use yulang_core_ir as core_ir;
use yulang_runtime as runtime;

use crate::cps_ir::{
    CpsContinuationId, CpsHandlerId, CpsLiteral, CpsStmt, CpsTerminator, CpsValueId,
};
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
    cranelift_ir: Vec<String>,
}

impl CpsReprJitModule {
    pub fn cranelift_ir(&self) -> &[String] {
        &self.cranelift_ir
    }

    pub fn run_roots_i64(&mut self) -> CpsReprCraneliftResult<Vec<i64>> {
        self.module
            .finalize_definitions()
            .map_err(cranelift_error)?;
        self.roots
            .iter()
            .map(|root| {
                reset_native_i64_cps_state();
                let ptr = self.module.get_finalized_function(*root);
                let call = unsafe { std::mem::transmute::<_, extern "C" fn() -> i64>(ptr) };
                Ok(call())
            })
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprObjectModule {
    bytes: Vec<u8>,
    roots: Vec<String>,
}

impl CpsReprObjectModule {
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn roots(&self) -> &[String] {
        &self.roots
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
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
    builder.symbol(
        "yulang_cps_make_env_i64_0",
        yulang_cps_make_env_i64_0 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_env_i64_1",
        yulang_cps_make_env_i64_1 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_env_i64_2",
        yulang_cps_make_env_i64_2 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_env_i64_3",
        yulang_cps_make_env_i64_3 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_env_i64_4",
        yulang_cps_make_env_i64_4 as *const u8,
    );
    builder.symbol("yulang_cps_resume_i64", yulang_cps_resume_i64 as *const u8);
    builder.symbol(
        "yulang_cps_resume_with_handler_i64",
        yulang_cps_resume_with_handler_i64 as *const u8,
    );
    builder.symbol(
        "yulang_cps_select_handler_i64",
        yulang_cps_select_handler_i64 as *const u8,
    );
    builder.symbol(
        "yulang_cps_capture_handler_env_i64",
        yulang_cps_capture_handler_env_i64 as *const u8,
    );
    builder.symbol(
        "yulang_cps_selected_handler_env_or_i64",
        yulang_cps_selected_handler_env_or_i64 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_thunk_i64_0",
        yulang_cps_make_thunk_i64_0 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_thunk_i64_1",
        yulang_cps_make_thunk_i64_1 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_thunk_i64_2",
        yulang_cps_make_thunk_i64_2 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_thunk_i64_3",
        yulang_cps_make_thunk_i64_3 as *const u8,
    );
    builder.symbol(
        "yulang_cps_make_thunk_i64_4",
        yulang_cps_make_thunk_i64_4 as *const u8,
    );
    builder.symbol(
        "yulang_cps_force_thunk_i64",
        yulang_cps_force_thunk_i64 as *const u8,
    );
    builder.symbol(
        "yulang_cps_fresh_guard_i64",
        yulang_cps_fresh_guard_i64 as *const u8,
    );
    builder.symbol(
        "yulang_cps_peek_guard_i64",
        yulang_cps_peek_guard_i64 as *const u8,
    );
    builder.symbol(
        "yulang_cps_find_guard_i64",
        yulang_cps_find_guard_i64 as *const u8,
    );
    let mut jit = JITModule::new(builder);
    let functions = declare_functions(&mut jit, module)?;
    let cranelift_ir = define_functions(&mut jit, module, &functions)?;
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
    Ok(CpsReprJitModule {
        module: jit,
        roots,
        cranelift_ir,
    })
}

pub fn compile_cps_repr_abi_module_to_object(
    module: &CpsReprAbiModule,
) -> CpsReprCraneliftResult<CpsReprObjectModule> {
    validate_scalar_subset(module)?;

    let isa_builder = cranelift_native::builder().map_err(cranelift_error)?;
    let flags = settings::Flags::new(settings::builder());
    let isa = isa_builder.finish(flags).map_err(cranelift_error)?;
    let builder = ObjectBuilder::new(
        isa,
        "yulang_cps_repr_object".to_string(),
        cranelift_module::default_libcall_names(),
    )
    .map_err(cranelift_error)?;
    let mut object = ObjectModule::new(builder);
    let functions = declare_functions(&mut object, module)?;
    let _ = define_functions(&mut object, module, &functions)?;
    let roots = module
        .roots
        .iter()
        .map(|root| root.name.clone())
        .collect::<Vec<_>>();
    let product = object.finish();
    let bytes = product.emit().map_err(cranelift_error)?;
    Ok(CpsReprObjectModule { bytes, roots })
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

pub fn compile_runtime_module_to_cps_repr_object(
    module: &runtime::Module,
) -> CpsReprCraneliftResult<CpsReprObjectModule> {
    let cps = lower_cps_module(module)?;
    validate_cps_module(&cps)?;
    let repr = crate::cps_repr::lower_cps_repr_module(&cps);
    let abi = lower_cps_repr_abi_module(&repr);
    compile_cps_repr_abi_module_to_object(&abi)
}

fn declare_functions<M: Module>(
    module_backend: &mut M,
    module: &CpsReprAbiModule,
) -> CpsReprCraneliftResult<DeclaredFunctions> {
    let mut functions = HashMap::new();
    let mut continuations = HashMap::new();
    for function in module.functions.iter().chain(&module.roots) {
        let sig = function_signature(module_backend, function);
        let id = module_backend
            .declare_function(&function.name, Linkage::Export, &sig)
            .map_err(cranelift_error)?;
        functions.insert(function.name.clone(), id);
        if function_has_effect_flow(function) {
            for continuation in &function.continuations {
                let name = continuation_symbol(function, continuation.id);
                let sig = continuation_signature(module_backend, continuation);
                let id = module_backend
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

fn define_functions<M: Module>(
    module_backend: &mut M,
    module: &CpsReprAbiModule,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<Vec<String>> {
    let mut cranelift_ir = Vec::new();
    for function in module.functions.iter().chain(&module.roots) {
        let id = functions
            .functions
            .get(&function.name)
            .copied()
            .ok_or_else(|| CpsReprCraneliftError::MissingFunction {
                name: function.name.clone(),
            })?;
        if function_has_effect_flow(function) {
            cranelift_ir.extend(define_effectful_function(
                module_backend,
                function,
                functions,
            )?);
        }
        let mut ctx = module_backend.make_context();
        ctx.func.signature = function_signature(module_backend, function);
        if function_has_effect_flow(function) {
            lower_effectful_function_wrapper(module_backend, &mut ctx, function, functions)?;
        } else {
            lower_function(module_backend, &mut ctx, function, functions)?;
        }
        cranelift_ir.push(format!(
            ";; cps-repr function {}\n{}",
            function.name,
            ctx.func.display()
        ));
        module_backend
            .define_function(id, &mut ctx)
            .map_err(cranelift_error)?;
        module_backend.clear_context(&mut ctx);
    }
    Ok(cranelift_ir)
}

#[derive(Debug, Default)]
struct DeclaredFunctions {
    functions: HashMap<String, FuncId>,
    continuations: HashMap<(String, CpsContinuationId), FuncId>,
}

fn define_effectful_function<M: Module>(
    module_backend: &mut M,
    function: &CpsReprAbiFunction,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<Vec<String>> {
    let mut cranelift_ir = Vec::new();
    for continuation in &function.continuations {
        let id = functions
            .continuations
            .get(&(function.name.clone(), continuation.id))
            .copied()
            .ok_or_else(|| CpsReprCraneliftError::MissingContinuation {
                function: function.name.clone(),
                continuation: continuation.id,
            })?;
        let mut ctx = module_backend.make_context();
        ctx.func.signature = continuation_signature(module_backend, continuation);
        lower_continuation_function(module_backend, &mut ctx, function, continuation, functions)?;
        cranelift_ir.push(format!(
            ";; cps-repr continuation {}::{:?}\n{}",
            function.name,
            continuation.id,
            ctx.func.display()
        ));
        module_backend
            .define_function(id, &mut ctx)
            .map_err(cranelift_error)?;
        module_backend.clear_context(&mut ctx);
    }
    Ok(cranelift_ir)
}

fn lower_effectful_function_wrapper<M: Module>(
    module_backend: &mut M,
    ctx: &mut cranelift_codegen::Context,
    function: &CpsReprAbiFunction,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    let mut builder_context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_context);
    let block = builder.create_block();
    builder.append_block_params_for_function_params(block);
    builder.switch_to_block(block);

    let entry = continuation_func_ref(
        module_backend,
        &mut builder,
        function,
        function.entry,
        functions,
    )?;
    let null_env = builder.ins().iconst(types::I64, 0);
    let mut args = vec![null_env];
    args.extend(builder.block_params(block).iter().copied());
    let call = builder.ins().call(entry, &args);
    let result = match builder.inst_results(call) {
        [result] => *result,
        results => {
            return Err(CpsReprCraneliftError::InvalidReturnArity {
                function: function.name.clone(),
                arity: results.len(),
            });
        }
    };
    let result = force_function_result_if_thunk(module_backend, &mut builder, function, result)?;
    builder.ins().return_(&[result]);
    builder.seal_all_blocks();
    builder.finalize();
    Ok(())
}

fn force_function_result_if_thunk<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    result: ir::Value,
) -> CpsReprCraneliftResult<ir::Value> {
    let entry = continuation(function, function.entry)?;
    if entry.return_lane != CpsReprAbiLane::ThunkPtr {
        return Ok(result);
    }
    let helper = declare_import(
        module_backend,
        builder,
        "yulang_cps_force_thunk_i64",
        &[types::I64],
        types::I64,
    )?;
    let call = builder.ins().call(helper, &[result]);
    Ok(builder.inst_results(call)[0])
}

fn function_has_effect_flow(function: &CpsReprAbiFunction) -> bool {
    !function.handlers.is_empty()
        || function.continuations.iter().any(|continuation| {
            !continuation.environment.is_empty()
                || matches!(continuation.terminator, CpsTerminator::Perform { .. })
                || continuation.stmts.iter().any(|stmt| {
                    matches!(
                        stmt,
                        CpsStmt::Resume { .. } | CpsStmt::ResumeWithHandler { .. }
                    )
                })
        })
}

fn continuation_signature<M: Module>(
    module_backend: &M,
    continuation: &CpsReprAbiContinuation,
) -> ir::Signature {
    let mut sig = module_backend.make_signature();
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

fn continuation_func_ref<M: Module>(
    module_backend: &mut M,
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
    Ok(module_backend.declare_func_in_func(id, builder.func))
}

fn lower_continuation_function<M: Module>(
    module_backend: &mut M,
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

    let mut defined_values = continuation
        .environment
        .iter()
        .map(|slot| slot.value)
        .chain(continuation.params.iter().map(|param| param.value))
        .collect::<HashSet<_>>();
    for stmt in &continuation.stmts {
        capture_handler_envs_for_stmt(
            module_backend,
            &mut builder,
            function,
            stmt,
            &defined_values,
        )?;
        lower_effect_stmt(module_backend, &mut builder, function, stmt, functions)?;
        if let Some(dest) = stmt_dest(stmt) {
            defined_values.insert(dest);
        }
    }
    lower_effect_terminator(
        module_backend,
        &mut builder,
        function,
        continuation,
        functions,
    )?;
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

fn capture_handler_envs_for_stmt<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    stmt: &CpsStmt,
    defined_values: &HashSet<CpsValueId>,
) -> CpsReprCraneliftResult<()> {
    if !matches!(stmt, CpsStmt::MakeThunk { .. }) || function.handlers.is_empty() {
        return Ok(());
    }

    for handler in &function.handlers {
        for arm in &handler.arms {
            let entry = continuation(function, arm.entry)?;
            if !entry
                .environment
                .iter()
                .all(|slot| defined_values.contains(&slot.value))
            {
                continue;
            }
            let env =
                continuation_environment_argument(module_backend, builder, function, arm.entry)?;
            let handler = builder.ins().iconst(types::I64, handler.id.0 as i64);
            let entry = builder.ins().iconst(types::I64, arm.entry.0 as i64);
            let _ = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_capture_handler_env_i64",
                &[handler, entry, env],
            )?;
        }
    }
    Ok(())
}

fn capture_handler_envs<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    handler: CpsHandlerId,
    envs: &[crate::cps_ir::CpsHandlerEnv],
) -> CpsReprCraneliftResult<()> {
    for env in envs {
        if env.values.len() > 4 {
            return Err(CpsReprCraneliftError::UnsupportedStmt {
                function: function.name.clone(),
                kind: "handler environment larger than four slots",
            });
        }
        let values = read_values(builder, function, &env.values)?;
        let env_ptr = make_env(module_backend, builder, function, &values)?;
        let handler = builder.ins().iconst(types::I64, handler.0 as i64);
        let entry = builder.ins().iconst(types::I64, env.entry.0 as i64);
        let _ = call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_capture_handler_env_i64",
            &[handler, entry, env_ptr],
        )?;
    }
    Ok(())
}

fn lower_effect_stmt<M: Module>(
    module_backend: &mut M,
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
        CpsStmt::FreshGuard { dest, .. } => {
            let value =
                call_i64_helper(module_backend, builder, "yulang_cps_fresh_guard_i64", &[])?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::PeekGuard { dest } => {
            let value = call_i64_helper(module_backend, builder, "yulang_cps_peek_guard_i64", &[])?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::FindGuard { dest, guard } => {
            let guard = read_value(builder, function, *guard)?;
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_find_guard_i64",
                &[guard],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::MakeThunk { dest, entry } => {
            let value = make_thunk(module_backend, builder, function, *entry, functions)?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::ForceThunk { dest, thunk } => {
            let helper = declare_import(
                module_backend,
                builder,
                "yulang_cps_force_thunk_i64",
                &[types::I64],
                types::I64,
            )?;
            let thunk = read_value(builder, function, *thunk)?;
            let call = builder.ins().call(helper, &[thunk]);
            let results = builder.inst_results(call);
            builder.def_var(variable(*dest), results[0]);
        }
        CpsStmt::Tuple { .. }
        | CpsStmt::Record { .. }
        | CpsStmt::Variant { .. }
        | CpsStmt::Select { .. } => {
            return Err(CpsReprCraneliftError::UnsupportedStmt {
                function: function.name.clone(),
                kind: "structural value",
            });
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
            let callee = module_backend.declare_func_in_func(id, builder.func);
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
        CpsStmt::CloneContinuation { dest, source } => {
            let source = read_value(builder, function, *source)?;
            builder.def_var(variable(*dest), source);
        }
        CpsStmt::Resume {
            dest,
            resumption,
            arg,
        } => {
            let helper = declare_import(
                module_backend,
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
        CpsStmt::ResumeWithHandler {
            dest,
            resumption,
            arg,
            handler,
            envs,
        } => {
            capture_handler_envs(module_backend, builder, function, *handler, envs)?;
            let helper = declare_import(
                module_backend,
                builder,
                "yulang_cps_resume_with_handler_i64",
                &[types::I64, types::I64, types::I64],
                types::I64,
            )?;
            let resumption = read_value(builder, function, *resumption)?;
            let arg = read_value(builder, function, *arg)?;
            let handler = builder.ins().iconst(types::I64, handler.0 as i64);
            let call = builder.ins().call(helper, &[resumption, arg, handler]);
            let results = builder.inst_results(call);
            builder.def_var(variable(*dest), results[0]);
        }
    }
    Ok(())
}

fn stmt_dest(stmt: &CpsStmt) -> Option<CpsValueId> {
    match stmt {
        CpsStmt::Literal { dest, .. }
        | CpsStmt::Primitive { dest, .. }
        | CpsStmt::Tuple { dest, .. }
        | CpsStmt::Record { dest, .. }
        | CpsStmt::Variant { dest, .. }
        | CpsStmt::Select { dest, .. }
        | CpsStmt::DirectCall { dest, .. }
        | CpsStmt::CloneContinuation { dest, .. }
        | CpsStmt::MakeThunk { dest, .. }
        | CpsStmt::ForceThunk { dest, .. }
        | CpsStmt::Resume { dest, .. }
        | CpsStmt::ResumeWithHandler { dest, .. }
        | CpsStmt::FreshGuard { dest, .. }
        | CpsStmt::PeekGuard { dest }
        | CpsStmt::FindGuard { dest, .. } => Some(*dest),
    }
}

fn lower_effect_terminator<M: Module>(
    module_backend: &mut M,
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
            let value =
                call_continuation(module_backend, builder, function, *target, args, functions)?;
            builder.ins().return_(&[value]);
        }
        CpsTerminator::Branch {
            cond,
            then_cont,
            else_cont,
        } => {
            lower_effect_branch(
                module_backend,
                builder,
                function,
                *cond,
                *then_cont,
                *else_cont,
                functions,
            )?;
        }
        CpsTerminator::Perform {
            effect,
            payload,
            resume,
            handler,
            blocked,
        } => {
            let candidates = handler_candidates_for_effect(function, effect)?;
            let allowed_mask = handler_mask(function, &candidates)?;
            let resumption = make_resumption(
                module_backend,
                builder,
                function,
                *resume,
                *handler,
                functions,
            )?;
            let payload = read_value(builder, function, *payload)?;
            let fallback = builder.ins().iconst(types::I64, handler.0 as i64);
            let allowed_mask = builder.ins().iconst(types::I64, allowed_mask);
            let blocked = blocked
                .map(|blocked| read_value(builder, function, blocked))
                .transpose()?
                .unwrap_or_else(|| builder.ins().iconst(types::I64, -1));
            let selected = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_select_handler_i64",
                &[fallback, allowed_mask, blocked],
            )?;
            lower_selected_handler_return(
                module_backend,
                builder,
                function,
                &candidates,
                selected,
                payload,
                resumption,
                functions,
            )?;
        }
    }
    Ok(())
}

fn lower_effect_branch<M: Module>(
    module_backend: &mut M,
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

    let cond_id = cond;
    let cond = read_value(builder, function, cond_id)?;
    let cond = force_branch_condition_if_thunk(module_backend, builder, function, cond_id, cond)?;
    let cond = builder
        .ins()
        .icmp_imm(ir::condcodes::IntCC::NotEqual, cond, 0);
    builder.ins().brif(cond, then_block, &[], else_block, &[]);

    builder.switch_to_block(then_block);
    let then_value =
        call_continuation(module_backend, builder, function, then_cont, &[], functions)?;
    builder
        .ins()
        .jump(merge_block, &[ir::BlockArg::Value(then_value)]);

    builder.switch_to_block(else_block);
    let else_value =
        call_continuation(module_backend, builder, function, else_cont, &[], functions)?;
    builder
        .ins()
        .jump(merge_block, &[ir::BlockArg::Value(else_value)]);

    builder.switch_to_block(merge_block);
    let result = builder.block_params(merge_block)[0];
    builder.ins().return_(&[result]);
    Ok(())
}

fn lower_selected_handler_return<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    candidates: &[(CpsHandlerId, CpsContinuationId)],
    selected: ir::Value,
    payload: ir::Value,
    resumption: ir::Value,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    let missing_block = builder.create_block();

    for (index, (handler_id, handler_entry)) in candidates.iter().enumerate() {
        let call_block = builder.create_block();
        let next_block = if index + 1 == candidates.len() {
            missing_block
        } else {
            builder.create_block()
        };
        let compare =
            builder
                .ins()
                .icmp_imm(ir::condcodes::IntCC::Equal, selected, handler_id.0 as i64);
        builder
            .ins()
            .brif(compare, call_block, &[], next_block, &[]);

        builder.switch_to_block(call_block);
        let callee =
            continuation_func_ref(module_backend, builder, function, *handler_entry, functions)?;
        let fallback_env =
            continuation_environment_argument(module_backend, builder, function, *handler_entry)?;
        let entry = builder.ins().iconst(types::I64, handler_entry.0 as i64);
        let handler_env = call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_selected_handler_env_or_i64",
            &[entry, fallback_env],
        )?;
        let call = builder
            .ins()
            .call(callee, &[handler_env, payload, resumption]);
        let results = builder.inst_results(call);
        if results.len() != 1 {
            return Err(CpsReprCraneliftError::InvalidReturnArity {
                function: function.name.clone(),
                arity: results.len(),
            });
        }
        let result = results[0];
        builder.ins().return_(&[result]);

        builder.switch_to_block(next_block);
    }

    builder.switch_to_block(missing_block);
    let value = builder.ins().iconst(types::I64, 0);
    builder.ins().return_(&[value]);
    builder.seal_block(missing_block);
    Ok(())
}

fn force_branch_condition_if_thunk<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    cond_id: CpsValueId,
    cond: ir::Value,
) -> CpsReprCraneliftResult<ir::Value> {
    if value_lane(function, cond_id) != Some(CpsReprAbiLane::ThunkPtr)
        && !value_is_make_thunk(function, cond_id)
    {
        return Ok(cond);
    }
    let helper = declare_import(
        module_backend,
        builder,
        "yulang_cps_force_thunk_i64",
        &[types::I64],
        types::I64,
    )?;
    let call = builder.ins().call(helper, &[cond]);
    Ok(builder.inst_results(call)[0])
}

fn call_continuation<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    target: CpsContinuationId,
    args: &[CpsValueId],
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<ir::Value> {
    let callee = continuation_func_ref(module_backend, builder, function, target, functions)?;
    let env = continuation_environment_argument(module_backend, builder, function, target)?;
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

fn continuation_environment_argument<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    target: CpsContinuationId,
) -> CpsReprCraneliftResult<ir::Value> {
    let target = continuation(function, target)?;
    if target.environment.is_empty() {
        return Ok(builder.ins().iconst(types::I64, 0));
    }
    if target.environment.len() > 4 {
        return Err(CpsReprCraneliftError::UnsupportedTerminator {
            function: function.name.clone(),
            kind: "continuation environment larger than four slots",
        });
    }
    let mut args = Vec::with_capacity(target.environment.len());
    for slot in &target.environment {
        validate_environment_lane(function, slot.value, slot.lane)?;
        args.push(read_value(builder, function, slot.value)?);
    }
    make_env(module_backend, builder, function, &args)
}

fn make_resumption<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    resume: CpsContinuationId,
    handler: CpsHandlerId,
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

    let func_ref = continuation_func_ref(module_backend, builder, function, resume, functions)?;
    let code = builder.ins().func_addr(types::I64, func_ref);
    let handler = builder.ins().iconst(types::I64, handler.0 as i64);
    let mut args = vec![code, handler];
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
    let helper = declare_import(module_backend, builder, helper_name, &params, types::I64)?;
    let call = builder.ins().call(helper, &args);
    let results = builder.inst_results(call);
    Ok(results[0])
}

fn make_thunk<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    entry: CpsContinuationId,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<ir::Value> {
    let thunk_continuation = continuation(function, entry)?;
    if !thunk_continuation.params.is_empty() {
        return Err(CpsReprCraneliftError::UnsupportedStmt {
            function: function.name.clone(),
            kind: "thunk entry arity",
        });
    }
    if thunk_continuation.environment.len() > 4 {
        return Err(CpsReprCraneliftError::UnsupportedStmt {
            function: function.name.clone(),
            kind: "thunk environment larger than four slots",
        });
    }

    let func_ref = continuation_func_ref(module_backend, builder, function, entry, functions)?;
    let code = builder.ins().func_addr(types::I64, func_ref);
    let mut args = vec![code];
    for slot in &thunk_continuation.environment {
        validate_environment_lane(function, slot.value, slot.lane)?;
        args.push(read_value(builder, function, slot.value)?);
    }
    let helper_name = match thunk_continuation.environment.len() {
        0 => "yulang_cps_make_thunk_i64_0",
        1 => "yulang_cps_make_thunk_i64_1",
        2 => "yulang_cps_make_thunk_i64_2",
        3 => "yulang_cps_make_thunk_i64_3",
        4 => "yulang_cps_make_thunk_i64_4",
        _ => unreachable!("environment length checked above"),
    };
    let params = vec![types::I64; args.len()];
    let helper = declare_import(module_backend, builder, helper_name, &params, types::I64)?;
    let call = builder.ins().call(helper, &args);
    let results = builder.inst_results(call);
    Ok(results[0])
}

fn call_i64_helper<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    name: &str,
    args: &[ir::Value],
) -> CpsReprCraneliftResult<ir::Value> {
    let params = vec![types::I64; args.len()];
    let helper = declare_import(module_backend, builder, name, &params, types::I64)?;
    let call = builder.ins().call(helper, args);
    Ok(builder.inst_results(call)[0])
}

fn make_env<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    args: &[ir::Value],
) -> CpsReprCraneliftResult<ir::Value> {
    let helper_name = match args.len() {
        0 => "yulang_cps_make_env_i64_0",
        1 => "yulang_cps_make_env_i64_1",
        2 => "yulang_cps_make_env_i64_2",
        3 => "yulang_cps_make_env_i64_3",
        4 => "yulang_cps_make_env_i64_4",
        _ => {
            return Err(CpsReprCraneliftError::UnsupportedTerminator {
                function: function.name.clone(),
                kind: "continuation environment larger than four slots",
            });
        }
    };
    let params = vec![types::I64; args.len()];
    let helper = declare_import(module_backend, builder, helper_name, &params, types::I64)?;
    let call = builder.ins().call(helper, args);
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

fn declare_import<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    name: &str,
    params: &[ir::Type],
    ret: ir::Type,
) -> CpsReprCraneliftResult<ir::FuncRef> {
    let mut sig = module_backend.make_signature();
    sig.params.extend(params.iter().copied().map(AbiParam::new));
    sig.returns.push(AbiParam::new(ret));
    let id = module_backend
        .declare_function(name, Linkage::Import, &sig)
        .map_err(cranelift_error)?;
    Ok(module_backend.declare_func_in_func(id, builder.func))
}

fn function_signature<M: Module>(
    module_backend: &M,
    function: &CpsReprAbiFunction,
) -> ir::Signature {
    let mut sig = module_backend.make_signature();
    sig.params
        .extend(function.params.iter().map(|_| AbiParam::new(types::I64)));
    sig.returns.push(AbiParam::new(types::I64));
    sig
}

fn lower_function<M: Module>(
    module_backend: &mut M,
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
            lower_stmt(module_backend, &mut builder, function, stmt, functions)?;
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
    let entry_continuation = function
        .continuations
        .iter()
        .find(|continuation| continuation.id == function.entry)
        .ok_or(CpsReprCraneliftError::MissingContinuation {
            function: function.name.clone(),
            continuation: function.entry,
        })?;
    if entry_continuation.params.len() != function.params.len() {
        return Err(CpsReprCraneliftError::UnsupportedFunction {
            function: function.name.clone(),
            reason: "entry continuation parameter arity",
        });
    }
    for ((function_param, continuation_param), value) in function
        .params
        .iter()
        .zip(&entry_continuation.params)
        .zip(params)
    {
        builder.def_var(variable(function_param.value), value);
        if continuation_param.value != function_param.value {
            builder.def_var(variable(continuation_param.value), value);
        }
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

fn lower_stmt<M: Module>(
    module_backend: &mut M,
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
        CpsStmt::FreshGuard { dest, .. } => {
            let value =
                call_i64_helper(module_backend, builder, "yulang_cps_fresh_guard_i64", &[])?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::PeekGuard { dest } => {
            let value = call_i64_helper(module_backend, builder, "yulang_cps_peek_guard_i64", &[])?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::FindGuard { dest, guard } => {
            let guard = read_value(builder, function, *guard)?;
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_find_guard_i64",
                &[guard],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::MakeThunk { dest, entry } => {
            let value = make_thunk(module_backend, builder, function, *entry, functions)?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::ForceThunk { dest, thunk } => {
            let helper = declare_import(
                module_backend,
                builder,
                "yulang_cps_force_thunk_i64",
                &[types::I64],
                types::I64,
            )?;
            let thunk = read_value(builder, function, *thunk)?;
            let call = builder.ins().call(helper, &[thunk]);
            let results = builder.inst_results(call);
            builder.def_var(variable(*dest), results[0]);
        }
        CpsStmt::Tuple { .. }
        | CpsStmt::Record { .. }
        | CpsStmt::Variant { .. }
        | CpsStmt::Select { .. } => {
            return Err(CpsReprCraneliftError::UnsupportedStmt {
                function: function.name.clone(),
                kind: "structural value",
            });
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
            let callee = module_backend.declare_func_in_func(id, builder.func);
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
        CpsStmt::CloneContinuation { dest, source } => {
            let source = read_value(builder, function, *source)?;
            builder.def_var(variable(*dest), source);
        }
        CpsStmt::Resume { .. } | CpsStmt::ResumeWithHandler { .. } => {
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

fn effect_matches(expected: &core_ir::Path, actual: &core_ir::Path) -> bool {
    actual == expected
        || (!expected.segments.is_empty()
            && actual.segments.len() == expected.segments.len() + 1
            && actual.segments.starts_with(&expected.segments))
        || (expected.segments.len() == 1 && actual.segments.last() == expected.segments.first())
}

fn handler_candidates_for_effect(
    function: &CpsReprAbiFunction,
    effect: &core_ir::Path,
) -> CpsReprCraneliftResult<Vec<(CpsHandlerId, CpsContinuationId)>> {
    let mut candidates = Vec::new();
    for handler in &function.handlers {
        if let Some(arm) = handler
            .arms
            .iter()
            .find(|arm| effect_matches(&arm.effect, effect))
        {
            candidates.push((handler.id, arm.entry));
        }
    }
    if candidates.is_empty() {
        Err(CpsReprCraneliftError::UnsupportedTerminator {
            function: function.name.clone(),
            kind: "perform without handler entry",
        })
    } else {
        Ok(candidates)
    }
}

fn handler_mask(
    function: &CpsReprAbiFunction,
    candidates: &[(CpsHandlerId, CpsContinuationId)],
) -> CpsReprCraneliftResult<i64> {
    let mut mask = 0_i64;
    for (handler, _) in candidates {
        if handler.0 >= 62 {
            return Err(CpsReprCraneliftError::UnsupportedFunction {
                function: function.name.clone(),
                reason: "handler id outside scalar handler mask",
            });
        }
        mask |= 1_i64 << handler.0;
    }
    Ok(mask)
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
    for function in &module.functions {
        validate_scalar_function(function, false)?;
    }
    for function in &module.roots {
        validate_scalar_function(function, true)?;
    }
    Ok(())
}

fn validate_scalar_function(
    function: &CpsReprAbiFunction,
    require_scalar_entry_return: bool,
) -> CpsReprCraneliftResult<()> {
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
                CpsStmt::FreshGuard { .. }
                | CpsStmt::PeekGuard { .. }
                | CpsStmt::FindGuard { .. } => {}
                CpsStmt::MakeThunk { .. } | CpsStmt::ForceThunk { .. } => {}
                CpsStmt::Primitive { op, .. } => validate_primitive(function, *op)?,
                CpsStmt::Tuple { .. }
                | CpsStmt::Record { .. }
                | CpsStmt::Variant { .. }
                | CpsStmt::Select { .. } => {
                    return Err(CpsReprCraneliftError::UnsupportedStmt {
                        function: function.name.clone(),
                        kind: "structural value",
                    });
                }
                CpsStmt::DirectCall { .. } | CpsStmt::CloneContinuation { .. } => {}
                CpsStmt::Resume { .. } if has_effect_flow => {}
                CpsStmt::ResumeWithHandler { .. } if has_effect_flow => {}
                CpsStmt::ResumeWithHandler { .. } => {
                    return Err(CpsReprCraneliftError::UnsupportedStmt {
                        function: function.name.clone(),
                        kind: "resume with dynamic handler",
                    });
                }
                CpsStmt::Resume { .. } => {
                    return Err(CpsReprCraneliftError::UnsupportedStmt {
                        function: function.name.clone(),
                        kind: "resume",
                    });
                }
            }
        }
        if require_scalar_entry_return
            && continuation.id == function.entry
            && continuation.return_lane != CpsReprAbiLane::ScalarI64
            && continuation.return_lane != CpsReprAbiLane::ThunkPtr
        {
            return Err(CpsReprCraneliftError::UnsupportedReturnLane {
                function: function.name.clone(),
                continuation: continuation.id,
                lane: continuation.return_lane,
            });
        }
        if continuation.return_lane != CpsReprAbiLane::ScalarI64 {
            match continuation.return_lane {
                CpsReprAbiLane::RuntimeValuePtr
                | CpsReprAbiLane::ThunkPtr
                | CpsReprAbiLane::ResumptionPtr
                | CpsReprAbiLane::Unknown => {}
                lane => {
                    return Err(CpsReprCraneliftError::UnsupportedReturnLane {
                        function: function.name.clone(),
                        continuation: continuation.id,
                        lane,
                    });
                }
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
        CpsReprAbiLane::ScalarI64
        | CpsReprAbiLane::RuntimeValuePtr
        | CpsReprAbiLane::ThunkPtr
        | CpsReprAbiLane::ResumptionPtr
        | CpsReprAbiLane::Unknown => Ok(()),
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
        CpsReprAbiLane::ScalarI64
        | CpsReprAbiLane::RuntimeValuePtr
        | CpsReprAbiLane::ThunkPtr
        | CpsReprAbiLane::ResumptionPtr
        | CpsReprAbiLane::Unknown => Ok(()),
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
                | CpsStmt::FreshGuard { dest, .. }
                | CpsStmt::PeekGuard { dest }
                | CpsStmt::FindGuard { dest, .. }
                | CpsStmt::MakeThunk { dest, .. }
                | CpsStmt::ForceThunk { dest, .. }
                | CpsStmt::Tuple { dest, .. }
                | CpsStmt::Record { dest, .. }
                | CpsStmt::Variant { dest, .. }
                | CpsStmt::Select { dest, .. }
                | CpsStmt::Primitive { dest, .. }
                | CpsStmt::DirectCall { dest, .. }
                | CpsStmt::CloneContinuation { dest, .. }
                | CpsStmt::Resume { dest, .. }
                | CpsStmt::ResumeWithHandler { dest, .. } => values.push(*dest),
            }
        }
    }
    values.sort();
    values.dedup();
    values
}

fn value_is_make_thunk(function: &CpsReprAbiFunction, value: CpsValueId) -> bool {
    function.continuations.iter().any(|continuation| {
        continuation
            .stmts
            .iter()
            .any(|stmt| matches!(stmt, CpsStmt::MakeThunk { dest, .. } if *dest == value))
    })
}

fn value_lane(function: &CpsReprAbiFunction, value: CpsValueId) -> Option<CpsReprAbiLane> {
    for param in &function.params {
        if param.value == value {
            return Some(param.lane);
        }
    }
    for continuation in &function.continuations {
        for param in &continuation.params {
            if param.value == value {
                return Some(param.lane);
            }
        }
        for slot in &continuation.environment {
            if slot.value == value {
                return Some(slot.lane);
            }
        }
    }
    None
}

fn variable(value: CpsValueId) -> Variable {
    Variable::from_u32(value.0 as u32)
}

fn cranelift_error(error: impl fmt::Display) -> CpsReprCraneliftError {
    CpsReprCraneliftError::Cranelift(error.to_string())
}

type NativeCpsI64Continuation = extern "C" fn(*const i64, i64) -> i64;
type NativeCpsI64ThunkEntry = extern "C" fn(*const i64) -> i64;

#[repr(C)]
struct NativeCpsI64Resumption {
    code: NativeCpsI64Continuation,
    env: Box<[i64]>,
    handlers: Box<[NativeCpsI64HandlerFrame]>,
    guard_stack: Box<[i64]>,
}

#[repr(C)]
struct NativeCpsI64Thunk {
    code: NativeCpsI64ThunkEntry,
    env: Box<[i64]>,
    handlers: Box<[NativeCpsI64HandlerFrame]>,
    guard_stack: Box<[i64]>,
}

#[derive(Clone)]
struct NativeCpsI64HandlerFrame {
    handler: i64,
    guard_stack: Box<[i64]>,
    envs: Vec<NativeCpsI64HandlerEnv>,
}

#[derive(Clone)]
struct NativeCpsI64HandlerEnv {
    entry: i64,
    env: i64,
}

thread_local! {
    static NATIVE_CPS_I64_THUNKS: RefCell<HashSet<usize>> = RefCell::new(HashSet::new());
    static NATIVE_CPS_I64_HANDLER_STACK: RefCell<Vec<NativeCpsI64HandlerFrame>> = const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_GUARD_STACK: RefCell<Vec<i64>> = const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_NEXT_GUARD: RefCell<i64> = const { RefCell::new(0) };
    static NATIVE_CPS_I64_PENDING_HANDLER_ENVS: RefCell<Vec<(i64, NativeCpsI64HandlerEnv)>> = const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_SELECTED_HANDLER_ENVS: RefCell<Vec<NativeCpsI64HandlerEnv>> = const { RefCell::new(Vec::new()) };
}

fn reset_native_i64_cps_state() {
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow_mut().clear());
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| stack.borrow_mut().clear());
    NATIVE_CPS_I64_NEXT_GUARD.with(|next| *next.borrow_mut() = 0);
    NATIVE_CPS_I64_PENDING_HANDLER_ENVS.with(|envs| envs.borrow_mut().clear());
    NATIVE_CPS_I64_SELECTED_HANDLER_ENVS.with(|envs| envs.borrow_mut().clear());
}

fn current_native_i64_guard_stack() -> Vec<i64> {
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| stack.borrow().clone())
}

fn current_native_i64_handler_stack_with_fallback(fallback: i64) -> Vec<NativeCpsI64HandlerFrame> {
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        let stack = stack.borrow();
        if stack.is_empty() {
            vec![NativeCpsI64HandlerFrame {
                handler: fallback,
                guard_stack: current_native_i64_guard_stack().into_boxed_slice(),
                envs: Vec::new(),
            }]
        } else {
            stack.clone()
        }
    })
}

fn take_pending_native_i64_handler_frames() -> Vec<NativeCpsI64HandlerFrame> {
    let pending =
        NATIVE_CPS_I64_PENDING_HANDLER_ENVS.with(|envs| std::mem::take(&mut *envs.borrow_mut()));
    let mut frames: Vec<NativeCpsI64HandlerFrame> = Vec::new();
    for (handler, env) in pending {
        if let Some(frame) = frames.iter_mut().find(|frame| frame.handler == handler) {
            frame.envs.push(env);
        } else {
            frames.push(NativeCpsI64HandlerFrame {
                handler,
                guard_stack: current_native_i64_guard_stack().into_boxed_slice(),
                envs: vec![env],
            });
        }
    }
    frames
}

fn take_pending_native_i64_handler_envs(handler: i64) -> Vec<NativeCpsI64HandlerEnv> {
    NATIVE_CPS_I64_PENDING_HANDLER_ENVS.with(|envs| {
        let mut envs = envs.borrow_mut();
        let mut selected = Vec::new();
        let mut index = 0;
        while index < envs.len() {
            if envs[index].0 == handler {
                selected.push(envs.remove(index).1);
            } else {
                index += 1;
            }
        }
        selected
    })
}

fn with_native_i64_cps_state<T>(
    handlers: Vec<NativeCpsI64HandlerFrame>,
    guard_stack: Vec<i64>,
    run: impl FnOnce() -> T,
) -> T {
    let previous_handlers = NATIVE_CPS_I64_HANDLER_STACK
        .with(|stack| std::mem::replace(&mut *stack.borrow_mut(), handlers));
    let previous_guards = NATIVE_CPS_I64_GUARD_STACK
        .with(|stack| std::mem::replace(&mut *stack.borrow_mut(), guard_stack));
    let result = run();
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| *stack.borrow_mut() = previous_handlers);
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| *stack.borrow_mut() = previous_guards);
    result
}

fn make_native_i64_resumption(
    code: usize,
    fallback_handler: i64,
    env: Vec<i64>,
) -> *mut NativeCpsI64Resumption {
    let code = unsafe { std::mem::transmute::<usize, NativeCpsI64Continuation>(code) };
    Box::into_raw(Box::new(NativeCpsI64Resumption {
        code,
        env: env.into_boxed_slice(),
        handlers: current_native_i64_handler_stack_with_fallback(fallback_handler)
            .into_boxed_slice(),
        guard_stack: current_native_i64_guard_stack().into_boxed_slice(),
    }))
}

fn make_native_i64_thunk(code: usize, env: Vec<i64>) -> usize {
    let code = unsafe { std::mem::transmute::<usize, NativeCpsI64ThunkEntry>(code) };
    let mut handlers = NATIVE_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow().clone());
    handlers.extend(take_pending_native_i64_handler_frames());
    let ptr = Box::into_raw(Box::new(NativeCpsI64Thunk {
        code,
        env: env.into_boxed_slice(),
        handlers: handlers.into_boxed_slice(),
        guard_stack: current_native_i64_guard_stack().into_boxed_slice(),
    })) as usize;
    NATIVE_CPS_I64_THUNKS.with(|thunks| {
        thunks.borrow_mut().insert(ptr);
    });
    ptr
}

fn make_native_i64_env(env: Vec<i64>) -> *const i64 {
    Box::leak(env.into_boxed_slice()).as_ptr()
}

extern "C" fn yulang_cps_make_resumption_i64_0(
    code: usize,
    handler: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, handler, Vec::new())
}

extern "C" fn yulang_cps_make_resumption_i64_1(
    code: usize,
    handler: i64,
    a: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, handler, vec![a])
}

extern "C" fn yulang_cps_make_resumption_i64_2(
    code: usize,
    handler: i64,
    a: i64,
    b: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, handler, vec![a, b])
}

extern "C" fn yulang_cps_make_resumption_i64_3(
    code: usize,
    handler: i64,
    a: i64,
    b: i64,
    c: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, handler, vec![a, b, c])
}

extern "C" fn yulang_cps_make_resumption_i64_4(
    code: usize,
    handler: i64,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, handler, vec![a, b, c, d])
}

extern "C" fn yulang_cps_make_env_i64_0() -> *const i64 {
    make_native_i64_env(Vec::new())
}

extern "C" fn yulang_cps_make_env_i64_1(a: i64) -> *const i64 {
    make_native_i64_env(vec![a])
}

extern "C" fn yulang_cps_make_env_i64_2(a: i64, b: i64) -> *const i64 {
    make_native_i64_env(vec![a, b])
}

extern "C" fn yulang_cps_make_env_i64_3(a: i64, b: i64, c: i64) -> *const i64 {
    make_native_i64_env(vec![a, b, c])
}

extern "C" fn yulang_cps_make_env_i64_4(a: i64, b: i64, c: i64, d: i64) -> *const i64 {
    make_native_i64_env(vec![a, b, c, d])
}

extern "C" fn yulang_cps_resume_i64(resumption: *const NativeCpsI64Resumption, arg: i64) -> i64 {
    let resumption = unsafe { &*resumption };
    with_native_i64_cps_state(
        resumption.handlers.to_vec(),
        resumption.guard_stack.to_vec(),
        || (resumption.code)(resumption.env.as_ptr(), arg),
    )
}

extern "C" fn yulang_cps_resume_with_handler_i64(
    resumption: *const NativeCpsI64Resumption,
    arg: i64,
    handler: i64,
) -> i64 {
    let resumption = unsafe { &*resumption };
    let mut handlers = resumption.handlers.to_vec();
    handlers.push(NativeCpsI64HandlerFrame {
        handler,
        guard_stack: current_native_i64_guard_stack().into_boxed_slice(),
        envs: take_pending_native_i64_handler_envs(handler),
    });
    with_native_i64_cps_state(handlers, resumption.guard_stack.to_vec(), || {
        (resumption.code)(resumption.env.as_ptr(), arg)
    })
}

extern "C" fn yulang_cps_select_handler_i64(
    fallback_handler: i64,
    allowed_mask: i64,
    blocked: i64,
) -> i64 {
    let stack = current_native_i64_handler_stack_with_fallback(fallback_handler);
    for (index, frame) in stack.iter().enumerate().rev() {
        let allowed = (allowed_mask & (1_i64 << frame.handler)) != 0;
        if !allowed {
            continue;
        }
        if blocked >= 0 && frame.guard_stack.contains(&blocked) {
            continue;
        }
        NATIVE_CPS_I64_HANDLER_STACK.with(|active| {
            *active.borrow_mut() = stack[..index].to_vec();
        });
        NATIVE_CPS_I64_SELECTED_HANDLER_ENVS.with(|envs| {
            *envs.borrow_mut() = frame.envs.to_vec();
        });
        return frame.handler;
    }
    NATIVE_CPS_I64_SELECTED_HANDLER_ENVS.with(|envs| envs.borrow_mut().clear());
    -1
}

extern "C" fn yulang_cps_capture_handler_env_i64(handler: i64, entry: i64, env: i64) -> i64 {
    NATIVE_CPS_I64_PENDING_HANDLER_ENVS.with(|envs| {
        envs.borrow_mut()
            .push((handler, NativeCpsI64HandlerEnv { entry, env }));
    });
    0
}

extern "C" fn yulang_cps_selected_handler_env_or_i64(entry: i64, fallback: i64) -> i64 {
    NATIVE_CPS_I64_SELECTED_HANDLER_ENVS.with(|envs| {
        envs.borrow()
            .iter()
            .find(|env| env.entry == entry)
            .map(|env| env.env)
            .unwrap_or(fallback)
    })
}

extern "C" fn yulang_cps_make_thunk_i64_0(code: usize) -> usize {
    make_native_i64_thunk(code, Vec::new())
}

extern "C" fn yulang_cps_make_thunk_i64_1(code: usize, a: i64) -> usize {
    make_native_i64_thunk(code, vec![a])
}

extern "C" fn yulang_cps_make_thunk_i64_2(code: usize, a: i64, b: i64) -> usize {
    make_native_i64_thunk(code, vec![a, b])
}

extern "C" fn yulang_cps_make_thunk_i64_3(code: usize, a: i64, b: i64, c: i64) -> usize {
    make_native_i64_thunk(code, vec![a, b, c])
}

extern "C" fn yulang_cps_make_thunk_i64_4(code: usize, a: i64, b: i64, c: i64, d: i64) -> usize {
    make_native_i64_thunk(code, vec![a, b, c, d])
}

extern "C" fn yulang_cps_force_thunk_i64(value: usize) -> i64 {
    let mut value = value;
    loop {
        let is_thunk = NATIVE_CPS_I64_THUNKS.with(|thunks| thunks.borrow().contains(&value));
        if !is_thunk {
            return value as i64;
        }
        let thunk = unsafe { &*(value as *const NativeCpsI64Thunk) };
        value =
            with_native_i64_cps_state(thunk.handlers.to_vec(), thunk.guard_stack.to_vec(), || {
                (thunk.code)(thunk.env.as_ptr())
            }) as usize;
    }
}

extern "C" fn yulang_cps_fresh_guard_i64() -> i64 {
    let id = NATIVE_CPS_I64_NEXT_GUARD.with(|next| {
        let mut next = next.borrow_mut();
        let id = *next;
        *next += 1;
        id
    });
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| {
        stack.borrow_mut().push(id);
    });
    id
}

extern "C" fn yulang_cps_peek_guard_i64() -> i64 {
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| stack.borrow().last().copied().unwrap_or(0))
}

extern "C" fn yulang_cps_find_guard_i64(id: i64) -> i64 {
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| i64::from(stack.borrow().contains(&id)))
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
    fn jit_runs_guard_stack_helpers_without_effect_flow() {
        let abi = guard_stack_abi();
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![1]);
    }

    #[test]
    fn jit_skips_handler_frame_blocked_by_guard_snapshot() {
        let abi = blocked_handler_snapshot_abi();
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![100]);
    }

    #[test]
    fn object_compiles_multishot_resumption_calls() {
        let abi = multishot_resume_effect_abi();
        let object = compile_cps_repr_abi_module_to_object(&abi).expect("compiled");

        assert!(!object.bytes().is_empty());
        assert_eq!(object.roots(), &["root".to_string()]);
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
                        blocked: None,
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

    fn guard_stack_abi() -> CpsReprAbiModule {
        lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
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
                    stmts: vec![
                        CpsStmt::FreshGuard {
                            dest: CpsValueId(0),
                            var: yulang_runtime::EffectIdVar(0),
                        },
                        CpsStmt::PeekGuard {
                            dest: CpsValueId(1),
                        },
                        CpsStmt::FindGuard {
                            dest: CpsValueId(2),
                            guard: CpsValueId(1),
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(2)),
                }],
            }],
        }))
    }

    fn blocked_handler_snapshot_abi() -> CpsReprAbiModule {
        let start = core_ir::Path::from_name(core_ir::Name("start".to_string()));
        let choose = core_ir::Path::from_name(core_ir::Name("choose".to_string()));
        lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: vec![
                    crate::cps_ir::CpsHandler {
                        id: crate::cps_ir::CpsHandlerId(0),
                        arms: vec![
                            crate::cps_ir::CpsHandlerArm {
                                effect: start.clone(),
                                entry: CpsContinuationId(2),
                            },
                            crate::cps_ir::CpsHandlerArm {
                                effect: choose.clone(),
                                entry: CpsContinuationId(5),
                            },
                        ],
                    },
                    crate::cps_ir::CpsHandler {
                        id: crate::cps_ir::CpsHandlerId(1),
                        arms: vec![crate::cps_ir::CpsHandlerArm {
                            effect: choose.clone(),
                            entry: CpsContinuationId(4),
                        }],
                    },
                ],
                continuations: vec![
                    CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("1".to_string()),
                        }],
                        terminator: CpsTerminator::Perform {
                            effect: start,
                            payload: CpsValueId(0),
                            resume: CpsContinuationId(1),
                            handler: crate::cps_ir::CpsHandlerId(0),
                            blocked: None,
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(1)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(2),
                            literal: CpsLiteral::Int("0".to_string()),
                        }],
                        terminator: CpsTerminator::Perform {
                            effect: choose.clone(),
                            payload: CpsValueId(2),
                            resume: CpsContinuationId(3),
                            handler: crate::cps_ir::CpsHandlerId(0),
                            blocked: Some(CpsValueId(1)),
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(2),
                        params: vec![CpsValueId(3), CpsValueId(4)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![
                            CpsStmt::FreshGuard {
                                dest: CpsValueId(5),
                                var: yulang_runtime::EffectIdVar(0),
                            },
                            CpsStmt::ResumeWithHandler {
                                dest: CpsValueId(6),
                                resumption: CpsValueId(4),
                                arg: CpsValueId(5),
                                handler: crate::cps_ir::CpsHandlerId(1),
                                envs: Vec::new(),
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(6)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(3),
                        params: vec![CpsValueId(7)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(7)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(4),
                        params: vec![CpsValueId(8), CpsValueId(9)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(10),
                            literal: CpsLiteral::Int("200".to_string()),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(10)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(5),
                        params: vec![CpsValueId(11), CpsValueId(12)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(13),
                            literal: CpsLiteral::Int("100".to_string()),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(13)),
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
                    arms: vec![crate::cps_ir::CpsHandlerArm {
                        effect: effect.clone(),
                        entry: CpsContinuationId(2),
                    }],
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
                            blocked: None,
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
                    arms: vec![crate::cps_ir::CpsHandlerArm {
                        effect: effect.clone(),
                        entry: CpsContinuationId(2),
                    }],
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
                            blocked: None,
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
                            CpsStmt::CloneContinuation {
                                dest: CpsValueId(9),
                                source: CpsValueId(5),
                            },
                            CpsStmt::Resume {
                                dest: CpsValueId(6),
                                resumption: CpsValueId(5),
                                arg: CpsValueId(4),
                            },
                            CpsStmt::Resume {
                                dest: CpsValueId(7),
                                resumption: CpsValueId(9),
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
