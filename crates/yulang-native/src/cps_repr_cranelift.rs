use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fmt;

use cranelift_codegen::ir::{self, AbiParam, InstBuilder, types};
use cranelift_codegen::settings;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use yulang_runtime as runtime;
use yulang_runtime::runtime::bytes_tree::BytesTree;
use yulang_typed_ir as typed_ir;

use crate::cps_ir::{
    CpsContinuationId, CpsHandlerId, CpsLiteral, CpsRecordField, CpsStmt, CpsTerminator, CpsValueId,
};
use crate::cps_lower::{CpsLowerError, lower_cps_module};
use crate::cps_optimize::{
    CpsOptimizationOutput, CpsOptimizationProfile, optimize_cps_repr_abi_module,
};
use crate::cps_repr::CpsReprAbiLane;
use crate::cps_repr_abi::{
    CpsReprAbiContinuation, CpsReprAbiFunction, CpsReprAbiModule, CpsReprAbiValue,
    lower_cps_repr_abi_module,
};
use crate::cps_validate::{CpsValidateError, validate_cps_module};

mod helper_arity;
mod runtime_symbols;

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
        op: typed_ir::PrimitiveOp,
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
    root_display_hints: Vec<CpsRootDisplayHint>,
    root_function_ids: Vec<u64>,
    cranelift_ir: Vec<String>,
    optimization_profile: CpsOptimizationProfile,
    _strings: Vec<Box<str>>,
}

impl CpsReprJitModule {
    pub fn cranelift_ir(&self) -> &[String] {
        &self.cranelift_ir
    }

    pub fn optimization_profile(&self) -> CpsOptimizationProfile {
        self.optimization_profile
    }

    pub fn run_roots_display(&mut self) -> CpsReprCraneliftResult<Vec<String>> {
        self.module
            .finalize_definitions()
            .map_err(cranelift_error)?;
        self.roots
            .iter()
            .zip(self.root_display_hints.iter().copied())
            .map(|(root, hint)| {
                reset_native_i64_cps_state();
                set_native_i64_root_function_ids(&self.root_function_ids);
                let ptr = self.module.get_finalized_function(*root);
                let call = unsafe { std::mem::transmute::<_, extern "C" fn() -> i64>(ptr) };
                let value = take_native_i64_root_result(call());
                Ok(describe_cps_repr_i64_value_with_hint(value, hint))
            })
            .collect()
    }

    pub fn run_roots_i64(&mut self) -> CpsReprCraneliftResult<Vec<i64>> {
        self.module
            .finalize_definitions()
            .map_err(cranelift_error)?;
        self.roots
            .iter()
            .map(|root| {
                reset_native_i64_cps_state();
                set_native_i64_root_function_ids(&self.root_function_ids);
                let ptr = self.module.get_finalized_function(*root);
                let call = unsafe { std::mem::transmute::<_, extern "C" fn() -> i64>(ptr) };
                let value = call();
                Ok(take_native_i64_root_result(value))
            })
            .collect()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CpsRootDisplayHint {
    Plain,
    Unit,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprObjectModule {
    bytes: Vec<u8>,
    roots: Vec<String>,
    root_lanes: Vec<CpsReprAbiLane>,
    root_function_ids: Vec<u64>,
    optimization_profile: CpsOptimizationProfile,
}

impl CpsReprObjectModule {
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn roots(&self) -> &[String] {
        &self.roots
    }

    pub fn root_lanes(&self) -> &[CpsReprAbiLane] {
        &self.root_lanes
    }

    pub fn root_function_ids(&self) -> &[u64] {
        &self.root_function_ids
    }

    pub fn optimization_profile(&self) -> CpsOptimizationProfile {
        self.optimization_profile
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }
}

pub fn compile_cps_repr_abi_module(
    module: &CpsReprAbiModule,
) -> CpsReprCraneliftResult<CpsReprJitModule> {
    compile_cps_repr_abi_module_with_root_hints(module, Vec::new())
}

fn compile_cps_repr_abi_module_with_root_hints(
    module: &CpsReprAbiModule,
    root_display_hints: Vec<CpsRootDisplayHint>,
) -> CpsReprCraneliftResult<CpsReprJitModule> {
    let optimized = if std::env::var_os("YULANG_CPS_JIT_DISABLE_OPT").is_some() {
        CpsOptimizationOutput {
            module: module.clone(),
            profile: CpsOptimizationProfile::default(),
        }
    } else {
        optimize_cps_repr_abi_module(module)
    };
    let module = &optimized.module;
    validate_scalar_subset(module)?;

    let mut builder =
        JITBuilder::new(cranelift_module::default_libcall_names()).map_err(cranelift_error)?;
    runtime_symbols::register_cps_runtime_symbols(&mut builder);
    let mut jit = JITModule::new(builder);
    let functions = declare_functions(&mut jit, module)?;
    let mut strings = Vec::new();
    let mut literals = HostLiteralStore {
        strings: &mut strings,
    };
    let cranelift_ir = define_functions(&mut jit, module, &functions, &mut literals)?;
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
    let root_display_hints = root_display_hints_for_len(root_display_hints, roots.len());
    let root_function_ids = module
        .roots
        .iter()
        .filter_map(|root| functions.function_ids.get(&root.name).copied())
        .collect::<Vec<_>>();
    Ok(CpsReprJitModule {
        module: jit,
        roots,
        root_display_hints,
        root_function_ids,
        cranelift_ir,
        optimization_profile: optimized.profile,
        _strings: strings,
    })
}

pub fn compile_cps_repr_abi_module_to_object(
    module: &CpsReprAbiModule,
) -> CpsReprCraneliftResult<CpsReprObjectModule> {
    let optimized = if std::env::var_os("YULANG_CPS_JIT_DISABLE_OPT").is_some() {
        CpsOptimizationOutput {
            module: module.clone(),
            profile: CpsOptimizationProfile::default(),
        }
    } else {
        optimize_cps_repr_abi_module(module)
    };
    let module = &optimized.module;
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
    let mut literals = ObjectLiteralStore::default();
    let _ = define_functions(&mut object, module, &functions, &mut literals)?;
    let roots = module
        .roots
        .iter()
        .map(|root| root.name.clone())
        .collect::<Vec<_>>();
    let root_lanes = module
        .roots
        .iter()
        .map(|root| {
            functions
                .function_returns
                .get(&root.name)
                .copied()
                .unwrap_or(CpsReprAbiLane::Unknown)
        })
        .collect::<Vec<_>>();
    let root_function_ids = module
        .roots
        .iter()
        .filter_map(|root| functions.function_ids.get(&root.name).copied())
        .collect::<Vec<_>>();
    let product = object.finish();
    let bytes = product.emit().map_err(cranelift_error)?;
    Ok(CpsReprObjectModule {
        bytes,
        roots,
        root_lanes,
        root_function_ids,
        optimization_profile: optimized.profile,
    })
}

pub fn compile_runtime_module_to_cps_repr_jit(
    module: &runtime::Module,
) -> CpsReprCraneliftResult<CpsReprJitModule> {
    let root_display_hints = runtime_root_display_hints(module);
    let cps = lower_cps_module(module)?;
    validate_cps_module(&cps)?;
    let repr = crate::cps_repr::lower_cps_repr_module(&cps);
    let abi = lower_cps_repr_abi_module(&repr);
    compile_cps_repr_abi_module_with_root_hints(&abi, root_display_hints)
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
    let mut function_ids = HashMap::new();
    let mut function_returns = HashMap::new();
    let mut function_params = HashMap::new();
    let mut function_effect_flow = HashMap::new();
    for (index, function) in module.functions.iter().chain(&module.roots).enumerate() {
        let sig = function_signature(module_backend, function);
        let id = module_backend
            .declare_function(&function.name, Linkage::Export, &sig)
            .map_err(cranelift_error)?;
        functions.insert(function.name.clone(), id);
        let function_id = (index + 1) as u64;
        function_ids.insert(function.name.clone(), function_id);
        if jit_trace_enabled() {
            eprintln!("[JIT-CPS] function_id: {} {}", function_id, function.name);
        }
        let has_effect_flow = function_has_effect_flow(function);
        function_effect_flow.insert(function.name.clone(), has_effect_flow);
        function_returns.insert(
            function.name.clone(),
            continuation(function, function.entry)
                .map(|entry| effective_continuation_return_lane(function, entry))
                .unwrap_or(CpsReprAbiLane::Unknown),
        );
        function_params.insert(
            function.name.clone(),
            effective_function_param_lanes(function),
        );
        if has_effect_flow {
            for continuation in &function.continuations {
                let name = continuation_symbol(function, continuation.id);
                let sig = continuation_signature(module_backend, function, continuation);
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
        function_ids,
        function_returns,
        function_params,
        function_effect_flow,
    })
}

fn root_display_hints_for_len(
    mut hints: Vec<CpsRootDisplayHint>,
    root_len: usize,
) -> Vec<CpsRootDisplayHint> {
    hints.resize(root_len, CpsRootDisplayHint::Plain);
    hints.truncate(root_len);
    hints
}

fn runtime_root_display_hints(module: &runtime::Module) -> Vec<CpsRootDisplayHint> {
    module
        .roots
        .iter()
        .map(|root| match root {
            runtime::Root::Expr(index) => module
                .root_exprs
                .get(*index)
                .map(|expr| root_display_hint_for_runtime_type(&expr.ty))
                .unwrap_or(CpsRootDisplayHint::Plain),
            runtime::Root::Binding(_) => CpsRootDisplayHint::Plain,
        })
        .collect()
}

fn root_display_hint_for_runtime_type(ty: &runtime::Type) -> CpsRootDisplayHint {
    match ty {
        runtime::Type::Core(core) if core_type_is_unit(core) => CpsRootDisplayHint::Unit,
        _ => CpsRootDisplayHint::Plain,
    }
}

fn core_type_is_unit(ty: &typed_ir::Type) -> bool {
    matches!(
        ty,
        typed_ir::Type::Named { path, args }
            if args.is_empty()
                && path.segments.len() == 1
                && path.segments[0].0 == "unit"
    )
}

fn define_functions<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    module: &CpsReprAbiModule,
    functions: &DeclaredFunctions,
    literals: &mut L,
) -> CpsReprCraneliftResult<Vec<String>> {
    let mut cranelift_ir = Vec::new();
    let handlers = HandlerRegistry::new(module);
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
                &handlers,
                literals,
            )?);
        }
        let mut ctx = module_backend.make_context();
        ctx.func.signature = function_signature(module_backend, function);
        if function_has_effect_flow(function) {
            lower_effectful_function_wrapper(module_backend, &mut ctx, function, functions)?;
        } else {
            lower_function(module_backend, &mut ctx, function, functions, literals)?;
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
    function_ids: HashMap<String, u64>,
    function_returns: HashMap<String, CpsReprAbiLane>,
    function_params: HashMap<String, Vec<CpsReprAbiLane>>,
    function_effect_flow: HashMap<String, bool>,
}

#[derive(Debug, Clone)]
struct HandlerCandidate {
    handler: CpsHandlerId,
    function: String,
    entry: CpsContinuationId,
    continues_to_installed_escape: bool,
}

#[derive(Debug, Clone, Default)]
struct HandlerRegistry {
    candidates: Vec<(typed_ir::Path, HandlerCandidate)>,
    effects: Vec<typed_ir::Path>,
}

#[derive(Debug, Default)]
struct LocalValueCache {
    native_float: HashMap<CpsValueId, ir::Value>,
}

use self::helper_arity::{
    EFFECTFUL_APPLY_RESUMPTION_HELPERS, INSTALL_HANDLER_FULL_HELPERS, MAKE_CLOSURE_HELPERS,
    MAKE_ENV_HELPERS, MAKE_RECURSIVE_CLOSURE_HELPERS, MAKE_RESUMPTION_HELPERS, MAKE_THUNK_HELPERS,
    PUSH_RETURN_FRAME_HELPERS, TUPLE_HELPERS,
};

struct CpsCraneliftLowerCx<'a, 'builder, M: Module, L: CpsLiteralStore> {
    module_backend: &'a mut M,
    builder: &'a mut FunctionBuilder<'builder>,
    function: &'a CpsReprAbiFunction,
    functions: &'a DeclaredFunctions,
    handlers: &'a HandlerRegistry,
    literals: &'a mut L,
    values: &'a mut LocalValueCache,
}

struct PerformTerminatorCase<'a> {
    effect: &'a typed_ir::Path,
    payload: CpsValueId,
    resume: CpsContinuationId,
    handler: CpsHandlerId,
    blocked: Option<CpsValueId>,
}

struct EffectfulCallTerminatorCase<'a> {
    target: &'a str,
    args: &'a [CpsValueId],
    resume: CpsContinuationId,
}

struct EffectfulForceTerminatorCase {
    thunk: CpsValueId,
    resume: CpsContinuationId,
}

struct EffectfulApplyTerminatorCase {
    closure: CpsValueId,
    arg: CpsValueId,
    resume: CpsContinuationId,
}

impl HandlerRegistry {
    fn new(module: &CpsReprAbiModule) -> Self {
        let candidates = module
            .functions
            .iter()
            .chain(&module.roots)
            .flat_map(|function| {
                function.handlers.iter().flat_map(|handler| {
                    handler.arms.iter().map(|arm| {
                        (
                            arm.effect.clone(),
                            HandlerCandidate {
                                handler: handler.id,
                                function: function.name.clone(),
                                entry: arm.entry,
                                continues_to_installed_escape:
                                    handler_arm_continues_to_installed_escape(
                                        function, handler.id, arm.entry,
                                    ) || handler_arm_uses_resume_with_handler(function, arm.entry),
                            },
                        )
                    })
                })
            })
            .collect::<Vec<_>>();
        let mut effects = Vec::new();
        for (effect, _) in &candidates {
            if !effects.iter().any(|existing| existing == effect) {
                effects.push(effect.clone());
            }
        }
        Self {
            candidates,
            effects,
        }
    }

    fn candidates_for_effect(&self, effect: &typed_ir::Path) -> Vec<HandlerCandidate> {
        self.candidates
            .iter()
            .filter(|(expected, _)| effect_matches(expected, effect))
            .map(|(_, candidate)| candidate.clone())
            .collect()
    }

    fn effect_mask(
        &self,
        function: &CpsReprAbiFunction,
        effect: &typed_ir::Path,
    ) -> CpsReprCraneliftResult<i64> {
        let mut mask = 0_i64;
        for (index, registered) in self.effects.iter().enumerate() {
            if index >= 62 {
                return Err(CpsReprCraneliftError::UnsupportedFunction {
                    function: function.name.clone(),
                    reason: "effect id outside scalar boundary mask",
                });
            }
            if effect_matches(registered, effect) {
                mask |= 1_i64 << index;
            }
        }
        Ok(mask)
    }

    fn handler_consumes_mask(
        &self,
        function: &CpsReprAbiFunction,
        handler: CpsHandlerId,
    ) -> CpsReprCraneliftResult<i64> {
        let mut mask = 0_i64;
        for candidate in self
            .candidates
            .iter()
            .filter(|(_, candidate)| candidate.handler == handler)
            .map(|(effect, _)| effect)
        {
            mask |= self.effect_mask(function, candidate)?;
        }
        Ok(mask)
    }

    fn allowed_mask(
        &self,
        function: &CpsReprAbiFunction,
        allowed: &typed_ir::Type,
    ) -> CpsReprCraneliftResult<i64> {
        if matches!(allowed, typed_ir::Type::Any) {
            return Ok(-1);
        }
        let mut mask = 0_i64;
        for (index, effect) in self.effects.iter().enumerate() {
            if index >= 62 {
                return Err(CpsReprCraneliftError::UnsupportedFunction {
                    function: function.name.clone(),
                    reason: "effect id outside scalar boundary mask",
                });
            }
            if effect_allowed_by_type(allowed, effect) {
                mask |= 1_i64 << index;
            }
        }
        Ok(mask)
    }
}

fn define_effectful_function<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    function: &CpsReprAbiFunction,
    functions: &DeclaredFunctions,
    handlers: &HandlerRegistry,
    literals: &mut L,
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
        ctx.func.signature = continuation_signature(module_backend, function, continuation);
        lower_continuation_function(
            module_backend,
            &mut ctx,
            function,
            continuation,
            functions,
            handlers,
            literals,
        )?;
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
                || matches!(
                    continuation.terminator,
                    CpsTerminator::Perform { .. }
                        | CpsTerminator::EffectfulCall { .. }
                        | CpsTerminator::EffectfulApply { .. }
                        | CpsTerminator::EffectfulForce { .. }
                )
                || continuation.stmts.iter().any(|stmt| {
                    matches!(
                        stmt,
                        CpsStmt::MakeClosure { .. }
                            | CpsStmt::MakeRecursiveClosure { .. }
                            | CpsStmt::Resume { .. }
                            | CpsStmt::ResumeWithHandler { .. }
                            | CpsStmt::InstallHandler { .. }
                            | CpsStmt::UninstallHandler { .. }
                            // Thunks introduce additional continuations
                            // (the thunk body) that the scalar path cannot
                            // discover from a single Cranelift block.
                            | CpsStmt::MakeThunk { .. }
                            | CpsStmt::AddThunkBoundary { .. }
                            | CpsStmt::ForceThunk { .. }
                    )
                })
        })
}

fn continuation_signature<M: Module>(
    module_backend: &M,
    function: &CpsReprAbiFunction,
    continuation: &CpsReprAbiContinuation,
) -> ir::Signature {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.extend(
        continuation
            .params
            .iter()
            .map(|param| AbiParam::new(lane_type(effective_value_lane(function, param.value)))),
    );
    sig.returns.push(AbiParam::new(lane_type(
        effective_continuation_return_lane(function, continuation),
    )));
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
    continuation_func_ref_by_name(module_backend, builder, &function.name, id, functions).map_err(
        |error| match error {
            CpsReprCraneliftError::MissingContinuation { continuation, .. } => {
                CpsReprCraneliftError::MissingContinuation {
                    function: function.name.clone(),
                    continuation,
                }
            }
            error => error,
        },
    )
}

fn function_runtime_id(
    function: &CpsReprAbiFunction,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<u64> {
    functions
        .function_ids
        .get(&function.name)
        .copied()
        .ok_or_else(|| CpsReprCraneliftError::MissingFunction {
            name: function.name.clone(),
        })
}

fn continuation_func_ref_by_name<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &str,
    id: CpsContinuationId,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<ir::FuncRef> {
    let id = functions
        .continuations
        .get(&(function.to_string(), id))
        .copied()
        .ok_or_else(|| CpsReprCraneliftError::MissingContinuation {
            function: function.to_string(),
            continuation: id,
        })?;
    Ok(module_backend.declare_func_in_func(id, builder.func))
}

fn lower_continuation_function<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    ctx: &mut cranelift_codegen::Context,
    function: &CpsReprAbiFunction,
    continuation: &CpsReprAbiContinuation,
    functions: &DeclaredFunctions,
    handlers: &HandlerRegistry,
    literals: &mut L,
) -> CpsReprCraneliftResult<()> {
    let direct_island = direct_style_island_from(function, continuation.id);
    if direct_island.len() > 1 {
        return lower_direct_style_continuation_island(
            module_backend,
            ctx,
            function,
            continuation,
            functions,
            literals,
            &direct_island,
        );
    }

    let mut builder_context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_context);
    let block = builder.create_block();
    builder.append_block_params_for_function_params(block);
    builder.switch_to_block(block);
    declare_variables(&mut builder, function);
    let mut values = LocalValueCache::default();

    let params = builder.block_params(block).to_vec();
    let Some(env_ptr) = params.first().copied() else {
        return Err(CpsReprCraneliftError::UnsupportedFunction {
            function: function.name.clone(),
            reason: "continuation function without environment pointer",
        });
    };
    bind_environment_slots(&mut builder, function, continuation, env_ptr)?;
    for (param, value) in continuation.params.iter().zip(params.iter().skip(1)) {
        define_value_as_lane(
            &mut builder,
            &mut values,
            param.value,
            effective_value_lane(function, param.value),
            *value,
        );
    }

    {
        let mut defined_values = continuation
            .environment
            .iter()
            .map(|slot| slot.value)
            .chain(continuation.params.iter().map(|param| param.value))
            .collect::<HashSet<_>>();
        let mut lower_cx = CpsCraneliftLowerCx {
            module_backend,
            builder: &mut builder,
            function,
            functions,
            handlers,
            literals,
            values: &mut values,
        };
        for stmt in &continuation.stmts {
            capture_handler_envs_for_stmt(
                lower_cx.module_backend,
                lower_cx.builder,
                function,
                stmt,
                &defined_values,
            )?;
            lower_effect_stmt(&mut lower_cx, stmt)?;
            if let Some(dest) = stmt_dest(stmt) {
                defined_values.insert(dest);
            }
        }
        lower_effect_terminator(&mut lower_cx, continuation)?;
        lower_cx.builder.seal_all_blocks();
    }
    builder.finalize();
    Ok(())
}

fn lower_direct_style_continuation_island<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    ctx: &mut cranelift_codegen::Context,
    function: &CpsReprAbiFunction,
    entry_continuation: &CpsReprAbiContinuation,
    functions: &DeclaredFunctions,
    literals: &mut L,
    island: &HashSet<CpsContinuationId>,
) -> CpsReprCraneliftResult<()> {
    let mut builder_context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_context);
    let blocks =
        create_direct_style_island_blocks(&mut builder, function, entry_continuation, island);
    declare_variables(&mut builder, function);
    let mut values = LocalValueCache::default();

    let entry_block = continuation_block(function, &blocks, entry_continuation.id)?;
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);
    let params = builder.block_params(entry_block).to_vec();
    for (param, value) in entry_continuation.params.iter().zip(params.iter().skip(1)) {
        define_value_as_lane(
            &mut builder,
            &mut values,
            param.value,
            effective_value_lane(function, param.value),
            *value,
        );
    }

    for continuation in function
        .continuations
        .iter()
        .filter(|continuation| island.contains(&continuation.id))
    {
        let block = continuation_block(function, &blocks, continuation.id)?;
        builder.switch_to_block(block);
        if continuation.id != entry_continuation.id {
            bind_continuation_params(&mut builder, function, continuation, block, &mut values)?;
        }
        for stmt in &continuation.stmts {
            lower_stmt(
                module_backend,
                &mut builder,
                function,
                stmt,
                functions,
                literals,
                &mut values,
            )?;
        }
        lower_direct_style_island_terminator(
            module_backend,
            &mut builder,
            function,
            &blocks,
            continuation,
            &continuation.terminator,
            functions,
            literals,
            &mut values,
            island,
        )?;
    }

    builder.seal_all_blocks();
    builder.finalize();
    Ok(())
}

fn create_direct_style_island_blocks(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    entry_continuation: &CpsReprAbiContinuation,
    island: &HashSet<CpsContinuationId>,
) -> HashMap<CpsContinuationId, ir::Block> {
    function
        .continuations
        .iter()
        .filter(|continuation| island.contains(&continuation.id))
        .map(|continuation| {
            let block = builder.create_block();
            if continuation.id != entry_continuation.id {
                for param in &continuation.params {
                    builder.append_block_param(
                        block,
                        lane_type(effective_value_lane(function, param.value)),
                    );
                }
            }
            (continuation.id, block)
        })
        .collect()
}

fn lower_direct_style_island_terminator<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    blocks: &HashMap<CpsContinuationId, ir::Block>,
    continuation: &CpsReprAbiContinuation,
    terminator: &CpsTerminator,
    functions: &DeclaredFunctions,
    literals: &mut L,
    values: &mut LocalValueCache,
    island: &HashSet<CpsContinuationId>,
) -> CpsReprCraneliftResult<()> {
    match terminator {
        CpsTerminator::Continue { target, args } if island.contains(target) => {
            let target_continuation = lookup_continuation(function, *target)?;
            let target = continuation_block(function, blocks, *target)?;
            let args = read_block_args(builder, function, values, target_continuation, args)?;
            builder.ins().jump(target, &args);
            Ok(())
        }
        CpsTerminator::Branch {
            cond,
            then_cont,
            else_cont,
        } if island.contains(then_cont) && island.contains(else_cont) => {
            let cond = read_value(builder, function, *cond)?;
            let cond = builder
                .ins()
                .icmp_imm(ir::condcodes::IntCC::NotEqual, cond, 0);
            let then_cont = continuation_block(function, blocks, *then_cont)?;
            let else_cont = continuation_block(function, blocks, *else_cont)?;
            builder.ins().brif(cond, then_cont, &[], else_cont, &[]);
            Ok(())
        }
        _ => {
            let handlers = HandlerRegistry::default();
            let mut cx = CpsCraneliftLowerCx {
                module_backend,
                builder,
                function,
                functions,
                handlers: &handlers,
                literals,
                values,
            };
            lower_effect_terminator(&mut cx, continuation)
        }
    }
}

fn direct_style_island_from(
    function: &CpsReprAbiFunction,
    start: CpsContinuationId,
) -> HashSet<CpsContinuationId> {
    let candidates = function
        .continuations
        .iter()
        .filter(|continuation| direct_style_codegen_candidate(continuation))
        .map(|continuation| continuation.id)
        .collect::<HashSet<_>>();
    if !candidates.contains(&start) {
        return HashSet::new();
    }

    let continuations = function
        .continuations
        .iter()
        .map(|continuation| (continuation.id, continuation))
        .collect::<HashMap<_, _>>();
    let mut island = HashSet::new();
    let mut work = vec![start];
    island.insert(start);

    while let Some(id) = work.pop() {
        let Some(continuation) = continuations.get(&id) else {
            continue;
        };
        for successor in direct_style_codegen_successors(&continuation.terminator) {
            if candidates.contains(&successor) && island.insert(successor) {
                work.push(successor);
            }
        }
    }

    island
}

fn direct_style_codegen_candidate(continuation: &CpsReprAbiContinuation) -> bool {
    continuation.environment.is_empty()
        && continuation.stmts.iter().all(direct_style_codegen_stmt)
        && matches!(
            continuation.terminator,
            CpsTerminator::Return(_)
                | CpsTerminator::Continue { .. }
                | CpsTerminator::Branch { .. }
        )
}

fn direct_style_codegen_stmt(stmt: &CpsStmt) -> bool {
    matches!(
        stmt,
        CpsStmt::Literal { .. }
            | CpsStmt::Tuple { .. }
            | CpsStmt::Record { .. }
            | CpsStmt::RecordWithoutFields { .. }
            | CpsStmt::Variant { .. }
            | CpsStmt::Select { .. }
            | CpsStmt::SelectWithDefault { .. }
            | CpsStmt::RecordHasField { .. }
            | CpsStmt::TupleGet { .. }
            | CpsStmt::VariantTagEq { .. }
            | CpsStmt::VariantPayload { .. }
            | CpsStmt::Primitive { .. }
            | CpsStmt::DirectCall { .. }
    )
}

fn direct_style_codegen_successors(terminator: &CpsTerminator) -> Vec<CpsContinuationId> {
    match terminator {
        CpsTerminator::Continue { target, .. } => vec![*target],
        CpsTerminator::Branch {
            then_cont,
            else_cont,
            ..
        } => vec![*then_cont, *else_cont],
        CpsTerminator::Return(_)
        | CpsTerminator::Perform { .. }
        | CpsTerminator::EffectfulCall { .. }
        | CpsTerminator::EffectfulApply { .. }
        | CpsTerminator::EffectfulForce { .. } => Vec::new(),
    }
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
    if !matches!(
        stmt,
        CpsStmt::MakeThunk { .. }
            | CpsStmt::AddThunkBoundary { .. }
            | CpsStmt::MakeClosure { .. }
            | CpsStmt::MakeRecursiveClosure { .. }
            | CpsStmt::ForceThunk { .. }
    ) || function.handlers.is_empty()
    {
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
            let entry = continuation(function, arm.entry)?;
            let env =
                continuation_environment_argument(module_backend, builder, function, arm.entry)?;
            let slots = entry
                .environment
                .iter()
                .map(|slot| {
                    validate_environment_lane(function, slot.value, slot.lane)?;
                    Ok((slot.value, read_value(builder, function, slot.value)?))
                })
                .collect::<CpsReprCraneliftResult<Vec<_>>>()?;
            let handler = builder.ins().iconst(types::I64, handler.id.0 as i64);
            let entry = builder.ins().iconst(types::I64, arm.entry.0 as i64);
            capture_handler_env(module_backend, builder, handler, entry, env, &slots)?;
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
        let (env_ptr, slots) = handler_env_argument(module_backend, builder, function, env)?;
        let handler = builder.ins().iconst(types::I64, handler.0 as i64);
        let entry = builder.ins().iconst(types::I64, env.entry.0 as i64);
        capture_handler_env(module_backend, builder, handler, entry, env_ptr, &slots)?;
    }
    Ok(())
}

fn handler_env_argument<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    env: &crate::cps_ir::CpsHandlerEnv,
) -> CpsReprCraneliftResult<(ir::Value, Vec<(CpsValueId, ir::Value)>)> {
    let mut slots = Vec::with_capacity(env.values.len());
    for (index, value) in env.values.iter().enumerate() {
        let target = env.targets.get(index).copied().unwrap_or(*value);
        slots.push((target, read_value(builder, function, *value)?));
    }

    if env.targets.is_empty() {
        if env.values.len() > 4 {
            return Err(CpsReprCraneliftError::UnsupportedStmt {
                function: function.name.clone(),
                kind: "handler environment larger than four slots",
            });
        }
        let values = read_values(builder, function, &env.values)?;
        let env = make_env(module_backend, builder, function, &values)?;
        return Ok((env, slots));
    }

    if env.values.len() != env.targets.len() {
        return Err(CpsReprCraneliftError::UnsupportedStmt {
            function: function.name.clone(),
            kind: "handler environment target/value arity mismatch",
        });
    }
    let target = continuation(function, env.entry)?;
    if target.environment.len() > 4 {
        return Err(CpsReprCraneliftError::UnsupportedStmt {
            function: function.name.clone(),
            kind: "handler environment larger than four slots",
        });
    }

    let mut values = Vec::with_capacity(target.environment.len());
    for slot in &target.environment {
        validate_environment_lane(function, slot.value, slot.lane)?;
        let source = env
            .targets
            .iter()
            .position(|target| *target == slot.value)
            .map(|index| env.values[index])
            .unwrap_or(slot.value);
        values.push(read_value(builder, function, source)?);
    }
    let env = make_env(module_backend, builder, function, &values)?;
    Ok((env, slots))
}

fn capture_handler_env<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    handler: ir::Value,
    entry: ir::Value,
    env: ir::Value,
    slots: &[(CpsValueId, ir::Value)],
) -> CpsReprCraneliftResult<()> {
    let targets = slots
        .iter()
        .map(|(target, _)| builder.ins().iconst(types::I64, target.0 as i64))
        .collect::<Vec<_>>();
    let values = slots.iter().map(|(_, value)| *value).collect::<Vec<_>>();
    let (target_ptr, target_len) = stack_i64_slice(builder, &targets)?;
    let (value_ptr, value_len) = stack_i64_slice(builder, &values)?;
    let _ = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_capture_handler_env_mapped_i64",
        &[
            handler, entry, env, target_ptr, value_ptr, target_len, value_len,
        ],
    )?;
    Ok(())
}

fn lower_effect_stmt<M: Module, L: CpsLiteralStore>(
    cx: &mut CpsCraneliftLowerCx<'_, '_, M, L>,
    stmt: &CpsStmt,
) -> CpsReprCraneliftResult<()> {
    match stmt {
        CpsStmt::Literal { .. }
        | CpsStmt::Tuple { .. }
        | CpsStmt::Record { .. }
        | CpsStmt::RecordWithoutFields { .. }
        | CpsStmt::Select { .. }
        | CpsStmt::SelectWithDefault { .. }
        | CpsStmt::RecordHasField { .. }
        | CpsStmt::Variant { .. }
        | CpsStmt::TupleGet { .. }
        | CpsStmt::VariantTagEq { .. }
        | CpsStmt::VariantPayload { .. }
        | CpsStmt::Primitive { .. } => lower_value_stmt(cx, stmt),
        CpsStmt::FreshGuard { .. }
        | CpsStmt::PeekGuard { .. }
        | CpsStmt::FindGuard { .. }
        | CpsStmt::MakeThunk { .. }
        | CpsStmt::AddThunkBoundary { .. }
        | CpsStmt::MakeClosure { .. }
        | CpsStmt::MakeRecursiveClosure { .. }
        | CpsStmt::ForceThunk { .. } => lower_runtime_value_stmt(cx, stmt),
        CpsStmt::DirectCall { .. }
        | CpsStmt::ApplyClosure { .. }
        | CpsStmt::CloneContinuation { .. }
        | CpsStmt::Resume { .. }
        | CpsStmt::ResumeWithHandler { .. } => lower_call_stmt_case(cx, stmt),
        CpsStmt::InstallHandler { .. } | CpsStmt::UninstallHandler { .. } => {
            lower_handler_stmt_case(cx, stmt)
        }
    }
}

fn lower_value_stmt<M: Module, L: CpsLiteralStore>(
    cx: &mut CpsCraneliftLowerCx<'_, '_, M, L>,
    stmt: &CpsStmt,
) -> CpsReprCraneliftResult<()> {
    lower_value_stmt_parts(
        cx.module_backend,
        cx.builder,
        cx.function,
        stmt,
        cx.literals,
        cx.values,
    )
}

fn lower_value_stmt_parts<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    stmt: &CpsStmt,
    literals: &mut L,
    values: &mut LocalValueCache,
) -> CpsReprCraneliftResult<()> {
    match stmt {
        CpsStmt::Literal { dest, literal } => {
            let value = lower_literal(module_backend, builder, function, literal, literals)?;
            if matches!(literal, CpsLiteral::Float(_)) {
                define_value_as_lane(builder, values, *dest, CpsReprAbiLane::NativeFloat, value);
                let boxed = call_helper(
                    module_backend,
                    builder,
                    "yulang_cps_box_float_f64",
                    &[types::F64],
                    types::I64,
                    &[value],
                )?;
                builder.def_var(variable(*dest), boxed);
                return Ok(());
            }
            define_value_as_lane(builder, values, *dest, literal_lane(literal), value);
        }
        CpsStmt::Tuple { dest, items } => {
            let items = read_runtime_values_i64(module_backend, builder, function, values, items)?;
            let value = make_tuple_value(module_backend, builder, &items)?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::Record { dest, base, fields } => {
            let value = make_record_value(
                module_backend,
                builder,
                function,
                *base,
                fields,
                literals,
                values,
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::RecordWithoutFields { dest, base, fields } => {
            let value = make_record_without_fields_value(
                module_backend,
                builder,
                function,
                *base,
                fields,
                literals,
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::Select { dest, base, field } => {
            let base = read_value(builder, function, *base)?;
            let (field_ptr, field_len) =
                literals.literal_bytes(module_backend, builder, field.0.as_bytes())?;
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_record_select_i64",
                &[base, field_ptr, field_len],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::SelectWithDefault {
            dest,
            base,
            field,
            default,
        } => {
            let base = read_value(builder, function, *base)?;
            let default = read_value(builder, function, *default)?;
            let (field_ptr, field_len) =
                literals.literal_bytes(module_backend, builder, field.0.as_bytes())?;
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_record_select_or_default_i64",
                &[base, field_ptr, field_len, default],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::RecordHasField { dest, base, field } => {
            let base = read_value(builder, function, *base)?;
            let (field_ptr, field_len) =
                literals.literal_bytes(module_backend, builder, field.0.as_bytes())?;
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_record_has_field_i64",
                &[base, field_ptr, field_len],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::Variant { dest, tag, value } => {
            let value = value
                .map(|value| {
                    read_runtime_value_i64(module_backend, builder, function, values, value)
                })
                .transpose()?;
            let tag = register_variant_tag(module_backend, builder, tag, literals)?;
            let result = if let Some(value) = value {
                call_i64_helper(
                    module_backend,
                    builder,
                    "yulang_cps_variant_i64_1",
                    &[tag, value],
                )?
            } else {
                call_i64_helper(module_backend, builder, "yulang_cps_variant_i64_0", &[tag])?
            };
            builder.def_var(variable(*dest), result);
        }
        CpsStmt::TupleGet { dest, tuple, index } => {
            let tuple = read_value(builder, function, *tuple)?;
            let index = builder.ins().iconst(types::I64, *index as i64);
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_tuple_get_i64",
                &[tuple, index],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::VariantTagEq { dest, variant, tag } => {
            let variant = read_value(builder, function, *variant)?;
            let tag = builder.ins().iconst(types::I64, tag_hash(tag));
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_variant_tag_eq_i64",
                &[variant, tag],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::VariantPayload { dest, variant } => {
            let variant = read_value(builder, function, *variant)?;
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_variant_payload_i64",
                &[variant],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::Primitive { dest, op, args } => {
            let args = read_primitive_args(module_backend, builder, function, values, *op, args)?;
            let value = lower_primitive(module_backend, builder, function, *op, &args)?;
            define_value_as_lane(builder, values, *dest, primitive_result_lane(*op), value);
        }
        _ => unreachable!("lower_value_stmt called with non-value statement"),
    }
    Ok(())
}

fn lower_runtime_value_stmt<M: Module, L: CpsLiteralStore>(
    cx: &mut CpsCraneliftLowerCx<'_, '_, M, L>,
    stmt: &CpsStmt,
) -> CpsReprCraneliftResult<()> {
    lower_runtime_value_stmt_parts(
        cx.module_backend,
        cx.builder,
        cx.function,
        stmt,
        cx.functions,
        cx.handlers,
        cx.values,
    )
}

fn lower_runtime_value_stmt_parts<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    stmt: &CpsStmt,
    functions: &DeclaredFunctions,
    handlers: &HandlerRegistry,
    values: &mut LocalValueCache,
) -> CpsReprCraneliftResult<()> {
    match stmt {
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
        CpsStmt::AddThunkBoundary {
            dest,
            thunk,
            guard,
            allowed,
            active,
        } => {
            let value = read_value(builder, function, *thunk)?;
            let guard = read_value(builder, function, *guard)?;
            let allowed_mask = handlers.allowed_mask(function, allowed)?;
            let allowed_mask = builder.ins().iconst(types::I64, allowed_mask);
            let active = builder.ins().iconst(types::I64, i64::from(*active));
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_add_thunk_boundary_i64",
                &[value, guard, allowed_mask, active],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::MakeClosure { dest, entry } => {
            let value = make_closure(module_backend, builder, function, *entry, functions)?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::MakeRecursiveClosure { dest, entry } => {
            let value = make_recursive_closure(
                module_backend,
                builder,
                function,
                *dest,
                *entry,
                functions,
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::ForceThunk { dest, thunk } => {
            if force_thunk_passes_native_float(function, values, *thunk) {
                let value = read_value_as_lane(
                    builder,
                    function,
                    values,
                    *thunk,
                    CpsReprAbiLane::NativeFloat,
                )?;
                define_value_as_lane(builder, values, *dest, CpsReprAbiLane::NativeFloat, value);
                return Ok(());
            }
            let helper = declare_import(
                module_backend,
                builder,
                "yulang_cps_force_thunk_i64",
                &[types::I64],
                types::I64,
            )?;
            let thunk = read_value(builder, function, *thunk)?;
            // write27-d d5: fresh eval context for the sync force.
            let (saved_eval, saved_initial) = enter_callee_eval_context(module_backend, builder)?;
            let call = builder.ins().call(helper, &[thunk]);
            let results = builder.inst_results(call);
            let result = results[0];
            restore_caller_eval_context(module_backend, builder, saved_eval, saved_initial)?;
            let result = abort_result_or_return(module_backend, builder, result)?;
            let scope_fallback = scope_return_fallback_value(builder, function, *dest, result);
            return_if_scope_return_active(module_backend, builder, scope_fallback)?;
            builder.def_var(variable(*dest), result);
        }
        _ => unreachable!("lower_runtime_value_stmt called with non-runtime-value statement"),
    }
    Ok(())
}

fn lower_call_stmt_case<M: Module, L: CpsLiteralStore>(
    cx: &mut CpsCraneliftLowerCx<'_, '_, M, L>,
    stmt: &CpsStmt,
) -> CpsReprCraneliftResult<()> {
    lower_call_stmt(
        cx.module_backend,
        cx.builder,
        cx.function,
        stmt,
        cx.functions,
        cx.handlers,
        cx.values,
    )
}

fn lower_handler_stmt_case<M: Module, L: CpsLiteralStore>(
    cx: &mut CpsCraneliftLowerCx<'_, '_, M, L>,
    stmt: &CpsStmt,
) -> CpsReprCraneliftResult<()> {
    lower_handler_stmt(
        cx.module_backend,
        cx.builder,
        cx.function,
        stmt,
        cx.functions,
        cx.handlers,
        cx.values,
    )
}

fn lower_call_stmt<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    stmt: &CpsStmt,
    functions: &DeclaredFunctions,
    handlers: &HandlerRegistry,
    values: &mut LocalValueCache,
) -> CpsReprCraneliftResult<()> {
    match stmt {
        CpsStmt::DirectCall { dest, target, args } => {
            lower_direct_call_stmt(
                module_backend,
                builder,
                function,
                functions,
                values,
                *dest,
                target,
                args,
            )?;
        }
        CpsStmt::ApplyClosure { dest, closure, arg } => {
            let closure = read_value(builder, function, *closure)?;
            let arg = read_value(builder, function, *arg)?;
            // write27-d d5: fresh eval context for the sync apply.
            let (saved_eval, saved_initial) = enter_callee_eval_context(module_backend, builder)?;
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_apply_closure_i64",
                &[closure, arg],
            )?;
            restore_caller_eval_context(module_backend, builder, saved_eval, saved_initial)?;
            let value = abort_result_or_return(module_backend, builder, value)?;
            return_if_scope_return_active(module_backend, builder, value)?;
            builder.def_var(variable(*dest), value);
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
            // write27-d d5: fresh eval context for the sync resume.
            let (saved_eval, saved_initial) = enter_callee_eval_context(module_backend, builder)?;
            let call = builder.ins().call(helper, &[resumption, arg]);
            let results = builder.inst_results(call);
            let result = results[0];
            restore_caller_eval_context(module_backend, builder, saved_eval, saved_initial)?;
            let result = abort_result_or_return(module_backend, builder, result)?;
            let scope_fallback = scope_return_fallback_value(builder, function, *dest, result);
            return_if_scope_return_active(module_backend, builder, scope_fallback)?;
            builder.def_var(variable(*dest), result);
        }
        CpsStmt::ResumeWithHandler {
            dest,
            resumption,
            arg,
            handler,
            envs,
        } => {
            let updates_existing_handler_env = envs.iter().any(|env| !env.targets.is_empty());
            capture_handler_envs(module_backend, builder, function, *handler, envs)?;
            let helper = declare_import(
                module_backend,
                builder,
                "yulang_cps_resume_with_handler_i64",
                &[
                    types::I64,
                    types::I64,
                    types::I64,
                    types::I64,
                    types::I64,
                    types::I64,
                ],
                types::I64,
            )?;
            let resumption = read_value(builder, function, *resumption)?;
            let arg = read_value(builder, function, *arg)?;
            let handler_id = *handler;
            let handler = builder.ins().iconst(types::I64, handler_id.0 as i64);
            let consumes_mask = builder.ins().iconst(
                types::I64,
                handlers.handler_consumes_mask(function, handler_id)?,
            );
            let owner_function = builder
                .ins()
                .iconst(types::I64, function_runtime_id(function, functions)? as i64);
            let updates_existing_handler_env = builder
                .ins()
                .iconst(types::I64, i64::from(updates_existing_handler_env));
            // write27-d d5: fresh eval context for the sync resume-with-handler.
            let (saved_eval, saved_initial) = enter_callee_eval_context(module_backend, builder)?;
            let call = builder.ins().call(
                helper,
                &[
                    resumption,
                    arg,
                    handler,
                    consumes_mask,
                    owner_function,
                    updates_existing_handler_env,
                ],
            );
            let results = builder.inst_results(call);
            let result = results[0];
            restore_caller_eval_context(module_backend, builder, saved_eval, saved_initial)?;
            let result = abort_result_or_return(module_backend, builder, result)?;
            let scope_fallback = scope_return_fallback_value(builder, function, *dest, result);
            return_if_scope_return_active_without_routing(module_backend, builder, scope_fallback)?;
            builder.def_var(variable(*dest), result);
        }
        _ => unreachable!("lower_call_stmt called with non-call statement"),
    }
    Ok(())
}

fn lower_handler_stmt<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    stmt: &CpsStmt,
    functions: &DeclaredFunctions,
    handlers: &HandlerRegistry,
    _values: &mut LocalValueCache,
) -> CpsReprCraneliftResult<()> {
    match stmt {
        CpsStmt::InstallHandler {
            handler,
            envs,
            value,
            escape,
        } => {
            capture_handler_envs(module_backend, builder, function, *handler, envs)?;
            // write27-c c3: prefer the full install helper when the
            // escape continuation has an environment shape we support
            // (<= 4 slots). Otherwise fall back to the legacy install
            // — those handlers still work through the abort_i64
            // path in `perform_finish_i64`.
            let escape_cont = lookup_continuation(function, *escape)?;
            if escape_cont.environment.len() <= 4 {
                let func_ref =
                    continuation_func_ref(module_backend, builder, function, *escape, functions)?;
                let escape_ptr = builder.ins().func_addr(types::I64, func_ref);
                let threshold = call_i64_helper(
                    module_backend,
                    builder,
                    "yulang_cps_handler_return_frame_threshold_i64",
                    &[],
                )?;
                let current_initial = call_i64_helper(
                    module_backend,
                    builder,
                    "yulang_cps_current_initial_frame_count_i64",
                    &[],
                )?;
                let prompt =
                    call_i64_helper(module_backend, builder, "yulang_cps_fresh_prompt_i64", &[])?;
                let install_eval = call_i64_helper(
                    module_backend,
                    builder,
                    "yulang_cps_current_eval_id_i64",
                    &[],
                )?;
                let owner_function = builder
                    .ins()
                    .iconst(types::I64, function_runtime_id(function, functions)? as i64);
                let inherited = builder.ins().iconst(types::I64, 0);
                let handler_id = builder.ins().iconst(types::I64, handler.0 as i64);
                let consumes_mask = builder.ins().iconst(
                    types::I64,
                    handlers.handler_consumes_mask(function, *handler)?,
                );
                let mut args = vec![
                    handler_id,
                    consumes_mask,
                    escape_ptr,
                    threshold,
                    prompt,
                    install_eval,
                    owner_function,
                    inherited,
                ];
                args.extend(read_continuation_environment_values(
                    builder,
                    function,
                    escape_cont,
                )?);
                let escape_targets = continuation_environment_targets(builder, escape_cont);
                let (target_ptr, target_len) = stack_i64_slice(builder, &escape_targets)?;
                let _ = call_i64_helper(
                    module_backend,
                    builder,
                    "yulang_cps_set_pending_escape_env_targets_i64",
                    &[target_ptr, target_len],
                )?;
                let helper_name = INSTALL_HANDLER_FULL_HELPERS.fixed(escape_cont.environment.len());
                let _ = call_i64_helper(module_backend, builder, helper_name, &args)?;
                let value_cont = lookup_continuation(function, *value)?;
                let value_ref =
                    continuation_func_ref(module_backend, builder, function, *value, functions)?;
                let value_ptr = builder.ins().func_addr(types::I64, value_ref);
                let value_continuation_id = builder.ins().iconst(types::I64, value.0 as i64);
                let immediately_forces = builder.ins().iconst(
                    types::I64,
                    i64::from(resume_continuation_immediately_forces_param(value_cont)),
                );
                let value_env =
                    read_continuation_environment_values(builder, function, value_cont)?;
                if value_env.is_empty() {
                    let _ = call_i64_helper(
                        module_backend,
                        builder,
                        "yulang_cps_push_prompt_exit_frame_i64_0",
                        &[
                            prompt,
                            value_ptr,
                            value_continuation_id,
                            current_initial,
                            install_eval,
                            owner_function,
                            immediately_forces,
                        ],
                    )?;
                } else {
                    let (env_ptr, env_len) = stack_i64_slice(builder, &value_env)?;
                    let _ = call_i64_helper(
                        module_backend,
                        builder,
                        "yulang_cps_push_prompt_exit_frame_i64_many",
                        &[
                            prompt,
                            value_ptr,
                            value_continuation_id,
                            current_initial,
                            install_eval,
                            owner_function,
                            immediately_forces,
                            env_ptr,
                            env_len,
                        ],
                    )?;
                }
            } else {
                let handler_id = builder.ins().iconst(types::I64, handler.0 as i64);
                let consumes_mask = builder.ins().iconst(
                    types::I64,
                    handlers.handler_consumes_mask(function, *handler)?,
                );
                let _ = call_i64_helper(
                    module_backend,
                    builder,
                    "yulang_cps_install_handler_i64",
                    &[handler_id, consumes_mask],
                )?;
            }
        }
        CpsStmt::UninstallHandler { handler } => {
            let handler = builder.ins().iconst(types::I64, handler.0 as i64);
            let _ = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_uninstall_handler_i64",
                &[handler],
            )?;
        }
        _ => unreachable!("lower_handler_stmt called with non-handler statement"),
    }
    Ok(())
}

fn stmt_dest(stmt: &CpsStmt) -> Option<CpsValueId> {
    match stmt {
        CpsStmt::Literal { dest, .. }
        | CpsStmt::Primitive { dest, .. }
        | CpsStmt::Tuple { dest, .. }
        | CpsStmt::Record { dest, .. }
        | CpsStmt::RecordWithoutFields { dest, .. }
        | CpsStmt::Variant { dest, .. }
        | CpsStmt::Select { dest, .. }
        | CpsStmt::SelectWithDefault { dest, .. }
        | CpsStmt::RecordHasField { dest, .. }
        | CpsStmt::TupleGet { dest, .. }
        | CpsStmt::VariantTagEq { dest, .. }
        | CpsStmt::VariantPayload { dest, .. }
        | CpsStmt::DirectCall { dest, .. }
        | CpsStmt::ApplyClosure { dest, .. }
        | CpsStmt::CloneContinuation { dest, .. }
        | CpsStmt::MakeThunk { dest, .. }
        | CpsStmt::AddThunkBoundary { dest, .. }
        | CpsStmt::MakeClosure { dest, .. }
        | CpsStmt::MakeRecursiveClosure { dest, .. }
        | CpsStmt::ForceThunk { dest, .. }
        | CpsStmt::Resume { dest, .. }
        | CpsStmt::ResumeWithHandler { dest, .. }
        | CpsStmt::FreshGuard { dest, .. }
        | CpsStmt::PeekGuard { dest }
        | CpsStmt::FindGuard { dest, .. } => Some(*dest),
        CpsStmt::InstallHandler { .. } | CpsStmt::UninstallHandler { .. } => None,
    }
}

fn lower_effect_terminator<M: Module, L: CpsLiteralStore>(
    cx: &mut CpsCraneliftLowerCx<'_, '_, M, L>,
    continuation: &CpsReprAbiContinuation,
) -> CpsReprCraneliftResult<()> {
    match &continuation.terminator {
        CpsTerminator::Return(value) => {
            lower_return_terminator(cx, *value)?;
        }
        CpsTerminator::Continue { target, args } => {
            lower_continue_terminator(cx, *target, args)?;
        }
        CpsTerminator::Branch {
            cond,
            then_cont,
            else_cont,
        } => {
            lower_branch_terminator(cx, *cond, *then_cont, *else_cont)?;
        }
        CpsTerminator::Perform {
            effect,
            payload,
            resume,
            handler,
            blocked,
        } => {
            lower_perform_terminator_case(
                cx,
                PerformTerminatorCase {
                    effect,
                    payload: *payload,
                    resume: *resume,
                    handler: *handler,
                    blocked: *blocked,
                },
            )?;
        }
        CpsTerminator::EffectfulCall {
            target,
            args,
            resume,
        } => {
            lower_effectful_call_terminator(
                cx,
                EffectfulCallTerminatorCase {
                    target,
                    args,
                    resume: *resume,
                },
            )?;
        }
        CpsTerminator::EffectfulForce { thunk, resume } => {
            lower_effectful_force_terminator(
                cx,
                EffectfulForceTerminatorCase {
                    thunk: *thunk,
                    resume: *resume,
                },
            )?;
        }
        CpsTerminator::EffectfulApply {
            closure,
            arg,
            resume,
        } => {
            lower_effectful_apply_terminator(
                cx,
                EffectfulApplyTerminatorCase {
                    closure: *closure,
                    arg: *arg,
                    resume: *resume,
                },
            )?;
        }
    }
    Ok(())
}

fn lower_return_terminator<M: Module, L: CpsLiteralStore>(
    cx: &mut CpsCraneliftLowerCx<'_, '_, M, L>,
    value: CpsValueId,
) -> CpsReprCraneliftResult<()> {
    // write27-b: route the return value through the JIT-side
    // `yulang_cps_return_i64` helper so the eval-level Return semantics
    // (pre-force v2, continue_return_frame on remaining own-frames) match
    // cps_eval/cps_repr.
    //
    // The helper is a no-op when there are no own return frames
    // (frame_len <= initial_frame_count), so this is safe even for tests
    // that don't use effectful terminators; the path simply returns
    // `value` unchanged.
    let value = read_value(cx.builder, cx.function, value)?;
    let routed = call_i64_helper(
        cx.module_backend,
        cx.builder,
        "yulang_cps_return_i64",
        &[value],
    )?;
    cx.builder.ins().return_(&[routed]);
    Ok(())
}

fn lower_continue_terminator<M: Module, L: CpsLiteralStore>(
    cx: &mut CpsCraneliftLowerCx<'_, '_, M, L>,
    target: CpsContinuationId,
    args: &[CpsValueId],
) -> CpsReprCraneliftResult<()> {
    let value = call_continuation(
        cx.module_backend,
        cx.builder,
        cx.function,
        target,
        args,
        cx.functions,
    )?;
    cx.builder.ins().return_(&[value]);
    Ok(())
}

fn lower_branch_terminator<M: Module, L: CpsLiteralStore>(
    cx: &mut CpsCraneliftLowerCx<'_, '_, M, L>,
    cond: CpsValueId,
    then_cont: CpsContinuationId,
    else_cont: CpsContinuationId,
) -> CpsReprCraneliftResult<()> {
    lower_effect_branch(
        cx.module_backend,
        cx.builder,
        cx.function,
        cond,
        then_cont,
        else_cont,
        cx.functions,
    )
}

fn lower_perform_terminator_case<M: Module, L: CpsLiteralStore>(
    cx: &mut CpsCraneliftLowerCx<'_, '_, M, L>,
    case: PerformTerminatorCase<'_>,
) -> CpsReprCraneliftResult<()> {
    lower_perform_terminator(
        cx.module_backend,
        cx.builder,
        cx.function,
        case.effect,
        case.payload,
        case.resume,
        case.handler,
        cx.functions,
        cx.handlers,
        case.blocked,
    )
}

fn lower_effectful_call_terminator<M: Module, L: CpsLiteralStore>(
    cx: &mut CpsCraneliftLowerCx<'_, '_, M, L>,
    case: EffectfulCallTerminatorCase<'_>,
) -> CpsReprCraneliftResult<()> {
    lower_effectful_call_tail(
        cx.module_backend,
        cx.builder,
        cx.function,
        case.target,
        case.args,
        case.resume,
        cx.functions,
    )
}

fn lower_effectful_force_terminator<M: Module, L: CpsLiteralStore>(
    cx: &mut CpsCraneliftLowerCx<'_, '_, M, L>,
    case: EffectfulForceTerminatorCase,
) -> CpsReprCraneliftResult<()> {
    lower_effectful_force_tail(
        cx.module_backend,
        cx.builder,
        cx.function,
        case.thunk,
        case.resume,
        cx.functions,
    )
}

fn lower_effectful_apply_terminator<M: Module, L: CpsLiteralStore>(
    cx: &mut CpsCraneliftLowerCx<'_, '_, M, L>,
    case: EffectfulApplyTerminatorCase,
) -> CpsReprCraneliftResult<()> {
    lower_effectful_apply_tail(
        cx.module_backend,
        cx.builder,
        cx.function,
        case.closure,
        case.arg,
        case.resume,
        cx.functions,
    )
}

fn lower_perform_terminator<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    effect: &typed_ir::Path,
    payload: CpsValueId,
    resume: CpsContinuationId,
    handler: CpsHandlerId,
    functions: &DeclaredFunctions,
    handlers: &HandlerRegistry,
    blocked: Option<CpsValueId>,
) -> CpsReprCraneliftResult<()> {
    let host_fallback = host_console_effect_kind(effect);
    let candidates = handlers.candidates_for_effect(effect);
    if candidates.is_empty() {
        let Some(kind) = host_fallback else {
            return Err(CpsReprCraneliftError::UnsupportedTerminator {
                function: function.name.clone(),
                kind: "perform without handler entry",
            });
        };
        let payload = read_value(builder, function, payload)?;
        lower_host_console_perform(
            module_backend,
            builder,
            function,
            kind,
            payload,
            resume,
            functions,
        )?;
        return Ok(());
    }
    let resumption = make_resumption(
        module_backend,
        builder,
        function,
        resume,
        handler,
        functions,
    )?;
    let payload = read_value(builder, function, payload)?;
    let fallback_handler = if handler.0 == usize::MAX {
        -1
    } else {
        handler.0 as i64
    };
    let fallback = builder.ins().iconst(types::I64, fallback_handler);
    let static_blocked = blocked
        .map(|blocked| read_value(builder, function, blocked))
        .transpose()?
        .unwrap_or_else(|| builder.ins().iconst(types::I64, -1));
    let effect_mask = handlers.effect_mask(function, effect)?;
    let effect_mask = builder.ins().iconst(types::I64, effect_mask);
    let active_blocked = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_active_blocked_guard_i64",
        &[effect_mask],
    )?;
    let no_static_block = builder
        .ins()
        .icmp_imm(ir::condcodes::IntCC::Equal, static_blocked, -1);
    let blocked = builder
        .ins()
        .select(no_static_block, active_blocked, static_blocked);
    let selected = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_select_handler_i64",
        &[fallback, effect_mask, blocked],
    )?;
    // write27-d d2: now that select_handler has recorded the
    // matched real handler's meta, write it back into the
    // resumption as `handled_anchor`. apply_resumption uses
    // this to drop redundant inherited frames during the
    // anchor merge.
    let _ = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_set_resumption_anchor_from_selected_i64",
        &[resumption],
    )?;
    lower_selected_handler_return(
        module_backend,
        builder,
        function,
        &candidates,
        selected,
        payload,
        resumption,
        host_fallback.map(|kind| (kind, resume)),
        functions,
    )
}

fn lower_effectful_call_tail<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    target: &str,
    args: &[CpsValueId],
    resume: CpsContinuationId,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    // write27-b: EffectfulCall codegen. Push a return frame for the
    // resume continuation, set a fresh eval context, and tail-call the
    // target. The target's Return helper (write27-b/yulang_cps_return_i64)
    // consumes the frame and invokes the resume continuation when it
    // finally bottoms out.
    let resume_cont = lookup_continuation(function, resume)?;
    check_resume_continuation_shape(function, resume_cont)?;
    let immediate_force = resume_continuation_immediately_forces_param(resume_cont);
    // c0: read pre_push_count BEFORE pushing F_post so the callee's
    // initial_frame_count points at F_post itself (matches Layer 1/2
    // semantics).
    let pre_push_count = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_return_frame_len_i64",
        &[],
    )?;
    // Push F_post(resume_cont, env, current_initial, current_eval, immediate_force).
    push_return_frame_for_resume(
        module_backend,
        builder,
        function,
        resume_cont,
        immediate_force,
        functions,
    )?;
    // Read target args BEFORE switching eval context (so we see the caller's value table state).
    let arg_values = read_values(builder, function, args)?;
    // Set callee eval context: fresh eval id + initial = pre_push_count
    // (F_post is consumable, frames below are not).
    switch_eval_context_for_callee(module_backend, builder, pre_push_count)?;
    let id = functions.functions.get(target).copied().ok_or_else(|| {
        CpsReprCraneliftError::MissingFunction {
            name: target.to_string(),
        }
    })?;
    let callee = module_backend.declare_func_in_func(id, builder.func);
    let call = builder.ins().call(callee, &arg_values);
    let results = builder.inst_results(call);
    if results.len() != 1 {
        return Err(CpsReprCraneliftError::InvalidReturnArity {
            function: target.to_string(),
            arity: results.len(),
        });
    }
    let result = results[0];
    builder.ins().return_(&[result]);
    Ok(())
}

fn lower_effectful_apply_tail<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    closure: CpsValueId,
    arg: CpsValueId,
    resume: CpsContinuationId,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    // write27-d d4: EffectfulApply dispatches at runtime between Closure
    // and Resumption based on `yulang_cps_is_resumption_i64`. The Closure
    // path pushes F_post and calls apply_closure_i64. The Resumption path
    // delegates anchor-merge + combined-frames logic to a Rust helper.
    let resume_cont = lookup_continuation(function, resume)?;
    check_resume_continuation_shape(function, resume_cont)?;
    let immediate_force = resume_continuation_immediately_forces_param(resume_cont);
    let closure_value = read_value(builder, function, closure)?;
    let arg_value = read_value(builder, function, arg)?;

    let func_ref =
        continuation_func_ref(module_backend, builder, function, resume_cont.id, functions)?;
    let post_cont_ptr = builder.ins().func_addr(types::I64, func_ref);
    let current_eval = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_current_eval_id_i64",
        &[],
    )?;
    let current_initial = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_current_initial_frame_count_i64",
        &[],
    )?;
    let owner_function = builder
        .ins()
        .iconst(types::I64, function_runtime_id(function, functions)? as i64);
    let immediate_force_value = builder.ins().iconst(types::I64, i64::from(immediate_force));
    let env_args = read_continuation_environment_values(builder, function, resume_cont)?;

    let is_resumption = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_is_resumption_i64",
        &[closure_value],
    )?;
    let resumption_block = builder.create_block();
    let closure_block = builder.create_block();
    builder
        .ins()
        .brif(is_resumption, resumption_block, &[], closure_block, &[]);

    builder.switch_to_block(closure_block);
    builder.seal_block(closure_block);
    let pre_push_count = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_return_frame_len_i64",
        &[],
    )?;
    push_return_frame_for_resume(
        module_backend,
        builder,
        function,
        resume_cont,
        immediate_force,
        functions,
    )?;
    switch_eval_context_for_callee(module_backend, builder, pre_push_count)?;
    let closure_result = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_apply_closure_i64",
        &[closure_value, arg_value],
    )?;
    builder.ins().return_(&[closure_result]);

    builder.switch_to_block(resumption_block);
    builder.seal_block(resumption_block);
    let mut resumption_args = vec![
        closure_value,
        arg_value,
        post_cont_ptr,
        current_initial,
        current_eval,
        owner_function,
        immediate_force_value,
    ];
    let resumption_helper = if env_args.len() > 4 {
        let (env_ptr, env_len) = stack_i64_slice(builder, &env_args)?;
        resumption_args.push(env_ptr);
        resumption_args.push(env_len);
        EFFECTFUL_APPLY_RESUMPTION_HELPERS.many
    } else {
        resumption_args.extend_from_slice(&env_args);
        EFFECTFUL_APPLY_RESUMPTION_HELPERS.fixed(resume_cont.environment.len())
    };
    let resumption_result =
        call_i64_helper(module_backend, builder, resumption_helper, &resumption_args)?;
    builder.ins().return_(&[resumption_result]);
    Ok(())
}

fn lower_effectful_force_tail<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    thunk: CpsValueId,
    resume: CpsContinuationId,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    let resume_cont = lookup_continuation(function, resume)?;
    check_resume_continuation_shape(function, resume_cont)?;
    let thunk_value = read_value(builder, function, thunk)?;
    let is_thunk = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_is_thunk_i64",
        &[thunk_value],
    )?;
    let is_thunk = builder
        .ins()
        .icmp_imm(ir::condcodes::IntCC::NotEqual, is_thunk, 0);
    let force_block = builder.create_block();
    let value_block = builder.create_block();
    builder
        .ins()
        .brif(is_thunk, force_block, &[], value_block, &[]);

    builder.switch_to_block(value_block);
    builder.seal_block(value_block);
    let value = call_continuation_with_values(
        module_backend,
        builder,
        function,
        resume,
        &[thunk_value],
        functions,
    )?;
    builder.ins().return_(&[value]);

    builder.switch_to_block(force_block);
    builder.seal_block(force_block);
    let immediate_force = resume_continuation_immediately_forces_param(resume_cont);
    let pre_push_count = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_return_frame_len_i64",
        &[],
    )?;
    push_return_frame_for_resume(
        module_backend,
        builder,
        function,
        resume_cont,
        immediate_force,
        functions,
    )?;
    // Force the thunk body with the just-pushed post frame inherited, not
    // consumable. Effects inside the body can still capture it, and the
    // EffectfulForce terminator consumes it only after forcing reaches a value.
    let force_initial = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_return_frame_len_i64",
        &[],
    )?;
    let force_eval = call_i64_helper(module_backend, builder, "yulang_cps_fresh_eval_id_i64", &[])?;
    let _ = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_set_eval_context_i64",
        &[force_eval, force_initial],
    )?;
    let result = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_force_thunk_i64",
        &[thunk_value],
    )?;
    switch_eval_context_for_callee(module_backend, builder, pre_push_count)?;
    let routed = call_i64_helper(module_backend, builder, "yulang_cps_return_i64", &[result])?;
    builder.ins().return_(&[routed]);
    Ok(())
}

/// write27-b: validate that a resume continuation has the shape the
/// return-frame stack supports: exactly 1 param (the call's result) and
/// at most 4 env slots.
fn check_resume_continuation_shape(
    function: &CpsReprAbiFunction,
    resume_cont: &CpsReprAbiContinuation,
) -> CpsReprCraneliftResult<()> {
    if resume_cont.params.len() != 1 {
        return Err(CpsReprCraneliftError::UnsupportedTerminator {
            function: function.name.clone(),
            kind: "resume continuation arity",
        });
    }
    Ok(())
}

fn read_continuation_environment_values(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    continuation: &CpsReprAbiContinuation,
) -> CpsReprCraneliftResult<Vec<ir::Value>> {
    let mut values = Vec::with_capacity(continuation.environment.len());
    for slot in &continuation.environment {
        validate_environment_lane(function, slot.value, slot.lane)?;
        values.push(read_value(builder, function, slot.value)?);
    }
    Ok(values)
}

fn continuation_environment_targets(
    builder: &mut FunctionBuilder<'_>,
    continuation: &CpsReprAbiContinuation,
) -> Vec<ir::Value> {
    continuation
        .environment
        .iter()
        .map(|slot| builder.ins().iconst(types::I64, slot.value.0 as i64))
        .collect()
}

fn handler_arm_continues_to_installed_escape(
    function: &CpsReprAbiFunction,
    handler: CpsHandlerId,
    entry: CpsContinuationId,
) -> bool {
    let Some(escape) = handler_arm_continue_chain_escape(function, handler, entry) else {
        return false;
    };
    function.continuations.iter().any(|continuation| {
        continuation.stmts.iter().any(|stmt| {
            matches!(
                stmt,
                CpsStmt::InstallHandler {
                    handler: id,
                    escape: installed_escape,
                    ..
                } if *id == handler && *installed_escape == escape
            )
        })
    })
}

fn handler_arm_continue_chain_escape(
    function: &CpsReprAbiFunction,
    handler: CpsHandlerId,
    entry: CpsContinuationId,
) -> Option<CpsContinuationId> {
    let mut current = entry;
    let mut saw_uninstall = false;
    let mut visited = HashSet::new();
    while visited.insert(current) {
        let continuation = function
            .continuations
            .iter()
            .find(|continuation| continuation.id == current)?;
        saw_uninstall |= continuation.stmts.iter().any(
            |stmt| matches!(stmt, CpsStmt::UninstallHandler { handler: id } if *id == handler),
        );
        let CpsTerminator::Continue { target, .. } = &continuation.terminator else {
            return saw_uninstall.then_some(current);
        };
        if saw_uninstall
            && function.continuations.iter().any(|candidate| {
                candidate.stmts.iter().any(|stmt| {
                    matches!(
                        stmt,
                        CpsStmt::InstallHandler {
                            handler: id,
                            escape,
                            ..
                        } if *id == handler && escape == target
                    )
                })
            })
        {
            return Some(*target);
        }
        current = *target;
    }
    None
}

fn handler_arm_uses_resume_with_handler(
    function: &CpsReprAbiFunction,
    entry: CpsContinuationId,
) -> bool {
    let mut current = entry;
    let mut visited = HashSet::new();
    while visited.insert(current) {
        let Some(continuation) = function
            .continuations
            .iter()
            .find(|continuation| continuation.id == current)
        else {
            return false;
        };
        if continuation
            .stmts
            .iter()
            .any(|stmt| matches!(stmt, CpsStmt::ResumeWithHandler { .. }))
        {
            return true;
        }
        let CpsTerminator::Continue { target, .. } = &continuation.terminator else {
            return false;
        };
        current = *target;
    }
    false
}

/// write27-b: mirror of `return_frame_immediately_forces_param` in
/// cps_eval/cps_repr. Returns true when the continuation's first stmt
/// is `ForceThunk` on its first param. Used to fire pre-force v2 in
/// the JIT Return path.
fn resume_continuation_immediately_forces_param(resume_cont: &CpsReprAbiContinuation) -> bool {
    let Some(first_param) = resume_cont.params.first() else {
        return false;
    };
    matches!(
        resume_cont.stmts.first(),
        Some(CpsStmt::ForceThunk { thunk, .. }) if *thunk == first_param.value
    )
}

/// write27-b: emit the codegen for "push a return frame for this
/// resume continuation". Reads the resume continuation's env slots from
/// the current function's value table, gets a function pointer to the
/// continuation, and calls `yulang_cps_push_return_frame_i64_N` or the
/// many-slot variant with current_initial, current_eval, the immediate_force
/// flag, and the env slots.
fn push_return_frame_for_resume<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    resume_cont: &CpsReprAbiContinuation,
    immediate_force: bool,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    let func_ref =
        continuation_func_ref(module_backend, builder, function, resume_cont.id, functions)?;
    let cont_ptr = builder.ins().func_addr(types::I64, func_ref);
    let current_eval = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_current_eval_id_i64",
        &[],
    )?;
    let current_initial = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_current_initial_frame_count_i64",
        &[],
    )?;
    let owner_function = builder
        .ins()
        .iconst(types::I64, function_runtime_id(function, functions)? as i64);
    let immediate_force_value = builder.ins().iconst(types::I64, i64::from(immediate_force));
    let continuation_id = builder.ins().iconst(types::I64, resume_cont.id.0 as i64);
    let mut env_values = Vec::with_capacity(resume_cont.environment.len());
    for slot in &resume_cont.environment {
        validate_environment_lane(function, slot.value, slot.lane)?;
        env_values.push(read_value(builder, function, slot.value)?);
    }
    if env_values.len() > 4 {
        let (env_ptr, env_len) = stack_i64_slice(builder, &env_values)?;
        let args = vec![
            cont_ptr,
            continuation_id,
            current_initial,
            current_eval,
            owner_function,
            immediate_force_value,
            env_ptr,
            env_len,
        ];
        let _ = call_i64_helper(
            module_backend,
            builder,
            PUSH_RETURN_FRAME_HELPERS.many,
            &args,
        )?;
        return Ok(());
    }
    let mut args = vec![
        cont_ptr,
        continuation_id,
        current_initial,
        current_eval,
        owner_function,
        immediate_force_value,
    ];
    args.extend(env_values);
    let helper_name = PUSH_RETURN_FRAME_HELPERS.fixed(resume_cont.environment.len());
    let _ = call_i64_helper(module_backend, builder, helper_name, &args)?;
    Ok(())
}

/// write27-c c0 HOTFIX: switch to the callee's eval context using
/// `pre_push_count` (return_frame_len observed BEFORE F_post push), not
/// the post-push length. Layer 1/2 semantics:
///   pre_push_count = return_frames.len();
///   push(F_post);
///   callee.initial_frame_count = pre_push_count;
/// If we used the post-push length, the callee's `frame_len <= initial`
/// invariant would hold immediately and F_post would never be consumed,
/// killing the EffectfulCall return-frame chain.
fn switch_eval_context_for_callee<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    pre_push_count: ir::Value,
) -> CpsReprCraneliftResult<()> {
    let fresh_eval = call_i64_helper(module_backend, builder, "yulang_cps_fresh_eval_id_i64", &[])?;
    let _ = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_set_eval_context_i64",
        &[fresh_eval, pre_push_count],
    )?;
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
    candidates: &[HandlerCandidate],
    selected: ir::Value,
    payload: ir::Value,
    resumption: ir::Value,
    host_fallback: Option<(HostConsoleEffect, CpsContinuationId)>,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    let missing_block = builder.create_block();

    for (index, candidate) in candidates.iter().enumerate() {
        let call_block = builder.create_block();
        let next_block = if index + 1 == candidates.len() {
            missing_block
        } else {
            builder.create_block()
        };
        let compare = builder.ins().icmp_imm(
            ir::condcodes::IntCC::Equal,
            selected,
            candidate.handler.0 as i64,
        );
        builder
            .ins()
            .brif(compare, call_block, &[], next_block, &[]);

        builder.switch_to_block(call_block);
        let callee = continuation_func_ref_by_name(
            module_backend,
            builder,
            &candidate.function,
            candidate.entry,
            functions,
        )?;
        let fallback_env = if candidate.function == function.name {
            continuation_environment_argument(module_backend, builder, function, candidate.entry)?
        } else {
            builder.ins().iconst(types::I64, 0)
        };
        let entry = builder.ins().iconst(types::I64, candidate.entry.0 as i64);
        let handler_env = call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_selected_handler_env_or_i64",
            &[entry, fallback_env],
        )?;
        // Handler arm bodies are evaluated with an empty return-frame stack in
        // cps_eval/cps_repr. Keeping the perform-site frames here would let
        // the arm's natural return continue the caller rest before
        // `perform_finish_i64` wraps the arm result.
        let _ = call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_enter_handler_arm_i64",
            &[],
        )?;
        // write27-d d5: arm body runs in a fresh eval context. The return
        // frame helper above makes `initial_frame_count` observe zero, matching
        // Layer 1/2's local `eval_continuations(..., return_frames = [])`.
        let (saved_eval, saved_initial) = enter_callee_eval_context(module_backend, builder)?;
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
        restore_caller_eval_context(module_backend, builder, saved_eval, saved_initial)?;
        let _ = call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_exit_handler_arm_i64",
            &[],
        )?;
        if candidate.continues_to_installed_escape {
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_perform_finish_escaped_i64",
                &[result],
            )?;
            builder.ins().return_(&[value]);
            builder.switch_to_block(next_block);
            continue;
        }
        // write27-c c3/c4: Perform-arm post-call routing via the
        // combined `perform_finish_i64` helper. It restores the outer
        // handler stack, wraps the arm result as a ScopeReturn when
        // the selected handler is real, routes the SR (current stack
        // walk, frame walk, or propagate), and falls back to the
        // legacy `abort_i64` slot for synthetic handlers.
        let routed = call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_perform_finish_i64",
            &[result],
        )?;
        builder.ins().return_(&[routed]);

        builder.switch_to_block(next_block);
    }

    builder.switch_to_block(missing_block);
    if let Some((kind, resume)) = host_fallback {
        lower_host_console_perform(
            module_backend,
            builder,
            function,
            kind,
            payload,
            resume,
            functions,
        )?;
    } else {
        let value = builder.ins().iconst(types::I64, 0);
        builder.ins().return_(&[value]);
    }
    builder.seal_block(missing_block);
    Ok(())
}

fn lower_host_console_perform<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    kind: HostConsoleEffect,
    payload: ir::Value,
    resume: CpsContinuationId,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
    let helper = match kind {
        HostConsoleEffect::Debug => "yulang_cps_debug_i64",
        HostConsoleEffect::OutWrite => "yulang_cps_out_write_i64",
        HostConsoleEffect::ErrWrite => "yulang_cps_err_write_i64",
        HostConsoleEffect::WarnWrite => "yulang_cps_warn_write_i64",
        HostConsoleEffect::DieDie => "yulang_cps_die_i64",
    };
    let result = call_i64_helper(module_backend, builder, helper, &[payload])?;
    let resume_value = match kind {
        HostConsoleEffect::OutWrite
        | HostConsoleEffect::ErrWrite
        | HostConsoleEffect::WarnWrite
        | HostConsoleEffect::DieDie => builder.ins().iconst(types::I64, 0),
        HostConsoleEffect::Debug => result,
    };
    let value = call_continuation_with_values(
        module_backend,
        builder,
        function,
        resume,
        &[resume_value],
        functions,
    )?;
    builder.ins().return_(&[value]);
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
    let args = read_values(builder, function, args)?;
    call_continuation_with_values(module_backend, builder, function, target, &args, functions)
}

fn call_continuation_with_values<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    target: CpsContinuationId,
    args: &[ir::Value],
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<ir::Value> {
    let callee = continuation_func_ref(module_backend, builder, function, target, functions)?;
    let env = continuation_environment_argument(module_backend, builder, function, target)?;
    let mut call_args = vec![env];
    call_args.extend_from_slice(args);
    let call = builder.ins().call(callee, &call_args);
    let results = builder.inst_results(call);
    if results.len() != 1 {
        return Err(CpsReprCraneliftError::InvalidReturnArity {
            function: function.name.clone(),
            arity: results.len(),
        });
    }
    let result = results[0];
    let result = abort_result_or_return(module_backend, builder, result)?;
    return_if_scope_return_active(module_backend, builder, result)?;
    Ok(result)
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
    let func_ref = continuation_func_ref(module_backend, builder, function, resume, functions)?;
    let code = builder.ins().func_addr(types::I64, func_ref);
    let handler = builder.ins().iconst(types::I64, handler.0 as i64);
    let mut env_values = Vec::with_capacity(resume_continuation.environment.len());
    for slot in &resume_continuation.environment {
        validate_environment_lane(function, slot.value, slot.lane)?;
        env_values.push(read_value(builder, function, slot.value)?);
    }
    if env_values.len() > 4 {
        let (env_ptr, env_len) = stack_i64_slice(builder, &env_values)?;
        return call_i64_helper(
            module_backend,
            builder,
            MAKE_RESUMPTION_HELPERS.many,
            &[code, handler, env_ptr, env_len],
        );
    }
    let mut args = vec![code, handler];
    args.extend(env_values);
    let helper_name = MAKE_RESUMPTION_HELPERS.fixed(resume_continuation.environment.len());
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

    let func_ref = continuation_func_ref(module_backend, builder, function, entry, functions)?;
    let code = builder.ins().func_addr(types::I64, func_ref);
    let mut args = vec![code];
    for slot in &thunk_continuation.environment {
        validate_environment_lane(function, slot.value, slot.lane)?;
        args.push(read_value(builder, function, slot.value)?);
    }
    if thunk_continuation.environment.len() > 4 {
        let (env_ptr, env_len) = stack_i64_slice(builder, &args[1..])?;
        return call_i64_helper(
            module_backend,
            builder,
            MAKE_THUNK_HELPERS.many,
            &[code, env_ptr, env_len],
        );
    }
    let helper_name = MAKE_THUNK_HELPERS.fixed(thunk_continuation.environment.len());
    let params = vec![types::I64; args.len()];
    let helper = declare_import(module_backend, builder, helper_name, &params, types::I64)?;
    let call = builder.ins().call(helper, &args);
    let results = builder.inst_results(call);
    Ok(results[0])
}

fn make_closure<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    entry: CpsContinuationId,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<ir::Value> {
    let closure_continuation = continuation(function, entry)?;
    if closure_continuation.params.len() != 1 {
        return Err(CpsReprCraneliftError::UnsupportedStmt {
            function: function.name.clone(),
            kind: "closure entry arity",
        });
    }
    let func_ref = continuation_func_ref(module_backend, builder, function, entry, functions)?;
    let code = builder.ins().func_addr(types::I64, func_ref);
    let mut args = vec![code];
    for slot in &closure_continuation.environment {
        validate_environment_lane(function, slot.value, slot.lane)?;
        args.push(read_value(builder, function, slot.value)?);
    }
    if closure_continuation.environment.len() > 4 {
        let (env_ptr, env_len) = stack_i64_slice(builder, &args[1..])?;
        return call_i64_helper(
            module_backend,
            builder,
            MAKE_CLOSURE_HELPERS.many,
            &[code, env_ptr, env_len],
        );
    }
    let helper_name = MAKE_CLOSURE_HELPERS.fixed(closure_continuation.environment.len());
    let params = vec![types::I64; args.len()];
    let helper = declare_import(module_backend, builder, helper_name, &params, types::I64)?;
    let call = builder.ins().call(helper, &args);
    let results = builder.inst_results(call);
    Ok(results[0])
}

fn make_recursive_closure<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    dest: CpsValueId,
    entry: CpsContinuationId,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<ir::Value> {
    let closure_continuation = continuation(function, entry)?;
    if closure_continuation.params.len() != 1 {
        return Err(CpsReprCraneliftError::UnsupportedStmt {
            function: function.name.clone(),
            kind: "recursive closure entry arity",
        });
    }
    let func_ref = continuation_func_ref(module_backend, builder, function, entry, functions)?;
    let code = builder.ins().func_addr(types::I64, func_ref);
    let mut args = vec![code];
    let mut self_slot = None;
    for (index, slot) in closure_continuation.environment.iter().enumerate() {
        validate_environment_lane(function, slot.value, slot.lane)?;
        if slot.value == dest {
            self_slot = Some(index);
            args.push(builder.ins().iconst(types::I64, 0));
        } else {
            args.push(read_value(builder, function, slot.value)?);
        }
    }
    let Some(self_slot) = self_slot else {
        return make_closure(module_backend, builder, function, entry, functions);
    };
    if closure_continuation.environment.len() > 4 {
        let self_slot_value = builder.ins().iconst(types::I64, self_slot as i64);
        let (env_ptr, env_len) = stack_i64_slice(builder, &args[1..])?;
        return call_i64_helper(
            module_backend,
            builder,
            MAKE_RECURSIVE_CLOSURE_HELPERS.many,
            &[code, self_slot_value, env_ptr, env_len],
        );
    }
    let self_slot = builder.ins().iconst(types::I64, self_slot as i64);
    args.insert(1, self_slot);
    let helper_name = MAKE_RECURSIVE_CLOSURE_HELPERS.fixed(closure_continuation.environment.len());
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

fn call_helper<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    name: &str,
    params: &[ir::Type],
    ret: ir::Type,
    args: &[ir::Value],
) -> CpsReprCraneliftResult<ir::Value> {
    let helper = declare_import(module_backend, builder, name, params, ret)?;
    let call = builder.ins().call(helper, args);
    Ok(builder.inst_results(call)[0])
}

fn stack_i64_slice(
    builder: &mut FunctionBuilder<'_>,
    args: &[ir::Value],
) -> CpsReprCraneliftResult<(ir::Value, ir::Value)> {
    let byte_size = u32::try_from(args.len().saturating_mul(8)).map_err(|_| {
        CpsReprCraneliftError::Cranelift("CPS repr stack slice is too large".to_string())
    })?;
    let slot = builder.create_sized_stack_slot(ir::StackSlotData::new(
        ir::StackSlotKind::ExplicitSlot,
        byte_size,
        3,
    ));
    for (index, arg) in args.iter().copied().enumerate() {
        builder.ins().stack_store(arg, slot, (index * 8) as i32);
    }
    let ptr = builder.ins().stack_addr(types::I64, slot, 0);
    let len = builder.ins().iconst(types::I64, args.len() as i64);
    Ok((ptr, len))
}

fn abort_result_or_return<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    value: ir::Value,
) -> CpsReprCraneliftResult<ir::Value> {
    let mode = call_i64_helper(module_backend, builder, "yulang_cps_abort_mode_i64", &[])?;
    let no_abort = builder.create_block();
    let abort = builder.create_block();
    builder.append_block_param(no_abort, types::I64);
    builder
        .ins()
        .brif(mode, abort, &[], no_abort, &[ir::BlockArg::Value(value)]);

    builder.switch_to_block(abort);
    builder.seal_block(abort);
    let consume = builder.ins().icmp_imm(ir::condcodes::IntCC::Equal, mode, 2);
    let consume_block = builder.create_block();
    let return_block = builder.create_block();
    builder
        .ins()
        .brif(consume, consume_block, &[], return_block, &[]);

    builder.switch_to_block(return_block);
    builder.seal_block(return_block);
    let abort_value = call_i64_helper(module_backend, builder, "yulang_cps_abort_value_i64", &[])?;
    builder.ins().return_(&[abort_value]);

    builder.switch_to_block(consume_block);
    builder.seal_block(consume_block);
    let abort_value =
        call_i64_helper(module_backend, builder, "yulang_cps_consume_abort_i64", &[])?;
    builder
        .ins()
        .jump(no_abort, &[ir::BlockArg::Value(abort_value)]);

    builder.switch_to_block(no_abort);
    builder.seal_block(no_abort);
    Ok(builder.block_params(no_abort)[0])
}

/// write27-d d5: enter a fresh eval context for a synchronous internal
/// call. Mirrors Layer 1/2 where each `eval_continuations` invocation
/// gets a fresh `CpsEvalId` plus `initial_frame_count = current frame
/// count`. Returns the saved caller `(eval_id, initial)` so the
/// caller can restore them post-call.
fn enter_callee_eval_context<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
) -> CpsReprCraneliftResult<(ir::Value, ir::Value)> {
    let saved_eval = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_current_eval_id_i64",
        &[],
    )?;
    let saved_initial = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_current_initial_frame_count_i64",
        &[],
    )?;
    let callee_initial = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_return_frame_len_i64",
        &[],
    )?;
    let callee_eval =
        call_i64_helper(module_backend, builder, "yulang_cps_fresh_eval_id_i64", &[])?;
    let _ = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_set_eval_context_i64",
        &[callee_eval, callee_initial],
    )?;
    Ok((saved_eval, saved_initial))
}

/// write27-d d5: pair with `enter_callee_eval_context` — restores the
/// caller's saved `(eval_id, initial)` after the sync call returns.
fn restore_caller_eval_context<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    saved_eval: ir::Value,
    saved_initial: ir::Value,
) -> CpsReprCraneliftResult<()> {
    let _ = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_set_eval_context_i64",
        &[saved_eval, saved_initial],
    )?;
    Ok(())
}

/// write27-c c5: after each synchronous internal call, check the
/// ScopeReturn slot. If active, route it; the route either jumps to
/// a matched handler's escape (return its result) or propagates with
/// the slot still active (return the fallback). Either way, the
/// current function short-circuits — sync callers up the chain run
/// their own post-call route to keep propagating.
fn return_if_scope_return_active<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    fallback: ir::Value,
) -> CpsReprCraneliftResult<()> {
    let active = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_scope_return_active_i64",
        &[],
    )?;
    let route_block = builder.create_block();
    let cont_block = builder.create_block();
    builder
        .ins()
        .brif(active, route_block, &[], cont_block, &[]);

    builder.switch_to_block(route_block);
    builder.seal_block(route_block);
    let routed = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_route_scope_return_i64",
        &[fallback],
    )?;
    builder.ins().return_(&[routed]);

    builder.switch_to_block(cont_block);
    builder.seal_block(cont_block);
    Ok(())
}

fn return_if_scope_return_active_without_routing<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    fallback: ir::Value,
) -> CpsReprCraneliftResult<()> {
    let active = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_scope_return_active_i64",
        &[],
    )?;
    let return_block = builder.create_block();
    let cont_block = builder.create_block();
    builder
        .ins()
        .brif(active, return_block, &[], cont_block, &[]);

    builder.switch_to_block(return_block);
    builder.seal_block(return_block);
    builder.ins().return_(&[fallback]);

    builder.switch_to_block(cont_block);
    builder.seal_block(cont_block);
    Ok(())
}

fn scope_return_fallback_value(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    value: CpsValueId,
    fallback: ir::Value,
) -> ir::Value {
    let lane = value_lane(function, value).unwrap_or(CpsReprAbiLane::Unknown);
    scope_return_fallback_for_lane(builder, lane, fallback)
}

fn scope_return_fallback_for_lane(
    builder: &mut FunctionBuilder<'_>,
    lane: CpsReprAbiLane,
    fallback: ir::Value,
) -> ir::Value {
    match lane {
        CpsReprAbiLane::NativeFloat => builder.ins().iconst(types::I64, 0),
        _ => fallback,
    }
}

fn make_env<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    _function: &CpsReprAbiFunction,
    args: &[ir::Value],
) -> CpsReprCraneliftResult<ir::Value> {
    if args.len() > 4 {
        let (env_ptr, env_len) = stack_i64_slice(builder, args)?;
        return call_i64_helper(
            module_backend,
            builder,
            MAKE_ENV_HELPERS.many,
            &[env_ptr, env_len],
        );
    }
    let helper_name = MAKE_ENV_HELPERS.fixed(args.len());
    let params = vec![types::I64; args.len()];
    let helper = declare_import(module_backend, builder, helper_name, &params, types::I64)?;
    let call = builder.ins().call(helper, args);
    let results = builder.inst_results(call);
    Ok(results[0])
}

fn make_tuple_value<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    args: &[ir::Value],
) -> CpsReprCraneliftResult<ir::Value> {
    let helper_name = TUPLE_HELPERS.select(args.len());
    if args.len() > 4 {
        return Err(CpsReprCraneliftError::UnsupportedStmt {
            function: "<tuple>".to_string(),
            kind: "tuple larger than four slots",
        });
    }
    call_i64_helper(module_backend, builder, helper_name, args)
}

fn make_record_value<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    base: Option<CpsValueId>,
    fields: &[CpsRecordField],
    literals: &mut L,
    values: &LocalValueCache,
) -> CpsReprCraneliftResult<ir::Value> {
    let mut record = match base {
        Some(base) => read_value(builder, function, base)?,
        None => call_i64_helper(module_backend, builder, "yulang_cps_record_empty_i64", &[])?,
    };
    for field in fields {
        let value = read_runtime_value_i64(module_backend, builder, function, values, field.value)?;
        let (field_ptr, field_len) =
            literals.literal_bytes(module_backend, builder, field.name.0.as_bytes())?;
        record = call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_record_insert_i64",
            &[record, field_ptr, field_len, value],
        )?;
    }
    Ok(record)
}

fn make_record_without_fields_value<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    base: CpsValueId,
    fields: &[typed_ir::Name],
    literals: &mut L,
) -> CpsReprCraneliftResult<ir::Value> {
    let mut record = read_value(builder, function, base)?;
    for field in fields {
        let (field_ptr, field_len) =
            literals.literal_bytes(module_backend, builder, field.0.as_bytes())?;
        record = call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_record_without_field_i64",
            &[record, field_ptr, field_len],
        )?;
    }
    Ok(record)
}

fn tag_hash(tag: &typed_ir::Name) -> i64 {
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in tag.0.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash as i64
}

fn register_variant_tag<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    tag: &typed_ir::Name,
    literals: &mut L,
) -> CpsReprCraneliftResult<ir::Value> {
    let tag_hash = builder.ins().iconst(types::I64, tag_hash(tag));
    let (name_ptr, name_len) = literals.literal_bytes(module_backend, builder, tag.0.as_bytes())?;
    let _ = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_register_tag_i64",
        &[tag_hash, name_ptr, name_len],
    )?;
    Ok(tag_hash)
}

trait CpsLiteralStore {
    fn literal_bytes<M: Module>(
        &mut self,
        module_backend: &mut M,
        builder: &mut FunctionBuilder<'_>,
        bytes: &[u8],
    ) -> CpsReprCraneliftResult<(ir::Value, ir::Value)>;
}

struct HostLiteralStore<'a> {
    strings: &'a mut Vec<Box<str>>,
}

impl CpsLiteralStore for HostLiteralStore<'_> {
    fn literal_bytes<M: Module>(
        &mut self,
        _module_backend: &mut M,
        builder: &mut FunctionBuilder<'_>,
        bytes: &[u8],
    ) -> CpsReprCraneliftResult<(ir::Value, ir::Value)> {
        let text = unsafe { std::str::from_utf8_unchecked(bytes) }
            .to_string()
            .into_boxed_str();
        let ptr = text.as_ptr() as i64;
        let len = text.len() as i64;
        self.strings.push(text);
        Ok((
            builder.ins().iconst(types::I64, ptr),
            builder.ins().iconst(types::I64, len),
        ))
    }
}

#[derive(Default)]
struct ObjectLiteralStore {
    next_id: usize,
}

impl CpsLiteralStore for ObjectLiteralStore {
    fn literal_bytes<M: Module>(
        &mut self,
        module_backend: &mut M,
        builder: &mut FunctionBuilder<'_>,
        bytes: &[u8],
    ) -> CpsReprCraneliftResult<(ir::Value, ir::Value)> {
        let name = format!("__yulang_cps_lit_{}", self.next_id);
        self.next_id += 1;
        let data_id = module_backend
            .declare_data(&name, Linkage::Local, false, false)
            .map_err(cranelift_error)?;
        let mut data = DataDescription::new();
        data.define(bytes.to_vec().into_boxed_slice());
        module_backend
            .define_data(data_id, &data)
            .map_err(cranelift_error)?;
        let global = module_backend.declare_data_in_func(data_id, builder.func);
        Ok((
            builder.ins().symbol_value(types::I64, global),
            builder.ins().iconst(types::I64, bytes.len() as i64),
        ))
    }
}

/// write27-b: alias for the `continuation()` lookup, used in scopes
/// where a parameter named `continuation` shadows the function name.
fn lookup_continuation<'a>(
    function: &'a CpsReprAbiFunction,
    id: CpsContinuationId,
) -> CpsReprCraneliftResult<&'a CpsReprAbiContinuation> {
    continuation(function, id)
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
    sig.params.extend(
        effective_function_param_lanes(function)
            .into_iter()
            .map(|lane| AbiParam::new(lane_type(lane))),
    );
    let return_lane = continuation(function, function.entry)
        .map(|entry| effective_continuation_return_lane(function, entry))
        .unwrap_or(CpsReprAbiLane::Unknown);
    sig.returns.push(AbiParam::new(lane_type(return_lane)));
    sig
}

fn lower_function<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    ctx: &mut cranelift_codegen::Context,
    function: &CpsReprAbiFunction,
    functions: &DeclaredFunctions,
    literals: &mut L,
) -> CpsReprCraneliftResult<()> {
    let mut builder_context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_context);
    let blocks = create_blocks(&mut builder, function);
    declare_variables(&mut builder, function);
    let mut values = LocalValueCache::default();
    bind_function_params(&mut builder, function, &blocks, &mut values)?;

    for continuation in &function.continuations {
        let block = continuation_block(function, &blocks, continuation.id)?;
        builder.switch_to_block(block);
        bind_continuation_params(&mut builder, function, continuation, block, &mut values)?;
        for stmt in &continuation.stmts {
            lower_stmt(
                module_backend,
                &mut builder,
                function,
                stmt,
                functions,
                literals,
                &mut values,
            )?;
        }
        lower_terminator(
            &mut builder,
            function,
            &blocks,
            continuation,
            &continuation.terminator,
            &mut values,
        )?;
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
                for param in &continuation.params {
                    builder.append_block_param(
                        block,
                        lane_type(effective_value_lane(function, param.value)),
                    );
                }
            }
            (continuation.id, block)
        })
        .collect()
}

fn declare_variables(builder: &mut FunctionBuilder<'_>, function: &CpsReprAbiFunction) {
    for value in function_value_ids(function) {
        builder.declare_var(variable(value), types::I64);
        builder.declare_var(
            variable_for_lane(value, CpsReprAbiLane::NativeFloat),
            types::F64,
        );
    }
}

fn bind_function_params(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    blocks: &HashMap<CpsContinuationId, ir::Block>,
    values: &mut LocalValueCache,
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
        let lane = effective_value_lane(function, continuation_param.value);
        define_value_as_lane(builder, values, function_param.value, lane, value);
        if continuation_param.value != function_param.value {
            define_value_as_lane(builder, values, continuation_param.value, lane, value);
        }
    }
    Ok(())
}

fn bind_continuation_params(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    continuation: &CpsReprAbiContinuation,
    block: ir::Block,
    values: &mut LocalValueCache,
) -> CpsReprCraneliftResult<()> {
    if continuation.id == function.entry {
        return Ok(());
    }
    let params = builder.block_params(block).to_vec();
    for (param, value) in continuation.params.iter().zip(params) {
        define_value_as_lane(
            builder,
            values,
            param.value,
            effective_value_lane(function, param.value),
            value,
        );
    }
    Ok(())
}

fn lower_stmt<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    stmt: &CpsStmt,
    functions: &DeclaredFunctions,
    literals: &mut L,
    values: &mut LocalValueCache,
) -> CpsReprCraneliftResult<()> {
    match stmt {
        CpsStmt::Literal { dest, literal } => {
            let value = lower_literal(module_backend, builder, function, literal, literals)?;
            if matches!(literal, CpsLiteral::Float(_)) {
                define_value_as_lane(builder, values, *dest, CpsReprAbiLane::NativeFloat, value);
                let boxed = call_helper(
                    module_backend,
                    builder,
                    "yulang_cps_box_float_f64",
                    &[types::F64],
                    types::I64,
                    &[value],
                )?;
                builder.def_var(variable(*dest), boxed);
                return Ok(());
            }
            define_value_as_lane(builder, values, *dest, literal_lane(literal), value);
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
        CpsStmt::AddThunkBoundary { dest, thunk, .. } => {
            let value = read_value(builder, function, *thunk)?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::MakeClosure { dest, entry } => {
            let value = make_closure(module_backend, builder, function, *entry, functions)?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::MakeRecursiveClosure { dest, entry } => {
            let value = make_recursive_closure(
                module_backend,
                builder,
                function,
                *dest,
                *entry,
                functions,
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::ForceThunk { dest, thunk } => {
            if force_thunk_passes_native_float(function, values, *thunk) {
                let value = read_value_as_lane(
                    builder,
                    function,
                    values,
                    *thunk,
                    CpsReprAbiLane::NativeFloat,
                )?;
                define_value_as_lane(builder, values, *dest, CpsReprAbiLane::NativeFloat, value);
                return Ok(());
            }
            let helper = declare_import(
                module_backend,
                builder,
                "yulang_cps_force_thunk_i64",
                &[types::I64],
                types::I64,
            )?;
            let thunk = read_value(builder, function, *thunk)?;
            // write27-d d5: fresh eval context for the sync force.
            let (saved_eval, saved_initial) = enter_callee_eval_context(module_backend, builder)?;
            let call = builder.ins().call(helper, &[thunk]);
            let results = builder.inst_results(call);
            let result = results[0];
            restore_caller_eval_context(module_backend, builder, saved_eval, saved_initial)?;
            let result = abort_result_or_return(module_backend, builder, result)?;
            let scope_fallback = scope_return_fallback_value(builder, function, *dest, result);
            return_if_scope_return_active(module_backend, builder, scope_fallback)?;
            builder.def_var(variable(*dest), result);
        }
        CpsStmt::Tuple { dest, items } => {
            let items = read_runtime_values_i64(module_backend, builder, function, values, items)?;
            let value = make_tuple_value(module_backend, builder, &items)?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::Record { dest, base, fields } => {
            let value = make_record_value(
                module_backend,
                builder,
                function,
                *base,
                fields,
                literals,
                values,
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::RecordWithoutFields { dest, base, fields } => {
            let value = make_record_without_fields_value(
                module_backend,
                builder,
                function,
                *base,
                fields,
                literals,
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::Select { dest, base, field } => {
            let base = read_value(builder, function, *base)?;
            let (field_ptr, field_len) =
                literals.literal_bytes(module_backend, builder, field.0.as_bytes())?;
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_record_select_i64",
                &[base, field_ptr, field_len],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::SelectWithDefault {
            dest,
            base,
            field,
            default,
        } => {
            let base = read_value(builder, function, *base)?;
            let default = read_value(builder, function, *default)?;
            let (field_ptr, field_len) =
                literals.literal_bytes(module_backend, builder, field.0.as_bytes())?;
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_record_select_or_default_i64",
                &[base, field_ptr, field_len, default],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::RecordHasField { dest, base, field } => {
            let base = read_value(builder, function, *base)?;
            let (field_ptr, field_len) =
                literals.literal_bytes(module_backend, builder, field.0.as_bytes())?;
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_record_has_field_i64",
                &[base, field_ptr, field_len],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::Variant { dest, tag, value } => {
            let value = value
                .map(|value| {
                    read_runtime_value_i64(module_backend, builder, function, values, value)
                })
                .transpose()?;
            let tag = register_variant_tag(module_backend, builder, tag, literals)?;
            let result = if let Some(value) = value {
                call_i64_helper(
                    module_backend,
                    builder,
                    "yulang_cps_variant_i64_1",
                    &[tag, value],
                )?
            } else {
                call_i64_helper(module_backend, builder, "yulang_cps_variant_i64_0", &[tag])?
            };
            builder.def_var(variable(*dest), result);
        }
        CpsStmt::TupleGet { dest, tuple, index } => {
            let tuple = read_value(builder, function, *tuple)?;
            let index = builder.ins().iconst(types::I64, *index as i64);
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_tuple_get_i64",
                &[tuple, index],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::VariantTagEq { dest, variant, tag } => {
            let variant = read_value(builder, function, *variant)?;
            let tag = builder.ins().iconst(types::I64, tag_hash(tag));
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_variant_tag_eq_i64",
                &[variant, tag],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::VariantPayload { dest, variant } => {
            let variant = read_value(builder, function, *variant)?;
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_variant_payload_i64",
                &[variant],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::Primitive { dest, op, args } => {
            let args = read_primitive_args(module_backend, builder, function, values, *op, args)?;
            let value = lower_primitive(module_backend, builder, function, *op, &args)?;
            define_value_as_lane(builder, values, *dest, primitive_result_lane(*op), value);
        }
        CpsStmt::DirectCall { dest, target, args } => {
            lower_direct_call_stmt(
                module_backend,
                builder,
                function,
                functions,
                values,
                *dest,
                target,
                args,
            )?;
        }
        CpsStmt::ApplyClosure { dest, closure, arg } => {
            let closure = read_value(builder, function, *closure)?;
            let arg = read_value(builder, function, *arg)?;
            // write27-d d5: fresh eval context for the sync apply.
            let (saved_eval, saved_initial) = enter_callee_eval_context(module_backend, builder)?;
            let value = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_apply_closure_i64",
                &[closure, arg],
            )?;
            restore_caller_eval_context(module_backend, builder, saved_eval, saved_initial)?;
            let value = abort_result_or_return(module_backend, builder, value)?;
            return_if_scope_return_active(module_backend, builder, value)?;
            builder.def_var(variable(*dest), value);
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
        CpsStmt::InstallHandler { handler, envs, .. } => {
            capture_handler_envs(module_backend, builder, function, *handler, envs)?;
            let handler = builder.ins().iconst(types::I64, handler.0 as i64);
            let consumes_mask = builder.ins().iconst(types::I64, -1);
            let _ = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_install_handler_i64",
                &[handler, consumes_mask],
            )?;
        }
        CpsStmt::UninstallHandler { handler } => {
            let handler = builder.ins().iconst(types::I64, handler.0 as i64);
            let _ = call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_uninstall_handler_i64",
                &[handler],
            )?;
        }
    }
    Ok(())
}

fn lower_terminator(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    blocks: &HashMap<CpsContinuationId, ir::Block>,
    continuation: &CpsReprAbiContinuation,
    terminator: &CpsTerminator,
    values: &LocalValueCache,
) -> CpsReprCraneliftResult<()> {
    match terminator {
        CpsTerminator::Return(value) => {
            let value = read_value_as_lane(
                builder,
                function,
                values,
                *value,
                effective_continuation_return_lane(function, continuation),
            )?;
            builder.ins().return_(&[value]);
        }
        CpsTerminator::Continue { target, args } => {
            let target_continuation = lookup_continuation(function, *target)?;
            let target = continuation_block(function, blocks, *target)?;
            let args = read_block_args(builder, function, values, target_continuation, args)?;
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
        CpsTerminator::EffectfulCall { .. } => {
            return Err(CpsReprCraneliftError::UnsupportedTerminator {
                function: function.name.clone(),
                kind: "effectful-call",
            });
        }
        CpsTerminator::EffectfulApply { .. } => {
            return Err(CpsReprCraneliftError::UnsupportedTerminator {
                function: function.name.clone(),
                kind: "effectful-apply",
            });
        }
        CpsTerminator::EffectfulForce { .. } => {
            return Err(CpsReprCraneliftError::UnsupportedTerminator {
                function: function.name.clone(),
                kind: "effectful-force",
            });
        }
    }
    Ok(())
}

fn lower_direct_call_stmt<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    functions: &DeclaredFunctions,
    values: &mut LocalValueCache,
    dest: CpsValueId,
    target: &str,
    args: &[CpsValueId],
) -> CpsReprCraneliftResult<()> {
    let id = functions.functions.get(target).copied().ok_or_else(|| {
        CpsReprCraneliftError::MissingFunction {
            name: target.to_string(),
        }
    })?;
    let callee = module_backend.declare_func_in_func(id, builder.func);
    let args = read_call_args(builder, function, values, args, target, functions)?;
    let result_lane = functions
        .function_returns
        .get(target)
        .copied()
        .unwrap_or(CpsReprAbiLane::Unknown);

    if !functions
        .function_effect_flow
        .get(target)
        .copied()
        .unwrap_or(true)
    {
        let call = builder.ins().call(callee, &args);
        let results = builder.inst_results(call);
        if results.len() != 1 {
            return Err(CpsReprCraneliftError::InvalidReturnArity {
                function: target.to_string(),
                arity: results.len(),
            });
        }
        define_value_as_lane(builder, values, dest, result_lane, results[0]);
        return Ok(());
    }

    // Effectful callees may route local returns through the eval context, so
    // they keep the heavier call protocol. Pure callees use the plain call
    // path above and can be optimized like ordinary SSA calls.
    let (saved_eval, saved_initial) = enter_callee_eval_context(module_backend, builder)?;
    let call = builder.ins().call(callee, &args);
    let results = builder.inst_results(call);
    if results.len() != 1 {
        return Err(CpsReprCraneliftError::InvalidReturnArity {
            function: target.to_string(),
            arity: results.len(),
        });
    }
    let result = results[0];
    restore_caller_eval_context(module_backend, builder, saved_eval, saved_initial)?;
    let result = abort_result_or_return(module_backend, builder, result)?;
    let scope_fallback = scope_return_fallback_for_lane(builder, result_lane, result);
    return_if_scope_return_active(module_backend, builder, scope_fallback)?;
    define_value_as_lane(builder, values, dest, result_lane, result);
    Ok(())
}

fn effect_matches(expected: &typed_ir::Path, actual: &typed_ir::Path) -> bool {
    effect_path_matches_allowed(expected, actual)
}

fn effect_allowed_by_type(allowed: &typed_ir::Type, effect: &typed_ir::Path) -> bool {
    match allowed {
        typed_ir::Type::Any => true,
        typed_ir::Type::Never => false,
        typed_ir::Type::Named { path, .. } => effect_path_matches_allowed(path, effect),
        typed_ir::Type::Row { items, tail } => {
            items
                .iter()
                .any(|item| effect_allowed_by_type(item, effect))
                || matches!(tail.as_ref(), typed_ir::Type::Any)
        }
        _ => false,
    }
}

fn effect_path_matches_allowed(allowed: &typed_ir::Path, effect: &typed_ir::Path) -> bool {
    if effect.segments.starts_with(&allowed.segments) {
        return true;
    }
    if allowed.segments.len() > 1
        && effect.segments.len() == allowed.segments.len()
        && effect.segments[..effect.segments.len() - 1]
            == allowed.segments[..allowed.segments.len() - 1]
        && effect_segment_matches_allowed(
            &allowed.segments[allowed.segments.len() - 1],
            &effect.segments[effect.segments.len() - 1],
        )
    {
        return true;
    }
    effect
        .segments
        .iter()
        .enumerate()
        .skip(1)
        .any(|(index, _)| effect.segments[index..].starts_with(&allowed.segments))
}

fn effect_segment_matches_allowed(allowed: &typed_ir::Name, effect: &typed_ir::Name) -> bool {
    allowed == effect
        || effect
            .0
            .strip_suffix("#effect")
            .is_some_and(|base| base == allowed.0)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HostConsoleEffect {
    Debug,
    OutWrite,
    ErrWrite,
    WarnWrite,
    DieDie,
}

fn host_console_effect_kind(effect: &typed_ir::Path) -> Option<HostConsoleEffect> {
    match effect.segments.as_slice() {
        [std, prelude, role, method]
            if std.0 == "std"
                && prelude.0 == "prelude"
                && role.0 == "Debug"
                && method.0 == "debug" =>
        {
            Some(HostConsoleEffect::Debug)
        }
        [std, module_seg, act_seg, operation] if std.0 == "std" && module_seg.0 == "out" => {
            match (act_seg.0.as_str(), operation.0.as_str()) {
                ("out", "write") => Some(HostConsoleEffect::OutWrite),
                ("err", "write") => Some(HostConsoleEffect::ErrWrite),
                ("warn", "warn") => Some(HostConsoleEffect::WarnWrite),
                ("die", "die") => Some(HostConsoleEffect::DieDie),
                _ => None,
            }
        }
        _ => None,
    }
}

fn lower_literal<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    literal: &CpsLiteral,
    literals: &mut L,
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
        CpsLiteral::Float(value) => {
            let value =
                value
                    .parse::<f64>()
                    .map_err(|_| CpsReprCraneliftError::UnsupportedLiteral {
                        function: function.name.clone(),
                        literal: literal.clone(),
                    })?;
            Ok(builder.ins().f64const(value))
        }
        CpsLiteral::String(value) => {
            let (ptr, len) = literals.literal_bytes(module_backend, builder, value.as_bytes())?;
            call_i64_helper(
                module_backend,
                builder,
                "yulang_cps_string_literal_i64",
                &[ptr, len],
            )
        }
    }
}

fn lower_primitive<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    _function: &CpsReprAbiFunction,
    op: typed_ir::PrimitiveOp,
    args: &[ir::Value],
) -> CpsReprCraneliftResult<ir::Value> {
    let value = match op {
        typed_ir::PrimitiveOp::BoolNot => {
            let zero = builder.ins().iconst(types::I64, 0);
            let is_zero = builder
                .ins()
                .icmp(ir::condcodes::IntCC::Equal, args[0], zero);
            builder.ins().uextend(types::I64, is_zero)
        }
        typed_ir::PrimitiveOp::BoolEq | typed_ir::PrimitiveOp::IntEq => {
            let eq = builder
                .ins()
                .icmp(ir::condcodes::IntCC::Equal, args[0], args[1]);
            builder.ins().uextend(types::I64, eq)
        }
        typed_ir::PrimitiveOp::IntAdd => builder.ins().iadd(args[0], args[1]),
        typed_ir::PrimitiveOp::IntSub => builder.ins().isub(args[0], args[1]),
        typed_ir::PrimitiveOp::IntMul => builder.ins().imul(args[0], args[1]),
        typed_ir::PrimitiveOp::IntDiv => builder.ins().sdiv(args[0], args[1]),
        typed_ir::PrimitiveOp::IntLt => {
            int_cmp(builder, ir::condcodes::IntCC::SignedLessThan, args)
        }
        typed_ir::PrimitiveOp::IntLe => {
            int_cmp(builder, ir::condcodes::IntCC::SignedLessThanOrEqual, args)
        }
        typed_ir::PrimitiveOp::IntGt => {
            int_cmp(builder, ir::condcodes::IntCC::SignedGreaterThan, args)
        }
        typed_ir::PrimitiveOp::IntGe => int_cmp(
            builder,
            ir::condcodes::IntCC::SignedGreaterThanOrEqual,
            args,
        ),
        typed_ir::PrimitiveOp::FloatAdd => builder.ins().fadd(args[0], args[1]),
        typed_ir::PrimitiveOp::FloatSub => builder.ins().fsub(args[0], args[1]),
        typed_ir::PrimitiveOp::FloatMul => builder.ins().fmul(args[0], args[1]),
        typed_ir::PrimitiveOp::FloatDiv => builder.ins().fdiv(args[0], args[1]),
        typed_ir::PrimitiveOp::FloatEq => float_cmp(builder, ir::condcodes::FloatCC::Equal, args),
        typed_ir::PrimitiveOp::FloatLt => {
            float_cmp(builder, ir::condcodes::FloatCC::LessThan, args)
        }
        typed_ir::PrimitiveOp::FloatLe => {
            float_cmp(builder, ir::condcodes::FloatCC::LessThanOrEqual, args)
        }
        typed_ir::PrimitiveOp::FloatGt => {
            float_cmp(builder, ir::condcodes::FloatCC::GreaterThan, args)
        }
        typed_ir::PrimitiveOp::FloatGe => {
            float_cmp(builder, ir::condcodes::FloatCC::GreaterThanOrEqual, args)
        }
        typed_ir::PrimitiveOp::ListEmpty => {
            call_i64_helper(module_backend, builder, "yulang_cps_list_empty_i64", &[])?
        }
        typed_ir::PrimitiveOp::ListSingleton => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_list_singleton_i64",
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::ListMerge => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_list_merge_i64",
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::ListLen => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_list_len_i64",
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::ListIndex => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_list_index_i64",
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::ListIndexRangeRaw => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_list_index_range_raw_i64",
            &[args[0], args[1], args[2]],
        )?,
        typed_ir::PrimitiveOp::ListIndexRange => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_list_index_range_i64",
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::ListSpliceRaw => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_list_splice_raw_i64",
            &[args[0], args[1], args[2], args[3]],
        )?,
        typed_ir::PrimitiveOp::ListSplice => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_list_splice_i64",
            &[args[0], args[1], args[2]],
        )?,
        typed_ir::PrimitiveOp::ListViewRaw => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_list_view_raw_i64",
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::IntToString => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_int_to_string_i64",
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::IntToHex => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_int_to_hex_i64",
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::IntToUpperHex => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_int_to_upper_hex_i64",
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::BoolToString => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_bool_to_string_i64",
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::FloatToString => call_helper(
            module_backend,
            builder,
            "yulang_cps_float_to_string_f64",
            &[types::F64],
            types::I64,
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::StringConcat => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_string_concat_i64",
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::StringEq => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_string_eq_i64",
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::StringLen => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_string_len_i64",
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::StringIndex => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_string_index_i64",
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::StringIndexRangeRaw => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_string_index_range_raw_i64",
            &[args[0], args[1], args[2]],
        )?,
        typed_ir::PrimitiveOp::StringIndexRange => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_string_index_range_i64",
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::StringSpliceRaw => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_string_splice_raw_i64",
            &[args[0], args[1], args[2], args[3]],
        )?,
        typed_ir::PrimitiveOp::StringSplice => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_string_splice_i64",
            &[args[0], args[1], args[2]],
        )?,
        typed_ir::PrimitiveOp::StringToBytes => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_string_to_bytes_i64",
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::BytesLen => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_bytes_len_i64",
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::BytesEq => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_bytes_eq_i64",
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::BytesConcat => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_bytes_concat_i64",
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::BytesIndex => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_bytes_index_i64",
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::BytesIndexRange => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_bytes_index_range_i64",
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::BytesToUtf8Raw => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_bytes_to_utf8_raw_i64",
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::BytesToPath => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_bytes_to_path_i64",
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::PathToBytes => call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_path_to_bytes_i64",
            &[args[0]],
        )?,
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

fn float_cmp(
    builder: &mut FunctionBuilder<'_>,
    code: ir::condcodes::FloatCC,
    args: &[ir::Value],
) -> ir::Value {
    let cmp = builder.ins().fcmp(code, args[0], args[1]);
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
        let return_lane = effective_continuation_return_lane(function, continuation);
        if !has_effect_flow && !continuation.environment.is_empty() {
            return Err(CpsReprCraneliftError::UnsupportedFunction {
                function: function.name.clone(),
                reason: "continuation environment",
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
                    CpsLiteral::Int(_)
                    | CpsLiteral::Float(_)
                    | CpsLiteral::Bool(_)
                    | CpsLiteral::Unit
                    | CpsLiteral::String(_) => {}
                },
                CpsStmt::FreshGuard { .. }
                | CpsStmt::PeekGuard { .. }
                | CpsStmt::FindGuard { .. } => {}
                CpsStmt::MakeThunk { .. }
                | CpsStmt::AddThunkBoundary { .. }
                | CpsStmt::MakeClosure { .. }
                | CpsStmt::MakeRecursiveClosure { .. }
                | CpsStmt::ForceThunk { .. } => {}
                CpsStmt::Primitive { op, .. } => validate_primitive(function, *op)?,
                CpsStmt::Tuple { .. }
                | CpsStmt::Record { .. }
                | CpsStmt::RecordWithoutFields { .. }
                | CpsStmt::Variant { .. }
                | CpsStmt::Select { .. }
                | CpsStmt::SelectWithDefault { .. }
                | CpsStmt::RecordHasField { .. }
                | CpsStmt::TupleGet { .. }
                | CpsStmt::VariantTagEq { .. }
                | CpsStmt::VariantPayload { .. } => {}
                CpsStmt::DirectCall { .. }
                | CpsStmt::ApplyClosure { .. }
                | CpsStmt::CloneContinuation { .. } => {}
                CpsStmt::InstallHandler { .. } | CpsStmt::UninstallHandler { .. } => {}
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
            && return_lane != CpsReprAbiLane::ScalarI64
            && return_lane != CpsReprAbiLane::RuntimeValuePtr
            && return_lane != CpsReprAbiLane::ClosurePtr
            && return_lane != CpsReprAbiLane::ThunkPtr
            && return_lane != CpsReprAbiLane::OpaqueI64
            && return_lane != CpsReprAbiLane::Unknown
        {
            return Err(CpsReprCraneliftError::UnsupportedReturnLane {
                function: function.name.clone(),
                continuation: continuation.id,
                lane: return_lane,
            });
        }
        if return_lane != CpsReprAbiLane::ScalarI64 {
            match return_lane {
                CpsReprAbiLane::NativeFloat
                    if !has_effect_flow && !continuation_has_internal_call(continuation) => {}
                CpsReprAbiLane::RuntimeValuePtr
                | CpsReprAbiLane::ClosurePtr
                | CpsReprAbiLane::ThunkPtr
                | CpsReprAbiLane::ResumptionPtr
                | CpsReprAbiLane::OpaqueI64
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

fn continuation_has_internal_call(continuation: &CpsReprAbiContinuation) -> bool {
    continuation.stmts.iter().any(|stmt| {
        matches!(
            stmt,
            CpsStmt::DirectCall { .. }
                | CpsStmt::ApplyClosure { .. }
                | CpsStmt::ForceThunk { .. }
                | CpsStmt::Resume { .. }
                | CpsStmt::ResumeWithHandler { .. }
        )
    })
}

fn validate_value_lane(
    function: &CpsReprAbiFunction,
    value: &CpsReprAbiValue,
) -> CpsReprCraneliftResult<()> {
    match value.lane {
        CpsReprAbiLane::ScalarI64
        | CpsReprAbiLane::NativeFloat
        | CpsReprAbiLane::RuntimeValuePtr
        | CpsReprAbiLane::ClosurePtr
        | CpsReprAbiLane::ThunkPtr
        | CpsReprAbiLane::ResumptionPtr
        | CpsReprAbiLane::OpaqueI64
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
        | CpsReprAbiLane::ClosurePtr
        | CpsReprAbiLane::ThunkPtr
        | CpsReprAbiLane::ResumptionPtr
        | CpsReprAbiLane::OpaqueI64
        | CpsReprAbiLane::Unknown => Ok(()),
        lane => Err(CpsReprCraneliftError::UnsupportedLane {
            function: function.name.clone(),
            value,
            lane,
        }),
    }
}

fn validate_primitive(
    _function: &CpsReprAbiFunction,
    op: typed_ir::PrimitiveOp,
) -> CpsReprCraneliftResult<()> {
    match op {
        typed_ir::PrimitiveOp::BoolNot
        | typed_ir::PrimitiveOp::BoolEq
        | typed_ir::PrimitiveOp::IntAdd
        | typed_ir::PrimitiveOp::IntSub
        | typed_ir::PrimitiveOp::IntMul
        | typed_ir::PrimitiveOp::IntDiv
        | typed_ir::PrimitiveOp::IntEq
        | typed_ir::PrimitiveOp::IntLt
        | typed_ir::PrimitiveOp::IntLe
        | typed_ir::PrimitiveOp::IntGt
        | typed_ir::PrimitiveOp::IntGe
        | typed_ir::PrimitiveOp::FloatAdd
        | typed_ir::PrimitiveOp::FloatSub
        | typed_ir::PrimitiveOp::FloatMul
        | typed_ir::PrimitiveOp::FloatDiv
        | typed_ir::PrimitiveOp::FloatEq
        | typed_ir::PrimitiveOp::FloatLt
        | typed_ir::PrimitiveOp::FloatLe
        | typed_ir::PrimitiveOp::FloatGt
        | typed_ir::PrimitiveOp::FloatGe
        | typed_ir::PrimitiveOp::ListEmpty
        | typed_ir::PrimitiveOp::ListSingleton
        | typed_ir::PrimitiveOp::ListMerge
        | typed_ir::PrimitiveOp::ListLen
        | typed_ir::PrimitiveOp::ListIndex
        | typed_ir::PrimitiveOp::ListIndexRangeRaw
        | typed_ir::PrimitiveOp::ListIndexRange
        | typed_ir::PrimitiveOp::ListSpliceRaw
        | typed_ir::PrimitiveOp::ListSplice
        | typed_ir::PrimitiveOp::ListViewRaw
        | typed_ir::PrimitiveOp::IntToString
        | typed_ir::PrimitiveOp::IntToHex
        | typed_ir::PrimitiveOp::IntToUpperHex
        | typed_ir::PrimitiveOp::BoolToString
        | typed_ir::PrimitiveOp::FloatToString
        | typed_ir::PrimitiveOp::StringConcat
        | typed_ir::PrimitiveOp::StringEq
        | typed_ir::PrimitiveOp::StringLen
        | typed_ir::PrimitiveOp::StringIndex
        | typed_ir::PrimitiveOp::StringIndexRangeRaw
        | typed_ir::PrimitiveOp::StringIndexRange
        | typed_ir::PrimitiveOp::StringSpliceRaw
        | typed_ir::PrimitiveOp::StringSplice
        | typed_ir::PrimitiveOp::StringToBytes
        | typed_ir::PrimitiveOp::BytesLen
        | typed_ir::PrimitiveOp::BytesEq
        | typed_ir::PrimitiveOp::BytesConcat
        | typed_ir::PrimitiveOp::BytesIndex
        | typed_ir::PrimitiveOp::BytesIndexRange
        | typed_ir::PrimitiveOp::BytesToUtf8Raw
        | typed_ir::PrimitiveOp::BytesToPath
        | typed_ir::PrimitiveOp::PathToBytes => Ok(()),
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

fn read_values_as_lanes(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    local_values: &LocalValueCache,
    values: &[CpsValueId],
    lanes: impl IntoIterator<Item = CpsReprAbiLane>,
) -> CpsReprCraneliftResult<Vec<ir::Value>> {
    values
        .iter()
        .zip(lanes)
        .map(|(value, lane)| read_value_as_lane(builder, function, local_values, *value, lane))
        .collect()
}

fn read_primitive_args<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    local_values: &LocalValueCache,
    op: typed_ir::PrimitiveOp,
    values: &[CpsValueId],
) -> CpsReprCraneliftResult<Vec<ir::Value>> {
    if op == typed_ir::PrimitiveOp::ListSingleton {
        return read_runtime_values_i64(module_backend, builder, function, local_values, values);
    }

    let lanes = primitive_arg_lanes(op);
    values
        .iter()
        .enumerate()
        .map(|(index, value)| {
            let lane = lanes
                .and_then(|lanes| lanes.get(index).copied())
                .unwrap_or(CpsReprAbiLane::ScalarI64);
            if lane == CpsReprAbiLane::NativeFloat {
                return read_native_float_value(
                    module_backend,
                    builder,
                    function,
                    local_values,
                    *value,
                );
            }
            read_value_as_lane(builder, function, local_values, *value, lane)
        })
        .collect()
}

fn read_call_args(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    local_values: &LocalValueCache,
    values: &[CpsValueId],
    target: &str,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<Vec<ir::Value>> {
    if let Some(lanes) = functions.function_params.get(target) {
        return read_values_as_lanes(
            builder,
            function,
            local_values,
            values,
            lanes.iter().copied(),
        );
    }
    read_values(builder, function, values)
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

fn read_value_as_lane(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    local_values: &LocalValueCache,
    value: CpsValueId,
    lane: CpsReprAbiLane,
) -> CpsReprCraneliftResult<ir::Value> {
    if !function_value_ids(function).contains(&value) {
        return Err(CpsReprCraneliftError::MissingValue {
            function: function.name.clone(),
            value,
        });
    }
    if lane == CpsReprAbiLane::NativeFloat
        && let Some(value) = local_values.native_float.get(&value).copied()
    {
        return Ok(value);
    }
    Ok(builder.use_var(variable_for_lane(value, lane)))
}

fn read_runtime_values_i64<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    local_values: &LocalValueCache,
    values: &[CpsValueId],
) -> CpsReprCraneliftResult<Vec<ir::Value>> {
    values
        .iter()
        .map(|value| {
            read_runtime_value_i64(module_backend, builder, function, local_values, *value)
        })
        .collect()
}

fn read_runtime_value_i64<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    local_values: &LocalValueCache,
    value: CpsValueId,
) -> CpsReprCraneliftResult<ir::Value> {
    if let Some(literal) = value_literal(function, value) {
        match literal {
            CpsLiteral::Bool(_) => {
                let value = read_value(builder, function, value)?;
                return call_i64_helper(
                    module_backend,
                    builder,
                    "yulang_cps_box_bool_i64",
                    &[value],
                );
            }
            CpsLiteral::Unit => {
                return call_i64_helper(module_backend, builder, "yulang_cps_unit_i64", &[]);
            }
            _ => {}
        }
    }
    if effective_value_lane(function, value) == CpsReprAbiLane::NativeFloat
        || local_values.native_float.contains_key(&value)
    {
        let value =
            read_native_float_value(module_backend, builder, function, local_values, value)?;
        return call_helper(
            module_backend,
            builder,
            "yulang_cps_box_float_f64",
            &[types::F64],
            types::I64,
            &[value],
        );
    }
    read_value(builder, function, value)
}

fn value_literal(function: &CpsReprAbiFunction, value: CpsValueId) -> Option<&CpsLiteral> {
    function
        .continuations
        .iter()
        .flat_map(|continuation| continuation.stmts.iter())
        .find_map(|stmt| match stmt {
            CpsStmt::Literal { dest, literal } if *dest == value => Some(literal),
            _ => None,
        })
}

fn read_native_float_value<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    local_values: &LocalValueCache,
    value: CpsValueId,
) -> CpsReprCraneliftResult<ir::Value> {
    if let Some(value) = local_values.native_float.get(&value).copied() {
        return Ok(value);
    }
    let value = read_value(builder, function, value)?;
    call_helper(
        module_backend,
        builder,
        "yulang_cps_unbox_float_i64",
        &[types::I64],
        types::F64,
        &[value],
    )
}

fn define_value_as_lane(
    builder: &mut FunctionBuilder<'_>,
    local_values: &mut LocalValueCache,
    value: CpsValueId,
    lane: CpsReprAbiLane,
    ir_value: ir::Value,
) {
    if lane == CpsReprAbiLane::NativeFloat {
        local_values.native_float.insert(value, ir_value);
    }
    builder.def_var(variable_for_lane(value, lane), ir_value);
}

fn force_thunk_passes_native_float(
    function: &CpsReprAbiFunction,
    local_values: &LocalValueCache,
    value: CpsValueId,
) -> bool {
    effective_value_lane(function, value) == CpsReprAbiLane::NativeFloat
        || local_values.native_float.contains_key(&value)
}

fn lane_type(lane: CpsReprAbiLane) -> ir::Type {
    match lane {
        CpsReprAbiLane::NativeFloat => types::F64,
        CpsReprAbiLane::ScalarI64
        | CpsReprAbiLane::RuntimeValuePtr
        | CpsReprAbiLane::ClosurePtr
        | CpsReprAbiLane::ThunkPtr
        | CpsReprAbiLane::ResumptionPtr
        | CpsReprAbiLane::OpaqueI64
        | CpsReprAbiLane::Conflict
        | CpsReprAbiLane::Unknown => types::I64,
    }
}

fn read_block_args(
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    local_values: &LocalValueCache,
    target: &CpsReprAbiContinuation,
    values: &[CpsValueId],
) -> CpsReprCraneliftResult<Vec<ir::BlockArg>> {
    Ok(read_values_as_lanes(
        builder,
        function,
        local_values,
        values,
        target
            .params
            .iter()
            .map(|param| effective_value_lane(function, param.value)),
    )?
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
                | CpsStmt::AddThunkBoundary { dest, .. }
                | CpsStmt::MakeClosure { dest, .. }
                | CpsStmt::MakeRecursiveClosure { dest, .. }
                | CpsStmt::ForceThunk { dest, .. }
                | CpsStmt::Tuple { dest, .. }
                | CpsStmt::Record { dest, .. }
                | CpsStmt::RecordWithoutFields { dest, .. }
                | CpsStmt::Variant { dest, .. }
                | CpsStmt::Select { dest, .. }
                | CpsStmt::SelectWithDefault { dest, .. }
                | CpsStmt::RecordHasField { dest, .. }
                | CpsStmt::TupleGet { dest, .. }
                | CpsStmt::VariantTagEq { dest, .. }
                | CpsStmt::VariantPayload { dest, .. }
                | CpsStmt::Primitive { dest, .. }
                | CpsStmt::DirectCall { dest, .. }
                | CpsStmt::ApplyClosure { dest, .. }
                | CpsStmt::CloneContinuation { dest, .. }
                | CpsStmt::Resume { dest, .. }
                | CpsStmt::ResumeWithHandler { dest, .. } => values.push(*dest),
                CpsStmt::InstallHandler { .. } | CpsStmt::UninstallHandler { .. } => {}
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
        for stmt in &continuation.stmts {
            if stmt_dest(stmt) == Some(value) {
                return Some(stmt_result_lane(stmt));
            }
        }
    }
    None
}

fn effective_value_lane(function: &CpsReprAbiFunction, value: CpsValueId) -> CpsReprAbiLane {
    match value_lane(function, value) {
        Some(CpsReprAbiLane::Unknown) | None => {
            inferred_value_lane(function, value).unwrap_or(CpsReprAbiLane::Unknown)
        }
        Some(CpsReprAbiLane::OpaqueI64) => {
            inferred_value_lane(function, value).unwrap_or(CpsReprAbiLane::OpaqueI64)
        }
        Some(lane) => lane,
    }
}

fn inferred_value_lane(function: &CpsReprAbiFunction, value: CpsValueId) -> Option<CpsReprAbiLane> {
    let mut lane = None;
    for continuation in &function.continuations {
        if matches!(&continuation.terminator, CpsTerminator::Return(returned) if *returned == value)
            && continuation.return_lane != CpsReprAbiLane::Unknown
        {
            merge_inferred_lane(&mut lane, continuation.return_lane);
        }
        for stmt in &continuation.stmts {
            if stmt_dest(stmt) == Some(value) {
                merge_inferred_lane(&mut lane, stmt_result_lane(stmt));
            }
            if let CpsStmt::Primitive { op, args, .. } = stmt
                && let Some(arg_lanes) = primitive_arg_lanes(*op)
            {
                for (arg, arg_lane) in args.iter().zip(arg_lanes.iter().copied()) {
                    if *arg == value {
                        merge_inferred_lane(&mut lane, arg_lane);
                    }
                }
            }
        }
    }
    lane
}

fn effective_continuation_return_lane(
    function: &CpsReprAbiFunction,
    continuation: &CpsReprAbiContinuation,
) -> CpsReprAbiLane {
    if continuation.return_lane != CpsReprAbiLane::Unknown {
        return continuation.return_lane;
    }
    match &continuation.terminator {
        CpsTerminator::Return(value) => effective_value_lane(function, *value),
        _ => CpsReprAbiLane::Unknown,
    }
}

fn effective_function_param_lanes(function: &CpsReprAbiFunction) -> Vec<CpsReprAbiLane> {
    let entry = continuation(function, function.entry).ok();
    function
        .params
        .iter()
        .enumerate()
        .map(|(index, param)| {
            entry
                .and_then(|entry| entry.params.get(index))
                .map(|entry_param| effective_value_lane(function, entry_param.value))
                .filter(|lane| *lane != CpsReprAbiLane::Unknown)
                .unwrap_or_else(|| effective_value_lane(function, param.value))
        })
        .collect()
}

fn merge_inferred_lane(slot: &mut Option<CpsReprAbiLane>, lane: CpsReprAbiLane) {
    if lane == CpsReprAbiLane::Unknown {
        return;
    }
    *slot = Some(match *slot {
        None | Some(CpsReprAbiLane::Unknown) => lane,
        Some(existing) if existing == lane => existing,
        Some(CpsReprAbiLane::NativeFloat) => CpsReprAbiLane::NativeFloat,
        Some(_) if lane == CpsReprAbiLane::NativeFloat => CpsReprAbiLane::NativeFloat,
        Some(existing) => existing,
    });
}

fn stmt_result_lane(stmt: &CpsStmt) -> CpsReprAbiLane {
    match stmt {
        CpsStmt::Literal { literal, .. } => literal_lane(literal),
        CpsStmt::FreshGuard { .. }
        | CpsStmt::PeekGuard { .. }
        | CpsStmt::FindGuard { .. }
        | CpsStmt::VariantTagEq { .. }
        | CpsStmt::RecordHasField { .. } => CpsReprAbiLane::ScalarI64,
        CpsStmt::MakeThunk { .. } | CpsStmt::AddThunkBoundary { .. } => CpsReprAbiLane::ThunkPtr,
        CpsStmt::MakeClosure { .. } | CpsStmt::MakeRecursiveClosure { .. } => {
            CpsReprAbiLane::ClosurePtr
        }
        CpsStmt::Tuple { .. }
        | CpsStmt::Record { .. }
        | CpsStmt::RecordWithoutFields { .. }
        | CpsStmt::Variant { .. }
        | CpsStmt::Select { .. }
        | CpsStmt::SelectWithDefault { .. }
        | CpsStmt::TupleGet { .. }
        | CpsStmt::VariantPayload { .. }
        | CpsStmt::ForceThunk { .. }
        | CpsStmt::DirectCall { .. }
        | CpsStmt::ApplyClosure { .. }
        | CpsStmt::CloneContinuation { .. }
        | CpsStmt::Resume { .. }
        | CpsStmt::ResumeWithHandler { .. } => CpsReprAbiLane::Unknown,
        CpsStmt::Primitive { op, .. } => primitive_result_lane(*op),
        CpsStmt::InstallHandler { .. } | CpsStmt::UninstallHandler { .. } => {
            CpsReprAbiLane::Unknown
        }
    }
}

fn literal_lane(literal: &CpsLiteral) -> CpsReprAbiLane {
    match literal {
        CpsLiteral::Int(_) | CpsLiteral::Bool(_) | CpsLiteral::Unit => CpsReprAbiLane::ScalarI64,
        CpsLiteral::Float(_) => CpsReprAbiLane::NativeFloat,
        CpsLiteral::String(_) => CpsReprAbiLane::RuntimeValuePtr,
    }
}

fn primitive_arg_lanes(op: typed_ir::PrimitiveOp) -> Option<&'static [CpsReprAbiLane]> {
    const FLOAT_UNARY: &[CpsReprAbiLane] = &[CpsReprAbiLane::NativeFloat];
    const FLOAT_BINARY: &[CpsReprAbiLane] =
        &[CpsReprAbiLane::NativeFloat, CpsReprAbiLane::NativeFloat];
    match op {
        typed_ir::PrimitiveOp::FloatToString => Some(FLOAT_UNARY),
        typed_ir::PrimitiveOp::FloatAdd
        | typed_ir::PrimitiveOp::FloatSub
        | typed_ir::PrimitiveOp::FloatMul
        | typed_ir::PrimitiveOp::FloatDiv
        | typed_ir::PrimitiveOp::FloatEq
        | typed_ir::PrimitiveOp::FloatLt
        | typed_ir::PrimitiveOp::FloatLe
        | typed_ir::PrimitiveOp::FloatGt
        | typed_ir::PrimitiveOp::FloatGe => Some(FLOAT_BINARY),
        _ => None,
    }
}

fn primitive_result_lane(op: typed_ir::PrimitiveOp) -> CpsReprAbiLane {
    match op {
        typed_ir::PrimitiveOp::BoolNot
        | typed_ir::PrimitiveOp::BoolEq
        | typed_ir::PrimitiveOp::IntEq
        | typed_ir::PrimitiveOp::IntLt
        | typed_ir::PrimitiveOp::IntLe
        | typed_ir::PrimitiveOp::IntGt
        | typed_ir::PrimitiveOp::IntGe
        | typed_ir::PrimitiveOp::IntAdd
        | typed_ir::PrimitiveOp::IntSub
        | typed_ir::PrimitiveOp::IntMul
        | typed_ir::PrimitiveOp::IntDiv
        | typed_ir::PrimitiveOp::ListLen
        | typed_ir::PrimitiveOp::StringLen
        | typed_ir::PrimitiveOp::BytesLen
        | typed_ir::PrimitiveOp::BytesIndex
        | typed_ir::PrimitiveOp::FloatEq
        | typed_ir::PrimitiveOp::FloatLt
        | typed_ir::PrimitiveOp::FloatLe
        | typed_ir::PrimitiveOp::FloatGt
        | typed_ir::PrimitiveOp::FloatGe
        | typed_ir::PrimitiveOp::StringEq
        | typed_ir::PrimitiveOp::BytesEq => CpsReprAbiLane::ScalarI64,
        typed_ir::PrimitiveOp::FloatAdd
        | typed_ir::PrimitiveOp::FloatSub
        | typed_ir::PrimitiveOp::FloatMul
        | typed_ir::PrimitiveOp::FloatDiv => CpsReprAbiLane::NativeFloat,
        typed_ir::PrimitiveOp::ListEmpty
        | typed_ir::PrimitiveOp::ListSingleton
        | typed_ir::PrimitiveOp::ListMerge
        | typed_ir::PrimitiveOp::ListIndexRange
        | typed_ir::PrimitiveOp::ListSplice
        | typed_ir::PrimitiveOp::ListIndexRangeRaw
        | typed_ir::PrimitiveOp::ListSpliceRaw
        | typed_ir::PrimitiveOp::ListViewRaw
        | typed_ir::PrimitiveOp::StringIndex
        | typed_ir::PrimitiveOp::StringIndexRange
        | typed_ir::PrimitiveOp::StringSplice
        | typed_ir::PrimitiveOp::StringIndexRangeRaw
        | typed_ir::PrimitiveOp::StringSpliceRaw
        | typed_ir::PrimitiveOp::StringConcat
        | typed_ir::PrimitiveOp::StringToBytes
        | typed_ir::PrimitiveOp::BytesConcat
        | typed_ir::PrimitiveOp::BytesIndexRange
        | typed_ir::PrimitiveOp::BytesToUtf8Raw
        | typed_ir::PrimitiveOp::BytesToPath
        | typed_ir::PrimitiveOp::PathToBytes
        | typed_ir::PrimitiveOp::IntToString
        | typed_ir::PrimitiveOp::IntToHex
        | typed_ir::PrimitiveOp::IntToUpperHex
        | typed_ir::PrimitiveOp::FloatToString
        | typed_ir::PrimitiveOp::BoolToString => CpsReprAbiLane::RuntimeValuePtr,
        typed_ir::PrimitiveOp::ListIndex => CpsReprAbiLane::Unknown,
    }
}

fn variable(value: CpsValueId) -> Variable {
    variable_for_lane(value, CpsReprAbiLane::ScalarI64)
}

fn variable_for_lane(value: CpsValueId, lane: CpsReprAbiLane) -> Variable {
    let slot = match lane {
        CpsReprAbiLane::NativeFloat => 1,
        _ => 0,
    };
    Variable::from_u32((value.0 as u32) * 2 + slot)
}

fn cranelift_error(error: impl fmt::Display) -> CpsReprCraneliftError {
    CpsReprCraneliftError::Cranelift(error.to_string())
}

type NativeCpsI64Continuation = extern "C" fn(*const i64, i64) -> i64;
type NativeCpsI64ThunkEntry = extern "C" fn(*const i64) -> i64;
type NativeCpsI64ClosureEntry = extern "C" fn(*const i64, i64) -> i64;

/// write27-d d2: prompt anchor captured at a Perform site. Mirrors
/// `CpsReprHandlerAnchor` — identifies which `(prompt, install_eval_id)`
/// pair was the matched real handler, so `apply_resumption`'s anchor
/// merge can drop redundant frames between the inherited and captured
/// portions of the resumption's stack.
#[derive(Debug, Clone, Copy)]
struct NativeCpsI64HandlerAnchor {
    prompt: u64,
    install_eval_id: u64,
}

#[derive(Debug, Clone, Copy)]
struct NativeCpsI64BlockedEffect {
    guard_id: i64,
    allowed_mask: i64,
    active: bool,
}

#[repr(C)]
struct NativeCpsI64Resumption {
    code: NativeCpsI64Continuation,
    env: Box<[i64]>,
    handlers: Box<[NativeCpsI64HandlerFrame]>,
    guard_stack: Box<[i64]>,
    /// write27-d d2: return-frame stack captured at the Perform call
    /// site. `effectful_apply_resumption` merges these with the new
    /// caller's frames (post-anchor) to rebuild Layer 1/2's
    /// `combined_frames`.
    return_frames: Box<[NativeCpsI64ReturnFrame]>,
    /// write27-d d2: anchor for the matched real handler at capture
    /// time. `None` when the Perform site only saw a synthetic frame
    /// (no merge needed).
    handled_anchor: Option<NativeCpsI64HandlerAnchor>,
    debug_id: u64,
}

#[repr(C)]
struct NativeCpsI64Thunk {
    code: NativeCpsI64ThunkEntry,
    env: Box<[i64]>,
    handlers: Box<[NativeCpsI64HandlerFrame]>,
    guard_stack: Box<[i64]>,
    active_blocked: Box<[NativeCpsI64BlockedEffect]>,
}

#[repr(C)]
struct NativeCpsI64Closure {
    code: NativeCpsI64ClosureEntry,
    env: Box<[i64]>,
    handlers: Box<[NativeCpsI64HandlerFrame]>,
    guard_stack: Box<[i64]>,
}

enum NativeCpsI64HeapValue {
    Tuple(Box<[i64]>),
    Record(Vec<(Box<str>, i64)>),
    Variant { tag: i64, value: Option<i64> },
    List(Vec<i64>),
    Bool(bool),
    Unit,
    Float(f64),
    String(Box<str>),
    Bytes(BytesTree),
    Path(std::path::PathBuf),
}

/// write27-d d1: tag where a `NativeCpsI64HandlerFrame` came from so
/// the trace + future origin-priority `select_handler` can distinguish
/// e.g. real installs from pending-env synthetic frames.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativeCpsI64HandlerFrameOrigin {
    /// Installed by an `InstallHandler` stmt through
    /// `install_handler_full_i64_N` (real prompt + escape).
    RealInstall,
    /// Installed by the legacy `yulang_cps_install_handler_i64` (no
    /// escape continuation, synthetic eval id).
    LegacyInstall,
    /// Built by `take_pending_native_i64_handler_frames` — a placeholder
    /// constructed from pending capture envs without scope info.
    PendingEnv,
    /// Pushed by `yulang_cps_resume_with_handler_i64` on top of a
    /// resumption's handler snapshot.
    ResumeWithHandler,
    /// Synthetic fallback inserted by
    /// `current_native_i64_handler_stack_with_fallback` when the active
    /// stack is empty.
    StaticFallback,
}

#[derive(Clone)]
struct NativeCpsI64HandlerFrame {
    handler: i64,
    consumes_mask: i64,
    guard_stack: Box<[i64]>,
    envs: Vec<NativeCpsI64HandlerEnv>,
    /// write27-c c2: dynamic prompt identity. Distinguishes frame
    /// instances installed under the same `CpsHandlerId` so that
    /// `ScopeReturn` targets a specific scope.
    prompt: u64,
    /// write27-c c2: which eval frame this handler was installed in.
    /// `ScopeReturn` routing only resolves a handler when current eval
    /// matches the install eval (mirrors cps_eval's CpsEvalId check).
    install_eval_id: u64,
    /// Function that owns the escape continuation. Layer 1/2 check this
    /// by name; the JIT keeps a compact id so frame-walk routing cannot
    /// jump to a continuation through a frame owned by a different
    /// function that happens to share the same eval id.
    escape_owner_function_id: u64,
    /// Owner function of the return frame immediately below this handler's
    /// dynamic extent at install time. Scoped abort uses this to know whether
    /// reaching `return_frame_threshold` means "resume the caller frame" or
    /// "keep escaping inside the same owner".
    threshold_owner_function_id: u64,
    /// write27-c c2: whether this frame was inherited from a captured
    /// resumption's handler stack (i.e., not freshly installed by an
    /// `InstallHandler` stmt in the current eval).
    inherited: bool,
    /// write27-c c2: JIT function pointer for the escape continuation
    /// (reached when the handler scope completes / aborts). 0 means
    /// "synthetic / no escape" (legacy passthrough).
    escape_continuation: usize,
    /// write27-c c2: env slots for the escape continuation. Stored as
    /// `Box<[i64]>` so the pointer stays stable while the frame lives.
    escape_env: Box<[i64]>,
    escape_env_targets: Box<[i64]>,
    /// write27-c c2: `return_frame_len` observed at install time. When
    /// a `ScopeReturn` resolves to this frame, the return-frame stack
    /// is truncated back to this length.
    return_frame_threshold: usize,
    return_frame_prefix: Box<[NativeCpsI64ReturnFrame]>,
    /// write27-d d1: provenance tag for diagnostics. Not load-bearing
    /// (yet); informs the JIT trace and lets future steps gate
    /// `select_handler` on real-vs-synthetic origin.
    origin: NativeCpsI64HandlerFrameOrigin,
}

#[derive(Clone)]
struct NativeCpsI64HandlerEnv {
    entry: i64,
    env: i64,
    slots: Vec<(i64, i64)>,
}

/// write27-a: prompt-targeted non-local return for Cranelift JIT.
/// Mirrors `cps_eval::CpsRuntimeValue::ScopeReturn` and
/// `cps_repr::CpsReprRuntimeValue::ScopeReturn`.
#[derive(Debug, Clone, Default)]
struct NativeCpsI64ScopeReturn {
    active: bool,
    prompt: u64,
    target: i64,
    value: i64,
}

/// Legacy non-local short-circuit slot used by paths that have not yet moved
/// to prompt-targeted `ScopeReturn`. Keeping the shape explicit makes the next
/// scoped-abort step local to this type instead of spreading more
/// `Option<i64>` checks through the JIT helpers.
#[derive(Clone, Default)]
enum NativeCpsI64Abort {
    #[default]
    None,
    Global(i64),
    #[allow(dead_code)]
    Scoped {
        value: i64,
        return_frame_threshold: usize,
        propagate_at_threshold: bool,
        restore_frames: Box<[NativeCpsI64ReturnFrame]>,
    },
    RoutedJump {
        value: i64,
        return_frame_threshold: usize,
        continuation: usize,
        env: Box<[i64]>,
        handlers: Vec<NativeCpsI64HandlerFrame>,
        guards: Vec<i64>,
        return_frames: Box<[NativeCpsI64ReturnFrame]>,
        eval_context: NativeCpsI64EvalContext,
    },
}

impl NativeCpsI64Abort {
    fn is_active(&self) -> bool {
        !matches!(self, NativeCpsI64Abort::None)
    }

    fn value_or_zero(&self) -> i64 {
        match self {
            NativeCpsI64Abort::None => 0,
            NativeCpsI64Abort::Global(value) => *value,
            NativeCpsI64Abort::Scoped { value, .. } => *value,
            NativeCpsI64Abort::RoutedJump { value, .. } => *value,
        }
    }

    fn mode_at_frame_len(&self, frame_len: usize) -> i64 {
        match self {
            NativeCpsI64Abort::None => 0,
            NativeCpsI64Abort::Global(_) => 1,
            NativeCpsI64Abort::Scoped {
                return_frame_threshold,
                propagate_at_threshold,
                ..
            } => {
                if frame_len > *return_frame_threshold
                    || (*propagate_at_threshold && frame_len == *return_frame_threshold)
                {
                    1
                } else {
                    2
                }
            }
            NativeCpsI64Abort::RoutedJump {
                return_frame_threshold,
                ..
            } => {
                if frame_len > *return_frame_threshold {
                    1
                } else {
                    2
                }
            }
        }
    }

    fn is_routed_jump(&self) -> bool {
        matches!(self, NativeCpsI64Abort::RoutedJump { .. })
    }

    fn is_unguarded_routed_jump(&self) -> bool {
        matches!(
            self,
            NativeCpsI64Abort::RoutedJump { guards, .. } if guards.is_empty()
        )
    }
}

/// write27-a/b: suspended caller continuation captured at
/// `EffectfulCall / EffectfulApply / EffectfulForce`. Mirrors
/// `CpsReturnFrame` from cps_eval/cps_repr but with raw function-
/// pointer continuation instead of a `CpsContinuationId`.
#[derive(Clone)]
struct NativeCpsI64ReturnFrame {
    prompt_exit: Option<NativeCpsI64PromptExitFrame>,
    debug_id: u64,
    /// JIT continuation function pointer
    /// (`extern "C" fn(env: *const i64, arg: i64) -> i64`, matching
    /// `NativeCpsI64Continuation`).
    continuation: usize,
    /// Debug-only CPS continuation id. `0` means the frame was built
    /// by a runtime helper that does not currently know the source id.
    continuation_id: u32,
    /// Captured environment for the continuation. Each `i64` mirrors
    /// one entry in the resume continuation's `environment`. Stored as
    /// `Box<[i64]>` (matches `NativeCpsI64Resumption::env`) so the
    /// pointer passed to the JIT continuation is stable.
    env: Box<[i64]>,
    /// Handler stack snapshot at push time.
    handlers: Vec<NativeCpsI64HandlerFrame>,
    /// Guard stack snapshot at push time.
    guards: Vec<i64>,
    /// Owner eval's `initial_frame_count` at push time.
    owner_initial_frame_count: usize,
    /// Owner eval's identity. Restored as `current_eval_id` when this
    /// frame is consumed via `continue_return_frame_i64`.
    owner_eval_id: u64,
    /// Function that owns `continuation`.
    owner_function_id: u64,
    /// write27-b: whether the resume continuation's body begins by
    /// `ForceThunk`-ing its first parameter (mirrors
    /// `return_frame_immediately_forces_param` in cps_eval/cps_repr).
    /// Computed at codegen time and stored here so the JIT Return path
    /// can fire pre-force v2 without crossing back into Cranelift IR.
    immediately_forces_param: bool,
}

#[derive(Clone)]
struct NativeCpsI64PromptExitFrame {
    prompt: u64,
}

#[derive(Default)]
struct NativeCpsI64HandlerArmReturnFrameSnapshot {
    frames: Vec<NativeCpsI64ReturnFrame>,
    consumed_start: usize,
}

/// write27-a: per-eval-frame context. Mirrors the `current_eval_id` +
/// `initial_frame_count` parameters threaded through cps_eval.
#[derive(Debug, Clone, Copy, Default)]
struct NativeCpsI64EvalContext {
    current_eval_id: u64,
    initial_frame_count: usize,
}

#[derive(Clone, Default)]
struct NativeCpsI64PendingRoutedReturnFrames {
    skip_initial_frame_count: usize,
    frames: Vec<NativeCpsI64ReturnFrame>,
}

/// write27-a: synthetic eval-id sentinel (matches
/// `cps_eval::SYNTHETIC_EVAL_ID`). Used for fallback handler frames
/// that should never resolve a `ScopeReturn`.
const NATIVE_CPS_I64_SYNTHETIC_EVAL_ID: u64 = u64::MAX;

/// write27-a: sentinel target for `ResumeWithHandler`-installed frames
/// (matches `cps_eval::EXIT_RWH_TARGET`). Stored as `i64`.
#[allow(dead_code)]
const NATIVE_CPS_I64_EXIT_RWH_TARGET: i64 = -1;

/// write27-c c1: env-guarded JIT runtime trace. Set
/// `YULANG_CPS_JIT_TRACE=1` to see push/return/route events as the
/// JIT-compiled code runs. The check itself is cached in a static, so
/// hot paths only pay one atomic load per call when disabled.
fn jit_trace_enabled() -> bool {
    use std::sync::atomic::{AtomicU8, Ordering};
    static STATE: AtomicU8 = AtomicU8::new(0); // 0 = uninit, 1 = off, 2 = on
    match STATE.load(Ordering::Relaxed) {
        2 => true,
        1 => false,
        _ => {
            let on = std::env::var("YULANG_CPS_JIT_TRACE")
                .map(|v| v == "1")
                .unwrap_or(false);
            STATE.store(if on { 2 } else { 1 }, Ordering::Relaxed);
            on
        }
    }
}

/// write27-e e4: debug toggle to skip the current-handler match in
/// `route_scope_return_i64` and force the frame-walk path. Used to
/// verify whether the test failure on Layer 3 is caused by an
/// over-eager current-handler match.
fn jit_force_frame_walk_sr() -> bool {
    use std::sync::atomic::{AtomicU8, Ordering};
    static STATE: AtomicU8 = AtomicU8::new(0);
    match STATE.load(Ordering::Relaxed) {
        2 => true,
        1 => false,
        _ => {
            let on = std::env::var("YULANG_CPS_JIT_FORCE_FRAME_WALK_SR")
                .map(|v| v == "1")
                .unwrap_or(false);
            STATE.store(if on { 2 } else { 1 }, Ordering::Relaxed);
            on
        }
    }
}

thread_local! {
    static NATIVE_CPS_I64_HEAP_VALUES: RefCell<HashSet<i64>> = RefCell::new(HashSet::new());
    static NATIVE_CPS_I64_TAG_NAMES: RefCell<HashMap<i64, Box<str>>> = RefCell::new(HashMap::new());
    static NATIVE_CPS_I64_THUNKS: RefCell<HashSet<usize>> = RefCell::new(HashSet::new());
    static NATIVE_CPS_I64_CLOSURES: RefCell<HashSet<usize>> = RefCell::new(HashSet::new());
    /// write27-d d4: pointers known to be `NativeCpsI64Resumption`,
    /// inserted at `make_native_i64_resumption` time. EffectfulApply
    /// codegen queries this set at runtime to dispatch between the
    /// closure path and the anchor-merging resumption path.
    static NATIVE_CPS_I64_RESUMPTIONS: RefCell<HashSet<usize>> = RefCell::new(HashSet::new());
    static NATIVE_CPS_I64_ROOT_FUNCTION_IDS: RefCell<Vec<u64>> = const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_HANDLER_STACK: RefCell<Vec<NativeCpsI64HandlerFrame>> = const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_GUARD_STACK: RefCell<Vec<i64>> = const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_ACTIVE_BLOCKED: RefCell<Vec<NativeCpsI64BlockedEffect>> = const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_NEXT_GUARD: RefCell<i64> = const { RefCell::new(0) };
    static NATIVE_CPS_I64_NEXT_RESUMPTION_DEBUG_ID: RefCell<u64> = const { RefCell::new(1) };
    static NATIVE_CPS_I64_NEXT_RETURN_FRAME_DEBUG_ID: RefCell<u64> = const { RefCell::new(1) };
    static NATIVE_CPS_I64_PENDING_HANDLER_ENVS: RefCell<Vec<(i64, NativeCpsI64HandlerEnv)>> = const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_PENDING_ESCAPE_ENV_TARGETS: RefCell<Vec<i64>> = const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_SELECTED_HANDLER_ENVS: RefCell<Vec<NativeCpsI64HandlerEnv>> = const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_SELECTED_HANDLER_ID: RefCell<i64> = const { RefCell::new(-1) };
    static NATIVE_CPS_I64_SELECTED_HANDLER_USED_RWH_ENV: RefCell<bool> = const { RefCell::new(false) };
    // Layer 2 keeps ResumeWithHandler siblings in the local active handler
    // stack until the surrounding scope-return dispatch decides whether the
    // flow is local or non-local. The JIT rebuilds that stack from snapshots,
    // so the sibling frames need a small side table for later frame restores.
    static NATIVE_CPS_I64_RESUME_WITH_HANDLER_SIBLINGS: RefCell<Vec<NativeCpsI64HandlerFrame>> =
        const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_ABORT: RefCell<NativeCpsI64Abort> =
        const { RefCell::new(NativeCpsI64Abort::None) };
    static NATIVE_CPS_I64_HANDLER_THRESHOLD_OFFSET: RefCell<usize> = const { RefCell::new(0) };
    // write27-a: ScopeReturn slot. Mirrors `cps_eval`/`cps_repr`'s
    // ScopeReturn variant. Set by the new `yulang_cps_scope_return_i64`
    // helper (called by Perform codegen once it migrates) and read by
    // the route_scope_return helper after every internal call.
    static NATIVE_CPS_I64_SCOPE_RETURN: RefCell<NativeCpsI64ScopeReturn> =
        const { RefCell::new(NativeCpsI64ScopeReturn {
            active: false,
            prompt: 0,
            target: 0,
            value: 0,
        }) };
    // write27-a: return-frame stack. Each EffectfulCall/Force/Apply
    // pushes a frame here; Return consumes them via the
    // continue_return_frames helper.
    static NATIVE_CPS_I64_RETURN_FRAMES: RefCell<Vec<NativeCpsI64ReturnFrame>> =
        const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_PENDING_ROUTED_RETURN_FRAMES: RefCell<Option<NativeCpsI64PendingRoutedReturnFrames>> =
        const { RefCell::new(None) };
    static NATIVE_CPS_I64_RETURN_FRAMES_ROUTED: RefCell<bool> = const { RefCell::new(false) };
    static NATIVE_CPS_I64_CONSUMED_RETURN_FRAME_IDS: RefCell<Vec<u64>> =
        const { RefCell::new(Vec::new()) };
    static NATIVE_CPS_I64_HANDLER_ARM_RETURN_FRAME_SNAPSHOTS: RefCell<Vec<NativeCpsI64HandlerArmReturnFrameSnapshot>> =
        const { RefCell::new(Vec::new()) };
    // write27-a: per-eval context (current eval id + initial frame
    // count). Threaded explicitly in cps_eval/cps_repr; here we use
    // a thread-local because adding hidden params to every JIT
    // continuation would balloon the codegen.
    static NATIVE_CPS_I64_EVAL_CONTEXT: RefCell<NativeCpsI64EvalContext> =
        const { RefCell::new(NativeCpsI64EvalContext {
            current_eval_id: 0,
            initial_frame_count: 0,
        }) };
    // write27-a: monotonic counter for fresh eval ids. Mirrors
    // `cps_eval::EVAL_ID_COUNTER`.
    static NATIVE_CPS_I64_NEXT_EVAL_ID: RefCell<u64> = const { RefCell::new(0) };
    // write27-c c2: monotonic counter for fresh prompt ids. Each
    // `InstallHandler` stmt that uses the full helper gets a unique
    // prompt; `ScopeReturn` carries this prompt to disambiguate which
    // scope to dispatch to.
    static NATIVE_CPS_I64_NEXT_PROMPT: RefCell<u64> = const { RefCell::new(1) };
    // write27-c c3: snapshot of the handler stack saved when
    // `select_handler` truncates. The Perform arm body runs with the
    // truncated stack (matching Layer 1/2's `handler_body_stack`
    // semantics); `restore_outer_handler_stack` reinstates the
    // pre-truncation stack so the post-arm `route_scope_return` can
    // walk it. Stored as a stack to support nested Performs.
    static NATIVE_CPS_I64_OUTER_HANDLER_SNAPSHOTS: RefCell<Vec<Vec<NativeCpsI64HandlerFrame>>> =
        const { RefCell::new(Vec::new()) };
    // write27-c c3: metadata for the handler frame just selected by
    // `select_handler` (prompt, escape continuation, escape env,
    // return-frame threshold, install eval id, synthetic flag). The
    // Perform path uses this to wrap the arm's natural return as a
    // ScopeReturn pointing at the selected handler's escape.
    static NATIVE_CPS_I64_SELECTED_HANDLER_META_STACK: RefCell<Vec<NativeCpsI64SelectedHandlerMeta>> =
        const { RefCell::new(Vec::new()) };
}

/// write27-c c3: meta captured at `select_handler` time about the
/// selected frame, so the Perform post-arm path can synthesize a
/// `ScopeReturn` targeting its escape without re-walking the stack.
#[derive(Clone)]
#[allow(dead_code)]
struct NativeCpsI64SelectedHandlerMeta {
    prompt: u64,
    escape_continuation: usize,
    escape_env: Box<[i64]>,
    return_frame_threshold: usize,
    install_eval_id: u64,
    synthetic: bool,
}

fn reset_native_i64_cps_state() {
    NATIVE_CPS_I64_HEAP_VALUES.with(|values| values.borrow_mut().clear());
    NATIVE_CPS_I64_TAG_NAMES.with(|names| names.borrow_mut().clear());
    NATIVE_CPS_I64_THUNKS.with(|thunks| thunks.borrow_mut().clear());
    NATIVE_CPS_I64_CLOSURES.with(|closures| closures.borrow_mut().clear());
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow_mut().clear());
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| stack.borrow_mut().clear());
    NATIVE_CPS_I64_ACTIVE_BLOCKED.with(|stack| stack.borrow_mut().clear());
    NATIVE_CPS_I64_NEXT_GUARD.with(|next| *next.borrow_mut() = 0);
    NATIVE_CPS_I64_NEXT_RESUMPTION_DEBUG_ID.with(|next| *next.borrow_mut() = 1);
    NATIVE_CPS_I64_NEXT_RETURN_FRAME_DEBUG_ID.with(|next| *next.borrow_mut() = 1);
    NATIVE_CPS_I64_PENDING_HANDLER_ENVS.with(|envs| envs.borrow_mut().clear());
    NATIVE_CPS_I64_PENDING_ESCAPE_ENV_TARGETS.with(|targets| targets.borrow_mut().clear());
    NATIVE_CPS_I64_SELECTED_HANDLER_ENVS.with(|envs| envs.borrow_mut().clear());
    NATIVE_CPS_I64_SELECTED_HANDLER_ID.with(|handler| *handler.borrow_mut() = -1);
    NATIVE_CPS_I64_SELECTED_HANDLER_USED_RWH_ENV.with(|used| *used.borrow_mut() = false);
    NATIVE_CPS_I64_RESUME_WITH_HANDLER_SIBLINGS.with(|handlers| handlers.borrow_mut().clear());
    NATIVE_CPS_I64_ABORT.with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::None);
    NATIVE_CPS_I64_HANDLER_THRESHOLD_OFFSET.with(|slot| *slot.borrow_mut() = 0);
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| {
        *slot.borrow_mut() = NativeCpsI64ScopeReturn::default();
    });
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow_mut().clear());
    NATIVE_CPS_I64_RETURN_FRAMES_ROUTED.with(|routed| *routed.borrow_mut() = false);
    NATIVE_CPS_I64_CONSUMED_RETURN_FRAME_IDS.with(|ids| ids.borrow_mut().clear());
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| {
        *ctx.borrow_mut() = NativeCpsI64EvalContext::default();
    });
    NATIVE_CPS_I64_NEXT_EVAL_ID.with(|next| *next.borrow_mut() = 0);
    NATIVE_CPS_I64_NEXT_PROMPT.with(|next| *next.borrow_mut() = 1);
    NATIVE_CPS_I64_OUTER_HANDLER_SNAPSHOTS.with(|snaps| snaps.borrow_mut().clear());
    NATIVE_CPS_I64_SELECTED_HANDLER_META_STACK.with(|meta| meta.borrow_mut().clear());
    NATIVE_CPS_I64_RESUMPTIONS.with(|s| s.borrow_mut().clear());
    NATIVE_CPS_I64_ROOT_FUNCTION_IDS.with(|ids| ids.borrow_mut().clear());
}

fn set_native_i64_root_function_ids(ids: &[u64]) {
    NATIVE_CPS_I64_ROOT_FUNCTION_IDS.with(|slot| {
        *slot.borrow_mut() = ids.to_vec();
    });
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_reset_i64() {
    reset_native_i64_cps_state();
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_set_root_function_ids_i64(ids: *const u64, len: usize) {
    if ids.is_null() {
        if len == 0 {
            set_native_i64_root_function_ids(&[]);
        }
        return;
    }
    let ids = unsafe { std::slice::from_raw_parts(ids, len) };
    set_native_i64_root_function_ids(ids);
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_take_root_result_i64(value: i64) -> i64 {
    take_native_i64_root_result(value)
}

fn take_native_i64_root_result(value: i64) -> i64 {
    let mode = yulang_cps_abort_mode_i64();
    if mode == 0 {
        return value;
    }
    let abort = if mode == 2 {
        yulang_cps_consume_abort_i64()
    } else {
        let value = yulang_cps_abort_value_i64();
        let _ = yulang_cps_clear_abort_i64();
        value
    };
    let _ = yulang_cps_clear_scope_return_i64();
    // The root boundary owns abort extraction. Leftover prompt-exit frames came
    // from skipped native callers and would re-apply handler value arms if a
    // thunk payload had to be forced for display.
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow_mut().clear());
    force_native_i64_root_result(abort)
}

fn force_native_i64_root_result(value: i64) -> i64 {
    let is_thunk = usize::try_from(value)
        .ok()
        .is_some_and(|value| NATIVE_CPS_I64_THUNKS.with(|thunks| thunks.borrow().contains(&value)));
    if is_thunk {
        yulang_cps_force_thunk_i64(value as usize)
    } else {
        value
    }
}

fn native_i64_abort_is_routed_jump() -> bool {
    NATIVE_CPS_I64_ABORT.with(|slot| slot.borrow().is_routed_jump())
}

fn native_i64_abort_is_unguarded_routed_jump() -> bool {
    NATIVE_CPS_I64_ABORT.with(|slot| slot.borrow().is_unguarded_routed_jump())
}

fn native_i64_abort_should_consume_after_thunk_force() -> bool {
    native_i64_abort_is_unguarded_routed_jump() && yulang_cps_abort_mode_i64() == 2
}

fn current_native_i64_guard_stack() -> Vec<i64> {
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| stack.borrow().clone())
}

fn current_native_i64_handler_stack_with_fallback(
    fallback: i64,
    effect_mask: i64,
) -> Vec<NativeCpsI64HandlerFrame> {
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        let stack = stack.borrow();
        if stack.is_empty() && fallback >= 0 {
            vec![NativeCpsI64HandlerFrame {
                handler: fallback,
                consumes_mask: effect_mask,
                guard_stack: current_native_i64_guard_stack().into_boxed_slice(),
                envs: Vec::new(),
                prompt: 0,
                install_eval_id: NATIVE_CPS_I64_SYNTHETIC_EVAL_ID,
                escape_owner_function_id: 0,
                threshold_owner_function_id: 0,
                inherited: false,
                escape_continuation: 0,
                escape_env: Box::new([]),
                escape_env_targets: Box::new([]),
                return_frame_threshold: 0,
                return_frame_prefix: Box::new([]),
                origin: NativeCpsI64HandlerFrameOrigin::StaticFallback,
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
                consumes_mask: -1,
                guard_stack: current_native_i64_guard_stack().into_boxed_slice(),
                envs: vec![env],
                prompt: 0,
                install_eval_id: NATIVE_CPS_I64_SYNTHETIC_EVAL_ID,
                escape_owner_function_id: 0,
                threshold_owner_function_id: 0,
                inherited: false,
                escape_continuation: 0,
                escape_env: Box::new([]),
                escape_env_targets: Box::new([]),
                return_frame_threshold: 0,
                return_frame_prefix: Box::new([]),
                origin: NativeCpsI64HandlerFrameOrigin::PendingEnv,
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

fn take_pending_native_i64_escape_env_targets() -> Vec<i64> {
    NATIVE_CPS_I64_PENDING_ESCAPE_ENV_TARGETS
        .with(|targets| std::mem::take(&mut *targets.borrow_mut()))
}

fn with_native_i64_cps_state<T>(
    handlers: Vec<NativeCpsI64HandlerFrame>,
    guard_stack: Vec<i64>,
    run: impl FnOnce() -> T,
) -> T {
    let active_blocked = NATIVE_CPS_I64_ACTIVE_BLOCKED.with(|stack| stack.borrow().clone());
    with_native_i64_cps_state_and_active(handlers, guard_stack, active_blocked, run)
}

fn with_native_i64_cps_state_and_active<T>(
    handlers: Vec<NativeCpsI64HandlerFrame>,
    guard_stack: Vec<i64>,
    active_blocked: Vec<NativeCpsI64BlockedEffect>,
    run: impl FnOnce() -> T,
) -> T {
    let previous_handlers = NATIVE_CPS_I64_HANDLER_STACK
        .with(|stack| std::mem::replace(&mut *stack.borrow_mut(), handlers));
    let previous_guards = NATIVE_CPS_I64_GUARD_STACK
        .with(|stack| std::mem::replace(&mut *stack.borrow_mut(), guard_stack));
    let previous_active = NATIVE_CPS_I64_ACTIVE_BLOCKED
        .with(|stack| std::mem::replace(&mut *stack.borrow_mut(), active_blocked));
    let result = run();
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| *stack.borrow_mut() = previous_handlers);
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| *stack.borrow_mut() = previous_guards);
    NATIVE_CPS_I64_ACTIVE_BLOCKED.with(|stack| *stack.borrow_mut() = previous_active);
    result
}

#[allow(dead_code)]
fn native_i64_handler_stack_with_captured(
    captured: &[NativeCpsI64HandlerFrame],
) -> Vec<NativeCpsI64HandlerFrame> {
    let mut handlers = NATIVE_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow().clone());
    handlers.extend(captured.iter().cloned());
    handlers
}

#[allow(dead_code)]
fn native_i64_handler_stack_for_force(
    captured: &[NativeCpsI64HandlerFrame],
) -> Vec<NativeCpsI64HandlerFrame> {
    let mut handlers = native_i64_handler_stack_with_captured(captured);
    handlers.extend(take_pending_native_i64_handler_frames());
    handlers
}

fn next_native_i64_resumption_debug_id() -> u64 {
    NATIVE_CPS_I64_NEXT_RESUMPTION_DEBUG_ID.with(|next| {
        let id = *next.borrow();
        *next.borrow_mut() = id + 1;
        id
    })
}

fn next_native_i64_return_frame_debug_id() -> u64 {
    NATIVE_CPS_I64_NEXT_RETURN_FRAME_DEBUG_ID.with(|next| {
        let id = *next.borrow();
        *next.borrow_mut() = id + 1;
        id
    })
}

fn make_native_i64_resumption(
    code: usize,
    fallback_handler: i64,
    env: Vec<i64>,
) -> *mut NativeCpsI64Resumption {
    let code = unsafe { std::mem::transmute::<usize, NativeCpsI64Continuation>(code) };
    // write27-d d2: capture the full Layer 1/2 resumption state.
    // `handled_anchor` is filled in later by
    // `yulang_cps_set_resumption_anchor_from_selected_i64` once
    // `select_handler` has decided which real handler was matched.
    let return_frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().clone());
    let handlers = current_native_i64_handler_stack_with_fallback(fallback_handler, -1);
    let debug_id = next_native_i64_resumption_debug_id();
    let ptr = Box::into_raw(Box::new(NativeCpsI64Resumption {
        code,
        env: env.into_boxed_slice(),
        handlers: handlers.clone().into_boxed_slice(),
        guard_stack: current_native_i64_guard_stack().into_boxed_slice(),
        return_frames: return_frames.into_boxed_slice(),
        handled_anchor: None,
        debug_id,
    }));
    NATIVE_CPS_I64_RESUMPTIONS.with(|s| {
        s.borrow_mut().insert(ptr as usize);
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] make_resumption: id={} ptr={:#x} handlers={} frames={}",
            debug_id,
            ptr as usize,
            format_handler_stack(&handlers),
            format_return_frames(unsafe { &(*ptr).return_frames }),
        );
    }
    ptr
}

/// write27-d d2: after `select_handler` records meta about the chosen
/// real handler, write that `(prompt, install_eval_id)` as the
/// resumption's `handled_anchor`. Called from the Perform codegen
/// immediately after `select_handler_i64` and before the arm call.
#[unsafe(no_mangle)]
extern "C" fn yulang_cps_set_resumption_anchor_from_selected_i64(
    resumption: *mut NativeCpsI64Resumption,
) -> i64 {
    let meta = NATIVE_CPS_I64_SELECTED_HANDLER_META_STACK.with(|m| m.borrow().last().cloned());
    if let Some(meta) = meta {
        if !meta.synthetic && meta.escape_continuation != 0 {
            unsafe {
                (*resumption).handled_anchor = Some(NativeCpsI64HandlerAnchor {
                    prompt: meta.prompt,
                    install_eval_id: meta.install_eval_id,
                });
                let start = native_i64_prompt_frame_start(
                    &(*resumption).return_frames,
                    meta.prompt,
                    meta.return_frame_threshold,
                );
                (*resumption).return_frames = capture_native_i64_return_frames_from_start(
                    &(*resumption).return_frames,
                    start,
                    meta.install_eval_id,
                );
                rebase_native_i64_captured_handlers(
                    &mut (*resumption).handlers,
                    start,
                    meta.install_eval_id,
                );
                // Inherited handlers (install_eval < anchor's install_eval) keep
                // their original absolute threshold after the shared rebase. When
                // the resumption is replayed inside an unrelated outer eval, the
                // slice frame layout no longer matches the original install
                // position, so re-derive the threshold from the prompt-exit
                // marker actually present in the slice. Apply the same fix to
                // each frame's handler snapshot.
                recalibrate_inherited_handler_thresholds(
                    &mut (*resumption).handlers,
                    &(*resumption).return_frames,
                    meta.install_eval_id,
                );
                let slice_snapshot = (*resumption).return_frames.clone();
                for frame in (*resumption).return_frames.iter_mut() {
                    recalibrate_inherited_handler_thresholds(
                        &mut frame.handlers,
                        &slice_snapshot,
                        meta.install_eval_id,
                    );
                }
            }
            if jit_trace_enabled() {
                eprintln!(
                    "[JIT-CPS] resumption_anchor: prompt={} install_eval={} frames={}",
                    meta.prompt,
                    meta.install_eval_id,
                    unsafe { format_return_frames(&(*resumption).return_frames) }
                );
            }
        }
    }
    0
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
        active_blocked: Box::new([]),
    })) as usize;
    NATIVE_CPS_I64_THUNKS.with(|thunks| {
        thunks.borrow_mut().insert(ptr);
    });
    ptr
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_add_thunk_boundary_i64(
    value: usize,
    guard_id: i64,
    allowed_mask: i64,
    active: i64,
) -> usize {
    let is_thunk = NATIVE_CPS_I64_THUNKS.with(|thunks| thunks.borrow().contains(&value));
    if !is_thunk {
        return value;
    }
    let thunk = unsafe { &*(value as *const NativeCpsI64Thunk) };
    let mut active_blocked = thunk.active_blocked.to_vec();
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] add_thunk_boundary: thunk={:#x} guard={} allowed_mask={} active={} existing={}",
            value,
            guard_id,
            allowed_mask,
            active,
            thunk.active_blocked.len(),
        );
    }
    active_blocked.push(NativeCpsI64BlockedEffect {
        guard_id,
        allowed_mask,
        active: active != 0,
    });
    let ptr = Box::into_raw(Box::new(NativeCpsI64Thunk {
        code: thunk.code,
        env: thunk.env.clone(),
        handlers: thunk.handlers.clone(),
        guard_stack: thunk.guard_stack.clone(),
        active_blocked: active_blocked.into_boxed_slice(),
    })) as usize;
    NATIVE_CPS_I64_THUNKS.with(|thunks| {
        thunks.borrow_mut().insert(ptr);
    });
    ptr
}

fn make_native_i64_closure(code: usize, env: Vec<i64>) -> usize {
    let code = unsafe { std::mem::transmute::<usize, NativeCpsI64ClosureEntry>(code) };
    let mut handlers = NATIVE_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow().clone());
    handlers.extend(take_pending_native_i64_handler_frames());
    let ptr = Box::into_raw(Box::new(NativeCpsI64Closure {
        code,
        env: env.into_boxed_slice(),
        handlers: handlers.into_boxed_slice(),
        guard_stack: current_native_i64_guard_stack().into_boxed_slice(),
    })) as usize;
    NATIVE_CPS_I64_CLOSURES.with(|closures| {
        closures.borrow_mut().insert(ptr);
    });
    ptr
}

fn make_native_i64_recursive_closure(code: usize, self_slot: usize, mut env: Vec<i64>) -> usize {
    let code = unsafe { std::mem::transmute::<usize, NativeCpsI64ClosureEntry>(code) };
    let closure = Box::into_raw(Box::new(NativeCpsI64Closure {
        code,
        env: Vec::new().into_boxed_slice(),
        handlers: Box::new([]),
        guard_stack: Box::new([]),
    }));
    let ptr = closure as usize;
    if self_slot < env.len() {
        env[self_slot] = ptr as i64;
    }
    unsafe {
        (*closure).env = env.into_boxed_slice();
        let mut handlers = NATIVE_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow().clone());
        handlers.extend(take_pending_native_i64_handler_frames());
        (*closure).handlers = handlers.into_boxed_slice();
        (*closure).guard_stack = current_native_i64_guard_stack().into_boxed_slice();
    }
    NATIVE_CPS_I64_CLOSURES.with(|closures| {
        closures.borrow_mut().insert(ptr);
    });
    ptr
}

fn make_native_i64_env(env: Vec<i64>) -> *const i64 {
    Box::leak(env.into_boxed_slice()).as_ptr()
}

unsafe fn native_i64_slice(ptr: *const i64, len: i64) -> Vec<i64> {
    let Ok(len) = usize::try_from(len) else {
        return Vec::new();
    };
    if len == 0 {
        return Vec::new();
    }
    if ptr.is_null() {
        return Vec::new();
    }
    unsafe { std::slice::from_raw_parts(ptr, len) }.to_vec()
}

fn native_cps_i64_heap(value: NativeCpsI64HeapValue) -> i64 {
    let pointer = Box::into_raw(Box::new(value)) as i64;
    NATIVE_CPS_I64_HEAP_VALUES.with(|values| {
        values.borrow_mut().insert(pointer);
    });
    pointer
}

fn native_cps_i64_variant(tag: &str, value: Option<i64>) -> i64 {
    let hash = tag_hash(&typed_ir::Name(tag.to_string()));
    register_native_i64_tag_name(hash, tag);
    native_cps_i64_heap(NativeCpsI64HeapValue::Variant { tag: hash, value })
}

fn register_native_i64_tag_name(tag: i64, name: &str) {
    NATIVE_CPS_I64_TAG_NAMES.with(|names| {
        names
            .borrow_mut()
            .entry(tag)
            .or_insert_with(|| name.to_string().into_boxed_str());
    });
}

fn native_i64_tag_name(tag: i64) -> String {
    NATIVE_CPS_I64_TAG_NAMES.with(|names| {
        names
            .borrow()
            .get(&tag)
            .map(|name| name.to_string())
            .unwrap_or_else(|| format!("#{tag}"))
    })
}

fn native_cps_i64_string_from_raw(ptr: *const u8, len: i64) -> Option<String> {
    if ptr.is_null() || len < 0 {
        return None;
    }
    let len = usize::try_from(len).ok()?;
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    std::str::from_utf8(bytes).ok().map(str::to_string)
}

pub fn describe_cps_repr_i64_value(value: i64) -> String {
    describe_native_i64_value(value)
}

fn describe_cps_repr_i64_value_with_hint(value: i64, hint: CpsRootDisplayHint) -> String {
    match hint {
        CpsRootDisplayHint::Unit if value == 0 => "()".to_string(),
        _ => describe_cps_repr_i64_value(value),
    }
}

fn describe_native_i64_value(value: i64) -> String {
    describe_native_i64_value_with_depth(value, 0)
}

fn describe_native_i64_debug_value(value: i64) -> String {
    describe_native_i64_debug_value_with_depth(value, 0)
}

fn describe_native_i64_value_with_depth(value: i64, depth: usize) -> String {
    if depth > 32 {
        return "...".to_string();
    }
    let resumption_id = NATIVE_CPS_I64_RESUMPTIONS.with(|resumptions| {
        if resumptions.borrow().contains(&(value as usize)) {
            Some(unsafe { (*(value as *const NativeCpsI64Resumption)).debug_id })
        } else {
            None
        }
    });
    if let Some(id) = resumption_id {
        return format!("resumption#{id}@{value:#x}");
    }

    let is_thunk = NATIVE_CPS_I64_THUNKS.with(|thunks| thunks.borrow().contains(&(value as usize)));
    if is_thunk {
        return format!("thunk@{value:#x}");
    }

    let is_closure =
        NATIVE_CPS_I64_CLOSURES.with(|closures| closures.borrow().contains(&(value as usize)));
    if is_closure {
        return format!("closure@{value:#x}");
    }

    let is_heap = NATIVE_CPS_I64_HEAP_VALUES.with(|values| values.borrow().contains(&value));
    if !is_heap {
        return value.to_string();
    }

    let heap = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    match heap {
        NativeCpsI64HeapValue::Tuple(items) => {
            let items = items
                .iter()
                .map(|item| describe_native_i64_value_with_depth(*item, depth + 1))
                .collect::<Vec<_>>();
            match items.as_slice() {
                [] => "()".to_string(),
                [single] => format!("({single},)"),
                _ => format!("({})", items.join(", ")),
            }
        }
        NativeCpsI64HeapValue::Record(fields) => format!(
            "{{ {} }}",
            fields
                .iter()
                .map(|(name, value)| format!(
                    "{name}: {}",
                    describe_native_i64_value_with_depth(*value, depth + 1)
                ))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        NativeCpsI64HeapValue::Variant { tag, value: None } => {
            format!(":{}", native_i64_tag_name(*tag))
        }
        NativeCpsI64HeapValue::Variant {
            tag,
            value: Some(payload),
        } => format!(
            ":{} {}",
            native_i64_tag_name(*tag),
            describe_native_i64_value_with_depth(*payload, depth + 1)
        ),
        NativeCpsI64HeapValue::List(items) => format!(
            "[{}]",
            items
                .iter()
                .map(|item| describe_native_i64_value_with_depth(*item, depth + 1))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        NativeCpsI64HeapValue::Bool(value) => value.to_string(),
        NativeCpsI64HeapValue::Unit => "()".to_string(),
        NativeCpsI64HeapValue::Float(value) => native_cps_format_float(*value),
        NativeCpsI64HeapValue::String(text) => text.to_string(),
        NativeCpsI64HeapValue::Bytes(value) => format!("<bytes len={}>", value.len()),
        NativeCpsI64HeapValue::Path(value) => value.display().to_string(),
    }
}

fn describe_native_i64_debug_value_with_depth(value: i64, depth: usize) -> String {
    if depth > 32 {
        return "...".to_string();
    }

    let is_heap = NATIVE_CPS_I64_HEAP_VALUES.with(|values| values.borrow().contains(&value));
    if !is_heap {
        return value.to_string();
    }

    let heap = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    match heap {
        NativeCpsI64HeapValue::Tuple(items) => {
            let items = items
                .iter()
                .map(|item| describe_native_i64_debug_value_with_depth(*item, depth + 1))
                .collect::<Vec<_>>();
            match items.as_slice() {
                [] => "()".to_string(),
                [single] => format!("({single},)"),
                _ => format!("({})", items.join(", ")),
            }
        }
        NativeCpsI64HeapValue::Record(fields) => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|(name, value)| format!(
                    "{name}: {}",
                    describe_native_i64_debug_value_with_depth(*value, depth + 1)
                ))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        NativeCpsI64HeapValue::Variant { tag, value: None } => native_i64_tag_name(*tag),
        NativeCpsI64HeapValue::Variant {
            tag,
            value: Some(payload),
        } => format!(
            "{} {}",
            native_i64_tag_name(*tag),
            describe_native_i64_debug_value_with_depth(*payload, depth + 1)
        ),
        NativeCpsI64HeapValue::List(items) => format!(
            "[{}]",
            items
                .iter()
                .map(|item| describe_native_i64_debug_value_with_depth(*item, depth + 1))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        NativeCpsI64HeapValue::Bool(value) => value.to_string(),
        NativeCpsI64HeapValue::Unit => "()".to_string(),
        NativeCpsI64HeapValue::Float(value) => native_cps_format_float(*value),
        NativeCpsI64HeapValue::String(text) => format!("{text:?}"),
        NativeCpsI64HeapValue::Bytes(value) => format!("<bytes len={}>", value.len()),
        NativeCpsI64HeapValue::Path(value) => format!("{:?}", value.display().to_string()),
    }
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_resumption_i64_0(
    code: usize,
    handler: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, handler, Vec::new())
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_resumption_i64_1(
    code: usize,
    handler: i64,
    a: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, handler, vec![a])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_resumption_i64_2(
    code: usize,
    handler: i64,
    a: i64,
    b: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, handler, vec![a, b])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_resumption_i64_3(
    code: usize,
    handler: i64,
    a: i64,
    b: i64,
    c: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, handler, vec![a, b, c])
}

#[unsafe(no_mangle)]
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

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_resumption_i64_many(
    code: usize,
    handler: i64,
    ptr: *const i64,
    len: i64,
) -> *mut NativeCpsI64Resumption {
    make_native_i64_resumption(code, handler, unsafe { native_i64_slice(ptr, len) })
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_env_i64_0() -> *const i64 {
    make_native_i64_env(Vec::new())
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_env_i64_1(a: i64) -> *const i64 {
    make_native_i64_env(vec![a])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_env_i64_2(a: i64, b: i64) -> *const i64 {
    make_native_i64_env(vec![a, b])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_env_i64_3(a: i64, b: i64, c: i64) -> *const i64 {
    make_native_i64_env(vec![a, b, c])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_env_i64_4(a: i64, b: i64, c: i64, d: i64) -> *const i64 {
    make_native_i64_env(vec![a, b, c, d])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_env_i64_many(ptr: *const i64, len: i64) -> *const i64 {
    make_native_i64_env(unsafe { native_i64_slice(ptr, len) })
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_closure_i64_0(code: usize) -> usize {
    make_native_i64_closure(code, Vec::new())
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_closure_i64_1(code: usize, a: i64) -> usize {
    make_native_i64_closure(code, vec![a])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_closure_i64_2(code: usize, a: i64, b: i64) -> usize {
    make_native_i64_closure(code, vec![a, b])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_closure_i64_3(code: usize, a: i64, b: i64, c: i64) -> usize {
    make_native_i64_closure(code, vec![a, b, c])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_closure_i64_4(code: usize, a: i64, b: i64, c: i64, d: i64) -> usize {
    make_native_i64_closure(code, vec![a, b, c, d])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_closure_i64_many(code: usize, ptr: *const i64, len: i64) -> usize {
    make_native_i64_closure(code, unsafe { native_i64_slice(ptr, len) })
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_recursive_closure_i64_0(code: usize, self_slot: i64) -> usize {
    make_native_i64_recursive_closure(code, self_slot as usize, Vec::new())
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_recursive_closure_i64_1(
    code: usize,
    self_slot: i64,
    a: i64,
) -> usize {
    make_native_i64_recursive_closure(code, self_slot as usize, vec![a])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_recursive_closure_i64_2(
    code: usize,
    self_slot: i64,
    a: i64,
    b: i64,
) -> usize {
    make_native_i64_recursive_closure(code, self_slot as usize, vec![a, b])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_recursive_closure_i64_3(
    code: usize,
    self_slot: i64,
    a: i64,
    b: i64,
    c: i64,
) -> usize {
    make_native_i64_recursive_closure(code, self_slot as usize, vec![a, b, c])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_recursive_closure_i64_4(
    code: usize,
    self_slot: i64,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> usize {
    make_native_i64_recursive_closure(code, self_slot as usize, vec![a, b, c, d])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_recursive_closure_i64_many(
    code: usize,
    self_slot: i64,
    ptr: *const i64,
    len: i64,
) -> usize {
    make_native_i64_recursive_closure(code, self_slot as usize, unsafe {
        native_i64_slice(ptr, len)
    })
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_apply_closure_i64(value: usize, arg: i64) -> i64 {
    let is_resumption = NATIVE_CPS_I64_RESUMPTIONS.with(|s| s.borrow().contains(&value));
    if is_resumption {
        return yulang_cps_resume_i64(value as *const NativeCpsI64Resumption, arg);
    }
    // write27-e: Layer 2 calls a closure with the **caller**'s active
    // handlers and guards (eval_continuations(..., active_handlers,
    // guard_stack, ...) at cps_repr.rs:2247). The previous JIT impl
    // appended `closure.handlers` to the thread-local stack, which
    // caused exponential growth: every nested apply_closure stacked
    // another copy of the handler chain on top, and a captured
    // resumption then re-inherited those duplicates. Use the
    // caller's thread-local state as-is and ignore `closure.handlers`
    // / `closure.guard_stack` at call time.
    let closure = unsafe { &*(value as *const NativeCpsI64Closure) };
    if jit_trace_enabled() {
        let frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|f| f.borrow().clone());
        let eval = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow());
        eprintln!(
            "[JIT-CPS] apply_closure: closure={:#x} arg={} eval={} initial={} frames={}",
            value,
            describe_native_i64_value(arg),
            eval.current_eval_id,
            eval.initial_frame_count,
            format_return_frames(&frames),
        );
    }
    let result = (closure.code)(closure.env.as_ptr(), arg);
    if jit_trace_enabled() {
        let frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|f| f.borrow().clone());
        let eval = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow());
        eprintln!(
            "[JIT-CPS] apply_closure.out: closure={:#x} result={} eval={} initial={} frames={}",
            value,
            describe_native_i64_value(result),
            eval.current_eval_id,
            eval.initial_frame_count,
            format_return_frames(&frames),
        );
    }
    result
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_tuple_i64_0() -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Tuple(Vec::new().into_boxed_slice()))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_tuple_i64_1(a: i64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Tuple(vec![a].into_boxed_slice()))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_tuple_i64_2(a: i64, b: i64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Tuple(vec![a, b].into_boxed_slice()))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_tuple_i64_3(a: i64, b: i64, c: i64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Tuple(
        vec![a, b, c].into_boxed_slice(),
    ))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_tuple_i64_4(a: i64, b: i64, c: i64, d: i64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Tuple(
        vec![a, b, c, d].into_boxed_slice(),
    ))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_tuple_get_i64(value: i64, index: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::Tuple(items) = value else {
        return 0;
    };
    items.get(index as usize).copied().unwrap_or(0)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_record_empty_i64() -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Record(Vec::new()))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_record_insert_i64(
    record: i64,
    field_ptr: *const u8,
    field_len: i64,
    value: i64,
) -> i64 {
    let Some(field) = native_cps_i64_string_from_raw(field_ptr, field_len) else {
        return record;
    };
    let record = unsafe { &*(record as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::Record(fields) = record else {
        return yulang_cps_record_empty_i64();
    };
    let mut fields = fields.clone();
    if let Some((_, slot)) = fields
        .iter_mut()
        .find(|(existing, _)| existing.as_ref() == field.as_str())
    {
        *slot = value;
    } else {
        fields.push((field.into_boxed_str(), value));
    }
    native_cps_i64_heap(NativeCpsI64HeapValue::Record(fields))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_record_select_i64(
    record: i64,
    field_ptr: *const u8,
    field_len: i64,
) -> i64 {
    let Some(field) = native_cps_i64_string_from_raw(field_ptr, field_len) else {
        return 0;
    };
    let record = unsafe { &*(record as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::Record(fields) = record else {
        return 0;
    };
    fields
        .iter()
        .find_map(|(name, value)| (name.as_ref() == field.as_str()).then_some(*value))
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_record_select_or_default_i64(
    record: i64,
    field_ptr: *const u8,
    field_len: i64,
    default: i64,
) -> i64 {
    let Some(field) = native_cps_i64_string_from_raw(field_ptr, field_len) else {
        return default;
    };
    let record = unsafe { &*(record as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::Record(fields) = record else {
        return default;
    };
    fields
        .iter()
        .find_map(|(name, value)| (name.as_ref() == field.as_str()).then_some(*value))
        .unwrap_or(default)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_record_has_field_i64(
    record: i64,
    field_ptr: *const u8,
    field_len: i64,
) -> i64 {
    let Some(field) = native_cps_i64_string_from_raw(field_ptr, field_len) else {
        return 0;
    };
    let record = unsafe { &*(record as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::Record(fields) = record else {
        return 0;
    };
    fields
        .iter()
        .any(|(name, _)| name.as_ref() == field.as_str()) as i64
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_record_without_field_i64(
    record: i64,
    field_ptr: *const u8,
    field_len: i64,
) -> i64 {
    let Some(field) = native_cps_i64_string_from_raw(field_ptr, field_len) else {
        return record;
    };
    let record = unsafe { &*(record as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::Record(fields) = record else {
        return yulang_cps_record_empty_i64();
    };
    let fields = fields
        .iter()
        .filter(|(name, _)| name.as_ref() != field.as_str())
        .cloned()
        .collect();
    native_cps_i64_heap(NativeCpsI64HeapValue::Record(fields))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_variant_i64_0(tag: i64) -> i64 {
    let result = native_cps_i64_heap(NativeCpsI64HeapValue::Variant { tag, value: None });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] variant_new: tag={} payload=none result={}",
            native_i64_tag_name(tag),
            describe_native_i64_value(result)
        );
    }
    result
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_variant_i64_1(tag: i64, value: i64) -> i64 {
    let result = native_cps_i64_heap(NativeCpsI64HeapValue::Variant {
        tag,
        value: Some(value),
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] variant_new: tag={} payload={} result={}",
            native_i64_tag_name(tag),
            describe_native_i64_value(value),
            describe_native_i64_value(result)
        );
    }
    result
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_variant_tag_eq_i64(value: i64, tag: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let result = match value {
        NativeCpsI64HeapValue::Variant { tag: actual, .. } => i64::from(*actual == tag),
        _ => 0,
    };
    if jit_trace_enabled() {
        let actual = match value {
            NativeCpsI64HeapValue::Variant { tag: actual, .. } => native_i64_tag_name(*actual),
            _ => "non_variant".to_string(),
        };
        eprintln!(
            "[JIT-CPS] variant_tag_eq: expected={} actual={} result={}",
            native_i64_tag_name(tag),
            actual,
            result
        );
    }
    result
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_variant_payload_i64(value: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let result = match value {
        NativeCpsI64HeapValue::Variant {
            value: Some(value), ..
        } => *value,
        _ => 0,
    };
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] variant_payload: payload={}",
            describe_native_i64_value(result)
        );
    }
    result
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_register_tag_i64(tag: i64, ptr: *const u8, len: i64) -> i64 {
    if ptr.is_null() || len < 0 {
        return 0;
    }
    let Ok(len) = usize::try_from(len) else {
        return 0;
    };
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    let Ok(name) = std::str::from_utf8(bytes) else {
        return 0;
    };
    register_native_i64_tag_name(tag, name);
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_print_i64(value: i64) {
    print!("{}", describe_native_i64_value(value));
    let mut stdout = std::io::stdout();
    let _ = std::io::Write::flush(&mut stdout);
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_print_debug_i64(value: i64) {
    print!("{}", describe_native_i64_debug_value(value));
    let mut stdout = std::io::stdout();
    let _ = std::io::Write::flush(&mut stdout);
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_debug_i64(value: i64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::String(
        describe_native_i64_debug_value(value).into_boxed_str(),
    ))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_out_write_i64(value: i64) -> i64 {
    print!("{}", describe_native_i64_value(value));
    let mut stdout = std::io::stdout();
    let _ = std::io::Write::flush(&mut stdout);
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_err_write_i64(value: i64) -> i64 {
    eprint!("{}", describe_native_i64_value(value));
    let mut stderr = std::io::stderr();
    let _ = std::io::Write::flush(&mut stderr);
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_warn_write_i64(value: i64) -> i64 {
    eprintln!("warning: {}", describe_native_i64_value(value));
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_die_i64(value: i64) -> i64 {
    eprintln!("die: {}", describe_native_i64_value(value));
    std::process::exit(1);
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_list_empty_i64() -> i64 {
    let result = native_cps_i64_heap(NativeCpsI64HeapValue::List(Vec::new()));
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] list_empty: result={}",
            describe_native_i64_value(result)
        );
    }
    result
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_list_singleton_i64(value: i64) -> i64 {
    let result = native_cps_i64_heap(NativeCpsI64HeapValue::List(vec![value]));
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] list_singleton: item={} result={}",
            describe_native_i64_value(value),
            describe_native_i64_value(result)
        );
    }
    result
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_list_merge_i64(left: i64, right: i64) -> i64 {
    let left = unsafe { &*(left as *const NativeCpsI64HeapValue) };
    let right = unsafe { &*(right as *const NativeCpsI64HeapValue) };
    let (NativeCpsI64HeapValue::List(left), NativeCpsI64HeapValue::List(right)) = (left, right)
    else {
        return yulang_cps_list_empty_i64();
    };
    let mut merged = left.clone();
    merged.extend(right.iter().copied());
    let result = native_cps_i64_heap(NativeCpsI64HeapValue::List(merged));
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] list_merge: left_len={} right_len={} result={}",
            left.len(),
            right.len(),
            describe_native_i64_value(result)
        );
    }
    result
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_list_len_i64(value: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    match value {
        NativeCpsI64HeapValue::List(items) => items.len() as i64,
        _ => 0,
    }
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_list_index_i64(value: i64, index: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::List(items) = value else {
        return 0;
    };
    items.get(index as usize).copied().unwrap_or(0)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_list_index_range_raw_i64(value: i64, start: i64, end: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::List(items) = value else {
        return yulang_cps_list_empty_i64();
    };
    let Ok(start) = usize::try_from(start) else {
        return yulang_cps_list_empty_i64();
    };
    let Ok(end) = usize::try_from(end) else {
        return yulang_cps_list_empty_i64();
    };
    if start > end || end > items.len() {
        return yulang_cps_list_empty_i64();
    }
    native_cps_i64_heap(NativeCpsI64HeapValue::List(items[start..end].to_vec()))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_list_index_range_i64(value: i64, range: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::List(items) = value else {
        return yulang_cps_list_empty_i64();
    };
    let Some((start, end)) = native_cps_i64_normalized_int_range(range, items.len()) else {
        return yulang_cps_list_empty_i64();
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::List(items[start..end].to_vec()))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_list_splice_raw_i64(value: i64, start: i64, end: i64, insert: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let insert = unsafe { &*(insert as *const NativeCpsI64HeapValue) };
    let (NativeCpsI64HeapValue::List(items), NativeCpsI64HeapValue::List(insert)) = (value, insert)
    else {
        return yulang_cps_list_empty_i64();
    };
    let Ok(start) = usize::try_from(start) else {
        return yulang_cps_list_empty_i64();
    };
    let Ok(end) = usize::try_from(end) else {
        return yulang_cps_list_empty_i64();
    };
    if start > end || end > items.len() {
        return yulang_cps_list_empty_i64();
    }
    let mut result = Vec::with_capacity(items.len() - (end - start) + insert.len());
    result.extend_from_slice(&items[..start]);
    result.extend(insert.iter().copied());
    result.extend_from_slice(&items[end..]);
    native_cps_i64_heap(NativeCpsI64HeapValue::List(result))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_list_splice_i64(value: i64, range: i64, insert: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let insert = unsafe { &*(insert as *const NativeCpsI64HeapValue) };
    let (NativeCpsI64HeapValue::List(items), NativeCpsI64HeapValue::List(insert)) = (value, insert)
    else {
        return yulang_cps_list_empty_i64();
    };
    let Some((start, end)) = native_cps_i64_normalized_int_range(range, items.len()) else {
        return yulang_cps_list_empty_i64();
    };
    let mut result = Vec::with_capacity(items.len() - (end - start) + insert.len());
    result.extend_from_slice(&items[..start]);
    result.extend(insert.iter().copied());
    result.extend_from_slice(&items[end..]);
    native_cps_i64_heap(NativeCpsI64HeapValue::List(result))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_list_view_raw_i64(value: i64) -> i64 {
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    let NativeCpsI64HeapValue::List(items) = value else {
        return native_cps_i64_variant("empty", None);
    };
    match items.len() {
        0 => {
            let result = native_cps_i64_variant("empty", None);
            if jit_trace_enabled() {
                eprintln!(
                    "[JIT-CPS] list_view: len=0 result={}",
                    describe_native_i64_value(result)
                );
            }
            result
        }
        1 => {
            let head = items.first().copied();
            let result = native_cps_i64_variant("leaf", head);
            if jit_trace_enabled() {
                eprintln!(
                    "[JIT-CPS] list_view: len=1 head={} result={}",
                    head.map(describe_native_i64_value)
                        .unwrap_or_else(|| "none".to_string()),
                    describe_native_i64_value(result)
                );
            }
            result
        }
        len => {
            let mid = len / 2;
            let left = native_cps_i64_heap(NativeCpsI64HeapValue::List(items[..mid].to_vec()));
            let right = native_cps_i64_heap(NativeCpsI64HeapValue::List(items[mid..].to_vec()));
            let tuple = native_cps_i64_heap(NativeCpsI64HeapValue::Tuple(
                vec![left, right].into_boxed_slice(),
            ));
            let result = native_cps_i64_variant("node", Some(tuple));
            if jit_trace_enabled() {
                eprintln!(
                    "[JIT-CPS] list_view: len={} left={} right={} result={}",
                    len,
                    describe_native_i64_value(left),
                    describe_native_i64_value(right),
                    describe_native_i64_value(result)
                );
            }
            result
        }
    }
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_int_to_string_i64(value: i64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::String(
        value.to_string().into_boxed_str(),
    ))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_int_to_hex_i64(value: i64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::String(
        format!("{value:x}").into_boxed_str(),
    ))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_int_to_upper_hex_i64(value: i64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::String(
        format!("{value:X}").into_boxed_str(),
    ))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_bool_to_string_i64(value: i64) -> i64 {
    let text = if value == 0 { "false" } else { "true" };
    native_cps_i64_heap(NativeCpsI64HeapValue::String(text.into()))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_box_bool_i64(value: i64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Bool(value != 0))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_unit_i64() -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Unit)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_float_to_string_f64(value: f64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::String(
        native_cps_format_float(value).into_boxed_str(),
    ))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_box_float_f64(value: f64) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Float(value))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_unbox_float_i64(value: i64) -> f64 {
    let Some(NativeCpsI64HeapValue::Float(value)) = native_cps_i64_heap_value(value) else {
        return value as f64;
    };
    *value
}

fn native_cps_format_float(value: f64) -> String {
    let mut rendered = value.to_string();
    if !rendered.contains('.') && !rendered.contains('e') && !rendered.contains('E') {
        rendered.push_str(".0");
    }
    rendered
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_string_literal_i64(ptr: *const u8, len: i64) -> i64 {
    let Some(text) = native_cps_i64_string_from_bytes(ptr, len) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::String(text.into_boxed_str()))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_string_concat_i64(left: i64, right: i64) -> i64 {
    let Some(left) = native_cps_i64_string_text(left) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    let Some(right) = native_cps_i64_string_text(right) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    let mut text = String::with_capacity(left.len() + right.len());
    text.push_str(left);
    text.push_str(right);
    native_cps_i64_heap(NativeCpsI64HeapValue::String(text.into_boxed_str()))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_string_eq_i64(left: i64, right: i64) -> i64 {
    let Some(left) = native_cps_i64_string_text(left) else {
        return 0;
    };
    let Some(right) = native_cps_i64_string_text(right) else {
        return 0;
    };
    i64::from(left == right)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_string_len_i64(value: i64) -> i64 {
    native_cps_i64_string_text(value)
        .map(|text| text.chars().count() as i64)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_string_index_i64(value: i64, index: i64) -> i64 {
    let Some(text) = native_cps_i64_string_text(value) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    let Ok(index) = usize::try_from(index) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    let Some(ch) = text.chars().nth(index) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::String(
        ch.to_string().into_boxed_str(),
    ))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_string_index_range_raw_i64(value: i64, start: i64, end: i64) -> i64 {
    let Some(text) = native_cps_i64_string_text(value) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    let Some(slice) = native_cps_i64_string_slice(text, start, end) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::String(
        slice.to_string().into_boxed_str(),
    ))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_string_index_range_i64(value: i64, range: i64) -> i64 {
    let Some(text) = native_cps_i64_string_text(value) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    let Some((start, end)) = native_cps_i64_normalized_int_range(range, text.chars().count())
    else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    let Some(slice) = native_cps_i64_string_slice(text, start as i64, end as i64) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::String(
        slice.to_string().into_boxed_str(),
    ))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_string_splice_raw_i64(
    value: i64,
    start: i64,
    end: i64,
    insert: i64,
) -> i64 {
    let Some(text) = native_cps_i64_string_text(value) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    let Some(insert) = native_cps_i64_string_text(insert) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    let Some((start, end)) = native_cps_i64_string_byte_range(text, start, end) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    let mut result = String::with_capacity(text.len() - (end - start) + insert.len());
    result.push_str(&text[..start]);
    result.push_str(insert);
    result.push_str(&text[end..]);
    native_cps_i64_heap(NativeCpsI64HeapValue::String(result.into_boxed_str()))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_string_splice_i64(value: i64, range: i64, insert: i64) -> i64 {
    let Some(text) = native_cps_i64_string_text(value) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    let Some(insert) = native_cps_i64_string_text(insert) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    let Some((start, end)) = native_cps_i64_normalized_int_range(range, text.chars().count())
    else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    let Some((start, end)) = native_cps_i64_string_byte_range(text, start as i64, end as i64)
    else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::String("".into()));
    };
    let mut result = String::with_capacity(text.len() - (end - start) + insert.len());
    result.push_str(&text[..start]);
    result.push_str(insert);
    result.push_str(&text[end..]);
    native_cps_i64_heap(NativeCpsI64HeapValue::String(result.into_boxed_str()))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_string_to_bytes_i64(value: i64) -> i64 {
    let Some(text) = native_cps_i64_string_text(value) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::empty()));
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::from_bytes(
        text.as_bytes(),
    )))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_bytes_len_i64(value: i64) -> i64 {
    native_cps_i64_bytes_value(value)
        .map(|value| value.len() as i64)
        .unwrap_or(0)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_bytes_eq_i64(left: i64, right: i64) -> i64 {
    let Some(left) = native_cps_i64_bytes_value(left) else {
        return 0;
    };
    let Some(right) = native_cps_i64_bytes_value(right) else {
        return 0;
    };
    i64::from(left.to_flat_vec() == right.to_flat_vec())
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_bytes_concat_i64(left: i64, right: i64) -> i64 {
    let Some(left) = native_cps_i64_bytes_value(left) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::empty()));
    };
    let Some(right) = native_cps_i64_bytes_value(right) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::empty()));
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::concat(
        left.clone(),
        right.clone(),
    )))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_bytes_index_i64(value: i64, index: i64) -> i64 {
    let Some(value) = native_cps_i64_bytes_value(value) else {
        return 0;
    };
    let Ok(index) = usize::try_from(index) else {
        return 0;
    };
    value.index(index).map(i64::from).unwrap_or(0)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_bytes_index_range_i64(value: i64, range: i64) -> i64 {
    let Some(value) = native_cps_i64_bytes_value(value) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::empty()));
    };
    let Some((start, end)) = native_cps_i64_normalized_int_range(range, value.len()) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::empty()));
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(
        value
            .index_range(start, end)
            .unwrap_or_else(BytesTree::empty),
    ))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_bytes_to_utf8_raw_i64(value: i64) -> i64 {
    let Some(value) = native_cps_i64_bytes_value(value) else {
        return native_cps_i64_utf8_raw_result("", 0);
    };
    let bytes = value.to_flat_vec();
    match std::str::from_utf8(&bytes) {
        Ok(text) => native_cps_i64_utf8_raw_result(text, bytes.len()),
        Err(error) => {
            let valid = error.valid_up_to();
            let text = std::str::from_utf8(&bytes[..valid]).unwrap_or("");
            native_cps_i64_utf8_raw_result(text, valid)
        }
    }
}

fn native_cps_i64_utf8_raw_result(text: &str, valid: usize) -> i64 {
    native_cps_i64_heap(NativeCpsI64HeapValue::Tuple(Box::new([
        native_cps_i64_heap(NativeCpsI64HeapValue::String(text.into())),
        valid as i64,
    ])))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_bytes_to_path_i64(value: i64) -> i64 {
    let Some(value) = native_cps_i64_bytes_value(value) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::Path(path_buf_from_bytes(&[])));
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::Path(path_buf_from_bytes(
        &value.to_flat_vec(),
    )))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_path_to_bytes_i64(value: i64) -> i64 {
    let Some(value) = native_cps_i64_path_value(value) else {
        return native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::empty()));
    };
    native_cps_i64_heap(NativeCpsI64HeapValue::Bytes(BytesTree::from_bytes(
        &path_buf_bytes(value),
    )))
}

fn native_cps_i64_string_from_bytes(ptr: *const u8, len: i64) -> Option<String> {
    if ptr.is_null() || len < 0 {
        return None;
    }
    let len = usize::try_from(len).ok()?;
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    std::str::from_utf8(bytes).ok().map(str::to_string)
}

fn native_cps_i64_string_text(value: i64) -> Option<&'static str> {
    let is_heap = NATIVE_CPS_I64_HEAP_VALUES.with(|values| values.borrow().contains(&value));
    if !is_heap {
        return None;
    }
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    match value {
        NativeCpsI64HeapValue::String(text) => Some(text.as_ref()),
        _ => None,
    }
}

fn native_cps_i64_bytes_value(value: i64) -> Option<&'static BytesTree> {
    let is_heap = NATIVE_CPS_I64_HEAP_VALUES.with(|values| values.borrow().contains(&value));
    if !is_heap {
        return None;
    }
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    match value {
        NativeCpsI64HeapValue::Bytes(value) => Some(value),
        _ => None,
    }
}

fn native_cps_i64_path_value(value: i64) -> Option<&'static std::path::PathBuf> {
    let is_heap = NATIVE_CPS_I64_HEAP_VALUES.with(|values| values.borrow().contains(&value));
    if !is_heap {
        return None;
    }
    let value = unsafe { &*(value as *const NativeCpsI64HeapValue) };
    match value {
        NativeCpsI64HeapValue::Path(value) => Some(value),
        _ => None,
    }
}

#[cfg(unix)]
fn path_buf_from_bytes(bytes: &[u8]) -> std::path::PathBuf {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;

    std::path::PathBuf::from(OsString::from_vec(bytes.to_vec()))
}

#[cfg(not(unix))]
fn path_buf_from_bytes(bytes: &[u8]) -> std::path::PathBuf {
    std::path::PathBuf::from(String::from_utf8_lossy(bytes).into_owned())
}

#[cfg(unix)]
fn path_buf_bytes(path: &std::path::PathBuf) -> Vec<u8> {
    use std::os::unix::ffi::OsStrExt;

    path.as_os_str().as_bytes().to_vec()
}

#[cfg(not(unix))]
fn path_buf_bytes(path: &std::path::PathBuf) -> Vec<u8> {
    path.to_string_lossy().as_bytes().to_vec()
}

fn native_cps_i64_string_slice(text: &str, start: i64, end: i64) -> Option<&str> {
    let (start, end) = native_cps_i64_string_byte_range(text, start, end)?;
    Some(&text[start..end])
}

fn native_cps_i64_string_byte_range(text: &str, start: i64, end: i64) -> Option<(usize, usize)> {
    let start = usize::try_from(start).ok()?;
    let end = usize::try_from(end).ok()?;
    if start > end || end > text.chars().count() {
        return None;
    }
    let start = native_cps_i64_string_char_boundary(text, start)?;
    let end = native_cps_i64_string_char_boundary(text, end)?;
    Some((start, end))
}

fn native_cps_i64_string_char_boundary(text: &str, index: usize) -> Option<usize> {
    if index == text.chars().count() {
        return Some(text.len());
    }
    text.char_indices().nth(index).map(|(byte, _)| byte)
}

fn native_cps_i64_normalized_int_range(value: i64, len: usize) -> Option<(usize, usize)> {
    let value = native_cps_i64_heap_value(value)?;
    let NativeCpsI64HeapValue::Variant {
        tag,
        value: Some(payload),
    } = value
    else {
        return None;
    };
    if *tag != tag_hash(&typed_ir::Name("within".to_string())) {
        return None;
    }
    let NativeCpsI64HeapValue::Tuple(items) = native_cps_i64_heap_value(*payload)? else {
        return None;
    };
    let [start, end] = items.as_ref() else {
        return None;
    };
    let start = native_cps_i64_normalized_start_bound(*start)?;
    let end = native_cps_i64_normalized_end_bound(*end, len)?;
    (start <= end && end <= len).then_some((start, end))
}

fn native_cps_i64_normalized_start_bound(value: i64) -> Option<usize> {
    let NativeCpsI64HeapValue::Variant { tag, value } = native_cps_i64_heap_value(value)? else {
        return None;
    };
    let tag = native_i64_tag_name(*tag);
    match tag.as_str() {
        "unbounded" => Some(0),
        "included" => usize::try_from(value.as_ref().copied()?).ok(),
        "excluded" => usize::try_from(value.as_ref().copied()? + 1).ok(),
        _ => None,
    }
}

fn native_cps_i64_normalized_end_bound(value: i64, len: usize) -> Option<usize> {
    let NativeCpsI64HeapValue::Variant { tag, value } = native_cps_i64_heap_value(value)? else {
        return None;
    };
    let tag = native_i64_tag_name(*tag);
    match tag.as_str() {
        "unbounded" => Some(len),
        "included" => usize::try_from(value.as_ref().copied()? + 1).ok(),
        "excluded" => usize::try_from(value.as_ref().copied()?).ok(),
        _ => None,
    }
}

fn native_cps_i64_heap_value(value: i64) -> Option<&'static NativeCpsI64HeapValue> {
    let is_heap = NATIVE_CPS_I64_HEAP_VALUES.with(|values| values.borrow().contains(&value));
    is_heap.then(|| unsafe { &*(value as *const NativeCpsI64HeapValue) })
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_resume_i64(resumption: *const NativeCpsI64Resumption, arg: i64) -> i64 {
    let resumption = unsafe { &*resumption };
    // write27-e: mirror Layer 2's `CpsStmt::Resume` (cps_repr.rs:1879).
    //   resumed_handlers  = merge_resumption_handlers(captured, current, anchor)
    //   adjusted_frames   = merge_extras_into_frames(captured_frames, current, anchor)
    //   eval_continuations(..., resumed_handlers, ..., adjusted_frames, initial=0)
    // The JIT version save/restores thread-local return_frames + eval
    // context around the call so the caller's outer frames stay
    // hidden during the resumed eval (matches Layer 2 where eval_continuations
    // gets its own local state).
    let current_handlers = NATIVE_CPS_I64_HANDLER_STACK.with(|s| s.borrow().clone());
    let anchor = resumption.handled_anchor;
    let resumed_handlers =
        merge_resumption_handlers_native(&resumption.handlers, &current_handlers, anchor);
    let adjusted_frames =
        merge_extras_into_frames_native(&resumption.return_frames, &current_handlers, anchor);
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] resume: anchor={:?} captured={} current={} resumed={} adjusted_frames={}",
            anchor,
            format_handler_stack(&resumption.handlers),
            format_handler_stack(&current_handlers),
            format_handler_stack(&resumed_handlers),
            adjusted_frames.len(),
        );
    }
    // Swap state.
    let saved_frames = NATIVE_CPS_I64_RETURN_FRAMES
        .with(|f| std::mem::replace(&mut *f.borrow_mut(), adjusted_frames));
    let fresh_eval = NATIVE_CPS_I64_NEXT_EVAL_ID.with(|next| {
        let id = *next.borrow();
        *next.borrow_mut() = id + 1;
        id
    });
    let saved_eval_ctx = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| {
        std::mem::replace(
            &mut *ctx.borrow_mut(),
            NativeCpsI64EvalContext {
                current_eval_id: fresh_eval,
                initial_frame_count: 0,
            },
        )
    });
    let mut result =
        with_native_i64_cps_state(resumed_handlers, resumption.guard_stack.to_vec(), || {
            (resumption.code)(resumption.env.as_ptr(), arg)
        });
    if yulang_cps_scope_return_active_i64() != 0 {
        result = yulang_cps_route_scope_return_i64(result);
    }
    // Restore state only for ordinary value flow. If a ScopeReturn / abort is
    // still propagating, the resumed eval may have updated captured return
    // frame snapshots (notably ResumeWithHandler hygiene); restoring the old
    // caller snapshot here would resurrect stale handlers.
    restore_native_i64_return_frames_after_resume(saved_frames, &resumption.return_frames);
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow_mut() = saved_eval_ctx);
    result
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_resume_with_handler_i64(
    resumption: *const NativeCpsI64Resumption,
    arg: i64,
    handler: i64,
    consumes_mask: i64,
    owner_function: i64,
    updates_existing_handler_env: i64,
) -> i64 {
    let resumption = unsafe { &*resumption };
    let prompt = yulang_cps_fresh_prompt_i64() as u64;
    let install_eval_id = yulang_cps_current_eval_id_i64() as u64;
    let return_frame_threshold = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
    let updates_existing_handler_env = updates_existing_handler_env != 0;
    let rebases_existing_handler = updates_existing_handler_env
        && resumption
            .handlers
            .iter()
            .any(|frame| frame.handler == handler);
    let guard_stack = if updates_existing_handler_env || rebases_existing_handler {
        Box::new([])
    } else {
        current_native_i64_guard_stack().into_boxed_slice()
    };
    let outer_handler = NativeCpsI64HandlerFrame {
        handler,
        consumes_mask,
        guard_stack,
        envs: take_pending_native_i64_handler_envs(handler),
        prompt,
        install_eval_id,
        escape_owner_function_id: owner_function.max(0) as u64,
        threshold_owner_function_id: owner_function.max(0) as u64,
        inherited: false,
        escape_continuation: 0,
        escape_env: Box::new([]),
        escape_env_targets: Box::new([]),
        return_frame_threshold,
        return_frame_prefix: Box::new([]),
        origin: NativeCpsI64HandlerFrameOrigin::ResumeWithHandler,
    };
    let mut inherited_handler = outer_handler.clone();
    inherited_handler.inherited = true;
    push_resume_with_handler_sibling(outer_handler.clone());
    let mut handlers = resumption.handlers.to_vec();
    if !rebases_existing_handler {
        handlers.push(inherited_handler.clone());
    }
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] resume_with_handler: rid={} handler={} rebased={} envs={} captured_frames={} handlers={}",
            resumption.debug_id,
            handler,
            rebases_existing_handler,
            format_handler_envs(&outer_handler.envs),
            format_return_frames(&resumption.return_frames),
            format_handler_stack(&handlers),
        );
    }
    let mut resumed_frames = resumption.return_frames.to_vec();
    if rebases_existing_handler {
        own_native_i64_captured_return_frames(&mut resumed_frames);
    } else {
        for frame in &mut resumed_frames {
            if !frame
                .handlers
                .iter()
                .any(|existing| same_handler_frame_native(existing, &inherited_handler))
            {
                frame.handlers.push(inherited_handler.clone());
            }
        }
    }
    let mut saved_frames = NATIVE_CPS_I64_RETURN_FRAMES
        .with(|frames| std::mem::replace(&mut *frames.borrow_mut(), resumed_frames));
    let mut previous_handlers = NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        let previous = stack.borrow().clone();
        *stack.borrow_mut() = handlers;
        previous
    });
    let previous_guards = NATIVE_CPS_I64_GUARD_STACK
        .with(|stack| std::mem::replace(&mut *stack.borrow_mut(), resumption.guard_stack.to_vec()));
    let fresh_eval = NATIVE_CPS_I64_NEXT_EVAL_ID.with(|next| {
        let id = *next.borrow();
        *next.borrow_mut() = id + 1;
        id
    });
    let saved_eval_ctx = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| {
        std::mem::replace(
            &mut *ctx.borrow_mut(),
            NativeCpsI64EvalContext {
                current_eval_id: fresh_eval,
                initial_frame_count: 0,
            },
        )
    });
    let result = (resumption.code)(resumption.env.as_ptr(), arg);
    let scope_return_active = NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().active);
    let abort_active = NATIVE_CPS_I64_ABORT.with(|slot| slot.borrow().is_active());
    if !rebases_existing_handler {
        append_resume_handler_to_frames(&mut saved_frames, &outer_handler);
        append_resume_handler_to_handler_prefixes(&mut previous_handlers, &outer_handler);
    }
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        let mut outer = previous_handlers;
        if !rebases_existing_handler {
            outer.push(outer_handler);
        }
        *stack.borrow_mut() = outer;
    });
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| *stack.borrow_mut() = previous_guards);
    if abort_active && !scope_return_active {
        restore_native_i64_return_frames_after_resume(saved_frames, &resumption.return_frames);
    } else {
        NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| *frames.borrow_mut() = saved_frames);
    }
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow_mut() = saved_eval_ctx);
    result
}

// =====================================================================
// write27-d d4: EffectfulApply Resumption helper (c6 of write27).
// =====================================================================

/// `same_handler_frame` port: equality on (prompt, install_eval_id).
/// Synthetic frames (install_eval == MAX) compare equal only to other
/// synthetic frames with the same prompt; in practice that's almost
/// always false, so synthetic frames are treated as distinct.
fn same_handler_frame_native(a: &NativeCpsI64HandlerFrame, b: &NativeCpsI64HandlerFrame) -> bool {
    a.prompt == b.prompt && a.install_eval_id == b.install_eval_id
}

/// `merge_resumption_handlers` port. Place resume-site siblings
/// between the captured prefix-through-anchor and the captured tail.
fn merge_resumption_handlers_native(
    captured: &[NativeCpsI64HandlerFrame],
    current: &[NativeCpsI64HandlerFrame],
    anchor: Option<NativeCpsI64HandlerAnchor>,
) -> Vec<NativeCpsI64HandlerFrame> {
    if let Some(anchor) = anchor {
        if let Some(anchor_index) = captured
            .iter()
            .position(|f| f.prompt == anchor.prompt && f.install_eval_id == anchor.install_eval_id)
        {
            let mut merged = Vec::with_capacity(captured.len() + current.len());
            merged.extend(captured[..=anchor_index].iter().cloned());
            for frame in current {
                let in_prefix = merged.iter().any(|m| same_handler_frame_native(m, frame));
                let in_tail = captured[anchor_index + 1..]
                    .iter()
                    .any(|c| same_handler_frame_native(c, frame));
                if !in_prefix && !in_tail {
                    merged.push(frame.clone());
                }
            }
            merged.extend(captured[anchor_index + 1..].iter().cloned());
            return merged;
        }
    }
    // Shared-prefix fallback.
    let mut shared = 0;
    while shared < captured.len()
        && shared < current.len()
        && same_handler_frame_native(&captured[shared], &current[shared])
    {
        shared += 1;
    }
    let mut merged = Vec::with_capacity(captured.len() + current.len());
    merged.extend(captured[..shared].iter().cloned());
    for frame in &current[shared..] {
        if !captured.iter().any(|c| same_handler_frame_native(c, frame)) {
            merged.push(frame.clone());
        }
    }
    merged.extend(captured[shared..].iter().cloned());
    merged
}

/// `merge_extras_into_frames` port. For each captured return frame,
/// re-merge its `handlers` snapshot with the current resume-site
/// handlers via anchor logic.
fn merge_extras_into_frames_native(
    frames: &[NativeCpsI64ReturnFrame],
    current: &[NativeCpsI64HandlerFrame],
    anchor: Option<NativeCpsI64HandlerAnchor>,
) -> Vec<NativeCpsI64ReturnFrame> {
    frames
        .iter()
        .map(|frame| {
            let merged = merge_resumption_handlers_native(&frame.handlers, current, anchor);
            NativeCpsI64ReturnFrame {
                prompt_exit: frame.prompt_exit.clone(),
                debug_id: frame.debug_id,
                continuation: frame.continuation,
                continuation_id: frame.continuation_id,
                env: frame.env.clone(),
                handlers: merged,
                guards: frame.guards.clone(),
                owner_initial_frame_count: frame.owner_initial_frame_count,
                owner_eval_id: frame.owner_eval_id,
                owner_function_id: frame.owner_function_id,
                immediately_forces_param: frame.immediately_forces_param,
            }
        })
        .collect()
}

fn capture_native_i64_return_frames_from_start(
    frames: &[NativeCpsI64ReturnFrame],
    start: usize,
    handled_install_eval_id: u64,
) -> Box<[NativeCpsI64ReturnFrame]> {
    let mut captured = frames[start..]
        .iter()
        .cloned()
        .map(|frame| rebase_native_i64_captured_return_frame(frame, start, handled_install_eval_id))
        .collect::<Vec<_>>();
    own_native_i64_captured_return_frames(&mut captured);
    captured.into_boxed_slice()
}

fn native_i64_prompt_frame_start(
    frames: &[NativeCpsI64ReturnFrame],
    prompt: u64,
    _fallback_threshold: usize,
) -> usize {
    frames
        .iter()
        .rposition(|frame| {
            frame
                .prompt_exit
                .as_ref()
                .is_some_and(|exit| exit.prompt == prompt)
        })
        .map(|index| index + 1)
        // If the marker is absent, this captured slice is already running
        // under an inherited prompt. Keep the whole slice; the handler
        // threshold may point at a replay-time post frame that still belongs
        // to this continuation.
        .unwrap_or(0)
        .min(frames.len())
}

fn rebase_native_i64_captured_return_frame(
    mut frame: NativeCpsI64ReturnFrame,
    dropped_frames: usize,
    handled_install_eval_id: u64,
) -> NativeCpsI64ReturnFrame {
    frame.owner_initial_frame_count = frame
        .owner_initial_frame_count
        .saturating_sub(dropped_frames);
    for handler in &mut frame.handlers {
        if handler.install_eval_id >= handled_install_eval_id {
            handler.return_frame_threshold = handler
                .return_frame_threshold
                .saturating_sub(dropped_frames);
        }
    }
    frame
}

fn rebase_native_i64_captured_handlers(
    handlers: &mut [NativeCpsI64HandlerFrame],
    dropped_frames: usize,
    handled_install_eval_id: u64,
) {
    for handler in handlers {
        if handler.install_eval_id >= handled_install_eval_id {
            handler.return_frame_threshold = handler
                .return_frame_threshold
                .saturating_sub(dropped_frames);
        }
    }
}

/// For handlers whose install_eval is below the anchor (inherited from an
/// outer eval), the captured threshold value is stale once the slice is
/// reused inside a nested resumption: the slice now contains a different
/// set of pre-install frames. Re-derive each inherited threshold from the
/// actual position of its prompt-exit marker inside the slice; if the
/// marker is not present, the handler was installed strictly before the
/// slice began, so the slice has no pre-install frames (threshold = 0).
fn recalibrate_inherited_handler_thresholds(
    handlers: &mut [NativeCpsI64HandlerFrame],
    slice: &[NativeCpsI64ReturnFrame],
    handled_install_eval_id: u64,
) {
    for handler in handlers {
        if handler.install_eval_id >= handled_install_eval_id {
            continue;
        }
        let prompt = handler.prompt;
        let marker = slice.iter().position(|frame| {
            frame
                .prompt_exit
                .as_ref()
                .is_some_and(|exit| exit.prompt == prompt)
        });
        handler.return_frame_threshold = marker.unwrap_or(0);
    }
}

fn own_native_i64_captured_return_frames(frames: &mut [NativeCpsI64ReturnFrame]) {
    for frame in frames {
        frame.owner_initial_frame_count = 0;
    }
}

fn append_resume_handler_to_frames(
    frames: &mut [NativeCpsI64ReturnFrame],
    handler: &NativeCpsI64HandlerFrame,
) {
    for frame in frames {
        if !frame
            .handlers
            .iter()
            .any(|existing| same_handler_frame_native(existing, handler))
        {
            frame.handlers.push(handler.clone());
        }
    }
}

fn append_resume_handler_to_handler_prefixes(
    handlers: &mut [NativeCpsI64HandlerFrame],
    handler: &NativeCpsI64HandlerFrame,
) {
    for active in handlers {
        if active.return_frame_prefix.is_empty() {
            continue;
        }
        let mut prefix = active.return_frame_prefix.to_vec();
        append_resume_handler_to_frames(&mut prefix, handler);
        active.return_frame_prefix = prefix.into_boxed_slice();
    }
}

fn push_resume_with_handler_sibling(handler: NativeCpsI64HandlerFrame) {
    NATIVE_CPS_I64_RESUME_WITH_HANDLER_SIBLINGS.with(|siblings| {
        let mut siblings = siblings.borrow_mut();
        if !siblings
            .iter()
            .any(|existing| same_handler_frame_native(existing, &handler))
        {
            if jit_trace_enabled() {
                eprintln!(
                    "[JIT-CPS] push_rwh_sibling: handler={} envs={}",
                    handler.handler,
                    format_handler_envs(&handler.envs)
                );
            }
            siblings.push(handler);
        }
    });
}

fn append_resume_with_handler_siblings(handlers: &mut Vec<NativeCpsI64HandlerFrame>) {
    NATIVE_CPS_I64_RESUME_WITH_HANDLER_SIBLINGS.with(|siblings| {
        for sibling in siblings.borrow().iter() {
            if !handlers
                .iter()
                .any(|existing| same_handler_frame_native(existing, sibling))
            {
                handlers.push(sibling.clone());
            }
        }
    });
}

fn restore_native_i64_return_frames_after_resume(
    saved_frames: Vec<NativeCpsI64ReturnFrame>,
    _resumed_frames: &[NativeCpsI64ReturnFrame],
) {
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        let current = frames.borrow().clone();
        let mut restored = Vec::new();
        let mut used_current = HashSet::new();
        for saved in saved_frames {
            if let Some((index, current_frame)) = current
                .iter()
                .enumerate()
                .find(|(_, frame)| frame.debug_id == saved.debug_id)
            {
                restored.push(current_frame.clone());
                used_current.insert(index);
            } else {
                restored.push(saved);
            }
        }
        for (index, current_frame) in current.into_iter().enumerate() {
            if !used_current.contains(&index) {
                restored.push(current_frame);
            }
        }
        *frames.borrow_mut() = restored;
    });
}

/// write27-d d4: shared core of `effectful_apply_resumption_i64_N`.
/// Mirrors Layer 2's `EffectfulApply { Resumption } ` arm:
///   1. push F_post(post_cont, env_slots, owner_initial, owner_eval)
///      onto current return frames.
///   2. anchor-merge resumption.handlers with the current handler stack.
///   3. anchor-merge each of resumption.return_frames' handler snapshots.
///   4. combined_frames = new_frames + adjusted_resumption_frames.
///   5. swap thread-local state and call `resumption.code(env, arg)`.
/// write27-e e1: compact formatter for a handler stack — emits
/// `[h<id>(p=..., ev=..., origin=..., inh=...) ...]` so trace lines
/// don't blow up but each frame's identity is still visible.
fn format_handler_stack(stack: &[NativeCpsI64HandlerFrame]) -> String {
    let mut s = String::from("[");
    for (i, frame) in stack.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        s.push_str(&format!(
            "h{}(p={},ev={},owner_fn={},thr_owner={},{:?},inh={},thr={},guards={:?})",
            frame.handler,
            frame.prompt,
            if frame.install_eval_id == NATIVE_CPS_I64_SYNTHETIC_EVAL_ID {
                "SYN".to_string()
            } else {
                frame.install_eval_id.to_string()
            },
            frame.escape_owner_function_id,
            frame.threshold_owner_function_id,
            frame.origin,
            frame.inherited,
            frame.return_frame_threshold,
            frame.guard_stack,
        ));
    }
    s.push(']');
    s
}

/// write27-e e1: compact formatter for a return-frame stack — useful
/// to verify anchor merge actually modified each frame's
/// `active_handlers`.
fn format_return_frames(frames: &[NativeCpsI64ReturnFrame]) -> String {
    const EDGE_FRAMES: usize = 4;
    let mut s = String::from("[");
    let mut wrote = 0usize;
    for (i, frame) in frames.iter().enumerate() {
        if frames.len() > EDGE_FRAMES * 2 && i == EDGE_FRAMES {
            if wrote > 0 {
                s.push_str(", ");
            }
            s.push_str(&format!("... {} more ...", frames.len() - EDGE_FRAMES * 2));
            wrote += 1;
            continue;
        }
        if frames.len() > EDGE_FRAMES * 2 && i >= EDGE_FRAMES && i < frames.len() - EDGE_FRAMES {
            continue;
        }
        if i > 0 {
            s.push_str(", ");
        }
        let prompt_exit = frame
            .prompt_exit
            .as_ref()
            .map(|exit| format!(",prompt_exit={}", exit.prompt))
            .unwrap_or_default();
        s.push_str(&format!(
            "F#{}/id{}:k{}(owner_eval={},owner_fn={},init={}{} ,handlers={})",
            i,
            frame.debug_id,
            frame.continuation_id,
            frame.owner_eval_id,
            frame.owner_function_id,
            frame.owner_initial_frame_count,
            prompt_exit,
            format_handler_stack(&frame.handlers),
        ));
        wrote += 1;
    }
    s.push(']');
    s
}

fn format_handler_envs(envs: &[NativeCpsI64HandlerEnv]) -> String {
    let parts = envs
        .iter()
        .map(|env| {
            let slots = if env.slots.is_empty() {
                String::new()
            } else {
                let slots = env
                    .slots
                    .iter()
                    .map(|(target, value)| {
                        format!("{}:{}", target, describe_native_i64_value(*value))
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                format!(" {{{}}}", slots)
            };
            format!(
                "{}={}{}",
                env.entry,
                describe_native_i64_value(env.env),
                slots
            )
        })
        .collect::<Vec<_>>();
    format!("[{}]", parts.join(", "))
}

fn refreshed_escape_env(frame: &NativeCpsI64HandlerFrame) -> Box<[i64]> {
    if frame.escape_env_targets.is_empty() {
        return frame.escape_env.clone();
    }
    let mut env = frame.escape_env.to_vec();
    for (index, target) in frame.escape_env_targets.iter().copied().enumerate() {
        let Some(slot) = env.get_mut(index) else {
            continue;
        };
        if let Some(value) = latest_handler_slot_value(frame.handler, target) {
            *slot = value;
        }
    }
    env.into_boxed_slice()
}

fn latest_handler_slot_value(handler: i64, target: i64) -> Option<i64> {
    NATIVE_CPS_I64_RESUME_WITH_HANDLER_SIBLINGS.with(|siblings| {
        siblings
            .borrow()
            .iter()
            .rev()
            .filter(|frame| frame.handler == handler)
            .flat_map(|frame| frame.envs.iter().rev())
            .flat_map(|env| env.slots.iter().rev())
            .find_map(|(slot_target, value)| (*slot_target == target).then_some(*value))
    })
}

fn append_distinct_return_frames(
    out: &mut Vec<NativeCpsI64ReturnFrame>,
    frames: impl IntoIterator<Item = NativeCpsI64ReturnFrame>,
) {
    for frame in frames {
        if out
            .iter()
            .any(|existing| existing.debug_id == frame.debug_id)
        {
            if jit_trace_enabled() {
                eprintln!("[JIT-CPS] return_frame_dedup: skip id={}", frame.debug_id);
            }
            continue;
        }
        out.push(frame);
    }
}

fn is_captured_handler_key(
    handler: &NativeCpsI64HandlerFrame,
    captured: &[NativeCpsI64HandlerFrame],
) -> bool {
    captured.iter().any(|candidate| {
        candidate.prompt == handler.prompt && candidate.install_eval_id == handler.install_eval_id
    })
}

fn rebase_captured_return_frame_threshold(
    old_threshold: usize,
    captured_frames: &[NativeCpsI64ReturnFrame],
    combined_prefix: &[NativeCpsI64ReturnFrame],
) -> usize {
    let mut rebased = combined_prefix.len();
    let captured_prefix_len = old_threshold.min(captured_frames.len());
    for captured in &captured_frames[..captured_prefix_len] {
        if !combined_prefix
            .iter()
            .any(|existing| existing.debug_id == captured.debug_id)
        {
            rebased += 1;
        }
    }
    rebased
}

fn rebase_captured_handler_thresholds(
    frames: &mut [NativeCpsI64ReturnFrame],
    captured_handlers: &[NativeCpsI64HandlerFrame],
    captured_frames: &[NativeCpsI64ReturnFrame],
    combined_prefix: &[NativeCpsI64ReturnFrame],
) {
    for frame in frames {
        for handler in &mut frame.handlers {
            if is_captured_handler_key(handler, captured_handlers) {
                handler.return_frame_threshold = rebase_captured_return_frame_threshold(
                    handler.return_frame_threshold,
                    captured_frames,
                    combined_prefix,
                );
            }
        }
    }
}

fn effectful_apply_resumption_native(
    resumption: *const NativeCpsI64Resumption,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: bool,
    env: Vec<i64>,
) -> i64 {
    let resumption = unsafe { &*resumption };
    let current_handlers = NATIVE_CPS_I64_HANDLER_STACK.with(|s| s.borrow().clone());
    let current_guards = NATIVE_CPS_I64_GUARD_STACK.with(|s| s.borrow().clone());
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] effectful_apply_resumption.in: rid={} anchor={:?} captured={} captured_frames={} current={}",
            resumption.debug_id,
            resumption.handled_anchor,
            format_handler_stack(&resumption.handlers),
            format_return_frames(&resumption.return_frames),
            format_handler_stack(&current_handlers),
        );
    }
    // 1. Build F_post.
    let f_post = NativeCpsI64ReturnFrame {
        prompt_exit: None,
        debug_id: next_native_i64_return_frame_debug_id(),
        continuation: post_cont as usize,
        continuation_id: 0,
        env: env.into_boxed_slice(),
        handlers: current_handlers.clone(),
        guards: current_guards.clone(),
        owner_initial_frame_count: owner_initial.max(0) as usize,
        owner_eval_id: owner_eval as u64,
        owner_function_id: owner_function.max(0) as u64,
        immediately_forces_param: immediately_forces,
    };
    let mut new_frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|f| f.borrow().clone());
    new_frames.push(f_post);
    // 2 + 3. Anchor merges.
    let anchor = resumption.handled_anchor;
    let resumed_handlers =
        merge_resumption_handlers_native(&resumption.handlers, &current_handlers, anchor);
    let mut adjusted_res =
        merge_extras_into_frames_native(&resumption.return_frames, &current_handlers, anchor);
    rebase_captured_handler_thresholds(
        &mut adjusted_res,
        &resumption.handlers,
        &resumption.return_frames,
        &new_frames,
    );
    // 4. combined frames. A captured resumption can be resumed while one
    // of its captured return-frame instances is already present at the
    // resume site. Re-adding that exact instance replays stale
    // continuations after reject/backtracking; only suppress identical
    // frame instances, not merely same-shaped fresh frames.
    append_distinct_return_frames(&mut new_frames, adjusted_res);
    let combined_len = new_frames.len();
    let resumed_len = resumed_handlers.len();
    // 5. swap state + call.
    NATIVE_CPS_I64_RETURN_FRAMES.with(|f| *f.borrow_mut() = new_frames.clone());
    NATIVE_CPS_I64_HANDLER_STACK.with(|s| *s.borrow_mut() = resumed_handlers.clone());
    NATIVE_CPS_I64_GUARD_STACK.with(|s| *s.borrow_mut() = resumption.guard_stack.to_vec());
    let fresh_eval = NATIVE_CPS_I64_NEXT_EVAL_ID.with(|next| {
        let id = *next.borrow();
        *next.borrow_mut() = id + 1;
        id
    });
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| {
        *ctx.borrow_mut() = NativeCpsI64EvalContext {
            current_eval_id: fresh_eval,
            initial_frame_count: 0,
        };
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] effectful_apply_resumption.out: rid={} anchor={:?} fresh_eval={} combined_len={} resumed={} resumed_handlers={} new_frames={}",
            resumption.debug_id,
            anchor,
            fresh_eval,
            combined_len,
            resumed_len,
            format_handler_stack(&resumed_handlers),
            format_return_frames(&new_frames),
        );
    }
    (resumption.code)(resumption.env.as_ptr(), arg)
}

/// write27-d d4: 0..4 env-slot variants for the resumption apply
/// helper. The codegen passes the resume continuation's env slots
/// inline so this helper doesn't need to read them from anywhere
/// else.
#[unsafe(no_mangle)]
extern "C" fn yulang_cps_effectful_apply_resumption_i64_0(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
) -> i64 {
    effectful_apply_resumption_native(
        resumption as *const NativeCpsI64Resumption,
        arg,
        post_cont,
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces != 0,
        Vec::new(),
    )
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_effectful_apply_resumption_i64_1(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    a: i64,
) -> i64 {
    effectful_apply_resumption_native(
        resumption as *const NativeCpsI64Resumption,
        arg,
        post_cont,
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces != 0,
        vec![a],
    )
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_effectful_apply_resumption_i64_2(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    a: i64,
    b: i64,
) -> i64 {
    effectful_apply_resumption_native(
        resumption as *const NativeCpsI64Resumption,
        arg,
        post_cont,
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces != 0,
        vec![a, b],
    )
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_effectful_apply_resumption_i64_3(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    a: i64,
    b: i64,
    c: i64,
) -> i64 {
    effectful_apply_resumption_native(
        resumption as *const NativeCpsI64Resumption,
        arg,
        post_cont,
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces != 0,
        vec![a, b, c],
    )
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_effectful_apply_resumption_i64_4(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> i64 {
    effectful_apply_resumption_native(
        resumption as *const NativeCpsI64Resumption,
        arg,
        post_cont,
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces != 0,
        vec![a, b, c, d],
    )
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_effectful_apply_resumption_i64_many(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    ptr: *const i64,
    len: i64,
) -> i64 {
    effectful_apply_resumption_native(
        resumption as *const NativeCpsI64Resumption,
        arg,
        post_cont,
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces != 0,
        unsafe { native_i64_slice(ptr, len) },
    )
}

/// write27-d d4: runtime predicate used by EffectfulApply codegen to
/// branch into the closure or resumption path.
#[unsafe(no_mangle)]
extern "C" fn yulang_cps_is_resumption_i64(value: i64) -> i64 {
    let is = NATIVE_CPS_I64_RESUMPTIONS.with(|s| s.borrow().contains(&(value as usize)));
    i64::from(is)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_select_handler_i64(
    fallback_handler: i64,
    effect_mask: i64,
    blocked: i64,
) -> i64 {
    let stack = current_native_i64_handler_stack_with_fallback(fallback_handler, effect_mask);
    // write27-d d6: two-pass search to dodge JIT-only `PendingEnv`
    // placeholders. `take_pending_native_i64_handler_frames` builds
    // these from capture envs without a real prompt/escape; they
    // appear in resumption/thunk handler snapshots and would
    // otherwise shadow legitimate handlers. Legacy installs and
    // static fallbacks stay first-class so existing abort_i64 paths
    // still resolve.
    let is_preferred_origin = |origin: NativeCpsI64HandlerFrameOrigin| {
        !matches!(origin, NativeCpsI64HandlerFrameOrigin::PendingEnv)
    };
    let frame_allowed = |frame: &NativeCpsI64HandlerFrame| {
        let allowed = (frame.consumes_mask & effect_mask) != 0;
        if !allowed {
            return false;
        }
        if blocked >= 0 && frame.guard_stack.contains(&blocked) {
            return false;
        }
        true
    };
    let chosen = stack
        .iter()
        .enumerate()
        .rev()
        .find(|(_, frame)| frame_allowed(frame) && is_preferred_origin(frame.origin))
        .or_else(|| {
            stack
                .iter()
                .enumerate()
                .rev()
                .find(|(_, frame)| frame_allowed(frame))
        });
    if let Some((index, frame)) = chosen {
        // write27-c c3: stash the pre-truncation stack so the post-arm
        // `restore_outer_handler_stack` can reinstate the matched
        // handler. The arm body itself still sees the truncated stack
        // (matches Layer 1/2's `handler_body_stack`).
        NATIVE_CPS_I64_OUTER_HANDLER_SNAPSHOTS.with(|snaps| {
            snaps.borrow_mut().push(stack.clone());
        });
        // write27-c c3: record the selected frame's metadata so the
        // post-arm path can wrap the natural return as a ScopeReturn
        // targeting this frame's escape.
        NATIVE_CPS_I64_SELECTED_HANDLER_META_STACK.with(|meta| {
            meta.borrow_mut().push(NativeCpsI64SelectedHandlerMeta {
                prompt: frame.prompt,
                escape_continuation: frame.escape_continuation,
                escape_env: frame.escape_env.clone(),
                return_frame_threshold: frame.return_frame_threshold,
                install_eval_id: frame.install_eval_id,
                synthetic: frame.install_eval_id == NATIVE_CPS_I64_SYNTHETIC_EVAL_ID
                    || frame.escape_continuation == 0,
            });
        });
        NATIVE_CPS_I64_HANDLER_STACK.with(|active| {
            *active.borrow_mut() = stack[..index].to_vec();
        });
        NATIVE_CPS_I64_SELECTED_HANDLER_ENVS.with(|envs| {
            *envs.borrow_mut() = frame.envs.to_vec();
        });
        NATIVE_CPS_I64_SELECTED_HANDLER_ID.with(|handler| *handler.borrow_mut() = frame.handler);
        NATIVE_CPS_I64_SELECTED_HANDLER_USED_RWH_ENV.with(|used| *used.borrow_mut() = false);
        if jit_trace_enabled() {
            eprintln!(
                "[JIT-CPS] perform_select: handler={} prompt={} install_eval={} synthetic={} threshold={} idx={} origin={:?} envs={}",
                frame.handler,
                frame.prompt,
                frame.install_eval_id,
                frame.install_eval_id == NATIVE_CPS_I64_SYNTHETIC_EVAL_ID,
                frame.return_frame_threshold,
                index,
                frame.origin,
                format_handler_envs(&frame.envs),
            );
        }
        return frame.handler;
    }
    NATIVE_CPS_I64_SELECTED_HANDLER_ENVS.with(|envs| envs.borrow_mut().clear());
    NATIVE_CPS_I64_SELECTED_HANDLER_ID.with(|handler| *handler.borrow_mut() = -1);
    NATIVE_CPS_I64_SELECTED_HANDLER_USED_RWH_ENV.with(|used| *used.borrow_mut() = false);
    -1
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_active_blocked_guard_i64(effect_mask: i64) -> i64 {
    NATIVE_CPS_I64_ACTIVE_BLOCKED.with(|stack| {
        let stack = stack.borrow();
        let mut peeled = HashSet::new();
        let mut selected = -1;
        for blocked in stack.iter().rev() {
            if peeled.contains(&blocked.guard_id) {
                continue;
            }
            if !blocked.active {
                // `add_id[peek, X]` lowers to an inactive boundary for the
                // same guard. It peels the corresponding active blocker for
                // inner operations, so keep the inactive marker in the stack
                // and let reverse dispatch cancel older entries.
                peeled.insert(blocked.guard_id);
                continue;
            }
            if (blocked.allowed_mask & effect_mask) == 0 {
                selected = blocked.guard_id;
                break;
            }
        }
        if jit_trace_enabled() {
            eprintln!(
                "[JIT-CPS] active_blocked: effect_mask={} selected={} stack={:?}",
                effect_mask,
                selected,
                stack
                    .iter()
                    .map(|entry| (entry.guard_id, entry.allowed_mask, entry.active))
                    .collect::<Vec<_>>()
            );
        }
        selected
    })
}

/// write27-c c3: reinstate the outer handler stack saved at the most
/// recent `select_handler` call. The Perform path calls this after
/// the arm body returns so the post-arm `route_scope_return` can walk
/// the full pre-truncation stack (mirrors Layer 1/2 where
/// `active_handlers` is a local variable and arm body mutations
/// don't propagate).
#[unsafe(no_mangle)]
extern "C" fn yulang_cps_restore_outer_handler_stack_i64() -> i64 {
    NATIVE_CPS_I64_OUTER_HANDLER_SNAPSHOTS.with(|snaps| {
        if let Some(snap) = snaps.borrow_mut().pop() {
            NATIVE_CPS_I64_HANDLER_STACK.with(|stack| *stack.borrow_mut() = snap);
        }
    });
    0
}

/// write27-c c3: combined Perform-arm finish path.
///   1. Restore the pre-truncation handler stack saved at
///      `select_handler` time.
///   2. If the selected handler is real (non-synthetic) AND no
///      ScopeReturn is already active, wrap `value` as a ScopeReturn
///      targeting that handler's escape.
///   3. Try to route any active ScopeReturn to its destination
///      (current handler stack walk, then return-frame walk). Returns
///      the escape's result on hit; the original `value` on miss
///      (with the slot left active to propagate further).
///   4. If the selected handler was synthetic (or no meta exists) AND
///      the legacy abort slot is not set, set it to `routed` so old
///      callback / fold propagation paths can bubble up.
/// Returns the value the JIT function should hand back to its caller.
#[unsafe(no_mangle)]
extern "C" fn yulang_cps_perform_finish_i64(value: i64) -> i64 {
    // 1. restore outer.
    NATIVE_CPS_I64_OUTER_HANDLER_SNAPSHOTS.with(|snaps| {
        if let Some(snap) = snaps.borrow_mut().pop() {
            NATIVE_CPS_I64_HANDLER_STACK.with(|stack| *stack.borrow_mut() = snap);
        }
    });
    // 2. wrap as ScopeReturn if applicable.
    let meta = NATIVE_CPS_I64_SELECTED_HANDLER_META_STACK.with(|m| m.borrow_mut().pop());
    let is_real = meta
        .as_ref()
        .map(|m| !m.synthetic && m.escape_continuation != 0)
        .unwrap_or(false);
    let already_active = NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().active);
    if is_real && !already_active {
        let meta = meta.as_ref().expect("is_real implies meta");
        NATIVE_CPS_I64_ABORT.with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::None);
        NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| {
            *slot.borrow_mut() = NativeCpsI64ScopeReturn {
                active: true,
                prompt: meta.prompt,
                target: meta.escape_continuation as i64,
                value,
            };
        });
        if jit_trace_enabled() {
            let current_eval = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().current_eval_id);
            let current_initial =
                NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().initial_frame_count);
            let stack = NATIVE_CPS_I64_HANDLER_STACK.with(|s| s.borrow().clone());
            let frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|f| f.borrow().clone());
            eprintln!(
                "[JIT-CPS] scope_return_set (perform_finish): prompt={} target={:#x} value={} current_eval={} initial={} stack={} frames={}",
                meta.prompt,
                meta.escape_continuation,
                describe_native_i64_value(value),
                current_eval,
                current_initial,
                format_handler_stack(&stack),
                format_return_frames(&frames),
            );
        }
    }
    // 3. route.
    let routed = yulang_cps_route_scope_return_i64(value);
    // 4. legacy abort fallback (synthetic handler / no SR path).
    if !is_real {
        let abort_already = NATIVE_CPS_I64_ABORT.with(|slot| slot.borrow().is_active());
        if !abort_already {
            NATIVE_CPS_I64_ABORT
                .with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::Global(routed));
        }
    }
    routed
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_perform_finish_escaped_i64(value: i64) -> i64 {
    NATIVE_CPS_I64_OUTER_HANDLER_SNAPSHOTS.with(|snaps| {
        if let Some(snap) = snaps.borrow_mut().pop() {
            NATIVE_CPS_I64_HANDLER_STACK.with(|stack| *stack.borrow_mut() = snap);
        }
    });
    let meta = NATIVE_CPS_I64_SELECTED_HANDLER_META_STACK.with(|meta| meta.borrow_mut().pop());
    if NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().active) {
        return yulang_cps_route_scope_return_i64(value);
    }
    let mut abort_outer_eval = false;
    if let Some(meta) = meta {
        if meta.synthetic || meta.escape_continuation == 0 {
            return value;
        }
        let current_eval = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().current_eval_id);
        let used_rwh_env = NATIVE_CPS_I64_SELECTED_HANDLER_USED_RWH_ENV.with(|used| *used.borrow());
        if meta.install_eval_id != current_eval && used_rwh_env {
            return value;
        }
        if meta.install_eval_id != current_eval {
            NATIVE_CPS_I64_ABORT.with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::None);
            NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| {
                *slot.borrow_mut() = NativeCpsI64ScopeReturn {
                    active: true,
                    prompt: meta.prompt,
                    target: meta.escape_continuation as i64,
                    value,
                };
            });
            return yulang_cps_route_scope_return_i64(value);
        }
        abort_outer_eval = meta.return_frame_threshold == 0;
        NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
            let mut frames = frames.borrow_mut();
            if frames.len() > meta.return_frame_threshold {
                frames.truncate(meta.return_frame_threshold);
            }
        });
    }
    let frame_len = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
    if frame_len == 0 {
        let current_initial =
            NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().initial_frame_count);
        if abort_outer_eval && current_initial > 0 {
            NATIVE_CPS_I64_ABORT.with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::Global(value));
        }
        return value;
    }
    let result = yulang_cps_continue_return_frame_i64(value);
    let current_initial = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().initial_frame_count);
    if abort_outer_eval && current_initial > 0 {
        NATIVE_CPS_I64_ABORT.with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::Global(result));
    }
    result
}

/// write27-c c3: if no ScopeReturn is active, wrap `value` as a
/// ScopeReturn targeting the most-recently-selected handler's escape.
/// If the selected handler is synthetic (no real escape), this is a
/// no-op and `value` flows through as the eval frame's natural result.
/// Always returns `value` so the codegen can `return` it directly.
#[unsafe(no_mangle)]
extern "C" fn yulang_cps_scope_return_from_selected_handler_i64(value: i64) -> i64 {
    let already_active = NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().active);
    if already_active {
        return value;
    }
    let meta = NATIVE_CPS_I64_SELECTED_HANDLER_META_STACK.with(|m| m.borrow().last().cloned());
    let Some(meta) = meta else {
        return value;
    };
    if meta.synthetic || meta.escape_continuation == 0 {
        return value;
    }
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| {
        *slot.borrow_mut() = NativeCpsI64ScopeReturn {
            active: true,
            prompt: meta.prompt,
            target: meta.escape_continuation as i64,
            value,
        };
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] scope_return_set (from selected): prompt={} target={:#x} value={}",
            meta.prompt, meta.escape_continuation, value
        );
    }
    value
}

/// write27-c c4: dispatch the active `ScopeReturn` slot. Returns the
/// resumed escape's result when a match is found, otherwise leaves
/// the slot active and returns `fallback_value` so the caller can
/// keep propagating up.
///
/// Search order mirrors `cps_eval`/`cps_repr`:
/// 1. Current handler stack: rposition by (prompt, install_eval_id ==
///    current_eval_id). On hit, truncate to that index, truncate
///    return_frames to the matched frame's threshold, clear slot,
///    call escape with the slot's value.
/// 2. Return frames `[current_initial..]`: rposition by frame snapshot
///    handler with (prompt, install_eval_id == frame.owner_eval_id).
///    On hit, restore that frame's snapshot, truncate stack/frames,
///    set eval context, clear slot, call escape.
#[unsafe(no_mangle)]
extern "C" fn yulang_cps_route_scope_return_i64(fallback_value: i64) -> i64 {
    let sr = NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().clone());
    if !sr.active {
        return fallback_value;
    }
    let prompt = sr.prompt;
    let value = sr.value;
    let current_eval = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().current_eval_id);
    let current_initial = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().initial_frame_count);

    if jit_trace_enabled() {
        let stack = NATIVE_CPS_I64_HANDLER_STACK.with(|s| s.borrow().clone());
        let frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|f| f.borrow().clone());
        eprintln!(
            "[JIT-CPS] route_scope_return.scan: prompt={} value={} current_eval={} initial={} force_frame_walk={} stack={} frames={}",
            prompt,
            describe_native_i64_value(value),
            current_eval,
            current_initial,
            jit_force_frame_walk_sr(),
            format_handler_stack(&stack),
            format_return_frames(&frames),
        );
    }

    // write27-e e4: optionally skip the current-handler scan so we can
    // see whether the frame-walk path matches Layer 1/2's frontier.
    // Toggled via `YULANG_CPS_JIT_FORCE_FRAME_WALK_SR=1`.
    let skip_current = jit_force_frame_walk_sr();

    // 1. Walk the current handler stack reverse.
    let cur_match: Option<(usize, NativeCpsI64HandlerFrame)> = if skip_current {
        None
    } else {
        NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
            let stack = stack.borrow();
            stack
                .iter()
                .rposition(|f| f.prompt == prompt && f.install_eval_id == current_eval)
                .map(|idx| (idx, stack[idx].clone()))
        })
    };
    if let Some((idx, frame)) = cur_match {
        let mut post_handlers = NATIVE_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow().clone());
        post_handlers.truncate(idx);
        let mut post_frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().clone());
        if post_frames.len() > frame.return_frame_threshold {
            post_frames.truncate(frame.return_frame_threshold);
        }
        NATIVE_CPS_I64_HANDLER_STACK.with(|stack| *stack.borrow_mut() = post_handlers.clone());
        NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| *frames.borrow_mut() = post_frames.clone());
        NATIVE_CPS_I64_SCOPE_RETURN
            .with(|slot| *slot.borrow_mut() = NativeCpsI64ScopeReturn::default());
        NATIVE_CPS_I64_RETURN_FRAMES_ROUTED.with(|routed| *routed.borrow_mut() = true);
        if jit_trace_enabled() {
            eprintln!(
                "[JIT-CPS] route_scope_return: prompt={} current_eval={} initial={} action=current_handler value={}",
                prompt,
                current_eval,
                current_initial,
                describe_native_i64_value(value)
            );
        }
        if frame.escape_continuation == 0 {
            if current_initial > 0 && post_handlers.is_empty() {
                NATIVE_CPS_I64_ABORT
                    .with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::Global(value));
            }
            return value;
        }
        let escape_env = refreshed_escape_env(&frame);
        if current_initial > 0 && post_handlers.is_empty() && frame.guard_stack.is_empty() {
            let cont: NativeCpsI64Continuation =
                unsafe { std::mem::transmute(frame.escape_continuation) };
            let result = cont(escape_env.as_ptr(), value);
            NATIVE_CPS_I64_ABORT
                .with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::Global(result));
            return result;
        }
        // A current-stack match can still jump out of an inner eval frame
        // when the dynamic handler was restored from a captured return frame.
        // Keep the same short-circuit signal used by the frame-walk path so
        // skipped native callers do not continue with their normal fallback.
        if current_initial > 0 {
            NATIVE_CPS_I64_ABORT.with(|slot| {
                *slot.borrow_mut() = routed_jump_abort(
                    value,
                    frame.return_frame_threshold,
                    frame.escape_continuation,
                    escape_env,
                    post_handlers,
                    frame.guard_stack.to_vec(),
                    post_frames,
                    NativeCpsI64EvalContext {
                        current_eval_id: frame.install_eval_id,
                        initial_frame_count: frame.return_frame_threshold,
                    },
                );
            });
            return value;
        }
        let cont: NativeCpsI64Continuation =
            unsafe { std::mem::transmute(frame.escape_continuation) };
        let result = cont(escape_env.as_ptr(), value);
        return result;
    }

    // 2. Walk the whole return-frame snapshot to find a captured handler
    //    that matches. The original install scope can live in an inherited
    //    prefix after callbacks or resumptions; matching by the frame's
    //    owner eval keeps this precise without relying on prompt-only
    //    routing.
    let frame_match = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        let frames = frames.borrow();
        let len = frames.len();
        if len == 0 {
            return None;
        }
        for fi in (0..len).rev() {
            let f = &frames[fi];
            for (hi, h) in f.handlers.iter().enumerate().rev() {
                if h.prompt == prompt
                    && h.install_eval_id == f.owner_eval_id
                    && h.escape_owner_function_id == f.owner_function_id
                {
                    return Some((fi, hi, f.clone(), h.clone()));
                }
            }
        }
        None
    });
    if let Some((fi, hi, frame, handler)) = frame_match {
        // Restore handler stack to frame.handlers[..hi].
        let mut post_handlers = frame.handlers.clone();
        post_handlers.truncate(hi);
        NATIVE_CPS_I64_HANDLER_STACK.with(|stack| *stack.borrow_mut() = post_handlers.clone());
        NATIVE_CPS_I64_GUARD_STACK.with(|stack| *stack.borrow_mut() = frame.guards.clone());
        let mut post_frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().clone());
        post_frames.truncate(fi);
        if post_frames.len() > handler.return_frame_threshold {
            post_frames.truncate(handler.return_frame_threshold);
        }
        NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| *frames.borrow_mut() = post_frames.clone());
        // Set eval context to frame's owner (capped to current frames).
        let rest_len = post_frames.len();
        let owner_initial = frame.owner_initial_frame_count.min(rest_len);
        let post_eval_context = NativeCpsI64EvalContext {
            current_eval_id: frame.owner_eval_id,
            initial_frame_count: owner_initial,
        };
        NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow_mut() = post_eval_context);
        NATIVE_CPS_I64_SCOPE_RETURN
            .with(|slot| *slot.borrow_mut() = NativeCpsI64ScopeReturn::default());
        NATIVE_CPS_I64_RETURN_FRAMES_ROUTED.with(|routed| *routed.borrow_mut() = true);
        if jit_trace_enabled() {
            eprintln!(
                "[JIT-CPS] route_scope_return: prompt={} current_eval={} initial={} action=frame_walk fi={} hi={} value={}",
                prompt,
                current_eval,
                current_initial,
                fi,
                hi,
                describe_native_i64_value(value)
            );
        }
        if handler.escape_continuation == 0 {
            if current_initial > 0 && post_handlers.is_empty() {
                NATIVE_CPS_I64_ABORT
                    .with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::Global(value));
            }
            return value;
        }
        let escape_env = refreshed_escape_env(&handler);
        if current_initial > 0 && post_handlers.is_empty() && handler.guard_stack.is_empty() {
            let cont: NativeCpsI64Continuation =
                unsafe { std::mem::transmute(handler.escape_continuation) };
            let result = cont(escape_env.as_ptr(), value);
            NATIVE_CPS_I64_ABORT
                .with(|slot| *slot.borrow_mut() = NativeCpsI64Abort::Global(result));
            return result;
        }
        // A frame-walk match jumps across an older eval frame. The native
        // call stack still needs a short-circuit signal until the next real
        // handler boundary re-wraps the value.
        if current_initial > 0 {
            NATIVE_CPS_I64_ABORT.with(|slot| {
                *slot.borrow_mut() = routed_jump_abort(
                    value,
                    handler.return_frame_threshold,
                    handler.escape_continuation,
                    escape_env,
                    post_handlers,
                    frame.guards.clone(),
                    post_frames,
                    post_eval_context,
                );
            });
            return value;
        }
        let cont: NativeCpsI64Continuation =
            unsafe { std::mem::transmute(handler.escape_continuation) };
        let result = cont(escape_env.as_ptr(), value);
        return result;
    }

    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] route_scope_return: prompt={} current_eval={} initial={} action=propagate value={}",
            prompt,
            current_eval,
            current_initial,
            describe_native_i64_value(value)
        );
    }
    fallback_value
}

#[allow(dead_code)]
fn routed_scope_return_abort(
    value: i64,
    return_frame_threshold: usize,
    restore_frames: Box<[NativeCpsI64ReturnFrame]>,
) -> NativeCpsI64Abort {
    NativeCpsI64Abort::Scoped {
        value,
        return_frame_threshold,
        propagate_at_threshold: false,
        restore_frames,
    }
}

fn routed_jump_abort(
    value: i64,
    return_frame_threshold: usize,
    continuation: usize,
    env: Box<[i64]>,
    handlers: Vec<NativeCpsI64HandlerFrame>,
    guards: Vec<i64>,
    return_frames: Vec<NativeCpsI64ReturnFrame>,
    eval_context: NativeCpsI64EvalContext,
) -> NativeCpsI64Abort {
    NativeCpsI64Abort::RoutedJump {
        value,
        return_frame_threshold,
        continuation,
        env,
        handlers,
        guards,
        return_frames: return_frames.into_boxed_slice(),
        eval_context,
    }
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_capture_handler_env_i64(handler: i64, entry: i64, env: i64) -> i64 {
    NATIVE_CPS_I64_PENDING_HANDLER_ENVS.with(|envs| {
        envs.borrow_mut().push((
            handler,
            NativeCpsI64HandlerEnv {
                entry,
                env,
                slots: Vec::new(),
            },
        ));
    });
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_capture_handler_env_mapped_i64(
    handler: i64,
    entry: i64,
    env: i64,
    target_ptr: *const i64,
    value_ptr: *const i64,
    target_len: i64,
    value_len: i64,
) -> i64 {
    let len = target_len.min(value_len).max(0) as usize;
    let targets = unsafe { native_i64_slice(target_ptr, len as i64) };
    let values = unsafe { native_i64_slice(value_ptr, len as i64) };
    let slots = targets
        .iter()
        .copied()
        .zip(values.iter().copied())
        .collect::<Vec<_>>();
    NATIVE_CPS_I64_PENDING_HANDLER_ENVS.with(|envs| {
        envs.borrow_mut()
            .push((handler, NativeCpsI64HandlerEnv { entry, env, slots }));
    });
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_set_pending_escape_env_targets_i64(ptr: *const i64, len: i64) -> i64 {
    let targets = unsafe { native_i64_slice(ptr, len) };
    NATIVE_CPS_I64_PENDING_ESCAPE_ENV_TARGETS.with(|slot| {
        *slot.borrow_mut() = targets.to_vec();
    });
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_install_handler_i64(handler: i64, consumes_mask: i64) -> i64 {
    let envs = take_pending_native_i64_handler_envs(handler);
    let frame = NativeCpsI64HandlerFrame {
        handler,
        consumes_mask,
        guard_stack: current_native_i64_guard_stack().into_boxed_slice(),
        envs,
        prompt: 0,
        install_eval_id: NATIVE_CPS_I64_SYNTHETIC_EVAL_ID,
        escape_owner_function_id: 0,
        threshold_owner_function_id: 0,
        inherited: false,
        escape_continuation: 0,
        escape_env: Box::new([]),
        escape_env_targets: Box::new([]),
        return_frame_threshold: 0,
        return_frame_prefix: Box::new([]),
        origin: NativeCpsI64HandlerFrameOrigin::LegacyInstall,
    };
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        stack.borrow_mut().push(frame);
    });
    if jit_trace_enabled() {
        eprintln!("[JIT-CPS] install_handler (legacy): handler={}", handler);
    }
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_uninstall_handler_i64(handler: i64) -> i64 {
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        let mut stack = stack.borrow_mut();
        if let Some(pos) = stack.iter().rposition(|frame| frame.handler == handler) {
            stack.remove(pos);
        }
    });
    0
}

// =====================================================================
// write27-c c2: full handler install. New helpers carry prompt /
// install_eval_id / escape_continuation / escape_env /
// return_frame_threshold so that ScopeReturn-based Perform (c3) and
// route_scope_return (c4) can dispatch correctly. The legacy
// `yulang_cps_install_handler_i64` stays in place — it constructs a
// synthetic frame with no escape and is only safe for paths that do
// not depend on ScopeReturn routing.
// =====================================================================

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_fresh_prompt_i64() -> i64 {
    NATIVE_CPS_I64_NEXT_PROMPT.with(|next| {
        let id = *next.borrow();
        *next.borrow_mut() = id.wrapping_add(1);
        id as i64
    })
}

fn install_native_i64_handler_full(
    handler: i64,
    consumes_mask: i64,
    escape_continuation: i64,
    return_frame_threshold: i64,
    prompt: i64,
    install_eval_id: i64,
    escape_owner_function_id: i64,
    inherited: i64,
    escape_env: Vec<i64>,
) {
    let envs = take_pending_native_i64_handler_envs(handler);
    let trace_envs = jit_trace_enabled().then(|| format_handler_envs(&envs));
    let threshold = return_frame_threshold.max(0) as usize;
    let escape_owner = escape_owner_function_id.max(0) as u64;
    let threshold_owner_function_id = if threshold == 0 {
        escape_owner
    } else {
        NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
            frames
                .borrow()
                .get(threshold - 1)
                .map(|frame| frame.owner_function_id)
                .unwrap_or(escape_owner)
        })
    };
    let return_frame_prefix = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        frames
            .borrow()
            .iter()
            .take(threshold)
            .cloned()
            .collect::<Vec<_>>()
            .into_boxed_slice()
    });
    let frame = NativeCpsI64HandlerFrame {
        handler,
        consumes_mask,
        guard_stack: current_native_i64_guard_stack().into_boxed_slice(),
        envs,
        prompt: prompt as u64,
        install_eval_id: install_eval_id as u64,
        escape_owner_function_id: escape_owner,
        threshold_owner_function_id,
        inherited: inherited != 0,
        escape_continuation: escape_continuation as usize,
        escape_env: escape_env.into_boxed_slice(),
        escape_env_targets: take_pending_native_i64_escape_env_targets().into_boxed_slice(),
        return_frame_threshold: threshold,
        return_frame_prefix,
        origin: NativeCpsI64HandlerFrameOrigin::RealInstall,
    };
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| {
        stack.borrow_mut().push(frame);
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] install_handler_full: handler={} prompt={} install_eval={} owner_fn={} threshold={} threshold_owner={} escape={:#x} envs={}",
            handler,
            prompt,
            install_eval_id,
            escape_owner_function_id,
            return_frame_threshold,
            threshold_owner_function_id,
            escape_continuation as usize,
            trace_envs.as_deref().unwrap_or("[]")
        );
    }
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_install_handler_full_i64_0(
    handler: i64,
    consumes_mask: i64,
    escape_continuation: i64,
    return_frame_threshold: i64,
    prompt: i64,
    install_eval_id: i64,
    escape_owner_function_id: i64,
    inherited: i64,
) -> i64 {
    install_native_i64_handler_full(
        handler,
        consumes_mask,
        escape_continuation,
        return_frame_threshold,
        prompt,
        install_eval_id,
        escape_owner_function_id,
        inherited,
        Vec::new(),
    );
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_install_handler_full_i64_1(
    handler: i64,
    consumes_mask: i64,
    escape_continuation: i64,
    return_frame_threshold: i64,
    prompt: i64,
    install_eval_id: i64,
    escape_owner_function_id: i64,
    inherited: i64,
    a: i64,
) -> i64 {
    install_native_i64_handler_full(
        handler,
        consumes_mask,
        escape_continuation,
        return_frame_threshold,
        prompt,
        install_eval_id,
        escape_owner_function_id,
        inherited,
        vec![a],
    );
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_install_handler_full_i64_2(
    handler: i64,
    consumes_mask: i64,
    escape_continuation: i64,
    return_frame_threshold: i64,
    prompt: i64,
    install_eval_id: i64,
    escape_owner_function_id: i64,
    inherited: i64,
    a: i64,
    b: i64,
) -> i64 {
    install_native_i64_handler_full(
        handler,
        consumes_mask,
        escape_continuation,
        return_frame_threshold,
        prompt,
        install_eval_id,
        escape_owner_function_id,
        inherited,
        vec![a, b],
    );
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_install_handler_full_i64_3(
    handler: i64,
    consumes_mask: i64,
    escape_continuation: i64,
    return_frame_threshold: i64,
    prompt: i64,
    install_eval_id: i64,
    escape_owner_function_id: i64,
    inherited: i64,
    a: i64,
    b: i64,
    c: i64,
) -> i64 {
    install_native_i64_handler_full(
        handler,
        consumes_mask,
        escape_continuation,
        return_frame_threshold,
        prompt,
        install_eval_id,
        escape_owner_function_id,
        inherited,
        vec![a, b, c],
    );
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_install_handler_full_i64_4(
    handler: i64,
    consumes_mask: i64,
    escape_continuation: i64,
    return_frame_threshold: i64,
    prompt: i64,
    install_eval_id: i64,
    escape_owner_function_id: i64,
    inherited: i64,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> i64 {
    install_native_i64_handler_full(
        handler,
        consumes_mask,
        escape_continuation,
        return_frame_threshold,
        prompt,
        install_eval_id,
        escape_owner_function_id,
        inherited,
        vec![a, b, c, d],
    );
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_abort_i64(value: i64) -> i64 {
    NATIVE_CPS_I64_ABORT.with(|slot| {
        *slot.borrow_mut() = NativeCpsI64Abort::Global(value);
    });
    value
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_abort_active_i64() -> i64 {
    NATIVE_CPS_I64_ABORT.with(|slot| {
        let value = slot.borrow().clone();
        let active = value.is_active();
        if jit_trace_enabled() && active {
            eprintln!(
                "[JIT-CPS] abort_active: value={}",
                describe_native_i64_value(value.value_or_zero())
            );
        }
        i64::from(active)
    })
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_abort_should_return_i64() -> i64 {
    i64::from(yulang_cps_abort_mode_i64() == 1)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_abort_mode_i64() -> i64 {
    NATIVE_CPS_I64_ABORT.with(|slot| {
        let abort = slot.borrow().clone();
        let frame_len = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
        let mode = abort.mode_at_frame_len(frame_len);
        if jit_trace_enabled() && mode != 0 {
            eprintln!(
                "[JIT-CPS] abort_mode: mode={} frame_len={} value={}",
                mode,
                frame_len,
                describe_native_i64_value(abort.value_or_zero())
            );
        }
        mode
    })
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_abort_value_i64() -> i64 {
    NATIVE_CPS_I64_ABORT.with(|slot| slot.borrow().value_or_zero())
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_consume_abort_i64() -> i64 {
    consume_native_i64_abort()
}

fn consume_native_i64_abort() -> i64 {
    let cleared_abort = NATIVE_CPS_I64_ABORT.with(|slot| {
        let mut slot = slot.borrow_mut();
        let cleared_abort = std::mem::take(&mut *slot);
        *slot = NativeCpsI64Abort::None;
        cleared_abort
    });
    match cleared_abort {
        NativeCpsI64Abort::None => 0,
        NativeCpsI64Abort::Global(value) => value,
        NativeCpsI64Abort::Scoped {
            value,
            return_frame_threshold,
            restore_frames,
            propagate_at_threshold: false,
        } => {
            restore_native_i64_return_frame_prefix(&restore_frames);
            let frame_len = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
            let offset = return_frame_threshold.saturating_sub(frame_len);
            if offset > 0 {
                NATIVE_CPS_I64_HANDLER_THRESHOLD_OFFSET.with(|slot| {
                    let mut slot = slot.borrow_mut();
                    *slot = (*slot).max(offset);
                });
            }
            value
        }
        NativeCpsI64Abort::Scoped { value, .. } => value,
        NativeCpsI64Abort::RoutedJump {
            value,
            continuation,
            env,
            handlers,
            guards,
            return_frames,
            eval_context,
            ..
        } => {
            let return_frames = return_frames.into_vec();
            NATIVE_CPS_I64_HANDLER_STACK.with(|stack| *stack.borrow_mut() = handlers);
            NATIVE_CPS_I64_GUARD_STACK.with(|stack| *stack.borrow_mut() = guards);
            NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow_mut().clear());
            NATIVE_CPS_I64_PENDING_ROUTED_RETURN_FRAMES.with(|pending| {
                *pending.borrow_mut() = Some(NativeCpsI64PendingRoutedReturnFrames {
                    skip_initial_frame_count: eval_context.initial_frame_count,
                    frames: return_frames.clone(),
                });
            });
            NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow_mut() = eval_context);
            let cont: NativeCpsI64Continuation = unsafe { std::mem::transmute(continuation) };
            let result = cont(env.as_ptr(), value);
            result
        }
    }
}

fn restore_pending_routed_return_frames_for_normal_return(initial: usize) {
    let pending = NATIVE_CPS_I64_PENDING_ROUTED_RETURN_FRAMES.with(|pending| {
        let mut pending = pending.borrow_mut();
        let Some(pending_frames) = pending.as_ref() else {
            return None;
        };
        if pending_frames.skip_initial_frame_count == initial {
            return None;
        }
        pending.take()
    });
    if let Some(pending) = pending {
        NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
            let mut frames = frames.borrow_mut();
            if frames.is_empty() {
                *frames = pending.frames;
            }
        });
    }
}

fn clear_native_i64_abort() {
    let cleared_abort = NATIVE_CPS_I64_ABORT.with(|slot| {
        let mut slot = slot.borrow_mut();
        let cleared_abort = std::mem::take(&mut *slot);
        *slot = NativeCpsI64Abort::None;
        cleared_abort
    });
    let restore_consumed_frames = matches!(
        cleared_abort,
        NativeCpsI64Abort::Scoped {
            propagate_at_threshold: false,
            ..
        }
    );
    if restore_consumed_frames {
        if let NativeCpsI64Abort::Scoped {
            return_frame_threshold,
            restore_frames,
            ..
        } = cleared_abort.clone()
        {
            restore_native_i64_return_frame_prefix(&restore_frames);
            let frame_len = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
            let offset = return_frame_threshold.saturating_sub(frame_len);
            if offset > 0 {
                NATIVE_CPS_I64_HANDLER_THRESHOLD_OFFSET.with(|slot| {
                    let mut slot = slot.borrow_mut();
                    *slot = (*slot).max(offset);
                });
            }
        }
    }
}

fn restore_native_i64_return_frame_prefix(prefix: &[NativeCpsI64ReturnFrame]) {
    if prefix.is_empty() {
        return;
    }
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        let mut frames = frames.borrow_mut();
        let current = frames
            .iter()
            .map(|frame| (frame.debug_id, frame.clone()))
            .collect::<HashMap<_, _>>();
        *frames = prefix
            .iter()
            .map(|frame| {
                current
                    .get(&frame.debug_id)
                    .cloned()
                    .unwrap_or_else(|| frame.clone())
            })
            .collect();
    });
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_clear_abort_i64() -> i64 {
    clear_native_i64_abort();
    0
}

// =====================================================================
// write27-a: ScopeReturn slot helpers.
// Mirrors `cps_eval`/`cps_repr` ScopeReturn { prompt, target, value }.
// Old `abort` helpers stay in place for backward-compat paths; new
// codegen (Perform/EffectfulCall etc.) should use these instead.
// =====================================================================

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_scope_return_i64(prompt: i64, target: i64, value: i64) -> i64 {
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| {
        *slot.borrow_mut() = NativeCpsI64ScopeReturn {
            active: true,
            prompt: prompt as u64,
            target,
            value,
        };
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] scope_return_set: prompt={} target={} value={}",
            prompt, target, value
        );
    }
    value
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_scope_return_active_i64() -> i64 {
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| i64::from(slot.borrow().active))
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_scope_return_prompt_i64() -> i64 {
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().prompt as i64)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_scope_return_target_i64() -> i64 {
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().target)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_scope_return_value_i64() -> i64 {
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().value)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_clear_scope_return_i64() -> i64 {
    NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| {
        *slot.borrow_mut() = NativeCpsI64ScopeReturn::default();
    });
    0
}

// =====================================================================
// write27-a: eval context helpers.
// Track current_eval_id and initial_frame_count for the JIT analogue
// of cps_eval's eval signatures. continue_return_frames-style logic
// restores eval_context from a popped return frame.
// =====================================================================

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_fresh_eval_id_i64() -> i64 {
    NATIVE_CPS_I64_NEXT_EVAL_ID.with(|next| {
        let id = *next.borrow();
        *next.borrow_mut() = id + 1;
        id as i64
    })
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_current_eval_id_i64() -> i64 {
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().current_eval_id as i64)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_current_initial_frame_count_i64() -> i64 {
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().initial_frame_count as i64)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_set_eval_context_i64(eval_id: i64, initial_frame_count: i64) -> i64 {
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| {
        *ctx.borrow_mut() = NativeCpsI64EvalContext {
            current_eval_id: eval_id as u64,
            initial_frame_count: initial_frame_count.max(0) as usize,
        };
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] set_eval_context: eval={} initial={}",
            eval_id, initial_frame_count
        );
    }
    0
}

// =====================================================================
// write27-a: return-frame stack helpers.
// Each EffectfulCall/Apply/Force pushes a frame; a continue_return_frames
// step pops the innermost frame and invokes its continuation. The actual
// "continue and resume" wiring is implemented by future write27 steps
// in concert with codegen; this commit only exposes the storage and
// raw push/pop primitives.
// =====================================================================

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_return_frame_len_i64() -> i64 {
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len() as i64)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_handler_return_frame_threshold_i64() -> i64 {
    let frame_len = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
    let offset = NATIVE_CPS_I64_HANDLER_THRESHOLD_OFFSET
        .with(|slot| std::mem::take(&mut *slot.borrow_mut()));
    (frame_len + offset) as i64
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_enter_handler_arm_i64() -> i64 {
    let saved =
        NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| std::mem::take(&mut *frames.borrow_mut()));
    let consumed_start = NATIVE_CPS_I64_CONSUMED_RETURN_FRAME_IDS.with(|ids| ids.borrow().len());
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] enter_handler_arm: saved_frames={}",
            format_return_frames(&saved)
        );
    }
    NATIVE_CPS_I64_HANDLER_ARM_RETURN_FRAME_SNAPSHOTS.with(|snapshots| {
        snapshots
            .borrow_mut()
            .push(NativeCpsI64HandlerArmReturnFrameSnapshot {
                frames: saved,
                consumed_start,
            });
    });
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_exit_handler_arm_i64() -> i64 {
    let snapshot = NATIVE_CPS_I64_HANDLER_ARM_RETURN_FRAME_SNAPSHOTS
        .with(|snapshots| snapshots.borrow_mut().pop().unwrap_or_default());
    let consumed_since = NATIVE_CPS_I64_CONSUMED_RETURN_FRAME_IDS.with(|ids| {
        ids.borrow()
            .iter()
            .skip(snapshot.consumed_start)
            .copied()
            .collect::<HashSet<_>>()
    });
    let restored: Vec<NativeCpsI64ReturnFrame> = snapshot
        .frames
        .into_iter()
        .filter(|frame| !consumed_since.contains(&frame.debug_id))
        .collect();
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] exit_handler_arm: restored_frames={}",
            format_return_frames(&restored)
        );
    }
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| *frames.borrow_mut() = restored);
    0
}

fn push_native_i64_return_frame_with_env(
    prompt_exit: Option<NativeCpsI64PromptExitFrame>,
    continuation: i64,
    continuation_id: i64,
    env: Vec<i64>,
    owner_initial_frame_count: i64,
    owner_eval_id: i64,
    owner_function_id: i64,
    immediately_forces_param: i64,
) {
    let handlers = NATIVE_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow().clone());
    let guards = NATIVE_CPS_I64_GUARD_STACK.with(|stack| stack.borrow().clone());
    let env_len = env.len();
    let len_before = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
    let debug_id = next_native_i64_return_frame_debug_id();
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        frames.borrow_mut().push(NativeCpsI64ReturnFrame {
            prompt_exit,
            debug_id,
            continuation: continuation as usize,
            continuation_id: continuation_id.max(0) as u32,
            env: env.into_boxed_slice(),
            handlers,
            guards,
            owner_initial_frame_count: owner_initial_frame_count.max(0) as usize,
            owner_eval_id: owner_eval_id as u64,
            owner_function_id: owner_function_id.max(0) as u64,
            immediately_forces_param: immediately_forces_param != 0,
        });
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] push_return_frame: id={} k={} len_before={} len_after={} cont={:#x} env_len={} owner_initial={} owner_eval={} owner_fn={} immediate_force={}",
            debug_id,
            continuation_id,
            len_before,
            len_before + 1,
            continuation as usize,
            env_len,
            owner_initial_frame_count,
            owner_eval_id,
            owner_function_id,
            immediately_forces_param != 0,
        );
    }
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_push_return_frame_i64_0(
    continuation: i64,
    continuation_id: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
) -> i64 {
    push_native_i64_return_frame_with_env(
        None,
        continuation,
        continuation_id,
        Vec::new(),
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces,
    );
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_push_return_frame_i64_1(
    continuation: i64,
    continuation_id: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    a: i64,
) -> i64 {
    push_native_i64_return_frame_with_env(
        None,
        continuation,
        continuation_id,
        vec![a],
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces,
    );
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_push_return_frame_i64_2(
    continuation: i64,
    continuation_id: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    a: i64,
    b: i64,
) -> i64 {
    push_native_i64_return_frame_with_env(
        None,
        continuation,
        continuation_id,
        vec![a, b],
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces,
    );
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_push_return_frame_i64_3(
    continuation: i64,
    continuation_id: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    a: i64,
    b: i64,
    c: i64,
) -> i64 {
    push_native_i64_return_frame_with_env(
        None,
        continuation,
        continuation_id,
        vec![a, b, c],
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces,
    );
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_push_return_frame_i64_4(
    continuation: i64,
    continuation_id: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> i64 {
    push_native_i64_return_frame_with_env(
        None,
        continuation,
        continuation_id,
        vec![a, b, c, d],
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces,
    );
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_push_return_frame_i64_many(
    continuation: i64,
    continuation_id: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    ptr: *const i64,
    len: i64,
) -> i64 {
    push_native_i64_return_frame_with_env(
        None,
        continuation,
        continuation_id,
        unsafe { native_i64_slice(ptr, len) },
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces,
    );
    0
}

fn push_native_i64_prompt_exit_frame_with_env(
    prompt: i64,
    continuation: i64,
    continuation_id: i64,
    env: Vec<i64>,
    owner_initial_frame_count: i64,
    owner_eval_id: i64,
    owner_function_id: i64,
    immediately_forces_param: i64,
) {
    push_native_i64_return_frame_with_env(
        Some(NativeCpsI64PromptExitFrame {
            prompt: prompt as u64,
        }),
        continuation,
        continuation_id,
        env,
        owner_initial_frame_count,
        owner_eval_id,
        owner_function_id,
        immediately_forces_param,
    );
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_push_prompt_exit_frame_i64_0(
    prompt: i64,
    continuation: i64,
    continuation_id: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
) -> i64 {
    push_native_i64_prompt_exit_frame_with_env(
        prompt,
        continuation,
        continuation_id,
        Vec::new(),
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces,
    );
    0
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_push_prompt_exit_frame_i64_many(
    prompt: i64,
    continuation: i64,
    continuation_id: i64,
    owner_initial: i64,
    owner_eval: i64,
    owner_function: i64,
    immediately_forces: i64,
    ptr: *const i64,
    len: i64,
) -> i64 {
    push_native_i64_prompt_exit_frame_with_env(
        prompt,
        continuation,
        continuation_id,
        unsafe { native_i64_slice(ptr, len) },
        owner_initial,
        owner_eval,
        owner_function,
        immediately_forces,
    );
    0
}

/// write27-b: pop the innermost return frame, restore its handler /
/// guard / eval context snapshots, and invoke the saved JIT
/// continuation with `value`. Returns the continuation's result.
///
/// Returning a Rust-side helper instead of just `pop` plus a Cranelift
/// trampoline keeps the env / state restore / continuation call atomic
/// — write27-b notes call this out as the main safety win.
///
/// Mirrors cps_eval / cps_repr's `continue_return_frames` single step.
#[unsafe(no_mangle)]
extern "C" fn yulang_cps_continue_return_frame_i64(value: i64) -> i64 {
    // Pop the frame first, dropping the borrow before we invoke the
    // continuation (which may push new frames).
    let frame = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow_mut().pop());
    let Some(frame) = frame else {
        // No frame to consume — caller should have checked
        // `return_frame_len_i64()`; treat this as a no-op for safety.
        return value;
    };
    NATIVE_CPS_I64_CONSUMED_RETURN_FRAME_IDS.with(|ids| {
        let mut ids = ids.borrow_mut();
        if !ids.contains(&frame.debug_id) {
            ids.push(frame.debug_id);
        }
    });
    let mut restored_handlers = frame.handlers;
    append_resume_with_handler_siblings(&mut restored_handlers);
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] continue_return_frame: id={} owner_eval={} owner_initial={} restored_handlers_len={} restored_guards_len={} value={}",
            frame.debug_id,
            frame.owner_eval_id,
            frame.owner_initial_frame_count,
            restored_handlers.len(),
            frame.guards.len(),
            describe_native_i64_value(value),
        );
    }
    NATIVE_CPS_I64_HANDLER_STACK.with(|stack| *stack.borrow_mut() = restored_handlers);
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| *stack.borrow_mut() = frame.guards);
    NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| {
        *ctx.borrow_mut() = NativeCpsI64EvalContext {
            current_eval_id: frame.owner_eval_id,
            initial_frame_count: frame.owner_initial_frame_count,
        };
    });
    // Safety: `frame.continuation` was obtained at `push_return_frame`
    // time via `func_addr` on a JIT-compiled continuation function and
    // therefore stays valid for the lifetime of the JIT module. The
    // env slice's pointer stays valid for the duration of the call
    // because the frame is owned by this stack-popped `Box<[i64]>`.
    let cont: NativeCpsI64Continuation = unsafe { std::mem::transmute(frame.continuation) };
    let env_ptr = frame.env.as_ptr();
    cont(env_ptr, value)
}

/// write27-b: peek at the innermost return frame's
/// `immediately_forces_param` flag without popping it. Used by the
/// JIT `Return` path to decide whether to fire pre-force v2.
#[unsafe(no_mangle)]
extern "C" fn yulang_cps_top_return_frame_pre_force_i64() -> i64 {
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        frames
            .borrow()
            .last()
            .map(|frame| i64::from(frame.immediately_forces_param))
            .unwrap_or(0)
    })
}

/// write27-b: pre-force v2 for the JIT. Mirrors cps_eval/cps_repr's
/// Return-terminator pre-force: when the Returned value is a Thunk and
/// the innermost own-frame's continuation immediately ForceThunks its
/// param, run that continuation in the top frame's owner context with
/// the frame retained in `return_frames` and the eval-context's
/// `initial_frame_count` set to the full frame length (so any deeper
/// Return that doesn't push new frames just bubbles back).
///
/// Caller has already verified:
///   - `value` is a thunk pointer (via `yulang_cps_is_thunk_i64`),
///   - `return_frame_len_i64() > current_initial_frame_count_i64()`,
///   - `yulang_cps_top_return_frame_pre_force_i64() != 0`.
#[unsafe(no_mangle)]
extern "C" fn yulang_cps_pre_force_top_frame_i64(value: i64) -> i64 {
    let saved_eval_ctx = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow());
    NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        let frames = frames.borrow();
        let top = frames.last().expect("pre-force called with no frame");
        // Restore the top frame's owner context. The frame is RETAINED
        // (we don't pop it) so the body's effects can capture it.
        NATIVE_CPS_I64_HANDLER_STACK.with(|stack| *stack.borrow_mut() = top.handlers.clone());
        NATIVE_CPS_I64_GUARD_STACK.with(|stack| *stack.borrow_mut() = top.guards.clone());
        NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| {
            *ctx.borrow_mut() = NativeCpsI64EvalContext {
                current_eval_id: top.owner_eval_id,
                // Keep the caller eval's barrier. The thunk body runs before
                // the top frame is consumed, so effects can capture the frame
                // and a plain return can still flow through the retained
                // caller chain.
                initial_frame_count: saved_eval_ctx.initial_frame_count,
            };
        });
    });
    let forced = yulang_cps_force_thunk_i64(value as usize);
    match yulang_cps_abort_mode_i64() {
        1 => {
            return yulang_cps_abort_value_i64();
        }
        2 => {
            if native_i64_abort_is_routed_jump() {
                return yulang_cps_abort_value_i64();
            }
            return yulang_cps_consume_abort_i64();
        }
        _ => {}
    }
    if yulang_cps_abort_active_i64() != 0 {
        return yulang_cps_abort_value_i64();
    }
    if yulang_cps_scope_return_active_i64() != 0 {
        return yulang_cps_route_scope_return_i64(forced);
    }
    yulang_cps_continue_return_frame_i64(forced)
}

/// write27-b: JIT-side analogue of cps_eval's Return terminator. Use
/// this in place of `ireturn value` so that:
/// - if the eval has no own return frames, return value directly,
/// - if pre-force v2 fires, run the top frame's continuation in owner
///   context with the frame retained,
/// - otherwise, consume the innermost own frame and run its
///   continuation with `value`.
///
/// Callers don't have to know about Thunk classification: this helper
/// asks `yulang_cps_is_thunk_i64` (existing) when deciding pre-force.
#[unsafe(no_mangle)]
extern "C" fn yulang_cps_return_i64(value: i64) -> i64 {
    let mut value = value;
    match yulang_cps_abort_mode_i64() {
        1 => {
            return yulang_cps_abort_value_i64();
        }
        2 => {
            if native_i64_abort_is_routed_jump() {
                return yulang_cps_abort_value_i64();
            }
            value = yulang_cps_consume_abort_i64();
        }
        _ => {}
    }
    let frame_len = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
    let initial = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| ctx.borrow().initial_frame_count);
    if frame_len == 0 {
        restore_pending_routed_return_frames_for_normal_return(initial);
    }
    let frame_len = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().len());
    if frame_len <= initial {
        if jit_trace_enabled() {
            eprintln!(
                "[JIT-CPS] return_i64: value={} frame_len={} initial={} action=noop",
                describe_native_i64_value(value),
                frame_len,
                initial
            );
        }
        return value;
    }
    // Pre-force v2 check.
    let is_thunk = NATIVE_CPS_I64_THUNKS.with(|thunks| thunks.borrow().contains(&(value as usize)));
    let top_forces = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
        frames
            .borrow()
            .last()
            .map(|frame| frame.immediately_forces_param)
            .unwrap_or(false)
    });
    if is_thunk && top_forces {
        if jit_trace_enabled() {
            eprintln!(
                "[JIT-CPS] return_i64: value={} frame_len={} initial={} action=pre_force",
                describe_native_i64_value(value),
                frame_len,
                initial
            );
        }
        return yulang_cps_pre_force_top_frame_i64(value);
    }
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] return_i64: value={} frame_len={} initial={} action=continue",
            describe_native_i64_value(value),
            frame_len,
            initial
        );
    }
    yulang_cps_continue_return_frame_i64(value)
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_selected_handler_env_or_i64(entry: i64, fallback: i64) -> i64 {
    let selected_handler = NATIVE_CPS_I64_SELECTED_HANDLER_ID.with(|handler| *handler.borrow());
    // ResumeWithHandler frames publish their handler env before the resumed
    // continuation runs and stay visible while it unwinds. Search newest first,
    // but only within the handler selected by `select_handler`: continuation
    // entry ids are local and can collide across independent mutable refs.
    if let Some(value) = NATIVE_CPS_I64_RESUME_WITH_HANDLER_SIBLINGS.with(|siblings| {
        siblings
            .borrow()
            .iter()
            .rev()
            .filter(|handler| handler.handler == selected_handler)
            .flat_map(|handler| handler.envs.iter().rev())
            .find(|env| env.entry == entry)
            .map(|env| env.env)
    }) {
        NATIVE_CPS_I64_SELECTED_HANDLER_USED_RWH_ENV.with(|used| *used.borrow_mut() = true);
        if jit_trace_enabled() {
            eprintln!(
                "[JIT-CPS] selected_handler_env: entry={} fallback={} value={} source=rwh_sibling",
                entry,
                describe_native_i64_value(fallback),
                describe_native_i64_value(value)
            );
        }
        return value;
    }
    let value = NATIVE_CPS_I64_SELECTED_HANDLER_ENVS.with(|envs| {
        envs.borrow()
            .iter()
            .rev()
            .find(|env| env.entry == entry)
            .map(|env| env.env)
            .unwrap_or(fallback)
    });
    if jit_trace_enabled() {
        eprintln!(
            "[JIT-CPS] selected_handler_env: entry={} fallback={} value={}",
            entry,
            describe_native_i64_value(fallback),
            describe_native_i64_value(value)
        );
    }
    value
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_thunk_i64_0(code: usize) -> usize {
    make_native_i64_thunk(code, Vec::new())
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_thunk_i64_1(code: usize, a: i64) -> usize {
    make_native_i64_thunk(code, vec![a])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_thunk_i64_2(code: usize, a: i64, b: i64) -> usize {
    make_native_i64_thunk(code, vec![a, b])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_thunk_i64_3(code: usize, a: i64, b: i64, c: i64) -> usize {
    make_native_i64_thunk(code, vec![a, b, c])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_thunk_i64_4(code: usize, a: i64, b: i64, c: i64, d: i64) -> usize {
    make_native_i64_thunk(code, vec![a, b, c, d])
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_make_thunk_i64_many(code: usize, ptr: *const i64, len: i64) -> usize {
    make_native_i64_thunk(code, unsafe { native_i64_slice(ptr, len) })
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_is_thunk_i64(value: i64) -> i64 {
    usize::try_from(value)
        .ok()
        .is_some_and(|value| NATIVE_CPS_I64_THUNKS.with(|thunks| thunks.borrow().contains(&value)))
        .into()
}

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_force_thunk_i64(value: usize) -> i64 {
    let mut value = value;
    loop {
        let is_thunk = NATIVE_CPS_I64_THUNKS.with(|thunks| thunks.borrow().contains(&value));
        if !is_thunk {
            if jit_trace_enabled() {
                eprintln!(
                    "[JIT-CPS] force_thunk.out: value={}",
                    describe_native_i64_value(value as i64)
                );
            }
            return value as i64;
        }
        let thunk = unsafe { &*(value as *const NativeCpsI64Thunk) };
        if jit_trace_enabled() {
            let frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|f| f.borrow().clone());
            let eval = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow());
            eprintln!(
                "[JIT-CPS] force_thunk: thunk={:#x} eval={} initial={} frames={}",
                value,
                eval.current_eval_id,
                eval.initial_frame_count,
                format_return_frames(&frames),
            );
        }
        // write27-e: Layer 2 (cps_repr.rs:1638-1681) uses
        // `if !active_handlers.is_empty() { active_handlers } else
        //  { thunk.handlers }` for the inner eval — i.e. the caller's
        // active handlers shadow the captured thunk handlers when the
        // caller has any. Previously the JIT appended thunk.handlers
        // onto the current stack (via
        // `native_i64_handler_stack_for_force`), which compounded the
        // synthetic PendingEnv frames every time a thunk got forced
        // inside another thunk. Use the caller stack as-is when it
        // has at least one frame; otherwise fall back to the thunk's
        // captured stack.
        let current_handlers_empty = NATIVE_CPS_I64_HANDLER_STACK.with(|s| s.borrow().is_empty());
        let current_guards_empty = NATIVE_CPS_I64_GUARD_STACK.with(|s| s.borrow().is_empty());
        let handlers = if current_handlers_empty {
            thunk.handlers.to_vec()
        } else {
            NATIVE_CPS_I64_HANDLER_STACK.with(|s| s.borrow().clone())
        };
        let guards = if current_guards_empty {
            thunk.guard_stack.to_vec()
        } else {
            NATIVE_CPS_I64_GUARD_STACK.with(|s| s.borrow().clone())
        };
        let mut active_blocked = NATIVE_CPS_I64_ACTIVE_BLOCKED.with(|stack| stack.borrow().clone());
        active_blocked.extend(thunk.active_blocked.iter().copied());
        let saved_frames = NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow().clone());
        let consumed_start =
            NATIVE_CPS_I64_CONSUMED_RETURN_FRAME_IDS.with(|ids| ids.borrow().len());
        let saved_eval_ctx = NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow());
        let result = with_native_i64_cps_state_and_active(handlers, guards, active_blocked, || {
            (thunk.code)(thunk.env.as_ptr())
        });
        if native_i64_abort_should_consume_after_thunk_force() {
            return yulang_cps_consume_abort_i64();
        }
        let routed_frames = NATIVE_CPS_I64_RETURN_FRAMES_ROUTED
            .with(|routed| std::mem::take(&mut *routed.borrow_mut()));
        let active_abort = NATIVE_CPS_I64_ABORT.with(|slot| slot.borrow().clone());
        let active_scope_return = NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| slot.borrow().active);
        let propagating_non_local = active_scope_return || active_abort.is_active();
        if propagating_non_local && (!routed_frames || active_scope_return) {
            let consumed_since = NATIVE_CPS_I64_CONSUMED_RETURN_FRAME_IDS.with(|ids| {
                ids.borrow()
                    .iter()
                    .skip(consumed_start)
                    .copied()
                    .collect::<HashSet<_>>()
            });
            let restore_consumed = matches!(
                active_abort,
                NativeCpsI64Abort::Scoped {
                    propagate_at_threshold: false,
                    ..
                }
            ) || active_scope_return;
            let restored = if restore_consumed {
                // An unresolved ScopeReturn still belongs to the caller's
                // boundary. Keep the full snapshot so resumption replay does
                // not silently lose post-effect frames while the jump climbs.
                saved_frames.clone()
            } else {
                saved_frames
                    .clone()
                    .into_iter()
                    .filter(|frame| !consumed_since.contains(&frame.debug_id))
                    .collect()
            };
            NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
                *frames.borrow_mut() = restored;
            });
        } else if !routed_frames {
            NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
                let mut frames = frames.borrow_mut();
                // Layer 2 evaluates the thunk with a cloned frame stack.
                // Mirror that for ordinary value flow: keep unconsumed
                // caller frames, drop frames created inside the thunk, and
                // keep any semantic updates made to surviving frame
                // snapshots. If ScopeReturn routing already rebuilt the
                // frame stack, the routed stack is the semantic result and
                // must keep propagating outward.
                let keep_len = frames
                    .iter()
                    .zip(saved_frames.iter())
                    .take_while(|(current, saved)| current.debug_id == saved.debug_id)
                    .count();
                frames.truncate(keep_len);
            });
        }
        NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow_mut() = saved_eval_ctx);
        NATIVE_CPS_I64_SCOPE_RETURN.with(|slot| {
            let mut slot = slot.borrow_mut();
            if slot.active && slot.value == value as i64 {
                slot.value = result;
            }
        });
        // Non-local flow payloads are not ordinary nested thunk results. Let
        // the surrounding routing boundary consume or propagate them.
        if yulang_cps_abort_active_i64() != 0 || yulang_cps_scope_return_active_i64() != 0 {
            return result;
        }
        value = result as usize;
    }
}

#[unsafe(no_mangle)]
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

#[unsafe(no_mangle)]
extern "C" fn yulang_cps_peek_guard_i64() -> i64 {
    NATIVE_CPS_I64_GUARD_STACK.with(|stack| stack.borrow().last().copied().unwrap_or(0))
}

#[unsafe(no_mangle)]
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
    fn jit_lowers_pure_effectful_continuation_successor_as_block() {
        let abi = effectful_function_with_pure_continue_abi();
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![42]);
        let entry_ir = jit
            .cranelift_ir()
            .iter()
            .find(|ir| ir.contains(";; cps-repr continuation root::CpsContinuationId(0)"))
            .expect("entry continuation ir");
        assert!(!entry_ir.contains("root$k1"));
    }

    #[test]
    fn jit_lowers_pure_effectful_branch_successors_as_blocks() {
        let abi = effectful_function_with_pure_branch_abi();
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![42]);
        let entry_ir = jit
            .cranelift_ir()
            .iter()
            .find(|ir| ir.contains(";; cps-repr continuation root::CpsContinuationId(0)"))
            .expect("entry continuation ir");
        assert!(!entry_ir.contains("root$k1"));
        assert!(!entry_ir.contains("root$k2"));
    }

    #[test]
    fn jit_calls_pure_callee_from_effectful_island_without_eval_context() {
        let abi = effectful_function_with_pure_direct_call_abi();
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![42]);
        let entry_ir = jit
            .cranelift_ir()
            .iter()
            .find(|ir| ir.contains(";; cps-repr continuation root::CpsContinuationId(0)"))
            .expect("entry continuation ir");
        assert!(entry_ir.contains("call fn"));
        assert!(!entry_ir.contains("yulang_cps_fresh_eval_id_i64"));
        assert!(!entry_ir.contains("yulang_cps_set_eval_context_i64"));
        assert!(!entry_ir.contains("yulang_cps_scope_return_active_i64"));
    }

    #[test]
    fn jit_rewrites_effectful_call_to_pure_callee_before_codegen() {
        let abi = effectful_call_to_pure_callee_abi();
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![42]);
        assert_eq!(jit.optimization_profile().rewritten_pure_effectful_calls, 1);
        let entry_ir = jit
            .cranelift_ir()
            .iter()
            .find(|ir| ir.contains(";; cps-repr continuation root::CpsContinuationId(0)"))
            .expect("entry continuation ir");
        assert!(!entry_ir.contains("yulang_cps_return_frame_len_i64"));
        assert!(!entry_ir.contains("yulang_cps_fresh_eval_id_i64"));
        assert!(!entry_ir.contains("yulang_cps_set_eval_context_i64"));
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
    fn jit_uses_active_thunk_boundary_when_selecting_handler() {
        let abi = active_thunk_boundary_abi(typed_ir::Type::Never, ThunkBoundaryStorage::Direct);
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![20]);
    }

    #[test]
    fn jit_uses_active_thunk_boundary_after_list_index() {
        let abi = active_thunk_boundary_abi(typed_ir::Type::Never, ThunkBoundaryStorage::ListIndex);
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![20]);
    }

    #[test]
    fn jit_uses_active_thunk_boundary_after_record_select() {
        let abi =
            active_thunk_boundary_abi(typed_ir::Type::Never, ThunkBoundaryStorage::RecordSelect);
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![20]);
    }

    #[test]
    fn jit_uses_active_thunk_boundary_after_variant_payload() {
        let abi =
            active_thunk_boundary_abi(typed_ir::Type::Never, ThunkBoundaryStorage::VariantPayload);
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![20]);
    }

    #[test]
    fn jit_keeps_allowed_thunk_boundary_visible_to_inner_handler() {
        let choose = typed_ir::Path::from_name(typed_ir::Name("choose".to_string()));
        let abi = active_thunk_boundary_abi(
            typed_ir::Type::Named {
                path: choose,
                args: Vec::new(),
            },
            ThunkBoundaryStorage::Direct,
        );
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![10]);
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
        let effect = typed_ir::Path::from_name(typed_ir::Name("choose".to_string()));
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
            CpsReprCraneliftError::UnsupportedTerminator {
                kind: "perform without handler entry",
                ..
            }
        ));
    }

    #[test]
    fn jit_runs_unhandled_host_out_write_and_resumes() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
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
                                literal: CpsLiteral::Int("42".to_string()),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(1),
                                op: typed_ir::PrimitiveOp::IntToString,
                                args: vec![CpsValueId(0)],
                            },
                        ],
                        terminator: CpsTerminator::Perform {
                            effect: out_effect_path("out", "write"),
                            payload: CpsValueId(1),
                            resume: CpsContinuationId(1),
                            handler: crate::cps_ir::CpsHandlerId(0),
                            blocked: None,
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(2)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(3),
                            literal: CpsLiteral::Int("7".to_string()),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                ],
            }],
        }));
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![7]);
    }

    #[test]
    fn jit_runs_runtime_module_through_cps_pipeline() {
        let expr = apply(
            apply(
                primitive(typed_ir::PrimitiveOp::IntAdd),
                unknown_lit(typed_ir::Lit::Int("20".to_string())),
            ),
            unknown_lit(typed_ir::Lit::Int("22".to_string())),
        );
        let mut jit = compile_runtime_module_to_cps_repr_jit(&module_with_root(expr))
            .expect("compiled runtime module through CPS repr");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![42]);
    }

    #[test]
    fn jit_runs_int_to_string_runtime_value_root() {
        let expr = apply(
            primitive(typed_ir::PrimitiveOp::IntToString),
            unknown_lit(typed_ir::Lit::Int("42".to_string())),
        );
        let mut jit = compile_runtime_module_to_cps_repr_jit(&module_with_root(expr))
            .expect("compiled runtime module through CPS repr");
        let roots = jit.run_roots_i64().expect("ran");

        assert_eq!(roots.len(), 1);
        assert_eq!(describe_native_i64_value(roots[0]), "42");
    }

    #[test]
    fn jit_runs_string_literal_runtime_value_root() {
        let mut jit = compile_runtime_module_to_cps_repr_jit(&module_with_root(unknown_lit(
            typed_ir::Lit::String("aあ🙂z".to_string()),
        )))
        .expect("compiled runtime module through CPS repr");
        let roots = jit.run_roots_i64().expect("ran");

        assert_eq!(roots.len(), 1);
        assert_eq!(describe_native_i64_value(roots[0]), "aあ🙂z");
    }

    #[test]
    fn jit_keeps_native_float_through_plain_force_thunk() {
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
                    stmts: vec![
                        CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Float("1.5".to_string()),
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(1),
                            thunk: CpsValueId(0),
                        },
                        CpsStmt::Literal {
                            dest: CpsValueId(2),
                            literal: CpsLiteral::Float("2.0".to_string()),
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(3),
                            thunk: CpsValueId(2),
                        },
                        CpsStmt::Primitive {
                            dest: CpsValueId(4),
                            op: typed_ir::PrimitiveOp::FloatAdd,
                            args: vec![CpsValueId(1), CpsValueId(3)],
                        },
                        CpsStmt::ForceThunk {
                            dest: CpsValueId(5),
                            thunk: CpsValueId(4),
                        },
                        CpsStmt::Primitive {
                            dest: CpsValueId(6),
                            op: typed_ir::PrimitiveOp::FloatToString,
                            args: vec![CpsValueId(5)],
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(6)),
                }],
            }],
        }));
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");
        let roots = jit.run_roots_i64().expect("ran");

        assert_eq!(roots.len(), 1);
        assert_eq!(describe_native_i64_value(roots[0]), "3.5");
    }

    #[test]
    fn jit_forces_thunk_with_many_environment_slots() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
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
                                literal: CpsLiteral::Int("1".to_string()),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(1),
                                literal: CpsLiteral::Int("2".to_string()),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(2),
                                literal: CpsLiteral::Int("3".to_string()),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(3),
                                literal: CpsLiteral::Int("4".to_string()),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(4),
                                literal: CpsLiteral::Int("5".to_string()),
                            },
                            CpsStmt::MakeThunk {
                                dest: CpsValueId(5),
                                entry: CpsContinuationId(1),
                            },
                            CpsStmt::ForceThunk {
                                dest: CpsValueId(6),
                                thunk: CpsValueId(5),
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(6)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: Vec::new(),
                        captures: vec![
                            CpsValueId(0),
                            CpsValueId(1),
                            CpsValueId(2),
                            CpsValueId(3),
                            CpsValueId(4),
                        ],
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Primitive {
                                dest: CpsValueId(7),
                                op: typed_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(0), CpsValueId(1)],
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(8),
                                op: typed_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(7), CpsValueId(2)],
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(9),
                                op: typed_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(8), CpsValueId(3)],
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(10),
                                op: typed_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(9), CpsValueId(4)],
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(10)),
                    },
                ],
            }],
        }));
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![15]);
    }

    #[test]
    fn jit_runs_record_construct_and_select() {
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
                    stmts: vec![
                        CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("10".to_string()),
                        },
                        CpsStmt::Literal {
                            dest: CpsValueId(1),
                            literal: CpsLiteral::Int("42".to_string()),
                        },
                        CpsStmt::Record {
                            dest: CpsValueId(2),
                            base: None,
                            fields: vec![
                                CpsRecordField {
                                    name: typed_ir::Name("a".to_string()),
                                    value: CpsValueId(0),
                                },
                                CpsRecordField {
                                    name: typed_ir::Name("answer".to_string()),
                                    value: CpsValueId(1),
                                },
                            ],
                        },
                        CpsStmt::Select {
                            dest: CpsValueId(3),
                            base: CpsValueId(2),
                            field: typed_ir::Name("answer".to_string()),
                        },
                    ],
                    terminator: CpsTerminator::Return(CpsValueId(3)),
                }],
            }],
        }));
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![42]);
    }

    #[test]
    fn jit_forces_thunk_selected_from_record() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
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
                            CpsStmt::MakeThunk {
                                dest: CpsValueId(0),
                                entry: CpsContinuationId(1),
                            },
                            CpsStmt::Record {
                                dest: CpsValueId(1),
                                base: None,
                                fields: vec![crate::cps_ir::CpsRecordField {
                                    name: typed_ir::Name("run".to_string()),
                                    value: CpsValueId(0),
                                }],
                            },
                            CpsStmt::Select {
                                dest: CpsValueId(2),
                                base: CpsValueId(1),
                                field: typed_ir::Name("run".to_string()),
                            },
                            CpsStmt::ForceThunk {
                                dest: CpsValueId(3),
                                thunk: CpsValueId(2),
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(4),
                            literal: CpsLiteral::Int("42".to_string()),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(4)),
                    },
                ],
            }],
        }));
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![42]);
    }

    #[test]
    fn jit_forces_thunk_indexed_from_list_more_than_once() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
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
                            CpsStmt::MakeThunk {
                                dest: CpsValueId(0),
                                entry: CpsContinuationId(1),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(1),
                                op: typed_ir::PrimitiveOp::ListSingleton,
                                args: vec![CpsValueId(0)],
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(2),
                                literal: CpsLiteral::Int("0".to_string()),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(3),
                                op: typed_ir::PrimitiveOp::ListIndex,
                                args: vec![CpsValueId(1), CpsValueId(2)],
                            },
                            CpsStmt::ForceThunk {
                                dest: CpsValueId(4),
                                thunk: CpsValueId(3),
                            },
                            CpsStmt::ForceThunk {
                                dest: CpsValueId(5),
                                thunk: CpsValueId(3),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(6),
                                op: typed_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(4), CpsValueId(5)],
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(6)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(7),
                            literal: CpsLiteral::Int("21".to_string()),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(7)),
                    },
                ],
            }],
        }));
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![42]);
    }

    #[test]
    fn jit_forces_string_thunk_indexed_from_list() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
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
                            CpsStmt::MakeThunk {
                                dest: CpsValueId(0),
                                entry: CpsContinuationId(1),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(1),
                                op: typed_ir::PrimitiveOp::ListSingleton,
                                args: vec![CpsValueId(0)],
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(2),
                                literal: CpsLiteral::Int("0".to_string()),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(3),
                                op: typed_ir::PrimitiveOp::ListIndex,
                                args: vec![CpsValueId(1), CpsValueId(2)],
                            },
                            CpsStmt::ForceThunk {
                                dest: CpsValueId(4),
                                thunk: CpsValueId(3),
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(4)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(5),
                            literal: CpsLiteral::String("thunked".to_string()),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(5)),
                    },
                ],
            }],
        }));
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");
        let roots = jit.run_roots_i64().expect("ran");

        assert_eq!(roots.len(), 1);
        assert_eq!(describe_native_i64_value(roots[0]), "thunked");
    }

    #[test]
    fn jit_calls_closure_indexed_from_list() {
        let abi = lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
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
                            CpsStmt::MakeClosure {
                                dest: CpsValueId(0),
                                entry: CpsContinuationId(1),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(1),
                                op: typed_ir::PrimitiveOp::ListSingleton,
                                args: vec![CpsValueId(0)],
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(2),
                                literal: CpsLiteral::Int("0".to_string()),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(3),
                                op: typed_ir::PrimitiveOp::ListIndex,
                                args: vec![CpsValueId(1), CpsValueId(2)],
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(4),
                                literal: CpsLiteral::Int("41".to_string()),
                            },
                            CpsStmt::ApplyClosure {
                                dest: CpsValueId(5),
                                closure: CpsValueId(3),
                                arg: CpsValueId(4),
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(5)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(6)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(7),
                                literal: CpsLiteral::Int("1".to_string()),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(8),
                                op: typed_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(6), CpsValueId(7)],
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(8)),
                    },
                ],
            }],
        }));
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_i64().expect("ran"), vec![42]);
    }

    #[test]
    fn jit_displays_nested_heap_values_as_yulang_values() {
        let expr = tuple(vec![
            unknown_lit(typed_ir::Lit::Int("1".to_string())),
            list_expr(vec![2, 3]),
            record(vec![(
                "answer",
                unknown_lit(typed_ir::Lit::Int("42".to_string())),
            )]),
        ]);
        let mut jit = compile_runtime_module_to_cps_repr_jit(&module_with_root(expr))
            .expect("compiled runtime module");
        let roots = jit.run_roots_i64().expect("ran");

        assert_eq!(roots.len(), 1);
        assert_eq!(
            describe_native_i64_value(roots[0]),
            "(1, [2, 3], { answer: 42 })"
        );
    }

    #[test]
    fn jit_forces_runtime_thunk_indexed_from_list() {
        let thunk_list = primitive_call(
            typed_ir::PrimitiveOp::ListSingleton,
            vec![thunk(unknown_lit(typed_ir::Lit::String(
                "runtime-thunk".to_string(),
            )))],
        );
        let indexed = primitive_call(
            typed_ir::PrimitiveOp::ListIndex,
            vec![thunk_list, unknown_lit(typed_ir::Lit::Int("0".to_string()))],
        );
        let mut jit = compile_runtime_module_to_cps_repr_jit(&module_with_root(bind_here(indexed)))
            .expect("compiled runtime module");
        let roots = jit.run_roots_i64().expect("ran");

        assert_eq!(roots.len(), 1);
        assert_eq!(describe_native_i64_value(roots[0]), "runtime-thunk");
    }

    #[test]
    fn jit_runs_string_primitives_runtime_value_roots() {
        let cases = vec![
            (
                apply(
                    apply(
                        primitive(typed_ir::PrimitiveOp::StringConcat),
                        unknown_lit(typed_ir::Lit::String("yu".to_string())),
                    ),
                    unknown_lit(typed_ir::Lit::String("lang".to_string())),
                ),
                "yulang",
            ),
            (
                apply(
                    primitive(typed_ir::PrimitiveOp::StringLen),
                    unknown_lit(typed_ir::Lit::String("aあ🙂".to_string())),
                ),
                "3",
            ),
            (
                apply(
                    apply(
                        primitive(typed_ir::PrimitiveOp::StringIndex),
                        unknown_lit(typed_ir::Lit::String("aあ🙂".to_string())),
                    ),
                    unknown_lit(typed_ir::Lit::Int("1".to_string())),
                ),
                "あ",
            ),
            (
                apply(
                    apply(
                        primitive(typed_ir::PrimitiveOp::StringIndexRange),
                        unknown_lit(typed_ir::Lit::String("aあ🙂z".to_string())),
                    ),
                    range_expr(1, 3),
                ),
                "あ🙂",
            ),
            (
                apply(
                    apply(
                        apply(
                            primitive(typed_ir::PrimitiveOp::StringSplice),
                            unknown_lit(typed_ir::Lit::String("abcz".to_string())),
                        ),
                        range_expr(1, 3),
                    ),
                    unknown_lit(typed_ir::Lit::String("XY".to_string())),
                ),
                "aXYz",
            ),
            (
                apply(
                    apply(
                        apply(
                            primitive(typed_ir::PrimitiveOp::StringIndexRangeRaw),
                            unknown_lit(typed_ir::Lit::String("aあ🙂z".to_string())),
                        ),
                        unknown_lit(typed_ir::Lit::Int("1".to_string())),
                    ),
                    unknown_lit(typed_ir::Lit::Int("3".to_string())),
                ),
                "あ🙂",
            ),
            (
                apply(
                    apply(
                        apply(
                            apply(
                                primitive(typed_ir::PrimitiveOp::StringSpliceRaw),
                                unknown_lit(typed_ir::Lit::String("abcz".to_string())),
                            ),
                            unknown_lit(typed_ir::Lit::Int("1".to_string())),
                        ),
                        unknown_lit(typed_ir::Lit::Int("3".to_string())),
                    ),
                    unknown_lit(typed_ir::Lit::String("XY".to_string())),
                ),
                "aXYz",
            ),
            (
                apply(
                    apply(
                        primitive(typed_ir::PrimitiveOp::StringEq),
                        unknown_lit(typed_ir::Lit::String("ok".to_string())),
                    ),
                    unknown_lit(typed_ir::Lit::String("ok".to_string())),
                ),
                "1",
            ),
            (
                apply(
                    primitive(typed_ir::PrimitiveOp::IntToHex),
                    unknown_lit(typed_ir::Lit::Int("255".to_string())),
                ),
                "ff",
            ),
            (
                apply(
                    primitive(typed_ir::PrimitiveOp::IntToUpperHex),
                    unknown_lit(typed_ir::Lit::Int("255".to_string())),
                ),
                "FF",
            ),
            (
                apply(
                    primitive(typed_ir::PrimitiveOp::BoolToString),
                    unknown_lit(typed_ir::Lit::Bool(true)),
                ),
                "true",
            ),
            (
                apply(
                    primitive(typed_ir::PrimitiveOp::FloatToString),
                    primitive_call(
                        typed_ir::PrimitiveOp::FloatAdd,
                        vec![
                            unknown_lit(typed_ir::Lit::Float("1.5".to_string())),
                            unknown_lit(typed_ir::Lit::Float("2.0".to_string())),
                        ],
                    ),
                ),
                "3.5",
            ),
            (
                apply(
                    primitive(typed_ir::PrimitiveOp::FloatToString),
                    primitive_call(
                        typed_ir::PrimitiveOp::FloatSub,
                        vec![
                            unknown_lit(typed_ir::Lit::Float("5.0".to_string())),
                            unknown_lit(typed_ir::Lit::Float("2.0".to_string())),
                        ],
                    ),
                ),
                "3.0",
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::FloatEq,
                    vec![
                        unknown_lit(typed_ir::Lit::Float("1.5".to_string())),
                        unknown_lit(typed_ir::Lit::Float("1.5".to_string())),
                    ],
                ),
                "1",
            ),
        ];

        for (expr, expected) in cases {
            let mut jit = compile_runtime_module_to_cps_repr_jit(&module_with_root(expr))
                .expect("compiled runtime module");
            let roots = jit.run_roots_i64().expect("ran");
            assert_eq!(roots.len(), 1);
            assert_eq!(describe_native_i64_value(roots[0]), expected);
        }
    }

    #[test]
    fn jit_runs_bytes_primitives_runtime_value_roots() {
        let hello_bytes = primitive_call(
            typed_ir::PrimitiveOp::StringToBytes,
            vec![unknown_lit(typed_ir::Lit::String("hello".to_string()))],
        );
        let cases = vec![
            (
                primitive_call(typed_ir::PrimitiveOp::BytesLen, vec![hello_bytes.clone()]),
                "5",
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::BytesIndex,
                    vec![
                        hello_bytes.clone(),
                        unknown_lit(typed_ir::Lit::Int("1".to_string())),
                    ],
                ),
                "101",
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::BytesLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::BytesConcat,
                        vec![hello_bytes.clone(), hello_bytes.clone()],
                    )],
                ),
                "10",
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::BytesEq,
                    vec![
                        hello_bytes.clone(),
                        primitive_call(
                            typed_ir::PrimitiveOp::StringToBytes,
                            vec![unknown_lit(typed_ir::Lit::String("hello".to_string()))],
                        ),
                    ],
                ),
                "1",
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::BytesLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::BytesIndexRange,
                        vec![hello_bytes, range_expr(1, 4)],
                    )],
                ),
                "3",
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::BytesLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::PathToBytes,
                        vec![primitive_call(
                            typed_ir::PrimitiveOp::BytesToPath,
                            vec![primitive_call(
                                typed_ir::PrimitiveOp::StringToBytes,
                                vec![unknown_lit(typed_ir::Lit::String("/tmp".to_string()))],
                            )],
                        )],
                    )],
                ),
                "4",
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::BytesToUtf8Raw,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::StringToBytes,
                        vec![unknown_lit(typed_ir::Lit::String("hello".to_string()))],
                    )],
                ),
                "(hello, 5)",
            ),
        ];

        for (expr, expected) in cases {
            let mut jit = compile_runtime_module_to_cps_repr_jit(&module_with_root(expr))
                .expect("compiled runtime module");
            let roots = jit.run_roots_i64().expect("ran");
            assert_eq!(roots.len(), 1);
            assert_eq!(describe_native_i64_value(roots[0]), expected);
        }
    }

    #[test]
    fn jit_runs_list_range_primitives_runtime_value_roots() {
        let sliced = apply(
            apply(
                primitive(typed_ir::PrimitiveOp::ListIndexRange),
                list_expr(vec![1, 2, 3, 4]),
            ),
            range_expr(1, 3),
        );
        let spliced = apply(
            apply(
                apply(
                    primitive(typed_ir::PrimitiveOp::ListSplice),
                    list_expr(vec![1, 2, 3, 4]),
                ),
                range_expr(1, 3),
            ),
            list_expr(vec![8, 9]),
        );
        let cases = vec![
            (
                apply(primitive(typed_ir::PrimitiveOp::ListLen), sliced.clone()),
                "2",
            ),
            (
                apply(
                    apply(primitive(typed_ir::PrimitiveOp::ListIndex), sliced),
                    unknown_lit(typed_ir::Lit::Int("0".to_string())),
                ),
                "2",
            ),
            (
                apply(primitive(typed_ir::PrimitiveOp::ListLen), spliced.clone()),
                "4",
            ),
            (
                apply(
                    apply(primitive(typed_ir::PrimitiveOp::ListIndex), spliced),
                    unknown_lit(typed_ir::Lit::Int("1".to_string())),
                ),
                "8",
            ),
        ];

        for (expr, expected) in cases {
            let mut jit = compile_runtime_module_to_cps_repr_jit(&module_with_root(expr))
                .expect("compiled runtime module");
            let roots = jit.run_roots_i64().expect("ran");
            assert_eq!(roots.len(), 1);
            assert_eq!(describe_native_i64_value(roots[0]), expected);
        }
    }

    #[test]
    fn jit_preserves_float_inside_runtime_value_containers() {
        let list = primitive_call(
            typed_ir::PrimitiveOp::ListSingleton,
            vec![unknown_lit(typed_ir::Lit::Float("2.0".to_string()))],
        );
        let indexed = primitive_call(
            typed_ir::PrimitiveOp::ListIndex,
            vec![list, unknown_lit(typed_ir::Lit::Int("0".to_string()))],
        );
        let rendered = primitive_call(typed_ir::PrimitiveOp::FloatToString, vec![indexed]);

        let mut jit = compile_runtime_module_to_cps_repr_jit(&module_with_root(rendered))
            .expect("compiled runtime module");
        let roots = jit.run_roots_i64().expect("ran");

        assert_eq!(roots.len(), 1);
        assert_eq!(describe_native_i64_value(roots[0]), "2.0");
    }

    fn out_effect_path(act: &str, operation: &str) -> typed_ir::Path {
        typed_ir::Path {
            segments: vec![
                typed_ir::Name("std".to_string()),
                typed_ir::Name("out".to_string()),
                typed_ir::Name(act.to_string()),
                typed_ir::Name(operation.to_string()),
            ],
        }
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
                                op: typed_ir::PrimitiveOp::IntAdd,
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

    fn effectful_function_with_pure_continue_abi() -> CpsReprAbiModule {
        let effect = typed_ir::Path::from_name(typed_ir::Name("unused".to_string()));
        lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: vec![crate::cps_ir::CpsHandler {
                    id: crate::cps_ir::CpsHandlerId(0),
                    arms: vec![crate::cps_ir::CpsHandlerArm {
                        effect,
                        entry: CpsContinuationId(2),
                    }],
                }],
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
                                op: typed_ir::PrimitiveOp::IntAdd,
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
                    CpsContinuation {
                        id: CpsContinuationId(2),
                        params: vec![CpsValueId(4), CpsValueId(5)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(4)),
                    },
                ],
            }],
        }))
    }

    fn effectful_function_with_pure_branch_abi() -> CpsReprAbiModule {
        let effect = typed_ir::Path::from_name(typed_ir::Name("unused".to_string()));
        lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: vec![crate::cps_ir::CpsHandler {
                    id: crate::cps_ir::CpsHandlerId(0),
                    arms: vec![crate::cps_ir::CpsHandlerArm {
                        effect,
                        entry: CpsContinuationId(3),
                    }],
                }],
                continuations: vec![
                    CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Bool(true),
                        }],
                        terminator: CpsTerminator::Branch {
                            cond: CpsValueId(0),
                            then_cont: CpsContinuationId(1),
                            else_cont: CpsContinuationId(2),
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(1),
                            literal: CpsLiteral::Int("42".to_string()),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(1)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(2),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(2),
                            literal: CpsLiteral::Int("0".to_string()),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(2)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(3),
                        params: vec![CpsValueId(3), CpsValueId(4)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                ],
            }],
        }))
    }

    fn effectful_function_with_pure_direct_call_abi() -> CpsReprAbiModule {
        let effect = typed_ir::Path::from_name(typed_ir::Name("unused".to_string()));
        lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: vec![CpsFunction {
                name: "add".to_string(),
                params: vec![CpsValueId(0), CpsValueId(1)],
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    CpsContinuation {
                        id: CpsContinuationId(0),
                        params: vec![CpsValueId(0), CpsValueId(1)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Primitive {
                            dest: CpsValueId(2),
                            op: typed_ir::PrimitiveOp::IntAdd,
                            args: vec![CpsValueId(0), CpsValueId(1)],
                        }],
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(1),
                            args: vec![CpsValueId(2)],
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(5)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(5)),
                    },
                ],
            }],
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: vec![crate::cps_ir::CpsHandler {
                    id: crate::cps_ir::CpsHandlerId(0),
                    arms: vec![crate::cps_ir::CpsHandlerArm {
                        effect,
                        entry: CpsContinuationId(1),
                    }],
                }],
                continuations: vec![
                    CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(3),
                                literal: CpsLiteral::Int("40".to_string()),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(4),
                                literal: CpsLiteral::Int("2".to_string()),
                            },
                            CpsStmt::DirectCall {
                                dest: CpsValueId(5),
                                target: "add".to_string(),
                                args: vec![CpsValueId(3), CpsValueId(4)],
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(5)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(6), CpsValueId(7)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(6)),
                    },
                ],
            }],
        }))
    }

    fn effectful_call_to_pure_callee_abi() -> CpsReprAbiModule {
        let effect = typed_ir::Path::from_name(typed_ir::Name("unused".to_string()));
        lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: vec![CpsFunction {
                name: "add".to_string(),
                params: vec![CpsValueId(0), CpsValueId(1)],
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    CpsContinuation {
                        id: CpsContinuationId(0),
                        params: vec![CpsValueId(0), CpsValueId(1)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![CpsStmt::Primitive {
                            dest: CpsValueId(2),
                            op: typed_ir::PrimitiveOp::IntAdd,
                            args: vec![CpsValueId(0), CpsValueId(1)],
                        }],
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(1),
                            args: vec![CpsValueId(2)],
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(8)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(8)),
                    },
                ],
            }],
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: vec![crate::cps_ir::CpsHandler {
                    id: crate::cps_ir::CpsHandlerId(0),
                    arms: vec![crate::cps_ir::CpsHandlerArm {
                        effect,
                        entry: CpsContinuationId(2),
                    }],
                }],
                continuations: vec![
                    CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(3),
                                literal: CpsLiteral::Int("40".to_string()),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(4),
                                literal: CpsLiteral::Int("2".to_string()),
                            },
                        ],
                        terminator: CpsTerminator::EffectfulCall {
                            target: "add".to_string(),
                            args: vec![CpsValueId(3), CpsValueId(4)],
                            resume: CpsContinuationId(1),
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(5)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(5)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(2),
                        params: vec![CpsValueId(6), CpsValueId(7)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(6)),
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
        let start = typed_ir::Path::from_name(typed_ir::Name("start".to_string()));
        let choose = typed_ir::Path::from_name(typed_ir::Name("choose".to_string()));
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

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum ThunkBoundaryStorage {
        Direct,
        ListIndex,
        RecordSelect,
        VariantPayload,
    }

    fn active_thunk_boundary_abi(
        allowed: typed_ir::Type,
        storage: ThunkBoundaryStorage,
    ) -> CpsReprAbiModule {
        let choose = typed_ir::Path::from_name(typed_ir::Name("choose".to_string()));
        let mut root_stmts = vec![
            CpsStmt::InstallHandler {
                handler: crate::cps_ir::CpsHandlerId(0),
                envs: Vec::new(),
                value: CpsContinuationId(5),
                escape: CpsContinuationId(5),
            },
            CpsStmt::FreshGuard {
                dest: CpsValueId(0),
                var: yulang_runtime::EffectIdVar(0),
            },
            CpsStmt::MakeThunk {
                dest: CpsValueId(1),
                entry: CpsContinuationId(1),
            },
            CpsStmt::AddThunkBoundary {
                dest: CpsValueId(2),
                thunk: CpsValueId(1),
                guard: CpsValueId(0),
                allowed,
                active: true,
            },
        ];
        let thunk = match storage {
            ThunkBoundaryStorage::Direct => CpsValueId(2),
            ThunkBoundaryStorage::ListIndex => {
                root_stmts.extend([
                    CpsStmt::Primitive {
                        dest: CpsValueId(14),
                        op: typed_ir::PrimitiveOp::ListSingleton,
                        args: vec![CpsValueId(2)],
                    },
                    CpsStmt::Literal {
                        dest: CpsValueId(15),
                        literal: CpsLiteral::Int("0".to_string()),
                    },
                    CpsStmt::Primitive {
                        dest: CpsValueId(16),
                        op: typed_ir::PrimitiveOp::ListIndex,
                        args: vec![CpsValueId(14), CpsValueId(15)],
                    },
                ]);
                CpsValueId(16)
            }
            ThunkBoundaryStorage::RecordSelect => {
                root_stmts.extend([
                    CpsStmt::Record {
                        dest: CpsValueId(14),
                        base: None,
                        fields: vec![CpsRecordField {
                            name: typed_ir::Name("callback".to_string()),
                            value: CpsValueId(2),
                        }],
                    },
                    CpsStmt::Select {
                        dest: CpsValueId(16),
                        base: CpsValueId(14),
                        field: typed_ir::Name("callback".to_string()),
                    },
                ]);
                CpsValueId(16)
            }
            ThunkBoundaryStorage::VariantPayload => {
                root_stmts.extend([
                    CpsStmt::Variant {
                        dest: CpsValueId(14),
                        tag: typed_ir::Name("some".to_string()),
                        value: Some(CpsValueId(2)),
                    },
                    CpsStmt::VariantPayload {
                        dest: CpsValueId(16),
                        variant: CpsValueId(14),
                    },
                ]);
                CpsValueId(16)
            }
        };
        root_stmts.extend([
            CpsStmt::InstallHandler {
                handler: crate::cps_ir::CpsHandlerId(1),
                envs: Vec::new(),
                value: CpsContinuationId(6),
                escape: CpsContinuationId(6),
            },
            CpsStmt::ForceThunk {
                dest: CpsValueId(3),
                thunk,
            },
        ]);
        lower_cps_repr_abi_module(&lower_cps_repr_module(&CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: vec![
                    crate::cps_ir::CpsHandler {
                        id: crate::cps_ir::CpsHandlerId(0),
                        arms: vec![crate::cps_ir::CpsHandlerArm {
                            effect: choose.clone(),
                            entry: CpsContinuationId(3),
                        }],
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
                        stmts: root_stmts,
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(4),
                            literal: CpsLiteral::Int("1".to_string()),
                        }],
                        terminator: CpsTerminator::Perform {
                            effect: choose,
                            payload: CpsValueId(4),
                            resume: CpsContinuationId(2),
                            handler: crate::cps_ir::CpsHandlerId(0),
                            blocked: None,
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(2),
                        params: vec![CpsValueId(5)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(5)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(3),
                        params: vec![CpsValueId(6), CpsValueId(7)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(8),
                            literal: CpsLiteral::Int("20".to_string()),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(8)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(4),
                        params: vec![CpsValueId(9), CpsValueId(10)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(11),
                            literal: CpsLiteral::Int("10".to_string()),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(11)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(5),
                        params: vec![CpsValueId(12)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(12)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(6),
                        params: vec![CpsValueId(13)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(13)),
                    },
                ],
            }],
        }))
    }

    fn tail_resume_effect_abi() -> CpsReprAbiModule {
        let effect = typed_ir::Path::from_name(typed_ir::Name("choose".to_string()));
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
                                op: typed_ir::PrimitiveOp::IntAdd,
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
        let effect = typed_ir::Path::from_name(typed_ir::Name("choose".to_string()));
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
                            op: typed_ir::PrimitiveOp::IntAdd,
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
                                op: typed_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(6), CpsValueId(7)],
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(8)),
                    },
                ],
            }],
        }))
    }

    fn unknown_lit(lit: typed_ir::Lit) -> runtime::Expr {
        runtime::Expr::typed(runtime::ExprKind::Lit(lit), runtime::Type::unknown())
    }

    fn primitive(op: typed_ir::PrimitiveOp) -> runtime::Expr {
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

    fn thunk(expr: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Thunk {
                effect: typed_ir::Type::Unknown,
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

    fn primitive_call(op: typed_ir::PrimitiveOp, args: Vec<runtime::Expr>) -> runtime::Expr {
        args.into_iter()
            .fold(primitive(op), |callee, arg| apply(callee, arg))
    }

    fn list_expr(items: Vec<i64>) -> runtime::Expr {
        items
            .into_iter()
            .map(|item| {
                primitive_call(
                    typed_ir::PrimitiveOp::ListSingleton,
                    vec![unknown_lit(typed_ir::Lit::Int(item.to_string()))],
                )
            })
            .fold(
                primitive_call(
                    typed_ir::PrimitiveOp::ListEmpty,
                    vec![unknown_lit(typed_ir::Lit::Unit)],
                ),
                |acc, item| primitive_call(typed_ir::PrimitiveOp::ListMerge, vec![acc, item]),
            )
    }

    fn range_expr(start: i64, end: i64) -> runtime::Expr {
        variant(
            "within",
            Some(tuple(vec![
                variant(
                    "included",
                    Some(unknown_lit(typed_ir::Lit::Int(start.to_string()))),
                ),
                variant(
                    "excluded",
                    Some(unknown_lit(typed_ir::Lit::Int(end.to_string()))),
                ),
            ])),
        )
    }

    fn tuple(items: Vec<runtime::Expr>) -> runtime::Expr {
        runtime::Expr::typed(runtime::ExprKind::Tuple(items), runtime::Type::unknown())
    }

    fn record(fields: Vec<(&str, runtime::Expr)>) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Record {
                fields: fields
                    .into_iter()
                    .map(|(name, value)| runtime::RecordExprField {
                        name: typed_ir::Name(name.to_string()),
                        value,
                    })
                    .collect(),
                spread: None,
            },
            runtime::Type::unknown(),
        )
    }

    fn variant(tag: &str, value: Option<runtime::Expr>) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Variant {
                tag: typed_ir::Name(tag.to_string()),
                value: value.map(Box::new),
            },
            runtime::Type::unknown(),
        )
    }

    fn module_with_root(expr: runtime::Expr) -> runtime::Module {
        runtime::Module {
            path: typed_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![expr],
            roots: vec![runtime::Root::Expr(0)],
            role_impls: Vec::new(),
        }
    }
}
