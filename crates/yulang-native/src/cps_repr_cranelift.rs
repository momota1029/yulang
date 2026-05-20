use std::collections::{HashMap, HashSet};
use std::fmt;

use cranelift_codegen::ir::{self, AbiParam, InstBuilder, types};
use cranelift_codegen::settings;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use yulang_runtime as runtime;
use yulang_typed_ir as typed_ir;

use crate::cps_ir::{
    CpsContinuationId, CpsEffectPerformOwnership, CpsHandlerId, CpsLiteral, CpsRecordField,
    CpsStmt, CpsTerminator, CpsValueId,
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
mod runtime_i64;
mod runtime_symbols;

#[cfg(test)]
use runtime_i64::describe_native_i64_value;
use runtime_i64::{
    describe_cps_repr_i64_value_with_hint, jit_trace_enabled, reset_native_i64_cps_state,
    set_native_i64_root_function_ids, take_native_i64_root_result,
};

pub type CpsReprCraneliftResult<T> = Result<T, CpsReprCraneliftError>;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CpsReprCraneliftOptions {
    pub mmtk_yvalue_primitives: bool,
}

impl CpsReprCraneliftOptions {
    pub fn mmtk_yvalue_primitives() -> Self {
        Self {
            mmtk_yvalue_primitives: true,
        }
    }
}

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
    options: CpsReprCraneliftOptions,
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
            .zip(self.root_display_hints.iter())
            .map(|(root, hint)| {
                reset_native_i64_cps_state();
                reset_mmtk_cps_state_for_options(self.options);
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
                reset_mmtk_cps_state_for_options(self.options);
                set_native_i64_root_function_ids(&self.root_function_ids);
                let ptr = self.module.get_finalized_function(*root);
                let call = unsafe { std::mem::transmute::<_, extern "C" fn() -> i64>(ptr) };
                let value = call();
                Ok(take_native_i64_root_result(value))
            })
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum CpsRootDisplayHint {
    Plain,
    Unit,
    Bool,
    Tuple(Vec<CpsRootDisplayHint>),
    List(Box<CpsRootDisplayHint>),
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
    compile_cps_repr_abi_module_with_root_hints_and_options(
        module,
        Vec::new(),
        CpsReprCraneliftOptions::default(),
    )
}

pub fn compile_cps_repr_abi_module_with_options(
    module: &CpsReprAbiModule,
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<CpsReprJitModule> {
    compile_cps_repr_abi_module_with_root_hints_and_options(module, Vec::new(), options)
}

fn compile_cps_repr_abi_module_with_root_hints_and_options(
    module: &CpsReprAbiModule,
    root_display_hints: Vec<CpsRootDisplayHint>,
    options: CpsReprCraneliftOptions,
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
    let cranelift_ir = define_functions(&mut jit, module, &functions, &mut literals, options)?;
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
        options,
        _strings: strings,
    })
}

fn reset_mmtk_cps_state_for_options(options: CpsReprCraneliftOptions) {
    if options.mmtk_yvalue_primitives {
        crate::mmtk_runtime::yulang_mmtk_cps_reset_i64();
    } else {
        crate::mmtk_runtime::yulang_mmtk_cps_disable_control_stack_i64();
    }
}

pub fn compile_cps_repr_abi_module_to_object(
    module: &CpsReprAbiModule,
) -> CpsReprCraneliftResult<CpsReprObjectModule> {
    compile_cps_repr_abi_module_to_object_with_options(module, CpsReprCraneliftOptions::default())
}

pub fn compile_cps_repr_abi_module_to_object_with_options(
    module: &CpsReprAbiModule,
    options: CpsReprCraneliftOptions,
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
    let _ = define_functions(&mut object, module, &functions, &mut literals, options)?;
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
    compile_runtime_module_to_cps_repr_jit_with_options(module, CpsReprCraneliftOptions::default())
}

pub fn compile_runtime_module_to_cps_repr_jit_with_options(
    module: &runtime::Module,
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<CpsReprJitModule> {
    let root_display_hints = runtime_root_display_hints(module);
    let cps = lower_cps_module(module)?;
    validate_cps_module(&cps)?;
    let repr = crate::cps_repr::lower_cps_repr_module(&cps);
    let abi = lower_cps_repr_abi_module(&repr);
    compile_cps_repr_abi_module_with_root_hints_and_options(&abi, root_display_hints, options)
}

pub fn compile_runtime_module_to_cps_repr_object(
    module: &runtime::Module,
) -> CpsReprCraneliftResult<CpsReprObjectModule> {
    compile_runtime_module_to_cps_repr_object_with_options(
        module,
        CpsReprCraneliftOptions::default(),
    )
}

pub fn compile_runtime_module_to_cps_repr_object_with_options(
    module: &runtime::Module,
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<CpsReprObjectModule> {
    let cps = lower_cps_module(module)?;
    validate_cps_module(&cps)?;
    let repr = crate::cps_repr::lower_cps_repr_module(&cps);
    let abi = lower_cps_repr_abi_module(&repr);
    compile_cps_repr_abi_module_to_object_with_options(&abi, options)
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
        runtime::Type::Core(core) => root_display_hint_for_core_type(core),
        runtime::Type::Thunk { value, .. } => root_display_hint_for_runtime_type(value),
        _ => CpsRootDisplayHint::Plain,
    }
}

fn root_display_hint_for_core_type(ty: &typed_ir::Type) -> CpsRootDisplayHint {
    match ty {
        typed_ir::Type::Named { path, args }
            if args.is_empty() && core_type_path_is(path, "unit") =>
        {
            CpsRootDisplayHint::Unit
        }
        typed_ir::Type::Named { path, args }
            if args.is_empty() && core_type_path_is(path, "bool") =>
        {
            CpsRootDisplayHint::Bool
        }
        typed_ir::Type::Named { path, args } if core_type_path_is(path, "list") => args
            .iter()
            .find_map(root_display_hint_for_type_arg)
            .map(|item| CpsRootDisplayHint::List(Box::new(item)))
            .unwrap_or(CpsRootDisplayHint::Plain),
        typed_ir::Type::Tuple(items) => {
            CpsRootDisplayHint::Tuple(items.iter().map(root_display_hint_for_core_type).collect())
        }
        _ => CpsRootDisplayHint::Plain,
    }
}

fn root_display_hint_for_type_arg(arg: &typed_ir::TypeArg) -> Option<CpsRootDisplayHint> {
    match arg {
        typed_ir::TypeArg::Type(ty) => Some(root_display_hint_for_core_type(ty)),
        typed_ir::TypeArg::Bounds(bounds) => bounds
            .lower
            .as_deref()
            .or(bounds.upper.as_deref())
            .map(root_display_hint_for_core_type),
    }
}

fn core_type_path_is(path: &typed_ir::Path, name: &str) -> bool {
    match path.segments.as_slice() {
        [single] => single.0 == name,
        [std, _, last] => std.0 == "std" && last.0 == name,
        _ => false,
    }
}

fn define_functions<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    module: &CpsReprAbiModule,
    functions: &DeclaredFunctions,
    literals: &mut L,
    options: CpsReprCraneliftOptions,
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
                options,
            )?);
        }
        let mut ctx = module_backend.make_context();
        ctx.func.signature = function_signature(module_backend, function);
        if function_has_effect_flow(function) {
            lower_effectful_function_wrapper(
                module_backend,
                &mut ctx,
                function,
                functions,
                options,
            )?;
        } else {
            lower_function(
                module_backend,
                &mut ctx,
                function,
                functions,
                &handlers,
                literals,
                options,
            )?;
        }
        let ir_dump = format!(
            ";; cps-repr function {}\n{}",
            function.name,
            ctx.func.display()
        );
        if std::env::var_os("YULANG_DUMP_CRANELIFT_IR").is_some() {
            eprintln!("{ir_dump}");
        }
        cranelift_ir.push(ir_dump);
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
    effects: Vec<RegisteredEffect>,
}

#[derive(Debug, Default)]
struct LocalValueCache {
    native_float: HashMap<CpsValueId, ir::Value>,
}

use self::helper_arity::{
    EFFECTFUL_APPLY_RESUMPTION_HELPERS, INSTALL_HANDLER_FULL_HELPERS, MAKE_CLOSURE_HELPERS,
    MAKE_ENV_HELPERS, MAKE_OWNED_RESUMPTION_HELPERS, MAKE_RECURSIVE_CLOSURE_HELPERS,
    MAKE_RESUMPTION_HELPERS, MAKE_THUNK_HELPERS, MMTK_MAKE_CLOSURE_HELPERS,
    MMTK_MAKE_THUNK_HELPERS, PUSH_RETURN_FRAME_HELPERS, TUPLE_HELPERS,
};

struct CpsCraneliftLowerCx<'a, 'builder, M: Module, L: CpsLiteralStore> {
    module_backend: &'a mut M,
    builder: &'a mut FunctionBuilder<'builder>,
    function: &'a CpsReprAbiFunction,
    functions: &'a DeclaredFunctions,
    handlers: &'a HandlerRegistry,
    literals: &'a mut L,
    values: &'a mut LocalValueCache,
    options: CpsReprCraneliftOptions,
}

struct PerformTerminatorCase<'a> {
    effect: &'a typed_ir::Path,
    payload: CpsValueId,
    resume: CpsContinuationId,
    handler: CpsHandlerId,
    blocked: Option<CpsValueId>,
    ownership: Option<&'a CpsEffectPerformOwnership>,
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

#[derive(Debug, Clone)]
struct RegisteredEffect {
    function: String,
    path: typed_ir::Path,
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
        for (effect, candidate) in &candidates {
            if !effects.iter().any(|existing: &RegisteredEffect| {
                existing.function == candidate.function && existing.path == *effect
            }) {
                effects.push(RegisteredEffect {
                    function: candidate.function.clone(),
                    path: effect.clone(),
                });
            }
        }
        if jit_trace_enabled() {
            for (index, effect) in effects.iter().enumerate() {
                eprintln!(
                    "[JIT-CPS] registered_effect: bit={} function={} path={}",
                    index,
                    effect.function,
                    format_typed_path(&effect.path),
                );
            }
            for (effect, candidate) in &candidates {
                eprintln!(
                    "[JIT-CPS] handler_candidate: handler={} function={} entry={} effect={} escape={}",
                    candidate.handler.0,
                    candidate.function,
                    candidate.entry.0,
                    format_typed_path(effect),
                    candidate.continues_to_installed_escape
                );
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

    fn candidate_for_owned_perform(
        &self,
        ownership: &CpsEffectPerformOwnership,
    ) -> Option<HandlerCandidate> {
        self.candidates
            .iter()
            .find(|(effect, candidate)| {
                candidate.function == ownership.owner_function
                    && candidate.handler == ownership.handler
                    && candidate.entry == ownership.arm_entry
                    && effect_matches(effect, &ownership.effect)
            })
            .map(|(_, candidate)| candidate.clone())
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
            if effect_matches(&registered.path, effect) {
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
        for effect in self
            .candidates
            .iter()
            .filter(|(_, candidate)| {
                candidate.function == function.name && candidate.handler == handler
            })
            .map(|(effect, _)| effect)
        {
            mask |= self.registered_effect_exact_mask(function, effect)?;
        }
        Ok(mask)
    }

    fn registered_effect_exact_mask(
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
            if registered.function == function.name && registered.path == *effect {
                mask |= 1_i64 << index;
            }
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
            if effect_allowed_by_type_for_registered(allowed, &effect.function, &effect.path) {
                mask |= 1_i64 << index;
            }
        }
        Ok(mask)
    }
}

fn format_typed_path(path: &typed_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn define_effectful_function<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    function: &CpsReprAbiFunction,
    functions: &DeclaredFunctions,
    handlers: &HandlerRegistry,
    literals: &mut L,
    options: CpsReprCraneliftOptions,
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
            options,
        )?;
        let ir_dump = format!(
            ";; cps-repr continuation {}::{:?}\n{}",
            function.name,
            continuation.id,
            ctx.func.display()
        );
        if std::env::var_os("YULANG_DUMP_CRANELIFT_IR").is_some() {
            eprintln!("{ir_dump}");
        }
        cranelift_ir.push(ir_dump);
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
    options: CpsReprCraneliftOptions,
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
    let result =
        force_function_result_if_thunk(module_backend, &mut builder, function, result, options)?;
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
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<ir::Value> {
    let entry = continuation(function, function.entry)?;
    if entry.return_lane != CpsReprAbiLane::ThunkPtr {
        return Ok(result);
    }
    let helper = declare_import(
        module_backend,
        builder,
        cps_control_helper(
            options,
            "yulang_cps_force_thunk_i64",
            "yulang_mmtk_cps_control_force_thunk_i64",
        ),
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
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<()> {
    let direct_island = direct_style_island_from(function, continuation.id);
    if direct_island.len() > 1 {
        return lower_direct_style_continuation_island(
            module_backend,
            ctx,
            function,
            continuation,
            functions,
            handlers,
            literals,
            options,
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
            options,
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
    handlers: &HandlerRegistry,
    literals: &mut L,
    options: CpsReprCraneliftOptions,
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
                handlers,
                literals,
                &mut values,
                options,
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
            options,
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
    options: CpsReprCraneliftOptions,
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
            let cond = branch_condition(module_backend, builder, options, cond)?;
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
                options,
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
        cx.options,
    )
}

fn lower_value_stmt_parts<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    stmt: &CpsStmt,
    literals: &mut L,
    values: &mut LocalValueCache,
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<()> {
    match stmt {
        CpsStmt::Literal { dest, literal } => {
            let value = lower_literal(
                module_backend,
                builder,
                function,
                literal,
                literals,
                options,
            )?;
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
            let items = read_runtime_values_i64(
                module_backend,
                builder,
                function,
                literals,
                values,
                items,
                options,
            )?;
            let value = make_tuple_value(module_backend, builder, &items, options)?;
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
                options,
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
                options,
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
                yvalue_primitive_helper(
                    options,
                    "yulang_cps_record_select_i64",
                    "yulang_mmtk_cps_record_select_i64",
                ),
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
            let default = read_runtime_value_i64(
                module_backend,
                builder,
                function,
                literals,
                values,
                *default,
                options,
            )?;
            let (field_ptr, field_len) =
                literals.literal_bytes(module_backend, builder, field.0.as_bytes())?;
            let value = call_i64_helper(
                module_backend,
                builder,
                yvalue_primitive_helper(
                    options,
                    "yulang_cps_record_select_or_default_i64",
                    "yulang_mmtk_cps_record_select_or_default_i64",
                ),
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
                yvalue_primitive_helper(
                    options,
                    "yulang_cps_record_has_field_i64",
                    "yulang_mmtk_cps_record_has_field_i64",
                ),
                &[base, field_ptr, field_len],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::Variant { dest, tag, value } => {
            let value = value
                .map(|value| {
                    read_runtime_value_i64(
                        module_backend,
                        builder,
                        function,
                        literals,
                        values,
                        value,
                        options,
                    )
                })
                .transpose()?;
            let tag = register_variant_tag(module_backend, builder, tag, literals, options)?;
            let result = if let Some(value) = value {
                call_i64_helper(
                    module_backend,
                    builder,
                    yvalue_primitive_helper(
                        options,
                        "yulang_cps_variant_i64_1",
                        "yulang_mmtk_cps_variant_i64_1",
                    ),
                    &[tag, value],
                )?
            } else {
                call_i64_helper(
                    module_backend,
                    builder,
                    yvalue_primitive_helper(
                        options,
                        "yulang_cps_variant_i64_0",
                        "yulang_mmtk_cps_variant_i64_0",
                    ),
                    &[tag],
                )?
            };
            builder.def_var(variable(*dest), result);
        }
        CpsStmt::TupleGet { dest, tuple, index } => {
            let tuple = read_value(builder, function, *tuple)?;
            let index = builder.ins().iconst(types::I64, *index as i64);
            let value = call_i64_helper(
                module_backend,
                builder,
                yvalue_primitive_helper(
                    options,
                    "yulang_cps_tuple_get_i64",
                    "yulang_mmtk_cps_tuple_get_i64",
                ),
                &[tuple, index],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::VariantTagEq { dest, variant, tag } => {
            let variant = read_value(builder, function, *variant)?;
            let tag = register_variant_tag(module_backend, builder, tag, literals, options)?;
            let value = call_i64_helper(
                module_backend,
                builder,
                yvalue_primitive_helper(
                    options,
                    "yulang_cps_variant_tag_eq_i64",
                    "yulang_mmtk_cps_variant_tag_eq_i64",
                ),
                &[variant, tag],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::VariantPayload { dest, variant } => {
            let variant = read_value(builder, function, *variant)?;
            let value = call_i64_helper(
                module_backend,
                builder,
                yvalue_primitive_helper(
                    options,
                    "yulang_cps_variant_payload_i64",
                    "yulang_mmtk_cps_variant_payload_i64",
                ),
                &[variant],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::Primitive { dest, op, args } => {
            let args = read_primitive_args(
                module_backend,
                builder,
                function,
                literals,
                values,
                *op,
                args,
                options,
            )?;
            let value = lower_primitive(module_backend, builder, function, *op, &args, options)?;
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
        cx.options,
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
    options: CpsReprCraneliftOptions,
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
            let value = make_thunk(
                module_backend,
                builder,
                function,
                *entry,
                functions,
                options,
            )?;
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
                cps_control_helper(
                    options,
                    "yulang_cps_add_thunk_boundary_i64",
                    "yulang_mmtk_cps_control_add_thunk_boundary_i64",
                ),
                &[value, guard, allowed_mask, active],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::MakeClosure { dest, entry } => {
            let value = make_closure(
                module_backend,
                builder,
                function,
                *entry,
                functions,
                options,
            )?;
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
                options,
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
                cps_control_helper(
                    options,
                    "yulang_cps_force_thunk_i64",
                    "yulang_mmtk_cps_control_force_thunk_i64",
                ),
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
        cx.options,
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
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<()> {
    match stmt {
        CpsStmt::DirectCall {
            dest, target, args, ..
        } => {
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
                cps_control_helper(
                    options,
                    "yulang_cps_apply_closure_i64",
                    "yulang_mmtk_cps_control_apply_closure_i64",
                ),
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
            ownership,
        } => {
            lower_perform_terminator_case(
                cx,
                PerformTerminatorCase {
                    effect,
                    payload: *payload,
                    resume: *resume,
                    handler: *handler,
                    blocked: *blocked,
                    ownership: ownership.as_ref(),
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
        CpsTerminator::EffectfulForce { thunk, resume, .. } => {
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
        cx.options,
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
        case.ownership,
        cx.options,
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
        cx.options,
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
        cx.options,
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
    ownership: Option<&CpsEffectPerformOwnership>,
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<()> {
    let host_fallback = host_console_effect_kind(effect);
    let candidates = ownership
        .and_then(|ownership| handlers.candidate_for_owned_perform(ownership))
        .map(|candidate| vec![candidate])
        .unwrap_or_else(|| handlers.candidates_for_effect(effect));
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
            options,
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
        ownership,
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
    let selected = if let Some(ownership) = ownership {
        let owner = functions
            .function_ids
            .get(&ownership.owner_function)
            .copied()
            .ok_or_else(|| CpsReprCraneliftError::MissingFunction {
                name: ownership.owner_function.clone(),
            })?;
        let expected_handler = builder.ins().iconst(types::I64, ownership.handler.0 as i64);
        let expected_owner = builder.ins().iconst(types::I64, owner as i64);
        call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_select_owned_handler_i64",
            &[
                expected_handler,
                expected_owner,
                fallback,
                effect_mask,
                blocked,
            ],
        )?
    } else {
        call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_select_handler_i64",
            &[fallback, effect_mask, blocked],
        )?
    };
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
    if let Some(ownership) = ownership
        && let Some(candidate) = handlers.candidate_for_owned_perform(ownership)
    {
        return lower_handler_candidate_return(
            module_backend,
            builder,
            function,
            &candidate,
            payload,
            resumption,
            functions,
        );
    }
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
        options,
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
    options: CpsReprCraneliftOptions,
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
        cps_control_helper(
            options,
            "yulang_cps_apply_closure_i64",
            "yulang_mmtk_cps_control_apply_closure_i64",
        ),
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
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<()> {
    let resume_cont = lookup_continuation(function, resume)?;
    check_resume_continuation_shape(function, resume_cont)?;
    let thunk_value = read_value(builder, function, thunk)?;
    let is_thunk = call_i64_helper(
        module_backend,
        builder,
        cps_control_helper(
            options,
            "yulang_cps_is_thunk_i64",
            "yulang_mmtk_cps_control_is_thunk_i64",
        ),
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
        cps_control_helper(
            options,
            "yulang_cps_force_thunk_i64",
            "yulang_mmtk_cps_control_force_thunk_i64",
        ),
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
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<()> {
    let then_block = builder.create_block();
    let else_block = builder.create_block();
    let merge_block = builder.create_block();
    builder.append_block_param(merge_block, types::I64);

    let cond_id = cond;
    let cond = read_value(builder, function, cond_id)?;
    let cond =
        force_branch_condition_if_thunk(module_backend, builder, function, cond_id, cond, options)?;
    let cond = branch_condition(module_backend, builder, options, cond)?;
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
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<()> {
    let missing_block = builder.create_block();
    let selected_owner = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_selected_handler_owner_function_i64",
        &[],
    )?;

    for (index, candidate) in candidates.iter().enumerate() {
        let call_block = builder.create_block();
        let owner_check_block = builder.create_block();
        let owner_compare_block = builder.create_block();
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
            .brif(compare, owner_check_block, &[], next_block, &[]);

        builder.switch_to_block(owner_check_block);
        let owner_unknown = builder
            .ins()
            .icmp_imm(ir::condcodes::IntCC::Equal, selected_owner, 0);
        builder
            .ins()
            .brif(owner_unknown, call_block, &[], owner_compare_block, &[]);

        builder.switch_to_block(owner_compare_block);
        let candidate_owner = functions
            .function_ids
            .get(&candidate.function)
            .copied()
            .ok_or_else(|| CpsReprCraneliftError::MissingFunction {
                name: candidate.function.clone(),
            })?;
        let candidate_owner = builder.ins().iconst(types::I64, candidate_owner as i64);
        let owner_matches =
            builder
                .ins()
                .icmp(ir::condcodes::IntCC::Equal, selected_owner, candidate_owner);
        builder
            .ins()
            .brif(owner_matches, call_block, &[], next_block, &[]);

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
            options,
        )?;
    } else {
        let value = builder.ins().iconst(types::I64, 0);
        builder.ins().return_(&[value]);
    }
    builder.seal_block(missing_block);
    Ok(())
}

fn lower_handler_candidate_return<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    candidate: &HandlerCandidate,
    payload: ir::Value,
    resumption: ir::Value,
    functions: &DeclaredFunctions,
) -> CpsReprCraneliftResult<()> {
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
    let _ = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_enter_handler_arm_i64",
        &[],
    )?;
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
    let value = if candidate.continues_to_installed_escape {
        call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_perform_finish_escaped_i64",
            &[result],
        )?
    } else {
        call_i64_helper(
            module_backend,
            builder,
            "yulang_cps_perform_finish_i64",
            &[result],
        )?
    };
    builder.ins().return_(&[value]);
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
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<()> {
    let helper = match (mmtk_yvalue_primitive_lane_enabled(options), kind) {
        (true, HostConsoleEffect::Debug) => "yulang_mmtk_cps_debug_i64",
        (true, HostConsoleEffect::OutWrite) => "yulang_mmtk_cps_out_write_i64",
        (true, HostConsoleEffect::ErrWrite) => "yulang_mmtk_cps_err_write_i64",
        (true, HostConsoleEffect::WarnWrite) => "yulang_mmtk_cps_warn_write_i64",
        (true, HostConsoleEffect::DieDie) => "yulang_mmtk_cps_die_i64",
        (false, HostConsoleEffect::Debug) => "yulang_cps_debug_i64",
        (false, HostConsoleEffect::OutWrite) => "yulang_cps_out_write_i64",
        (false, HostConsoleEffect::ErrWrite) => "yulang_cps_err_write_i64",
        (false, HostConsoleEffect::WarnWrite) => "yulang_cps_warn_write_i64",
        (false, HostConsoleEffect::DieDie) => "yulang_cps_die_i64",
    };
    let result = call_i64_helper(module_backend, builder, helper, &[payload])?;
    let value = call_continuation_with_values(
        module_backend,
        builder,
        function,
        resume,
        &[result],
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
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<ir::Value> {
    if value_lane(function, cond_id) != Some(CpsReprAbiLane::ThunkPtr)
        && !value_is_make_thunk(function, cond_id)
    {
        return Ok(cond);
    }
    let helper = declare_import(
        module_backend,
        builder,
        cps_control_helper(
            options,
            "yulang_cps_force_thunk_i64",
            "yulang_mmtk_cps_control_force_thunk_i64",
        ),
        &[types::I64],
        types::I64,
    )?;
    let call = builder.ins().call(helper, &[cond]);
    Ok(builder.inst_results(call)[0])
}

fn branch_condition<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    options: CpsReprCraneliftOptions,
    cond: ir::Value,
) -> CpsReprCraneliftResult<ir::Value> {
    let cond = if mmtk_yvalue_primitive_lane_enabled(options) {
        call_i64_helper(
            module_backend,
            builder,
            "yulang_mmtk_cps_bool_truthy_i64",
            &[cond],
        )?
    } else {
        cond
    };
    Ok(builder
        .ins()
        .icmp_imm(ir::condcodes::IntCC::NotEqual, cond, 0))
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
    ownership: Option<&CpsEffectPerformOwnership>,
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
    let owned_prefix = if let Some(ownership) = ownership {
        let owner = functions
            .function_ids
            .get(&ownership.owner_function)
            .copied()
            .ok_or_else(|| CpsReprCraneliftError::MissingFunction {
                name: ownership.owner_function.clone(),
            })?;
        Some([
            builder.ins().iconst(types::I64, owner as i64),
            builder
                .ins()
                .iconst(types::I64, ownership.return_frame_resume.0 as i64),
            builder.ins().iconst(types::I64, resume.0 as i64),
            builder
                .ins()
                .iconst(types::I64, ownership.arm_entry.0 as i64),
        ])
    } else {
        None
    };
    if env_values.len() > 4 {
        let (env_ptr, env_len) = stack_i64_slice(builder, &env_values)?;
        if let Some(prefix) = owned_prefix {
            return call_i64_helper(
                module_backend,
                builder,
                MAKE_OWNED_RESUMPTION_HELPERS.many,
                &[
                    code, handler, prefix[0], prefix[1], prefix[2], prefix[3], env_ptr, env_len,
                ],
            );
        }
        return call_i64_helper(
            module_backend,
            builder,
            MAKE_RESUMPTION_HELPERS.many,
            &[code, handler, env_ptr, env_len],
        );
    }
    let mut args = vec![code, handler];
    let helper_name = if let Some(prefix) = owned_prefix {
        args.extend(prefix);
        MAKE_OWNED_RESUMPTION_HELPERS.fixed(resume_continuation.environment.len())
    } else {
        MAKE_RESUMPTION_HELPERS.fixed(resume_continuation.environment.len())
    };
    args.extend(env_values);
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
    options: CpsReprCraneliftOptions,
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
        let helpers = if mmtk_cps_control_objects_enabled(options) {
            &MMTK_MAKE_THUNK_HELPERS
        } else {
            &MAKE_THUNK_HELPERS
        };
        return call_i64_helper(
            module_backend,
            builder,
            helpers.many,
            &[code, env_ptr, env_len],
        );
    }
    let helper_name = if mmtk_cps_control_objects_enabled(options) {
        MMTK_MAKE_THUNK_HELPERS.fixed(thunk_continuation.environment.len())
    } else {
        MAKE_THUNK_HELPERS.fixed(thunk_continuation.environment.len())
    };
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
    options: CpsReprCraneliftOptions,
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
        let helpers = if mmtk_cps_control_objects_enabled(options) {
            &MMTK_MAKE_CLOSURE_HELPERS
        } else {
            &MAKE_CLOSURE_HELPERS
        };
        return call_i64_helper(
            module_backend,
            builder,
            helpers.many,
            &[code, env_ptr, env_len],
        );
    }
    let helper_name = if mmtk_cps_control_objects_enabled(options) {
        MMTK_MAKE_CLOSURE_HELPERS.fixed(closure_continuation.environment.len())
    } else {
        MAKE_CLOSURE_HELPERS.fixed(closure_continuation.environment.len())
    };
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
    options: CpsReprCraneliftOptions,
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
        return make_closure(module_backend, builder, function, entry, functions, options);
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
    let should_return_routed_jump = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_routed_jump_should_return_i64",
        &[],
    )?;
    let routed_jump_block = builder.create_block();
    let scoped_abort_block = builder.create_block();
    builder.ins().brif(
        should_return_routed_jump,
        routed_jump_block,
        &[],
        scoped_abort_block,
        &[],
    );

    builder.switch_to_block(routed_jump_block);
    builder.seal_block(routed_jump_block);
    let abort_value =
        call_i64_helper(module_backend, builder, "yulang_cps_consume_abort_i64", &[])?;
    builder.ins().return_(&[abort_value]);

    builder.switch_to_block(scoped_abort_block);
    builder.seal_block(scoped_abort_block);
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
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<ir::Value> {
    if args.len() > 4 {
        return Err(CpsReprCraneliftError::UnsupportedStmt {
            function: "<tuple>".to_string(),
            kind: "tuple larger than four slots",
        });
    }
    let helper_name = if mmtk_yvalue_primitive_lane_enabled(options) {
        match args.len() {
            0 => "yulang_mmtk_cps_tuple_i64_0",
            1 => "yulang_mmtk_cps_tuple_i64_1",
            2 => "yulang_mmtk_cps_tuple_i64_2",
            3 => "yulang_mmtk_cps_tuple_i64_3",
            4 => "yulang_mmtk_cps_tuple_i64_4",
            _ => unreachable!("tuple arity checked above"),
        }
    } else {
        TUPLE_HELPERS.select(args.len())
    };
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
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<ir::Value> {
    let mut record = match base {
        Some(base) => read_value(builder, function, base)?,
        None => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_record_empty_i64",
                "yulang_mmtk_cps_record_empty_i64",
            ),
            &[],
        )?,
    };
    for field in fields {
        let value = read_runtime_value_i64(
            module_backend,
            builder,
            function,
            literals,
            values,
            field.value,
            options,
        )?;
        let (field_ptr, field_len) =
            literals.literal_bytes(module_backend, builder, field.name.0.as_bytes())?;
        record = call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_record_insert_i64",
                "yulang_mmtk_cps_record_insert_i64",
            ),
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
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<ir::Value> {
    let mut record = read_value(builder, function, base)?;
    for field in fields {
        let (field_ptr, field_len) =
            literals.literal_bytes(module_backend, builder, field.0.as_bytes())?;
        record = call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_record_without_field_i64",
                "yulang_mmtk_cps_record_without_field_i64",
            ),
            &[record, field_ptr, field_len],
        )?;
    }
    Ok(record)
}

pub(super) fn tag_hash(tag: &typed_ir::Name) -> i64 {
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
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<ir::Value> {
    let tag_hash = builder.ins().iconst(types::I64, tag_hash(tag));
    let (name_ptr, name_len) = literals.literal_bytes(module_backend, builder, tag.0.as_bytes())?;
    let _ = call_i64_helper(
        module_backend,
        builder,
        yvalue_primitive_helper(
            options,
            "yulang_cps_register_tag_i64",
            "yulang_mmtk_cps_register_tag_i64",
        ),
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
    handlers: &HandlerRegistry,
    literals: &mut L,
    options: CpsReprCraneliftOptions,
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
                handlers,
                literals,
                &mut values,
                options,
            )?;
        }
        lower_terminator(
            module_backend,
            &mut builder,
            function,
            &blocks,
            continuation,
            &continuation.terminator,
            &mut values,
            options,
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
    handlers: &HandlerRegistry,
    literals: &mut L,
    values: &mut LocalValueCache,
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<()> {
    match stmt {
        CpsStmt::Literal { dest, literal } => {
            let value = lower_literal(
                module_backend,
                builder,
                function,
                literal,
                literals,
                options,
            )?;
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
            let value = make_thunk(
                module_backend,
                builder,
                function,
                *entry,
                functions,
                options,
            )?;
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
                cps_control_helper(
                    options,
                    "yulang_cps_add_thunk_boundary_i64",
                    "yulang_mmtk_cps_control_add_thunk_boundary_i64",
                ),
                &[value, guard, allowed_mask, active],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::MakeClosure { dest, entry } => {
            let value = make_closure(
                module_backend,
                builder,
                function,
                *entry,
                functions,
                options,
            )?;
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
                options,
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
                cps_control_helper(
                    options,
                    "yulang_cps_force_thunk_i64",
                    "yulang_mmtk_cps_control_force_thunk_i64",
                ),
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
            let items = read_runtime_values_i64(
                module_backend,
                builder,
                function,
                literals,
                values,
                items,
                options,
            )?;
            let value = make_tuple_value(module_backend, builder, &items, options)?;
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
                options,
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
                options,
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
                yvalue_primitive_helper(
                    options,
                    "yulang_cps_record_select_i64",
                    "yulang_mmtk_cps_record_select_i64",
                ),
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
            let default = read_runtime_value_i64(
                module_backend,
                builder,
                function,
                literals,
                values,
                *default,
                options,
            )?;
            let (field_ptr, field_len) =
                literals.literal_bytes(module_backend, builder, field.0.as_bytes())?;
            let value = call_i64_helper(
                module_backend,
                builder,
                yvalue_primitive_helper(
                    options,
                    "yulang_cps_record_select_or_default_i64",
                    "yulang_mmtk_cps_record_select_or_default_i64",
                ),
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
                yvalue_primitive_helper(
                    options,
                    "yulang_cps_record_has_field_i64",
                    "yulang_mmtk_cps_record_has_field_i64",
                ),
                &[base, field_ptr, field_len],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::Variant { dest, tag, value } => {
            let value = value
                .map(|value| {
                    read_runtime_value_i64(
                        module_backend,
                        builder,
                        function,
                        literals,
                        values,
                        value,
                        options,
                    )
                })
                .transpose()?;
            let tag = register_variant_tag(module_backend, builder, tag, literals, options)?;
            let result = if let Some(value) = value {
                call_i64_helper(
                    module_backend,
                    builder,
                    yvalue_primitive_helper(
                        options,
                        "yulang_cps_variant_i64_1",
                        "yulang_mmtk_cps_variant_i64_1",
                    ),
                    &[tag, value],
                )?
            } else {
                call_i64_helper(
                    module_backend,
                    builder,
                    yvalue_primitive_helper(
                        options,
                        "yulang_cps_variant_i64_0",
                        "yulang_mmtk_cps_variant_i64_0",
                    ),
                    &[tag],
                )?
            };
            builder.def_var(variable(*dest), result);
        }
        CpsStmt::TupleGet { dest, tuple, index } => {
            let tuple = read_value(builder, function, *tuple)?;
            let index = builder.ins().iconst(types::I64, *index as i64);
            let value = call_i64_helper(
                module_backend,
                builder,
                yvalue_primitive_helper(
                    options,
                    "yulang_cps_tuple_get_i64",
                    "yulang_mmtk_cps_tuple_get_i64",
                ),
                &[tuple, index],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::VariantTagEq { dest, variant, tag } => {
            let variant = read_value(builder, function, *variant)?;
            let tag = register_variant_tag(module_backend, builder, tag, literals, options)?;
            let value = call_i64_helper(
                module_backend,
                builder,
                yvalue_primitive_helper(
                    options,
                    "yulang_cps_variant_tag_eq_i64",
                    "yulang_mmtk_cps_variant_tag_eq_i64",
                ),
                &[variant, tag],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::VariantPayload { dest, variant } => {
            let variant = read_value(builder, function, *variant)?;
            let value = call_i64_helper(
                module_backend,
                builder,
                yvalue_primitive_helper(
                    options,
                    "yulang_cps_variant_payload_i64",
                    "yulang_mmtk_cps_variant_payload_i64",
                ),
                &[variant],
            )?;
            builder.def_var(variable(*dest), value);
        }
        CpsStmt::Primitive { dest, op, args } => {
            let args = read_primitive_args(
                module_backend,
                builder,
                function,
                literals,
                values,
                *op,
                args,
                options,
            )?;
            let value = lower_primitive(module_backend, builder, function, *op, &args, options)?;
            define_value_as_lane(builder, values, *dest, primitive_result_lane(*op), value);
        }
        CpsStmt::DirectCall {
            dest, target, args, ..
        } => {
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
                cps_control_helper(
                    options,
                    "yulang_cps_apply_closure_i64",
                    "yulang_mmtk_cps_control_apply_closure_i64",
                ),
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

fn lower_terminator<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    blocks: &HashMap<CpsContinuationId, ir::Block>,
    continuation: &CpsReprAbiContinuation,
    terminator: &CpsTerminator,
    values: &LocalValueCache,
    options: CpsReprCraneliftOptions,
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
            let cond = branch_condition(module_backend, builder, options, cond)?;
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

fn effect_allowed_by_type_for_registered(
    allowed: &typed_ir::Type,
    function: &str,
    effect: &typed_ir::Path,
) -> bool {
    if effect_allowed_by_type(allowed, effect) {
        return true;
    }
    registered_effect_absolute_path(function, effect)
        .as_ref()
        .is_some_and(|effect| effect_allowed_by_type(allowed, effect))
}

fn registered_effect_absolute_path(
    function: &str,
    effect: &typed_ir::Path,
) -> Option<typed_ir::Path> {
    // Handler candidates may carry paths relative to their defining
    // function, while effect masks are checked against caller-visible
    // absolute effect paths.
    if effect
        .segments
        .first()
        .is_some_and(|segment| segment.0 == "std")
    {
        return Some(effect.clone());
    }
    let base = function
        .split_once("__mono")
        .map_or(function, |(base, _)| base);
    let mut segments = base
        .split("::")
        .map(|segment| typed_ir::Name(segment.to_string()))
        .collect::<Vec<_>>();
    segments.pop()?;
    segments.extend(effect.segments.iter().cloned());
    Some(typed_ir::Path { segments })
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
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<ir::Value> {
    match literal {
        CpsLiteral::Int(value) => {
            if mmtk_yvalue_primitive_lane_enabled(options) {
                let (ptr, len) =
                    literals.literal_bytes(module_backend, builder, value.as_bytes())?;
                return call_i64_helper(
                    module_backend,
                    builder,
                    "yulang_mmtk_cps_make_int_i64",
                    &[ptr, len],
                );
            }
            let value =
                value
                    .parse::<i64>()
                    .map_err(|_| CpsReprCraneliftError::UnsupportedLiteral {
                        function: function.name.clone(),
                        literal: literal.clone(),
                    })?;
            Ok(builder.ins().iconst(types::I64, value))
        }
        CpsLiteral::Bool(value) => {
            let value = builder.ins().iconst(types::I64, i64::from(*value));
            if mmtk_yvalue_primitive_lane_enabled(options) {
                return call_i64_helper(
                    module_backend,
                    builder,
                    "yulang_mmtk_cps_box_bool_i64",
                    &[value],
                );
            }
            Ok(value)
        }
        CpsLiteral::Unit => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(options, "yulang_cps_unit_i64", "yulang_mmtk_cps_unit_i64"),
            &[],
        ),
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
                yvalue_primitive_helper(
                    options,
                    "yulang_cps_string_literal_i64",
                    "yulang_mmtk_cps_string_literal_i64",
                ),
                &[ptr, len],
            )
        }
    }
}

fn yvalue_primitive_helper(
    options: CpsReprCraneliftOptions,
    prototype: &'static str,
    mmtk: &'static str,
) -> &'static str {
    if mmtk_yvalue_primitive_lane_enabled(options) {
        mmtk
    } else {
        prototype
    }
}

fn cps_control_helper(
    options: CpsReprCraneliftOptions,
    prototype: &'static str,
    mmtk: &'static str,
) -> &'static str {
    if mmtk_cps_control_objects_enabled(options) {
        mmtk
    } else {
        prototype
    }
}

fn mmtk_yvalue_primitive_lane_enabled(options: CpsReprCraneliftOptions) -> bool {
    options.mmtk_yvalue_primitives
}

fn mmtk_cps_control_objects_enabled(options: CpsReprCraneliftOptions) -> bool {
    options.mmtk_yvalue_primitives
        && !std::env::var_os("YULANG_MMTK_CPS_CONTROL_OBJECTS").is_some_and(|value| {
            matches!(
                value.to_string_lossy().as_ref(),
                "0" | "false" | "off" | "disabled"
            )
        })
}

fn mmtk_yvalue_primitive_supported(op: typed_ir::PrimitiveOp) -> bool {
    match op {
        typed_ir::PrimitiveOp::YadaYada => false,
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
        | typed_ir::PrimitiveOp::StringConcat
        | typed_ir::PrimitiveOp::StringEq
        | typed_ir::PrimitiveOp::StringLen
        | typed_ir::PrimitiveOp::StringToBytes
        | typed_ir::PrimitiveOp::BytesLen
        | typed_ir::PrimitiveOp::BytesEq
        | typed_ir::PrimitiveOp::BytesConcat
        | typed_ir::PrimitiveOp::BytesIndex
        | typed_ir::PrimitiveOp::BytesToPath
        | typed_ir::PrimitiveOp::PathToBytes
        | typed_ir::PrimitiveOp::ListEmpty
        | typed_ir::PrimitiveOp::ListSingleton
        | typed_ir::PrimitiveOp::ListMerge
        | typed_ir::PrimitiveOp::ListLen
        | typed_ir::PrimitiveOp::ListIndex
        | typed_ir::PrimitiveOp::ListIndexRangeRaw
        | typed_ir::PrimitiveOp::ListIndexRange
        | typed_ir::PrimitiveOp::ListSpliceRaw
        | typed_ir::PrimitiveOp::ListSplice
        | typed_ir::PrimitiveOp::StringIndex
        | typed_ir::PrimitiveOp::StringIndexRangeRaw
        | typed_ir::PrimitiveOp::StringIndexRange
        | typed_ir::PrimitiveOp::StringSpliceRaw
        | typed_ir::PrimitiveOp::StringSplice
        | typed_ir::PrimitiveOp::BytesIndexRange
        | typed_ir::PrimitiveOp::BytesToUtf8Raw
        | typed_ir::PrimitiveOp::ListViewRaw
        | typed_ir::PrimitiveOp::IntToString
        | typed_ir::PrimitiveOp::IntToHex
        | typed_ir::PrimitiveOp::IntToUpperHex
        | typed_ir::PrimitiveOp::BoolToString
        | typed_ir::PrimitiveOp::FloatToString => true,
        typed_ir::PrimitiveOp::IntMod
        | typed_ir::PrimitiveOp::CharEq
        | typed_ir::PrimitiveOp::CharToString
        | typed_ir::PrimitiveOp::CharIsWhitespace
        | typed_ir::PrimitiveOp::CharIsPunctuation
        | typed_ir::PrimitiveOp::CharIsWord => false,
    }
}

fn lower_primitive<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    op: typed_ir::PrimitiveOp,
    args: &[ir::Value],
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<ir::Value> {
    if mmtk_yvalue_primitive_lane_enabled(options) && !mmtk_yvalue_primitive_supported(op) {
        return Err(CpsReprCraneliftError::UnsupportedPrimitive {
            function: function.name.clone(),
            op,
        });
    }

    let value = match op {
        typed_ir::PrimitiveOp::YadaYada => {
            return Err(CpsReprCraneliftError::UnsupportedPrimitive {
                function: function.name.clone(),
                op,
            });
        }
        typed_ir::PrimitiveOp::CharEq
        | typed_ir::PrimitiveOp::CharToString
        | typed_ir::PrimitiveOp::CharIsWhitespace
        | typed_ir::PrimitiveOp::CharIsPunctuation
        | typed_ir::PrimitiveOp::CharIsWord => {
            return Err(CpsReprCraneliftError::UnsupportedPrimitive {
                function: function.name.clone(),
                op,
            });
        }
        typed_ir::PrimitiveOp::BoolNot => {
            if mmtk_yvalue_primitive_lane_enabled(options) {
                call_i64_helper(
                    module_backend,
                    builder,
                    "yulang_mmtk_cps_bool_not_i64",
                    &[args[0]],
                )?
            } else {
                let zero = builder.ins().iconst(types::I64, 0);
                let is_zero = builder
                    .ins()
                    .icmp(ir::condcodes::IntCC::Equal, args[0], zero);
                builder.ins().uextend(types::I64, is_zero)
            }
        }
        typed_ir::PrimitiveOp::BoolEq => {
            if mmtk_yvalue_primitive_lane_enabled(options) {
                call_i64_helper(
                    module_backend,
                    builder,
                    "yulang_mmtk_cps_bool_eq_i64",
                    &[args[0], args[1]],
                )?
            } else {
                let eq = builder
                    .ins()
                    .icmp(ir::condcodes::IntCC::Equal, args[0], args[1]);
                builder.ins().uextend(types::I64, eq)
            }
        }
        typed_ir::PrimitiveOp::IntAdd => {
            if mmtk_yvalue_primitive_lane_enabled(options) {
                mmtk_i63_add_sub_or_helper(
                    module_backend,
                    builder,
                    "yulang_mmtk_cps_int_add_i64",
                    args[0],
                    args[1],
                    MmtkI63AddSubOp::Add,
                )?
            } else {
                builder.ins().iadd(args[0], args[1])
            }
        }
        typed_ir::PrimitiveOp::IntSub => {
            if mmtk_yvalue_primitive_lane_enabled(options) {
                mmtk_i63_add_sub_or_helper(
                    module_backend,
                    builder,
                    "yulang_mmtk_cps_int_sub_i64",
                    args[0],
                    args[1],
                    MmtkI63AddSubOp::Sub,
                )?
            } else {
                builder.ins().isub(args[0], args[1])
            }
        }
        typed_ir::PrimitiveOp::IntMul => {
            if mmtk_yvalue_primitive_lane_enabled(options) {
                call_i64_helper(
                    module_backend,
                    builder,
                    "yulang_mmtk_cps_int_mul_i64",
                    &[args[0], args[1]],
                )?
            } else {
                builder.ins().imul(args[0], args[1])
            }
        }
        typed_ir::PrimitiveOp::IntDiv => {
            if mmtk_yvalue_primitive_lane_enabled(options) {
                call_i64_helper(
                    module_backend,
                    builder,
                    "yulang_mmtk_cps_int_div_i64",
                    &[args[0], args[1]],
                )?
            } else {
                builder.ins().sdiv(args[0], args[1])
            }
        }
        typed_ir::PrimitiveOp::IntMod => {
            if mmtk_yvalue_primitive_lane_enabled(options) {
                return Err(CpsReprCraneliftError::UnsupportedPrimitive {
                    function: function.name.clone(),
                    op,
                });
            } else {
                builder.ins().srem(args[0], args[1])
            }
        }
        typed_ir::PrimitiveOp::IntEq => mmtk_int_pred_or_scalar_cmp(
            module_backend,
            builder,
            options,
            "yulang_mmtk_cps_int_eq_i64",
            ir::condcodes::IntCC::Equal,
            args,
        )?,
        typed_ir::PrimitiveOp::IntLt => mmtk_int_pred_or_scalar_cmp(
            module_backend,
            builder,
            options,
            "yulang_mmtk_cps_int_lt_i64",
            ir::condcodes::IntCC::SignedLessThan,
            args,
        )?,
        typed_ir::PrimitiveOp::IntLe => mmtk_int_pred_or_scalar_cmp(
            module_backend,
            builder,
            options,
            "yulang_mmtk_cps_int_le_i64",
            ir::condcodes::IntCC::SignedLessThanOrEqual,
            args,
        )?,
        typed_ir::PrimitiveOp::IntGt => mmtk_int_pred_or_scalar_cmp(
            module_backend,
            builder,
            options,
            "yulang_mmtk_cps_int_gt_i64",
            ir::condcodes::IntCC::SignedGreaterThan,
            args,
        )?,
        typed_ir::PrimitiveOp::IntGe => mmtk_int_pred_or_scalar_cmp(
            module_backend,
            builder,
            options,
            "yulang_mmtk_cps_int_ge_i64",
            ir::condcodes::IntCC::SignedGreaterThanOrEqual,
            args,
        )?,
        typed_ir::PrimitiveOp::FloatAdd => builder.ins().fadd(args[0], args[1]),
        typed_ir::PrimitiveOp::FloatSub => builder.ins().fsub(args[0], args[1]),
        typed_ir::PrimitiveOp::FloatMul => builder.ins().fmul(args[0], args[1]),
        typed_ir::PrimitiveOp::FloatDiv => builder.ins().fdiv(args[0], args[1]),
        typed_ir::PrimitiveOp::FloatEq => mmtk_float_pred_or_scalar_cmp(
            module_backend,
            builder,
            options,
            ir::condcodes::FloatCC::Equal,
            args,
        )?,
        typed_ir::PrimitiveOp::FloatLt => mmtk_float_pred_or_scalar_cmp(
            module_backend,
            builder,
            options,
            ir::condcodes::FloatCC::LessThan,
            args,
        )?,
        typed_ir::PrimitiveOp::FloatLe => mmtk_float_pred_or_scalar_cmp(
            module_backend,
            builder,
            options,
            ir::condcodes::FloatCC::LessThanOrEqual,
            args,
        )?,
        typed_ir::PrimitiveOp::FloatGt => mmtk_float_pred_or_scalar_cmp(
            module_backend,
            builder,
            options,
            ir::condcodes::FloatCC::GreaterThan,
            args,
        )?,
        typed_ir::PrimitiveOp::FloatGe => mmtk_float_pred_or_scalar_cmp(
            module_backend,
            builder,
            options,
            ir::condcodes::FloatCC::GreaterThanOrEqual,
            args,
        )?,
        typed_ir::PrimitiveOp::ListEmpty => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_list_empty_i64",
                "yulang_mmtk_cps_list_empty_i64",
            ),
            &[],
        )?,
        typed_ir::PrimitiveOp::ListSingleton => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_list_singleton_i64",
                "yulang_mmtk_cps_list_singleton_i64",
            ),
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::ListMerge => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_list_merge_i64",
                "yulang_mmtk_cps_list_merge_i64",
            ),
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::ListLen => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_list_len_i64",
                "yulang_mmtk_cps_list_len_i64",
            ),
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::ListIndex => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_list_index_i64",
                "yulang_mmtk_cps_list_index_i64",
            ),
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::ListIndexRangeRaw => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_list_index_range_raw_i64",
                "yulang_mmtk_cps_list_slice_i64",
            ),
            &[args[0], args[1], args[2]],
        )?,
        typed_ir::PrimitiveOp::ListIndexRange => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_list_index_range_i64",
                "yulang_mmtk_cps_list_slice_range_i64",
            ),
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::ListSpliceRaw => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_list_splice_raw_i64",
                "yulang_mmtk_cps_list_splice_i64",
            ),
            &[args[0], args[1], args[2], args[3]],
        )?,
        typed_ir::PrimitiveOp::ListSplice => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_list_splice_i64",
                "yulang_mmtk_cps_list_splice_range_i64",
            ),
            &[args[0], args[1], args[2]],
        )?,
        typed_ir::PrimitiveOp::ListViewRaw => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_list_view_raw_i64",
                "yulang_mmtk_cps_list_view_raw_i64",
            ),
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::IntToString => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_int_to_string_i64",
                "yulang_mmtk_cps_int_to_string_i64",
            ),
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::IntToHex => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_int_to_hex_i64",
                "yulang_mmtk_cps_int_to_hex_i64",
            ),
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::IntToUpperHex => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_int_to_upper_hex_i64",
                "yulang_mmtk_cps_int_to_upper_hex_i64",
            ),
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::BoolToString => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_bool_to_string_i64",
                "yulang_mmtk_cps_bool_to_string_i64",
            ),
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::FloatToString => call_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_float_to_string_f64",
                "yulang_mmtk_cps_float_to_string_f64",
            ),
            &[types::F64],
            types::I64,
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::StringConcat => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_string_concat_i64",
                "yulang_mmtk_cps_string_concat_i64",
            ),
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::StringEq => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_string_eq_i64",
                "yulang_mmtk_cps_string_eq_i64",
            ),
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::StringLen => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_string_len_i64",
                "yulang_mmtk_cps_string_len_i64",
            ),
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::StringIndex => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_string_index_i64",
                "yulang_mmtk_cps_string_index_i64",
            ),
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::StringIndexRangeRaw => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_string_index_range_raw_i64",
                "yulang_mmtk_cps_string_slice_i64",
            ),
            &[args[0], args[1], args[2]],
        )?,
        typed_ir::PrimitiveOp::StringIndexRange => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_string_index_range_i64",
                "yulang_mmtk_cps_string_slice_range_i64",
            ),
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::StringSpliceRaw => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_string_splice_raw_i64",
                "yulang_mmtk_cps_string_splice_i64",
            ),
            &[args[0], args[1], args[2], args[3]],
        )?,
        typed_ir::PrimitiveOp::StringSplice => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_string_splice_i64",
                "yulang_mmtk_cps_string_splice_range_i64",
            ),
            &[args[0], args[1], args[2]],
        )?,
        typed_ir::PrimitiveOp::StringToBytes => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_string_to_bytes_i64",
                "yulang_mmtk_cps_string_to_bytes_i64",
            ),
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::BytesLen => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_bytes_len_i64",
                "yulang_mmtk_cps_bytes_len_i64",
            ),
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::BytesEq => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_bytes_eq_i64",
                "yulang_mmtk_cps_bytes_eq_i64",
            ),
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::BytesConcat => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_bytes_concat_i64",
                "yulang_mmtk_cps_bytes_concat_i64",
            ),
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::BytesIndex => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_bytes_index_i64",
                "yulang_mmtk_cps_bytes_index_i64",
            ),
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::BytesIndexRange => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_bytes_index_range_i64",
                "yulang_mmtk_cps_bytes_slice_range_i64",
            ),
            &[args[0], args[1]],
        )?,
        typed_ir::PrimitiveOp::BytesToUtf8Raw => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_bytes_to_utf8_raw_i64",
                "yulang_mmtk_cps_bytes_to_utf8_raw_i64",
            ),
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::BytesToPath => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_bytes_to_path_i64",
                "yulang_mmtk_cps_bytes_to_path_i64",
            ),
            &[args[0]],
        )?,
        typed_ir::PrimitiveOp::PathToBytes => call_i64_helper(
            module_backend,
            builder,
            yvalue_primitive_helper(
                options,
                "yulang_cps_path_to_bytes_i64",
                "yulang_mmtk_cps_path_to_bytes_i64",
            ),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MmtkI63AddSubOp {
    Add,
    Sub,
}

fn mmtk_i63_add_sub_or_helper<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    helper_name: &'static str,
    left: ir::Value,
    right: ir::Value,
    op: MmtkI63AddSubOp,
) -> CpsReprCraneliftResult<ir::Value> {
    const YVALUE_I63_TAG: i64 = 1;
    const YVALUE_I63_MIN: i64 = -(1_i64 << 62);
    const YVALUE_I63_MAX: i64 = (1_i64 << 62) - 1;

    let fast_block = builder.create_block();
    let upper_bound_block = builder.create_block();
    let encode_block = builder.create_block();
    let fallback_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64);

    let both_tags = builder.ins().band(left, right);
    let both_tags = builder.ins().band_imm(both_tags, YVALUE_I63_TAG);
    let both_i63 = builder
        .ins()
        .icmp_imm(ir::condcodes::IntCC::Equal, both_tags, YVALUE_I63_TAG);
    builder
        .ins()
        .brif(both_i63, fast_block, &[], fallback_block, &[]);

    builder.switch_to_block(fast_block);
    builder.seal_block(fast_block);
    let left_raw = builder.ins().sshr_imm(left, 1);
    let right_raw = builder.ins().sshr_imm(right, 1);
    let raw = match op {
        MmtkI63AddSubOp::Add => builder.ins().iadd(left_raw, right_raw),
        MmtkI63AddSubOp::Sub => builder.ins().isub(left_raw, right_raw),
    };
    let above_min = builder.ins().icmp_imm(
        ir::condcodes::IntCC::SignedGreaterThanOrEqual,
        raw,
        YVALUE_I63_MIN,
    );
    builder
        .ins()
        .brif(above_min, upper_bound_block, &[], fallback_block, &[]);

    builder.switch_to_block(upper_bound_block);
    builder.seal_block(upper_bound_block);
    let below_max = builder.ins().icmp_imm(
        ir::condcodes::IntCC::SignedLessThanOrEqual,
        raw,
        YVALUE_I63_MAX,
    );
    builder
        .ins()
        .brif(below_max, encode_block, &[], fallback_block, &[]);

    builder.switch_to_block(encode_block);
    builder.seal_block(encode_block);
    let encoded = builder.ins().ishl_imm(raw, 1);
    let encoded = builder.ins().bor_imm(encoded, YVALUE_I63_TAG);
    builder
        .ins()
        .jump(done_block, &[ir::BlockArg::Value(encoded)]);

    builder.switch_to_block(fallback_block);
    builder.seal_block(fallback_block);
    let fallback = call_i64_helper(module_backend, builder, helper_name, &[left, right])?;
    builder
        .ins()
        .jump(done_block, &[ir::BlockArg::Value(fallback)]);

    builder.switch_to_block(done_block);
    builder.seal_block(done_block);
    Ok(builder.block_params(done_block)[0])
}

fn mmtk_int_pred_or_scalar_cmp<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    options: CpsReprCraneliftOptions,
    mmtk_helper: &'static str,
    scalar_code: ir::condcodes::IntCC,
    args: &[ir::Value],
) -> CpsReprCraneliftResult<ir::Value> {
    if mmtk_yvalue_primitive_lane_enabled(options) {
        return mmtk_i63_compare_or_helper(
            module_backend,
            builder,
            mmtk_helper,
            scalar_code,
            args[0],
            args[1],
        );
    }
    Ok(int_cmp(builder, scalar_code, args))
}

fn mmtk_i63_compare_or_helper<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    helper_name: &'static str,
    code: ir::condcodes::IntCC,
    left: ir::Value,
    right: ir::Value,
) -> CpsReprCraneliftResult<ir::Value> {
    const YVALUE_I63_TAG: i64 = 1;
    const YVALUE_FALSE_BITS: i64 = 0b010;
    const YVALUE_TRUE_BITS: i64 = 0b110;

    let fast_block = builder.create_block();
    let fallback_block = builder.create_block();
    let done_block = builder.create_block();
    builder.append_block_param(done_block, types::I64);

    let both_tags = builder.ins().band(left, right);
    let both_tags = builder.ins().band_imm(both_tags, YVALUE_I63_TAG);
    let both_i63 = builder
        .ins()
        .icmp_imm(ir::condcodes::IntCC::Equal, both_tags, YVALUE_I63_TAG);
    builder
        .ins()
        .brif(both_i63, fast_block, &[], fallback_block, &[]);

    builder.switch_to_block(fast_block);
    builder.seal_block(fast_block);
    let left_raw = builder.ins().sshr_imm(left, 1);
    let right_raw = builder.ins().sshr_imm(right, 1);
    let cmp = builder.ins().icmp(code, left_raw, right_raw);
    let true_value = builder.ins().iconst(types::I64, YVALUE_TRUE_BITS);
    let false_value = builder.ins().iconst(types::I64, YVALUE_FALSE_BITS);
    let value = builder.ins().select(cmp, true_value, false_value);
    builder
        .ins()
        .jump(done_block, &[ir::BlockArg::Value(value)]);

    builder.switch_to_block(fallback_block);
    builder.seal_block(fallback_block);
    let fallback = call_i64_helper(module_backend, builder, helper_name, &[left, right])?;
    builder
        .ins()
        .jump(done_block, &[ir::BlockArg::Value(fallback)]);

    builder.switch_to_block(done_block);
    builder.seal_block(done_block);
    Ok(builder.block_params(done_block)[0])
}

fn float_cmp(
    builder: &mut FunctionBuilder<'_>,
    code: ir::condcodes::FloatCC,
    args: &[ir::Value],
) -> ir::Value {
    let cmp = builder.ins().fcmp(code, args[0], args[1]);
    builder.ins().uextend(types::I64, cmp)
}

fn mmtk_float_pred_or_scalar_cmp<M: Module>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    options: CpsReprCraneliftOptions,
    code: ir::condcodes::FloatCC,
    args: &[ir::Value],
) -> CpsReprCraneliftResult<ir::Value> {
    let value = float_cmp(builder, code, args);
    if mmtk_yvalue_primitive_lane_enabled(options) {
        return call_i64_helper(
            module_backend,
            builder,
            "yulang_mmtk_cps_box_bool_i64",
            &[value],
        );
    }
    Ok(value)
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
        typed_ir::PrimitiveOp::YadaYada => Err(CpsReprCraneliftError::UnsupportedPrimitive {
            function: _function.name.clone(),
            op,
        }),
        typed_ir::PrimitiveOp::CharEq
        | typed_ir::PrimitiveOp::CharToString
        | typed_ir::PrimitiveOp::CharIsWhitespace
        | typed_ir::PrimitiveOp::CharIsPunctuation
        | typed_ir::PrimitiveOp::CharIsWord => Err(CpsReprCraneliftError::UnsupportedPrimitive {
            function: _function.name.clone(),
            op,
        }),
        typed_ir::PrimitiveOp::BoolNot
        | typed_ir::PrimitiveOp::BoolEq
        | typed_ir::PrimitiveOp::IntAdd
        | typed_ir::PrimitiveOp::IntSub
        | typed_ir::PrimitiveOp::IntMul
        | typed_ir::PrimitiveOp::IntDiv
        | typed_ir::PrimitiveOp::IntMod
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

fn read_primitive_args<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    literals: &mut L,
    local_values: &LocalValueCache,
    op: typed_ir::PrimitiveOp,
    values: &[CpsValueId],
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<Vec<ir::Value>> {
    if mmtk_yvalue_primitive_lane_enabled(options) {
        return values
            .iter()
            .enumerate()
            .map(|(index, value)| {
                let lane = primitive_arg_lanes(op)
                    .and_then(|lanes| lanes.get(index).copied())
                    .unwrap_or(CpsReprAbiLane::RuntimeValuePtr);
                if lane == CpsReprAbiLane::NativeFloat {
                    return read_native_float_value(
                        module_backend,
                        builder,
                        function,
                        local_values,
                        *value,
                    );
                }
                read_runtime_value_i64(
                    module_backend,
                    builder,
                    function,
                    literals,
                    local_values,
                    *value,
                    options,
                )
            })
            .collect();
    }

    if op == typed_ir::PrimitiveOp::ListSingleton {
        return read_runtime_values_i64(
            module_backend,
            builder,
            function,
            literals,
            local_values,
            values,
            options,
        );
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

fn read_runtime_values_i64<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    literals: &mut L,
    local_values: &LocalValueCache,
    values: &[CpsValueId],
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<Vec<ir::Value>> {
    values
        .iter()
        .map(|value| {
            read_runtime_value_i64(
                module_backend,
                builder,
                function,
                literals,
                local_values,
                *value,
                options,
            )
        })
        .collect()
}

fn read_runtime_value_i64<M: Module, L: CpsLiteralStore>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &CpsReprAbiFunction,
    _literals: &mut L,
    local_values: &LocalValueCache,
    value: CpsValueId,
    options: CpsReprCraneliftOptions,
) -> CpsReprCraneliftResult<ir::Value> {
    if mmtk_yvalue_primitive_lane_enabled(options) {
        if let Some(literal) = value_literal(function, value) {
            match literal {
                CpsLiteral::Int(_)
                | CpsLiteral::Bool(_)
                | CpsLiteral::Unit
                | CpsLiteral::String(_) => return read_value(builder, function, value),
                CpsLiteral::Float(_) => {
                    return Err(CpsReprCraneliftError::UnsupportedLane {
                        function: function.name.clone(),
                        value,
                        lane: CpsReprAbiLane::NativeFloat,
                    });
                }
            }
        }

        let lane = effective_value_lane(function, value);
        return match lane {
            CpsReprAbiLane::ScalarI64
            | CpsReprAbiLane::RuntimeValuePtr
            | CpsReprAbiLane::ClosurePtr
            | CpsReprAbiLane::ThunkPtr
            | CpsReprAbiLane::ResumptionPtr
            | CpsReprAbiLane::OpaqueI64
            | CpsReprAbiLane::Unknown => read_value(builder, function, value),
            lane => Err(CpsReprCraneliftError::UnsupportedLane {
                function: function.name.clone(),
                value,
                lane,
            }),
        };
    }

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
        typed_ir::PrimitiveOp::YadaYada => CpsReprAbiLane::Unknown,
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
        | typed_ir::PrimitiveOp::IntMod
        | typed_ir::PrimitiveOp::ListLen
        | typed_ir::PrimitiveOp::StringLen
        | typed_ir::PrimitiveOp::BytesLen
        | typed_ir::PrimitiveOp::BytesIndex
        | typed_ir::PrimitiveOp::CharEq
        | typed_ir::PrimitiveOp::CharIsWhitespace
        | typed_ir::PrimitiveOp::CharIsPunctuation
        | typed_ir::PrimitiveOp::CharIsWord
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
        | typed_ir::PrimitiveOp::BoolToString
        | typed_ir::PrimitiveOp::CharToString => CpsReprAbiLane::RuntimeValuePtr,
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

#[cfg(test)]
mod tests {
    use crate::cps_ir::{
        CpsContinuation, CpsFunction, CpsLiteral, CpsModule, CpsShotKind, CpsStmt, CpsTerminator,
        CpsValueId,
    };
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
    fn jit_preserves_unit_literal_after_continuation_hop_in_runtime_tuple() {
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
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Unit,
                        }],
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(1),
                            args: vec![CpsValueId(0)],
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(1)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Tuple {
                            dest: CpsValueId(2),
                            items: vec![CpsValueId(1)],
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(2)),
                    },
                ],
            }],
        }));
        let mut jit = compile_cps_repr_abi_module(&abi).expect("compiled");

        assert_eq!(jit.run_roots_display().expect("ran"), vec!["((),)"]);
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
                        ownership: None,
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
                            ownership: None,
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
    fn jit_can_opt_into_mmtk_yvalue_string_bytes_primitives() {
        let _guard = crate::mmtk_runtime::mmtk_test_lock();
        let options = CpsReprCraneliftOptions::mmtk_yvalue_primitives();
        let cases = vec![
            (
                primitive_call(
                    typed_ir::PrimitiveOp::StringLen,
                    vec![unknown_lit(typed_ir::Lit::String("aあ🙂".to_string()))],
                ),
                mmtk_i63(3),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::StringLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::StringConcat,
                        vec![
                            unknown_lit(typed_ir::Lit::String("yu".to_string())),
                            unknown_lit(typed_ir::Lit::String("lang".to_string())),
                        ],
                    )],
                ),
                mmtk_i63(6),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::BytesLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::BytesConcat,
                        vec![
                            primitive_call(
                                typed_ir::PrimitiveOp::StringToBytes,
                                vec![unknown_lit(typed_ir::Lit::String("ab".to_string()))],
                            ),
                            primitive_call(
                                typed_ir::PrimitiveOp::StringToBytes,
                                vec![unknown_lit(typed_ir::Lit::String("cd".to_string()))],
                            ),
                        ],
                    )],
                ),
                mmtk_i63(4),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::BytesEq,
                    vec![
                        primitive_call(
                            typed_ir::PrimitiveOp::StringToBytes,
                            vec![unknown_lit(typed_ir::Lit::String("ok".to_string()))],
                        ),
                        primitive_call(
                            typed_ir::PrimitiveOp::StringToBytes,
                            vec![unknown_lit(typed_ir::Lit::String("ok".to_string()))],
                        ),
                    ],
                ),
                mmtk_bool(true),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::BytesIndex,
                    vec![
                        primitive_call(
                            typed_ir::PrimitiveOp::StringToBytes,
                            vec![unknown_lit(typed_ir::Lit::String("abc".to_string()))],
                        ),
                        unknown_lit(typed_ir::Lit::Int("1".to_string())),
                    ],
                ),
                mmtk_i63(i64::from(b'b')),
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
                mmtk_i63(4),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::StringLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::StringIndexRangeRaw,
                        vec![
                            unknown_lit(typed_ir::Lit::String("aあ🙂z".to_string())),
                            unknown_lit(typed_ir::Lit::Int("1".to_string())),
                            unknown_lit(typed_ir::Lit::Int("3".to_string())),
                        ],
                    )],
                ),
                mmtk_i63(2),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::StringLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::StringIndex,
                        vec![
                            unknown_lit(typed_ir::Lit::String("aあ🙂z".to_string())),
                            unknown_lit(typed_ir::Lit::Int("2".to_string())),
                        ],
                    )],
                ),
                mmtk_i63(1),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::StringLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::StringIndexRange,
                        vec![
                            unknown_lit(typed_ir::Lit::String("aあ🙂z".to_string())),
                            range_expr(1, 3),
                        ],
                    )],
                ),
                mmtk_i63(2),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::StringLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::StringSpliceRaw,
                        vec![
                            unknown_lit(typed_ir::Lit::String("abcz".to_string())),
                            unknown_lit(typed_ir::Lit::Int("1".to_string())),
                            unknown_lit(typed_ir::Lit::Int("3".to_string())),
                            unknown_lit(typed_ir::Lit::String("XY".to_string())),
                        ],
                    )],
                ),
                mmtk_i63(4),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::StringLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::StringSplice,
                        vec![
                            unknown_lit(typed_ir::Lit::String("abcz".to_string())),
                            range_expr(1, 3),
                            unknown_lit(typed_ir::Lit::String("XY".to_string())),
                        ],
                    )],
                ),
                mmtk_i63(4),
            ),
            (
                primitive_call(typed_ir::PrimitiveOp::ListLen, vec![list_expr(vec![1, 2])]),
                mmtk_i63(2),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::StringLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::ListIndex,
                        vec![
                            primitive_call(
                                typed_ir::PrimitiveOp::ListMerge,
                                vec![
                                    primitive_call(
                                        typed_ir::PrimitiveOp::ListSingleton,
                                        vec![unknown_lit(typed_ir::Lit::String("a".to_string()))],
                                    ),
                                    primitive_call(
                                        typed_ir::PrimitiveOp::ListSingleton,
                                        vec![unknown_lit(typed_ir::Lit::String(
                                            "abcd".to_string(),
                                        ))],
                                    ),
                                ],
                            ),
                            unknown_lit(typed_ir::Lit::Int("1".to_string())),
                        ],
                    )],
                ),
                mmtk_i63(4),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::ListLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::ListIndexRangeRaw,
                        vec![
                            list_expr(vec![1, 2, 3, 4]),
                            unknown_lit(typed_ir::Lit::Int("1".to_string())),
                            unknown_lit(typed_ir::Lit::Int("3".to_string())),
                        ],
                    )],
                ),
                mmtk_i63(2),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::ListLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::ListIndexRange,
                        vec![list_expr(vec![1, 2, 3, 4]), range_expr(1, 3)],
                    )],
                ),
                mmtk_i63(2),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::ListLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::ListSpliceRaw,
                        vec![
                            list_expr(vec![1, 2, 3]),
                            unknown_lit(typed_ir::Lit::Int("1".to_string())),
                            unknown_lit(typed_ir::Lit::Int("2".to_string())),
                            list_expr(vec![8, 9]),
                        ],
                    )],
                ),
                mmtk_i63(4),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::ListLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::ListSplice,
                        vec![
                            list_expr(vec![1, 2, 3]),
                            range_expr(1, 2),
                            list_expr(vec![8, 9]),
                        ],
                    )],
                ),
                mmtk_i63(4),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::BytesLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::BytesIndexRange,
                        vec![
                            primitive_call(
                                typed_ir::PrimitiveOp::StringToBytes,
                                vec![unknown_lit(typed_ir::Lit::String("abcde".to_string()))],
                            ),
                            range_expr(1, 4),
                        ],
                    )],
                ),
                mmtk_i63(3),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::StringLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::IntToString,
                        vec![unknown_lit(typed_ir::Lit::Int("-42".to_string()))],
                    )],
                ),
                mmtk_i63(3),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::StringLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::IntToString,
                        vec![primitive_call(
                            typed_ir::PrimitiveOp::IntAdd,
                            vec![
                                unknown_lit(typed_ir::Lit::Int("1".to_string())),
                                unknown_lit(typed_ir::Lit::Int("2".to_string())),
                            ],
                        )],
                    )],
                ),
                mmtk_i63(1),
            ),
            (
                if_expr(
                    primitive_call(
                        typed_ir::PrimitiveOp::IntLt,
                        vec![
                            unknown_lit(typed_ir::Lit::Int("1".to_string())),
                            unknown_lit(typed_ir::Lit::Int("2".to_string())),
                        ],
                    ),
                    unknown_lit(typed_ir::Lit::Int("7".to_string())),
                    unknown_lit(typed_ir::Lit::Int("9".to_string())),
                ),
                mmtk_i63(7),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::StringLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::IntToHex,
                        vec![unknown_lit(typed_ir::Lit::Int("255".to_string()))],
                    )],
                ),
                mmtk_i63(2),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::StringLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::IntToUpperHex,
                        vec![unknown_lit(typed_ir::Lit::Int("255".to_string()))],
                    )],
                ),
                mmtk_i63(2),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::StringLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::BoolToString,
                        vec![unknown_lit(typed_ir::Lit::Bool(false))],
                    )],
                ),
                mmtk_i63(5),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::StringLen,
                    vec![primitive_call(
                        typed_ir::PrimitiveOp::FloatToString,
                        vec![unknown_lit(typed_ir::Lit::Float("1.0".to_string()))],
                    )],
                ),
                mmtk_i63(3),
            ),
            (
                primitive_call(
                    typed_ir::PrimitiveOp::StringLen,
                    vec![select(
                        record(vec![(
                            "name",
                            unknown_lit(typed_ir::Lit::String("yulang".to_string())),
                        )]),
                        "name",
                    )],
                ),
                mmtk_i63(6),
            ),
        ];

        for (expr, expected) in cases {
            crate::mmtk_runtime::yulang_mmtk_cps_reset_i64();
            let mut jit = compile_runtime_module_to_cps_repr_jit_with_options(
                &module_with_root(expr),
                options,
            )
            .expect("compiled runtime module with MMTk YValue primitives");

            assert_eq!(jit.run_roots_i64().expect("ran"), vec![expected]);
        }
    }
    #[test]
    fn mmtk_yvalue_primitive_lane_runs_list_view_raw() {
        let _guard = crate::mmtk_runtime::mmtk_test_lock();
        let expr = primitive_call(
            typed_ir::PrimitiveOp::ListViewRaw,
            vec![list_expr(vec![1, 2])],
        );

        crate::mmtk_runtime::yulang_mmtk_cps_reset_i64();
        let mut jit = compile_runtime_module_to_cps_repr_jit_with_options(
            &module_with_root(expr),
            CpsReprCraneliftOptions::mmtk_yvalue_primitives(),
        )
        .expect("compiled list view with MMTk YValue primitives");

        let roots = jit.run_roots_i64().expect("ran");
        assert_eq!(roots.len(), 1);
        assert_ne!(roots[0], 0);
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
                                ownership: None,
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
                            ownership: None,
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
                            ownership: None,
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
                            ownership: None,
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
                            ownership: None,
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
                            ownership: None,
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
    fn mmtk_i63(value: i64) -> i64 {
        crate::gc_runtime::YValue::from_i63(value)
            .expect("test integer should fit i63")
            .raw() as i64
    }
    fn mmtk_bool(value: bool) -> i64 {
        crate::gc_runtime::YValue::from_bool(value).raw() as i64
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
    fn select(base: runtime::Expr, field: &str) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Select {
                base: Box::new(base),
                field: typed_ir::Name(field.to_string()),
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
