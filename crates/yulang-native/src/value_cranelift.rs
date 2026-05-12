use std::collections::{HashMap, HashSet};
use std::fmt;

use cranelift_codegen::ir::{self, AbiParam, InstBuilder, types};
use cranelift_codegen::settings;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use yulang_runtime as runtime;

use crate::abi::{NativeAbiFunction, NativeAbiModule, NativeAbiStmt};
use crate::abi_validate::{NativeAbiValidateError, validate_abi_module};
use crate::control_ir::{BlockId, NativeLiteral, NativeTerminator, ValueId};
use crate::native_runtime::{
    NATIVE_PRIMITIVE_BOOL_EQ, NATIVE_PRIMITIVE_BOOL_NOT, NATIVE_PRIMITIVE_BOOL_TO_STRING,
    NATIVE_PRIMITIVE_FLOAT_ADD, NATIVE_PRIMITIVE_FLOAT_DIV, NATIVE_PRIMITIVE_FLOAT_EQ,
    NATIVE_PRIMITIVE_FLOAT_GE, NATIVE_PRIMITIVE_FLOAT_GT, NATIVE_PRIMITIVE_FLOAT_LE,
    NATIVE_PRIMITIVE_FLOAT_LT, NATIVE_PRIMITIVE_FLOAT_MUL, NATIVE_PRIMITIVE_FLOAT_SUB,
    NATIVE_PRIMITIVE_FLOAT_TO_STRING, NATIVE_PRIMITIVE_INT_ADD, NATIVE_PRIMITIVE_INT_DIV,
    NATIVE_PRIMITIVE_INT_EQ, NATIVE_PRIMITIVE_INT_GE, NATIVE_PRIMITIVE_INT_GT,
    NATIVE_PRIMITIVE_INT_LE, NATIVE_PRIMITIVE_INT_LT, NATIVE_PRIMITIVE_INT_MUL,
    NATIVE_PRIMITIVE_INT_SUB, NATIVE_PRIMITIVE_INT_TO_HEX, NATIVE_PRIMITIVE_INT_TO_STRING,
    NATIVE_PRIMITIVE_INT_TO_UPPER_HEX, NATIVE_PRIMITIVE_STRING_INDEX, NATIVE_PRIMITIVE_STRING_LEN,
    NativeRuntimeContext, yulang_native_concat_string, yulang_native_list_empty,
    yulang_native_list_index, yulang_native_list_index_range, yulang_native_list_index_range_raw,
    yulang_native_list_len, yulang_native_list_merge, yulang_native_list_singleton,
    yulang_native_make_bool, yulang_native_make_float, yulang_native_make_int,
    yulang_native_make_string, yulang_native_make_unit, yulang_native_primitive_binary,
    yulang_native_primitive_unary, yulang_native_record_empty, yulang_native_record_insert,
    yulang_native_record_select, yulang_native_tuple_empty, yulang_native_tuple_push,
    yulang_native_variant,
};

pub type NativeValueCraneliftResult<T> = Result<T, NativeValueCraneliftError>;

#[derive(Debug)]
pub enum NativeValueCraneliftError {
    AbiInvalid(NativeAbiValidateError),
    UnsupportedFunction {
        function: String,
        reason: &'static str,
    },
    UnsupportedStmt {
        function: String,
        kind: &'static str,
    },
    UnsupportedLiteral {
        function: String,
        literal: NativeLiteral,
    },
    MissingBlock {
        function: String,
        block: BlockId,
    },
    MissingValue {
        function: String,
        value: ValueId,
    },
    InvalidReturnArity {
        function: String,
        arity: usize,
    },
    Cranelift(String),
}

impl fmt::Display for NativeValueCraneliftError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeValueCraneliftError::AbiInvalid(error) => write!(f, "{error}"),
            NativeValueCraneliftError::UnsupportedFunction { function, reason } => {
                write!(
                    f,
                    "native value Cranelift prototype does not support `{function}` yet: {reason}"
                )
            }
            NativeValueCraneliftError::UnsupportedStmt { function, kind } => write!(
                f,
                "native value Cranelift prototype does not support {kind} statements in `{function}` yet"
            ),
            NativeValueCraneliftError::UnsupportedLiteral { function, literal } => write!(
                f,
                "native value Cranelift prototype does not support literal {literal:?} in `{function}` yet"
            ),
            NativeValueCraneliftError::MissingBlock { function, block } => {
                write!(
                    f,
                    "native value Cranelift block {block:?} is missing in `{function}`"
                )
            }
            NativeValueCraneliftError::MissingValue { function, value } => write!(
                f,
                "native value Cranelift value {value:?} is missing in `{function}`"
            ),
            NativeValueCraneliftError::InvalidReturnArity { function, arity } => write!(
                f,
                "native value Cranelift function `{function}` has {arity} return values"
            ),
            NativeValueCraneliftError::Cranelift(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for NativeValueCraneliftError {}

impl From<NativeAbiValidateError> for NativeValueCraneliftError {
    fn from(error: NativeAbiValidateError) -> Self {
        NativeValueCraneliftError::AbiInvalid(error)
    }
}

pub struct NativeValueJitModule {
    module: JITModule,
    roots: Vec<FuncId>,
    strings: Vec<Box<str>>,
}

impl NativeValueJitModule {
    pub fn run_roots(&mut self) -> NativeValueCraneliftResult<Vec<runtime::VmValue>> {
        self.module
            .finalize_definitions()
            .map_err(cranelift_error)?;
        let _string_literals_are_kept_alive = self.strings.len();
        self.roots
            .iter()
            .map(|root| {
                let ptr = self.module.get_finalized_function(*root);
                let call = unsafe {
                    std::mem::transmute::<
                        _,
                        extern "C" fn(*mut NativeRuntimeContext) -> *mut runtime::VmValue,
                    >(ptr)
                };
                let mut context = NativeRuntimeContext::new();
                let value = call(&mut context);
                if value.is_null() {
                    return Err(NativeValueCraneliftError::Cranelift(
                        "native value root returned null".to_string(),
                    ));
                }
                Ok(unsafe { (*value).clone() })
            })
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeValueObjectModule {
    bytes: Vec<u8>,
    roots: Vec<String>,
}

impl NativeValueObjectModule {
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

pub fn compile_value_abi_module(
    module: &NativeAbiModule,
) -> NativeValueCraneliftResult<NativeValueJitModule> {
    validate_abi_module(module)?;
    validate_value_prototype_subset(module)?;

    let mut builder =
        JITBuilder::new(cranelift_module::default_libcall_names()).map_err(cranelift_error)?;
    builder.symbol(
        "yulang_native_make_string",
        yulang_native_make_string as *const u8,
    );
    builder.symbol(
        "yulang_native_make_int",
        yulang_native_make_int as *const u8,
    );
    builder.symbol(
        "yulang_native_make_float",
        yulang_native_make_float as *const u8,
    );
    builder.symbol(
        "yulang_native_make_bool",
        yulang_native_make_bool as *const u8,
    );
    builder.symbol(
        "yulang_native_make_unit",
        yulang_native_make_unit as *const u8,
    );
    builder.symbol(
        "yulang_native_concat_string",
        yulang_native_concat_string as *const u8,
    );
    builder.symbol(
        "yulang_native_primitive_unary",
        yulang_native_primitive_unary as *const u8,
    );
    builder.symbol(
        "yulang_native_primitive_binary",
        yulang_native_primitive_binary as *const u8,
    );
    builder.symbol(
        "yulang_native_list_empty",
        yulang_native_list_empty as *const u8,
    );
    builder.symbol(
        "yulang_native_list_singleton",
        yulang_native_list_singleton as *const u8,
    );
    builder.symbol(
        "yulang_native_list_merge",
        yulang_native_list_merge as *const u8,
    );
    builder.symbol(
        "yulang_native_list_len",
        yulang_native_list_len as *const u8,
    );
    builder.symbol(
        "yulang_native_list_index",
        yulang_native_list_index as *const u8,
    );
    builder.symbol(
        "yulang_native_list_index_range",
        yulang_native_list_index_range as *const u8,
    );
    builder.symbol(
        "yulang_native_list_index_range_raw",
        yulang_native_list_index_range_raw as *const u8,
    );
    builder.symbol(
        "yulang_native_tuple_empty",
        yulang_native_tuple_empty as *const u8,
    );
    builder.symbol(
        "yulang_native_tuple_push",
        yulang_native_tuple_push as *const u8,
    );
    builder.symbol(
        "yulang_native_record_empty",
        yulang_native_record_empty as *const u8,
    );
    builder.symbol(
        "yulang_native_record_insert",
        yulang_native_record_insert as *const u8,
    );
    builder.symbol(
        "yulang_native_record_select",
        yulang_native_record_select as *const u8,
    );
    builder.symbol("yulang_native_variant", yulang_native_variant as *const u8);
    let mut jit = JITModule::new(builder);

    let helpers = declare_helpers(&mut jit)?;
    let mut strings = Vec::new();
    let functions = declare_functions(&mut jit, module)?;
    let mut literals = HostLiteralStore {
        strings: &mut strings,
    };
    define_functions(&mut jit, module, &functions, &helpers, &mut literals)?;
    Ok(NativeValueJitModule {
        module: jit,
        roots: module
            .roots
            .iter()
            .map(|root| {
                functions.get(&root.name).copied().ok_or_else(|| {
                    NativeValueCraneliftError::UnsupportedFunction {
                        function: root.name.clone(),
                        reason: "root was not declared",
                    }
                })
            })
            .collect::<NativeValueCraneliftResult<Vec<_>>>()?,
        strings,
    })
}

pub fn compile_value_abi_module_to_object(
    module: &NativeAbiModule,
) -> NativeValueCraneliftResult<NativeValueObjectModule> {
    validate_abi_module(module)?;
    validate_value_prototype_subset(module)?;

    let isa_builder = cranelift_native::builder().map_err(cranelift_error)?;
    let flags = settings::Flags::new(settings::builder());
    let isa = isa_builder.finish(flags).map_err(cranelift_error)?;
    let builder = ObjectBuilder::new(
        isa,
        "yulang_native_value_object".to_string(),
        cranelift_module::default_libcall_names(),
    )
    .map_err(cranelift_error)?;
    let mut object = ObjectModule::new(builder);

    let helpers = declare_helpers(&mut object)?;
    let functions = declare_functions(&mut object, module)?;
    let mut literals = ObjectLiteralStore::default();
    define_functions(&mut object, module, &functions, &helpers, &mut literals)?;
    let roots = module
        .roots
        .iter()
        .map(|root| root.name.clone())
        .collect::<Vec<_>>();
    let product = object.finish();
    let bytes = product.emit().map_err(cranelift_error)?;
    Ok(NativeValueObjectModule { bytes, roots })
}

fn validate_value_prototype_subset(module: &NativeAbiModule) -> NativeValueCraneliftResult<()> {
    for function in module.functions.iter().chain(&module.roots) {
        if function.environment_slots != 0 {
            return Err(NativeValueCraneliftError::UnsupportedFunction {
                function: function.name.clone(),
                reason: "environment slots",
            });
        }
        for block in &function.blocks {
            for stmt in &block.stmts {
                match stmt {
                    NativeAbiStmt::Literal {
                        literal:
                            NativeLiteral::Int(_)
                            | NativeLiteral::Float(_)
                            | NativeLiteral::Bool(_)
                            | NativeLiteral::Unit,
                        ..
                    } => {}
                    NativeAbiStmt::Literal {
                        literal: NativeLiteral::String(_),
                        ..
                    } => {}
                    NativeAbiStmt::Primitive {
                        op: yulang_typed_ir::PrimitiveOp::StringConcat,
                        ..
                    } => {}
                    NativeAbiStmt::Primitive {
                        op:
                            yulang_typed_ir::PrimitiveOp::ListEmpty
                            | yulang_typed_ir::PrimitiveOp::ListSingleton
                            | yulang_typed_ir::PrimitiveOp::ListMerge
                            | yulang_typed_ir::PrimitiveOp::ListLen
                            | yulang_typed_ir::PrimitiveOp::ListIndex
                            | yulang_typed_ir::PrimitiveOp::ListIndexRange
                            | yulang_typed_ir::PrimitiveOp::ListIndexRangeRaw,
                        ..
                    } => {}
                    NativeAbiStmt::Primitive { op, .. }
                        if primitive_unary_code(*op).is_some()
                            || primitive_binary_code(*op).is_some() => {}
                    NativeAbiStmt::Primitive { .. } => {
                        return Err(NativeValueCraneliftError::UnsupportedStmt {
                            function: function.name.clone(),
                            kind: "primitive",
                        });
                    }
                    NativeAbiStmt::DirectCall { .. } => {}
                    NativeAbiStmt::Tuple { .. }
                    | NativeAbiStmt::Record { .. }
                    | NativeAbiStmt::Variant { .. }
                    | NativeAbiStmt::Select { .. } => {}
                    NativeAbiStmt::LoadEnv { .. } => {
                        return Err(NativeValueCraneliftError::UnsupportedStmt {
                            function: function.name.clone(),
                            kind: "environment load",
                        });
                    }
                    NativeAbiStmt::AllocateClosure { .. } => {
                        return Err(NativeValueCraneliftError::UnsupportedStmt {
                            function: function.name.clone(),
                            kind: "closure allocation",
                        });
                    }
                    NativeAbiStmt::IndirectClosureCall { .. } => {
                        return Err(NativeValueCraneliftError::UnsupportedStmt {
                            function: function.name.clone(),
                            kind: "indirect closure call",
                        });
                    }
                }
            }
            match &block.terminator {
                NativeTerminator::Return(_) => {}
                NativeTerminator::Jump { .. } | NativeTerminator::Branch { .. } => {
                    return Err(NativeValueCraneliftError::UnsupportedFunction {
                        function: function.name.clone(),
                        reason: "multi-block control flow",
                    });
                }
            }
        }
    }
    Ok(())
}

fn declare_functions<M: Module>(
    module_backend: &mut M,
    module: &NativeAbiModule,
) -> NativeValueCraneliftResult<HashMap<String, FuncId>> {
    let mut functions = HashMap::new();
    for function in module.functions.iter().chain(&module.roots) {
        let sig = value_function_signature(module_backend, function);
        let id = module_backend
            .declare_function(&function.name, Linkage::Export, &sig)
            .map_err(cranelift_error)?;
        functions.insert(function.name.clone(), id);
    }
    Ok(functions)
}

fn define_functions<M: Module, L: ValueLiteralStore>(
    module_backend: &mut M,
    module: &NativeAbiModule,
    functions: &HashMap<String, FuncId>,
    helpers: &ValueHelpers,
    literals: &mut L,
) -> NativeValueCraneliftResult<()> {
    for function in module.functions.iter().chain(&module.roots) {
        let id = functions.get(&function.name).copied().ok_or_else(|| {
            NativeValueCraneliftError::UnsupportedFunction {
                function: function.name.clone(),
                reason: "function was not declared",
            }
        })?;
        let mut ctx = module_backend.make_context();
        ctx.func.signature = value_function_signature(module_backend, function);
        lower_value_function(
            module_backend,
            &mut ctx,
            function,
            functions,
            helpers,
            literals,
        )?;
        module_backend
            .define_function(id, &mut ctx)
            .map_err(cranelift_error)?;
        module_backend.clear_context(&mut ctx);
    }
    Ok(())
}

#[derive(Debug, Clone, Copy)]
struct ValueHelpers {
    make_int: FuncId,
    make_float: FuncId,
    make_bool: FuncId,
    make_unit: FuncId,
    make_string: FuncId,
    concat_string: FuncId,
    primitive_unary: FuncId,
    primitive_binary: FuncId,
    list_empty: FuncId,
    list_singleton: FuncId,
    list_merge: FuncId,
    list_len: FuncId,
    list_index: FuncId,
    list_index_range: FuncId,
    list_index_range_raw: FuncId,
    tuple_empty: FuncId,
    tuple_push: FuncId,
    record_empty: FuncId,
    record_insert: FuncId,
    record_select: FuncId,
    variant: FuncId,
}

fn declare_helpers<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<ValueHelpers> {
    Ok(ValueHelpers {
        make_int: declare_make_int(module_backend)?,
        make_float: declare_make_float(module_backend)?,
        make_bool: declare_make_bool(module_backend)?,
        make_unit: declare_make_unit(module_backend)?,
        make_string: declare_make_string(module_backend)?,
        concat_string: declare_concat_string(module_backend)?,
        primitive_unary: declare_primitive_unary(module_backend)?,
        primitive_binary: declare_primitive_binary(module_backend)?,
        list_empty: declare_list_empty(module_backend)?,
        list_singleton: declare_list_singleton(module_backend)?,
        list_merge: declare_list_merge(module_backend)?,
        list_len: declare_list_len(module_backend)?,
        list_index: declare_list_index(module_backend)?,
        list_index_range: declare_list_index_range(module_backend)?,
        list_index_range_raw: declare_list_index_range_raw(module_backend)?,
        tuple_empty: declare_tuple_empty(module_backend)?,
        tuple_push: declare_tuple_push(module_backend)?,
        record_empty: declare_record_empty(module_backend)?,
        record_insert: declare_record_insert(module_backend)?,
        record_select: declare_record_select(module_backend)?,
        variant: declare_variant(module_backend)?,
    })
}

fn declare_make_int<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_make_int", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_make_float<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_make_float", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_make_bool<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_make_bool", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_make_unit<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_make_unit", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_make_string<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_make_string", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_list_empty<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_list_empty", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_list_singleton<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_list_singleton", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_list_merge<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_list_merge", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_list_len<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_list_len", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_list_index<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_list_index", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_list_index_range<M: Module>(
    module_backend: &mut M,
) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_list_index_range", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_list_index_range_raw<M: Module>(
    module_backend: &mut M,
) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_list_index_range_raw", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_tuple_empty<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_tuple_empty", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_tuple_push<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_tuple_push", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_record_empty<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_record_empty", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_record_insert<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_record_insert", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_record_select<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_record_select", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_variant<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_variant", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_concat_string<M: Module>(module_backend: &mut M) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_concat_string", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_primitive_unary<M: Module>(
    module_backend: &mut M,
) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_primitive_unary", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn declare_primitive_binary<M: Module>(
    module_backend: &mut M,
) -> NativeValueCraneliftResult<FuncId> {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    module_backend
        .declare_function("yulang_native_primitive_binary", Linkage::Import, &sig)
        .map_err(cranelift_error)
}

fn value_function_signature<M: Module>(
    module_backend: &M,
    function: &NativeAbiFunction,
) -> ir::Signature {
    let mut sig = module_backend.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.params
        .extend(function.params.iter().map(|_| AbiParam::new(types::I64)));
    sig.returns.push(AbiParam::new(types::I64));
    sig
}

fn lower_value_function<M: Module, L: ValueLiteralStore>(
    module_backend: &mut M,
    ctx: &mut cranelift_codegen::Context,
    function: &NativeAbiFunction,
    functions: &HashMap<String, FuncId>,
    helpers: &ValueHelpers,
    literals: &mut L,
) -> NativeValueCraneliftResult<()> {
    let mut builder_context = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_context);
    let block = function
        .blocks
        .first()
        .ok_or_else(|| NativeValueCraneliftError::MissingBlock {
            function: function.name.clone(),
            block: BlockId(0),
        })?;
    let clif_block = builder.create_block();
    builder.append_block_params_for_function_params(clif_block);
    builder.switch_to_block(clif_block);
    let block_params = builder.block_params(clif_block).to_vec();
    let context = block_params[0];
    let mut values = HashMap::new();
    let mut declared = HashSet::new();
    for value in function_value_ids(function) {
        if declared.insert(value) {
            builder.declare_var(variable(value), types::I64);
        }
    }
    for (param, value) in function.params.iter().zip(block_params.into_iter().skip(1)) {
        builder.def_var(variable(*param), value);
        values.insert(*param, ());
    }
    for stmt in &block.stmts {
        let dest = lower_value_stmt(
            module_backend,
            &mut builder,
            function,
            stmt,
            functions,
            helpers,
            context,
            &values,
            literals,
        )?;
        values.insert(dest, ());
    }
    match &block.terminator {
        NativeTerminator::Return(value) => {
            if !values.contains_key(value) {
                return Err(NativeValueCraneliftError::MissingValue {
                    function: function.name.clone(),
                    value: *value,
                });
            }
            let value = builder.use_var(variable(*value));
            builder.ins().return_(&[value]);
        }
        NativeTerminator::Jump { .. } | NativeTerminator::Branch { .. } => {
            return Err(NativeValueCraneliftError::UnsupportedFunction {
                function: function.name.clone(),
                reason: "multi-block control flow",
            });
        }
    }
    builder.seal_all_blocks();
    builder.finalize();
    Ok(())
}

fn lower_value_stmt<M: Module, L: ValueLiteralStore>(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    function: &NativeAbiFunction,
    stmt: &NativeAbiStmt,
    functions: &HashMap<String, FuncId>,
    helpers: &ValueHelpers,
    context: ir::Value,
    defined: &HashMap<ValueId, ()>,
    literals: &mut L,
) -> NativeValueCraneliftResult<ValueId> {
    match stmt {
        NativeAbiStmt::Literal {
            dest,
            literal: NativeLiteral::Int(value),
        } => {
            let (ptr, len) = literals.literal_bytes(module_backend, builder, value.as_bytes())?;
            let callee = module_backend.declare_func_in_func(helpers.make_int, builder.func);
            let call = builder.ins().call(callee, &[context, ptr, len]);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: "yulang_native_make_int".to_string(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::Literal {
            dest,
            literal: NativeLiteral::Float(value),
        } => {
            let (ptr, len) = literals.literal_bytes(module_backend, builder, value.as_bytes())?;
            let callee = module_backend.declare_func_in_func(helpers.make_float, builder.func);
            let call = builder.ins().call(callee, &[context, ptr, len]);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: "yulang_native_make_float".to_string(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::Literal {
            dest,
            literal: NativeLiteral::Bool(value),
        } => {
            let raw = builder.ins().iconst(types::I64, i64::from(*value));
            let callee = module_backend.declare_func_in_func(helpers.make_bool, builder.func);
            let call = builder.ins().call(callee, &[context, raw]);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: "yulang_native_make_bool".to_string(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::Literal {
            dest,
            literal: NativeLiteral::Unit,
        } => {
            let callee = module_backend.declare_func_in_func(helpers.make_unit, builder.func);
            let call = builder.ins().call(callee, &[context]);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: "yulang_native_make_unit".to_string(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::Literal {
            dest,
            literal: NativeLiteral::String(value),
        } => {
            let (ptr, len) = literals.literal_bytes(module_backend, builder, value.as_bytes())?;
            let callee = module_backend.declare_func_in_func(helpers.make_string, builder.func);
            let call = builder.ins().call(callee, &[context, ptr, len]);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: "yulang_native_make_string".to_string(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::Primitive {
            dest,
            op: yulang_typed_ir::PrimitiveOp::StringConcat,
            args,
        } => {
            let args = read_values(builder, function, defined, args)?;
            let callee = module_backend.declare_func_in_func(helpers.concat_string, builder.func);
            let call = builder.ins().call(callee, &[context, args[0], args[1]]);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: "yulang_native_concat_string".to_string(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::Primitive {
            dest,
            op: yulang_typed_ir::PrimitiveOp::ListEmpty,
            args,
        } => {
            if !args.is_empty() {
                return Err(NativeValueCraneliftError::UnsupportedStmt {
                    function: function.name.clone(),
                    kind: "list empty arity",
                });
            }
            let callee = module_backend.declare_func_in_func(helpers.list_empty, builder.func);
            let call = builder.ins().call(callee, &[context]);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: "yulang_native_list_empty".to_string(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::Primitive {
            dest,
            op: yulang_typed_ir::PrimitiveOp::ListSingleton,
            args,
        } => {
            let args = read_values(builder, function, defined, args)?;
            let callee = module_backend.declare_func_in_func(helpers.list_singleton, builder.func);
            let call = builder.ins().call(callee, &[context, args[0]]);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: "yulang_native_list_singleton".to_string(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::Primitive {
            dest,
            op: yulang_typed_ir::PrimitiveOp::ListMerge,
            args,
        } => {
            let args = read_values(builder, function, defined, args)?;
            let callee = module_backend.declare_func_in_func(helpers.list_merge, builder.func);
            let call = builder.ins().call(callee, &[context, args[0], args[1]]);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: "yulang_native_list_merge".to_string(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::Primitive {
            dest,
            op: yulang_typed_ir::PrimitiveOp::ListLen,
            args,
        } => {
            let args = read_values(builder, function, defined, args)?;
            let callee = module_backend.declare_func_in_func(helpers.list_len, builder.func);
            let call = builder.ins().call(callee, &[context, args[0]]);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: "yulang_native_list_len".to_string(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::Primitive {
            dest,
            op: yulang_typed_ir::PrimitiveOp::ListIndex,
            args,
        } => {
            let args = read_values(builder, function, defined, args)?;
            let callee = module_backend.declare_func_in_func(helpers.list_index, builder.func);
            let call = builder.ins().call(callee, &[context, args[0], args[1]]);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: "yulang_native_list_index".to_string(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::Primitive {
            dest,
            op: yulang_typed_ir::PrimitiveOp::ListIndexRange,
            args,
        } => {
            let args = read_values(builder, function, defined, args)?;
            let callee =
                module_backend.declare_func_in_func(helpers.list_index_range, builder.func);
            let call = builder.ins().call(callee, &[context, args[0], args[1]]);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: "yulang_native_list_index_range".to_string(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::Primitive {
            dest,
            op: yulang_typed_ir::PrimitiveOp::ListIndexRangeRaw,
            args,
        } => {
            let args = read_values(builder, function, defined, args)?;
            let callee =
                module_backend.declare_func_in_func(helpers.list_index_range_raw, builder.func);
            let call = builder
                .ins()
                .call(callee, &[context, args[0], args[1], args[2]]);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: "yulang_native_list_index_range_raw".to_string(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::Primitive { dest, op, args } if primitive_unary_code(*op).is_some() => {
            let [arg] = args.as_slice() else {
                return Err(NativeValueCraneliftError::UnsupportedStmt {
                    function: function.name.clone(),
                    kind: "primitive unary arity",
                });
            };
            let arg = read_values(builder, function, defined, &[*arg])?;
            let op_code = builder
                .ins()
                .iconst(types::I64, primitive_unary_code(*op).expect("checked"));
            let callee = module_backend.declare_func_in_func(helpers.primitive_unary, builder.func);
            let call = builder.ins().call(callee, &[context, op_code, arg[0]]);
            let result = single_call_result(builder, call, "yulang_native_primitive_unary")?;
            builder.def_var(variable(*dest), result);
            Ok(*dest)
        }
        NativeAbiStmt::Primitive { dest, op, args } if primitive_binary_code(*op).is_some() => {
            let [left, right] = args.as_slice() else {
                return Err(NativeValueCraneliftError::UnsupportedStmt {
                    function: function.name.clone(),
                    kind: "primitive binary arity",
                });
            };
            let args = read_values(builder, function, defined, &[*left, *right])?;
            let op_code = builder
                .ins()
                .iconst(types::I64, primitive_binary_code(*op).expect("checked"));
            let callee =
                module_backend.declare_func_in_func(helpers.primitive_binary, builder.func);
            let call = builder
                .ins()
                .call(callee, &[context, op_code, args[0], args[1]]);
            let result = single_call_result(builder, call, "yulang_native_primitive_binary")?;
            builder.def_var(variable(*dest), result);
            Ok(*dest)
        }
        NativeAbiStmt::Primitive { .. } => Err(NativeValueCraneliftError::UnsupportedStmt {
            function: function.name.clone(),
            kind: "primitive",
        }),
        NativeAbiStmt::DirectCall { dest, target, args } => {
            let id = functions.get(target).copied().ok_or_else(|| {
                NativeValueCraneliftError::UnsupportedFunction {
                    function: target.clone(),
                    reason: "target was not declared",
                }
            })?;
            let callee = module_backend.declare_func_in_func(id, builder.func);
            let mut call_args = vec![context];
            call_args.extend(read_values(builder, function, defined, args)?);
            let call = builder.ins().call(callee, &call_args);
            let results = builder.inst_results(call);
            if results.len() != 1 {
                return Err(NativeValueCraneliftError::InvalidReturnArity {
                    function: target.clone(),
                    arity: results.len(),
                });
            }
            builder.def_var(variable(*dest), results[0]);
            Ok(*dest)
        }
        NativeAbiStmt::Tuple { dest, items } => {
            let callee = module_backend.declare_func_in_func(helpers.tuple_empty, builder.func);
            let call = builder.ins().call(callee, &[context]);
            let mut tuple = single_call_result(builder, call, "yulang_native_tuple_empty")?;
            for item in read_values(builder, function, defined, items)? {
                let callee = module_backend.declare_func_in_func(helpers.tuple_push, builder.func);
                let call = builder.ins().call(callee, &[context, tuple, item]);
                tuple = single_call_result(builder, call, "yulang_native_tuple_push")?;
            }
            builder.def_var(variable(*dest), tuple);
            Ok(*dest)
        }
        NativeAbiStmt::Record { dest, fields } => {
            let callee = module_backend.declare_func_in_func(helpers.record_empty, builder.func);
            let call = builder.ins().call(callee, &[context]);
            let mut record = single_call_result(builder, call, "yulang_native_record_empty")?;
            for field in fields {
                if !defined.contains_key(&field.value) {
                    return Err(NativeValueCraneliftError::MissingValue {
                        function: function.name.clone(),
                        value: field.value,
                    });
                }
                let value = builder.use_var(variable(field.value));
                let (name_ptr, name_len) =
                    literals.literal_bytes(module_backend, builder, field.name.0.as_bytes())?;
                let callee =
                    module_backend.declare_func_in_func(helpers.record_insert, builder.func);
                let call = builder
                    .ins()
                    .call(callee, &[context, record, name_ptr, name_len, value]);
                record = single_call_result(builder, call, "yulang_native_record_insert")?;
            }
            builder.def_var(variable(*dest), record);
            Ok(*dest)
        }
        NativeAbiStmt::Variant { dest, tag, value } => {
            let (tag_ptr, tag_len) =
                literals.literal_bytes(module_backend, builder, tag.0.as_bytes())?;
            let value = if let Some(value) = value {
                if !defined.contains_key(value) {
                    return Err(NativeValueCraneliftError::MissingValue {
                        function: function.name.clone(),
                        value: *value,
                    });
                }
                builder.use_var(variable(*value))
            } else {
                builder.ins().iconst(types::I64, 0)
            };
            let callee = module_backend.declare_func_in_func(helpers.variant, builder.func);
            let call = builder
                .ins()
                .call(callee, &[context, tag_ptr, tag_len, value]);
            let result = single_call_result(builder, call, "yulang_native_variant")?;
            builder.def_var(variable(*dest), result);
            Ok(*dest)
        }
        NativeAbiStmt::Select { dest, base, field } => {
            if !defined.contains_key(base) {
                return Err(NativeValueCraneliftError::MissingValue {
                    function: function.name.clone(),
                    value: *base,
                });
            }
            let base = builder.use_var(variable(*base));
            let (field_ptr, field_len) =
                literals.literal_bytes(module_backend, builder, field.0.as_bytes())?;
            let callee = module_backend.declare_func_in_func(helpers.record_select, builder.func);
            let call = builder
                .ins()
                .call(callee, &[context, base, field_ptr, field_len]);
            let result = single_call_result(builder, call, "yulang_native_record_select")?;
            builder.def_var(variable(*dest), result);
            Ok(*dest)
        }
        NativeAbiStmt::LoadEnv { .. } => Err(NativeValueCraneliftError::UnsupportedStmt {
            function: function.name.clone(),
            kind: "environment load",
        }),
        NativeAbiStmt::AllocateClosure { .. } => Err(NativeValueCraneliftError::UnsupportedStmt {
            function: function.name.clone(),
            kind: "closure allocation",
        }),
        NativeAbiStmt::IndirectClosureCall { .. } => {
            Err(NativeValueCraneliftError::UnsupportedStmt {
                function: function.name.clone(),
                kind: "indirect closure call",
            })
        }
    }
}

fn single_call_result(
    builder: &FunctionBuilder<'_>,
    call: cranelift_codegen::ir::Inst,
    function: &str,
) -> NativeValueCraneliftResult<ir::Value> {
    let results = builder.inst_results(call);
    if results.len() != 1 {
        return Err(NativeValueCraneliftError::InvalidReturnArity {
            function: function.to_string(),
            arity: results.len(),
        });
    }
    Ok(results[0])
}

fn read_values(
    builder: &mut FunctionBuilder<'_>,
    function: &NativeAbiFunction,
    defined: &HashMap<ValueId, ()>,
    values: &[ValueId],
) -> NativeValueCraneliftResult<Vec<ir::Value>> {
    values
        .iter()
        .map(|value| {
            if !defined.contains_key(value) {
                return Err(NativeValueCraneliftError::MissingValue {
                    function: function.name.clone(),
                    value: *value,
                });
            }
            Ok(builder.use_var(variable(*value)))
        })
        .collect()
}

fn function_value_ids(function: &NativeAbiFunction) -> Vec<ValueId> {
    let mut values = Vec::new();
    values.extend(function.params.iter().copied());
    for block in &function.blocks {
        values.extend(block.params.iter().copied());
        for stmt in &block.stmts {
            match stmt {
                NativeAbiStmt::Literal { dest, .. }
                | NativeAbiStmt::Primitive { dest, .. }
                | NativeAbiStmt::DirectCall { dest, .. }
                | NativeAbiStmt::Tuple { dest, .. }
                | NativeAbiStmt::Record { dest, .. }
                | NativeAbiStmt::Variant { dest, .. }
                | NativeAbiStmt::Select { dest, .. }
                | NativeAbiStmt::LoadEnv { dest, .. }
                | NativeAbiStmt::AllocateClosure { dest, .. }
                | NativeAbiStmt::IndirectClosureCall { dest, .. } => values.push(*dest),
            }
        }
    }
    values
}

fn variable(value: ValueId) -> Variable {
    Variable::from_u32(value.0 as u32)
}

fn primitive_unary_code(op: yulang_typed_ir::PrimitiveOp) -> Option<i64> {
    match op {
        yulang_typed_ir::PrimitiveOp::BoolNot => Some(NATIVE_PRIMITIVE_BOOL_NOT),
        yulang_typed_ir::PrimitiveOp::IntToString => Some(NATIVE_PRIMITIVE_INT_TO_STRING),
        yulang_typed_ir::PrimitiveOp::IntToHex => Some(NATIVE_PRIMITIVE_INT_TO_HEX),
        yulang_typed_ir::PrimitiveOp::IntToUpperHex => Some(NATIVE_PRIMITIVE_INT_TO_UPPER_HEX),
        yulang_typed_ir::PrimitiveOp::FloatToString => Some(NATIVE_PRIMITIVE_FLOAT_TO_STRING),
        yulang_typed_ir::PrimitiveOp::BoolToString => Some(NATIVE_PRIMITIVE_BOOL_TO_STRING),
        yulang_typed_ir::PrimitiveOp::StringLen => Some(NATIVE_PRIMITIVE_STRING_LEN),
        _ => None,
    }
}

fn primitive_binary_code(op: yulang_typed_ir::PrimitiveOp) -> Option<i64> {
    match op {
        yulang_typed_ir::PrimitiveOp::BoolEq => Some(NATIVE_PRIMITIVE_BOOL_EQ),
        yulang_typed_ir::PrimitiveOp::IntAdd => Some(NATIVE_PRIMITIVE_INT_ADD),
        yulang_typed_ir::PrimitiveOp::IntSub => Some(NATIVE_PRIMITIVE_INT_SUB),
        yulang_typed_ir::PrimitiveOp::IntMul => Some(NATIVE_PRIMITIVE_INT_MUL),
        yulang_typed_ir::PrimitiveOp::IntDiv => Some(NATIVE_PRIMITIVE_INT_DIV),
        yulang_typed_ir::PrimitiveOp::IntEq => Some(NATIVE_PRIMITIVE_INT_EQ),
        yulang_typed_ir::PrimitiveOp::IntLt => Some(NATIVE_PRIMITIVE_INT_LT),
        yulang_typed_ir::PrimitiveOp::IntLe => Some(NATIVE_PRIMITIVE_INT_LE),
        yulang_typed_ir::PrimitiveOp::IntGt => Some(NATIVE_PRIMITIVE_INT_GT),
        yulang_typed_ir::PrimitiveOp::IntGe => Some(NATIVE_PRIMITIVE_INT_GE),
        yulang_typed_ir::PrimitiveOp::FloatAdd => Some(NATIVE_PRIMITIVE_FLOAT_ADD),
        yulang_typed_ir::PrimitiveOp::FloatSub => Some(NATIVE_PRIMITIVE_FLOAT_SUB),
        yulang_typed_ir::PrimitiveOp::FloatMul => Some(NATIVE_PRIMITIVE_FLOAT_MUL),
        yulang_typed_ir::PrimitiveOp::FloatDiv => Some(NATIVE_PRIMITIVE_FLOAT_DIV),
        yulang_typed_ir::PrimitiveOp::FloatEq => Some(NATIVE_PRIMITIVE_FLOAT_EQ),
        yulang_typed_ir::PrimitiveOp::FloatLt => Some(NATIVE_PRIMITIVE_FLOAT_LT),
        yulang_typed_ir::PrimitiveOp::FloatLe => Some(NATIVE_PRIMITIVE_FLOAT_LE),
        yulang_typed_ir::PrimitiveOp::FloatGt => Some(NATIVE_PRIMITIVE_FLOAT_GT),
        yulang_typed_ir::PrimitiveOp::FloatGe => Some(NATIVE_PRIMITIVE_FLOAT_GE),
        yulang_typed_ir::PrimitiveOp::StringIndex => Some(NATIVE_PRIMITIVE_STRING_INDEX),
        _ => None,
    }
}

trait ValueLiteralStore {
    fn literal_bytes<M: Module>(
        &mut self,
        module_backend: &mut M,
        builder: &mut FunctionBuilder<'_>,
        bytes: &[u8],
    ) -> NativeValueCraneliftResult<(ir::Value, ir::Value)>;
}

struct HostLiteralStore<'a> {
    strings: &'a mut Vec<Box<str>>,
}

impl ValueLiteralStore for HostLiteralStore<'_> {
    fn literal_bytes<M: Module>(
        &mut self,
        _module_backend: &mut M,
        builder: &mut FunctionBuilder<'_>,
        bytes: &[u8],
    ) -> NativeValueCraneliftResult<(ir::Value, ir::Value)> {
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

impl ValueLiteralStore for ObjectLiteralStore {
    fn literal_bytes<M: Module>(
        &mut self,
        module_backend: &mut M,
        builder: &mut FunctionBuilder<'_>,
        bytes: &[u8],
    ) -> NativeValueCraneliftResult<(ir::Value, ir::Value)> {
        let name = format!("__yulang_lit_{}", self.next_id);
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

fn cranelift_error(error: impl fmt::Display) -> NativeValueCraneliftError {
    NativeValueCraneliftError::Cranelift(error.to_string())
}

#[cfg(test)]
mod tests {
    use crate::abi::{NativeAbiBlock, NativeAbiFunction, NativeAbiModule, NativeAbiStmt};

    use super::*;

    #[test]
    fn jit_runs_string_literal_root() {
        let mut module = compile_value_abi_module(&NativeAbiModule {
            functions: Vec::new(),
            roots: vec![NativeAbiFunction {
                name: "root".to_string(),
                params: Vec::new(),
                environment_slots: 0,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![NativeAbiStmt::Literal {
                        dest: ValueId(0),
                        literal: NativeLiteral::String("hello".to_string()),
                    }],
                    terminator: NativeTerminator::Return(ValueId(0)),
                }],
            }],
        })
        .expect("compiled");

        assert_eq!(
            module.run_roots().expect("ran"),
            vec![runtime::VmValue::String(
                runtime::runtime::string_tree::StringTree::from_str("hello")
            )]
        );
    }

    #[test]
    fn jit_runs_string_concat_direct_call() {
        let mut module = compile_value_abi_module(&NativeAbiModule {
            functions: vec![NativeAbiFunction {
                name: "concat".to_string(),
                params: vec![ValueId(0), ValueId(1)],
                environment_slots: 0,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![NativeAbiStmt::Primitive {
                        dest: ValueId(2),
                        op: yulang_typed_ir::PrimitiveOp::StringConcat,
                        args: vec![ValueId(0), ValueId(1)],
                    }],
                    terminator: NativeTerminator::Return(ValueId(2)),
                }],
            }],
            roots: vec![NativeAbiFunction {
                name: "root".to_string(),
                params: Vec::new(),
                environment_slots: 0,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![
                        NativeAbiStmt::Literal {
                            dest: ValueId(0),
                            literal: NativeLiteral::String("hello, ".to_string()),
                        },
                        NativeAbiStmt::Literal {
                            dest: ValueId(1),
                            literal: NativeLiteral::String("world".to_string()),
                        },
                        NativeAbiStmt::DirectCall {
                            dest: ValueId(2),
                            target: "concat".to_string(),
                            args: vec![ValueId(0), ValueId(1)],
                        },
                    ],
                    terminator: NativeTerminator::Return(ValueId(2)),
                }],
            }],
        })
        .expect("compiled");

        assert_eq!(
            module.run_roots().expect("ran"),
            vec![runtime::VmValue::String(
                runtime::runtime::string_tree::StringTree::from_str("hello, world")
            )]
        );
    }

    #[test]
    fn jit_runs_list_literal_root() {
        let mut module = compile_value_abi_module(&NativeAbiModule {
            functions: Vec::new(),
            roots: vec![NativeAbiFunction {
                name: "root".to_string(),
                params: Vec::new(),
                environment_slots: 0,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: vec![
                        NativeAbiStmt::Literal {
                            dest: ValueId(0),
                            literal: NativeLiteral::Int("1".to_string()),
                        },
                        NativeAbiStmt::Primitive {
                            dest: ValueId(1),
                            op: yulang_typed_ir::PrimitiveOp::ListSingleton,
                            args: vec![ValueId(0)],
                        },
                        NativeAbiStmt::Literal {
                            dest: ValueId(2),
                            literal: NativeLiteral::Int("2".to_string()),
                        },
                        NativeAbiStmt::Primitive {
                            dest: ValueId(3),
                            op: yulang_typed_ir::PrimitiveOp::ListSingleton,
                            args: vec![ValueId(2)],
                        },
                        NativeAbiStmt::Primitive {
                            dest: ValueId(4),
                            op: yulang_typed_ir::PrimitiveOp::ListMerge,
                            args: vec![ValueId(1), ValueId(3)],
                        },
                    ],
                    terminator: NativeTerminator::Return(ValueId(4)),
                }],
            }],
        })
        .expect("compiled");

        let values = module.run_roots().expect("ran");
        let [runtime::VmValue::List(list)] = values.as_slice() else {
            panic!("expected one list value");
        };
        assert_eq!(
            list.to_vec()
                .into_iter()
                .map(|value| value.as_ref().clone())
                .collect::<Vec<_>>(),
            vec![
                runtime::VmValue::Int("1".to_string()),
                runtime::VmValue::Int("2".to_string())
            ]
        );
    }

    #[test]
    fn jit_runs_scalar_literal_roots() {
        let mut module = compile_value_abi_module(&NativeAbiModule {
            functions: Vec::new(),
            roots: vec![
                literal_root("bool_root", NativeLiteral::Bool(true)),
                literal_root("unit_root", NativeLiteral::Unit),
                literal_root("float_root", NativeLiteral::Float("1.5".to_string())),
            ],
        })
        .expect("compiled");

        assert_eq!(
            module.run_roots().expect("ran"),
            vec![
                runtime::VmValue::Bool(true),
                runtime::VmValue::Unit,
                runtime::VmValue::Float("1.5".to_string())
            ]
        );
    }

    #[test]
    fn jit_runs_list_len_and_index() {
        let mut module = compile_value_abi_module(&NativeAbiModule {
            functions: Vec::new(),
            roots: vec![
                NativeAbiFunction {
                    name: "len_root".to_string(),
                    params: Vec::new(),
                    environment_slots: 0,
                    blocks: vec![NativeAbiBlock {
                        id: BlockId(0),
                        params: Vec::new(),
                        stmts: list_with_len_or_index_stmts(ValueId(6), None),
                        terminator: NativeTerminator::Return(ValueId(6)),
                    }],
                },
                NativeAbiFunction {
                    name: "index_root".to_string(),
                    params: Vec::new(),
                    environment_slots: 0,
                    blocks: vec![NativeAbiBlock {
                        id: BlockId(0),
                        params: Vec::new(),
                        stmts: list_with_len_or_index_stmts(ValueId(7), Some(ValueId(5))),
                        terminator: NativeTerminator::Return(ValueId(7)),
                    }],
                },
            ],
        })
        .expect("compiled");

        assert_eq!(
            module.run_roots().expect("ran"),
            vec![
                runtime::VmValue::Int("2".to_string()),
                runtime::VmValue::Int("2".to_string())
            ]
        );
    }

    #[test]
    fn jit_runs_list_index_range_raw() {
        let mut module = compile_value_abi_module(&NativeAbiModule {
            functions: Vec::new(),
            roots: vec![NativeAbiFunction {
                name: "range_root".to_string(),
                params: Vec::new(),
                environment_slots: 0,
                blocks: vec![NativeAbiBlock {
                    id: BlockId(0),
                    params: Vec::new(),
                    stmts: list_index_range_raw_stmts(),
                    terminator: NativeTerminator::Return(ValueId(10)),
                }],
            }],
        })
        .expect("compiled");

        let values = module.run_roots().expect("ran");
        let [runtime::VmValue::List(value)] = values.as_slice() else {
            panic!("expected one list value, got {values:?}");
        };
        let items = value
            .to_vec()
            .into_iter()
            .map(|value| match value.as_ref() {
                runtime::VmValue::Int(value) => value.clone(),
                value => panic!("expected int value, got {value:?}"),
            })
            .collect::<Vec<_>>();
        assert_eq!(items, vec!["2", "3"]);
    }

    fn literal_root(name: &str, literal: NativeLiteral) -> NativeAbiFunction {
        NativeAbiFunction {
            name: name.to_string(),
            params: Vec::new(),
            environment_slots: 0,
            blocks: vec![NativeAbiBlock {
                id: BlockId(0),
                params: Vec::new(),
                stmts: vec![NativeAbiStmt::Literal {
                    dest: ValueId(0),
                    literal,
                }],
                terminator: NativeTerminator::Return(ValueId(0)),
            }],
        }
    }

    fn list_with_len_or_index_stmts(dest: ValueId, index: Option<ValueId>) -> Vec<NativeAbiStmt> {
        let mut stmts = vec![
            NativeAbiStmt::Literal {
                dest: ValueId(0),
                literal: NativeLiteral::Int("1".to_string()),
            },
            NativeAbiStmt::Primitive {
                dest: ValueId(1),
                op: yulang_typed_ir::PrimitiveOp::ListSingleton,
                args: vec![ValueId(0)],
            },
            NativeAbiStmt::Literal {
                dest: ValueId(2),
                literal: NativeLiteral::Int("2".to_string()),
            },
            NativeAbiStmt::Primitive {
                dest: ValueId(3),
                op: yulang_typed_ir::PrimitiveOp::ListSingleton,
                args: vec![ValueId(2)],
            },
            NativeAbiStmt::Primitive {
                dest: ValueId(4),
                op: yulang_typed_ir::PrimitiveOp::ListMerge,
                args: vec![ValueId(1), ValueId(3)],
            },
        ];
        if let Some(index) = index {
            stmts.push(NativeAbiStmt::Literal {
                dest: index,
                literal: NativeLiteral::Int("1".to_string()),
            });
            stmts.push(NativeAbiStmt::Primitive {
                dest,
                op: yulang_typed_ir::PrimitiveOp::ListIndex,
                args: vec![ValueId(4), index],
            });
        } else {
            stmts.push(NativeAbiStmt::Primitive {
                dest,
                op: yulang_typed_ir::PrimitiveOp::ListLen,
                args: vec![ValueId(4)],
            });
        }
        stmts
    }

    fn list_index_range_raw_stmts() -> Vec<NativeAbiStmt> {
        let mut stmts = list_with_len_or_index_stmts(ValueId(6), None);
        stmts.pop();
        stmts.extend([
            NativeAbiStmt::Literal {
                dest: ValueId(5),
                literal: NativeLiteral::Int("3".to_string()),
            },
            NativeAbiStmt::Primitive {
                dest: ValueId(6),
                op: yulang_typed_ir::PrimitiveOp::ListSingleton,
                args: vec![ValueId(5)],
            },
            NativeAbiStmt::Primitive {
                dest: ValueId(7),
                op: yulang_typed_ir::PrimitiveOp::ListMerge,
                args: vec![ValueId(4), ValueId(6)],
            },
            NativeAbiStmt::Literal {
                dest: ValueId(8),
                literal: NativeLiteral::Int("1".to_string()),
            },
            NativeAbiStmt::Literal {
                dest: ValueId(9),
                literal: NativeLiteral::Int("3".to_string()),
            },
            NativeAbiStmt::Primitive {
                dest: ValueId(10),
                op: yulang_typed_ir::PrimitiveOp::ListIndexRangeRaw,
                args: vec![ValueId(7), ValueId(8), ValueId(9)],
            },
        ]);
        stmts
    }
}
