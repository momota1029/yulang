//! Compatibility stub for the archived native backend.
//!
//! The historical Cranelift/MMTk implementation now lives under
//! `archive/yulang-native`. Active crates keep this small API surface while the
//! user-facing native CLI is removed.

use std::collections::BTreeMap;
use std::fmt;

use yulang_runtime as runtime;
use yulang_typed_ir as typed_ir;
use yulang_vm as runtime_vm;

const ARCHIVED_NATIVE_BACKEND: &str =
    "the native backend has been archived under archive/yulang-native";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeModule;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeClosureModule;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeAbiModule {
    pub roots: Vec<NativeAbiRoot>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeAbiRoot {
    pub name: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeObjectModule {
    bytes: Vec<u8>,
}

impl NativeObjectModule {
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprObjectModule {
    bytes: Vec<u8>,
    roots: Vec<String>,
    root_lanes: Vec<CpsReprAbiLane>,
    root_function_ids: Vec<u64>,
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeJitModule;

impl NativeJitModule {
    pub fn run_roots_i64(&mut self) -> Result<Vec<i64>, NativeCraneliftError> {
        Err(NativeCraneliftError::Archived)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeValueJitModule;

impl NativeValueJitModule {
    pub fn run_roots(&mut self) -> Result<Vec<runtime_vm::VmValue>, NativeValueCraneliftError> {
        Err(NativeValueCraneliftError::Archived)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprJitModule;

impl CpsReprJitModule {
    pub fn run_roots_display(&mut self) -> Result<Vec<String>, CpsReprCraneliftError> {
        Err(CpsReprCraneliftError::Archived)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

impl Default for CpsReprCraneliftOptions {
    fn default() -> Self {
        Self {
            mmtk_yvalue_primitives: false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CpsReprAbiLane {
    NativeFloat,
    ScalarI64,
    RuntimeValuePtr,
    ClosurePtr,
    ThunkPtr,
    ResumptionPtr,
    OpaqueI64,
    Conflict,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeRuntimePtrKind {
    String,
    RuntimeValue,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeAbiRepr {
    Unit,
    Bool,
    Int,
    Float,
    List(Box<NativeAbiRepr>),
    Tuple(Vec<NativeAbiRepr>),
    Record(Vec<NativeAbiField>),
    Variant(Vec<NativeAbiVariantCase>),
    RuntimeValuePtr(NativeRuntimePtrKind),
    ClosurePtr,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeAbiField {
    pub name: typed_ir::Name,
    pub value: NativeAbiRepr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeAbiVariantCase {
    pub tag: typed_ir::Name,
    pub value: Option<Box<NativeAbiRepr>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct NativeAbiReprAnalysis {
    pub functions: BTreeMap<String, NativeAbiRepr>,
}

impl NativeAbiReprAnalysis {
    pub fn function_repr(&self, name: &str) -> Option<&NativeAbiRepr> {
        self.functions.get(name)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeLowerError {
    UnsupportedRoot { message: String },
    UnsupportedExpr { message: String },
    UnsupportedPattern { message: String },
    UnsupportedBinding { message: String },
    MissingRootExpr { index: usize },
    PrimitiveArityMismatch { message: String },
    CallArityMismatch { message: String },
    Archived,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeValueCraneliftError {
    UnsupportedFunction { message: String },
    UnsupportedStmt { message: String },
    UnsupportedLiteral { message: String },
    AbiInvalid(String),
    MissingBlock { message: String },
    MissingValue { message: String },
    InvalidReturnArity { message: String },
    Cranelift(String),
    Archived,
}

macro_rules! archived_error {
    ($name:ident) => {
        #[derive(Debug, Clone, PartialEq, Eq)]
        pub enum $name {
            Archived,
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{ARCHIVED_NATIVE_BACKEND}")
            }
        }

        impl std::error::Error for $name {}
    };
}

archived_error!(NativeEvalError);
archived_error!(NativeCraneliftError);
archived_error!(CpsReprCraneliftError);
archived_error!(CpsCompareError);
archived_error!(NativeSourceCompareError);
archived_error!(CpsLowerError);
archived_error!(CpsEvalError);
archived_error!(CpsReprEvalError);

impl fmt::Display for NativeLowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeLowerError::UnsupportedRoot { message }
            | NativeLowerError::UnsupportedExpr { message }
            | NativeLowerError::UnsupportedPattern { message }
            | NativeLowerError::UnsupportedBinding { message }
            | NativeLowerError::PrimitiveArityMismatch { message }
            | NativeLowerError::CallArityMismatch { message } => write!(f, "{message}"),
            NativeLowerError::MissingRootExpr { index } => {
                write!(f, "missing native root expression {index}")
            }
            NativeLowerError::Archived => write!(f, "{ARCHIVED_NATIVE_BACKEND}"),
        }
    }
}

impl std::error::Error for NativeLowerError {}

impl fmt::Display for NativeValueCraneliftError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeValueCraneliftError::UnsupportedFunction { message }
            | NativeValueCraneliftError::UnsupportedStmt { message }
            | NativeValueCraneliftError::UnsupportedLiteral { message }
            | NativeValueCraneliftError::AbiInvalid(message)
            | NativeValueCraneliftError::MissingBlock { message }
            | NativeValueCraneliftError::MissingValue { message }
            | NativeValueCraneliftError::InvalidReturnArity { message }
            | NativeValueCraneliftError::Cranelift(message) => write!(f, "{message}"),
            NativeValueCraneliftError::Archived => write!(f, "{ARCHIVED_NATIVE_BACKEND}"),
        }
    }
}

impl std::error::Error for NativeValueCraneliftError {}

pub type NativeLowerResult<T> = Result<T, NativeLowerError>;
pub type CpsLowerResult<T> = Result<T, CpsLowerError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsModule;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprModule;

pub fn lower_module(_module: &runtime::Module) -> NativeLowerResult<NativeModule> {
    Err(NativeLowerError::Archived)
}

pub fn eval_module(_module: &NativeModule) -> Result<Vec<runtime_vm::VmValue>, NativeEvalError> {
    Err(NativeEvalError::Archived)
}

pub fn closure_convert_module(_module: &NativeModule) -> NativeClosureModule {
    NativeClosureModule
}

pub fn lower_closure_module_to_abi(_module: &NativeClosureModule) -> NativeAbiModule {
    NativeAbiModule { roots: Vec::new() }
}

pub fn analyze_abi_reprs(_module: &NativeAbiModule) -> NativeAbiReprAnalysis {
    NativeAbiReprAnalysis::default()
}

pub fn compile_abi_module(
    _module: &NativeAbiModule,
) -> Result<NativeJitModule, NativeCraneliftError> {
    Err(NativeCraneliftError::Archived)
}

pub fn compile_abi_module_to_object(
    _module: &NativeAbiModule,
) -> Result<NativeObjectModule, NativeCraneliftError> {
    Err(NativeCraneliftError::Archived)
}

pub fn compile_value_abi_module(
    _module: &NativeAbiModule,
) -> Result<NativeValueJitModule, NativeValueCraneliftError> {
    Err(NativeValueCraneliftError::Archived)
}

pub fn compile_value_abi_module_to_object(
    _module: &NativeAbiModule,
) -> Result<NativeValueObjectModule, NativeValueCraneliftError> {
    Err(NativeValueCraneliftError::Archived)
}

pub fn compare_module_i64(_module: &runtime::Module) -> Result<(), NativeSourceCompareError> {
    Err(NativeSourceCompareError::Archived)
}

pub fn compare_cps_repr_cranelift_i64(_module: &runtime::Module) -> Result<(), CpsCompareError> {
    Err(CpsCompareError::Archived)
}

pub fn lower_cps_module(_module: &runtime::Module) -> CpsLowerResult<CpsModule> {
    Err(CpsLowerError::Archived)
}

pub fn eval_cps_module(_module: &CpsModule) -> Result<Vec<runtime_vm::VmValue>, CpsEvalError> {
    Err(CpsEvalError::Archived)
}

pub fn lower_cps_repr_module(_module: &CpsModule) -> CpsReprModule {
    CpsReprModule
}

pub fn eval_cps_repr_module(
    _module: &CpsReprModule,
) -> Result<Vec<runtime_vm::VmValue>, CpsReprEvalError> {
    Err(CpsReprEvalError::Archived)
}

pub fn compile_runtime_module_to_cps_repr_jit(
    _module: &runtime::Module,
) -> Result<CpsReprJitModule, CpsReprCraneliftError> {
    Err(CpsReprCraneliftError::Archived)
}

pub fn compile_runtime_module_to_cps_repr_object_with_options(
    _module: &runtime::Module,
    _options: CpsReprCraneliftOptions,
) -> Result<CpsReprObjectModule, CpsReprCraneliftError> {
    Err(CpsReprCraneliftError::Archived)
}

pub fn with_cps_frame_trace<T>(
    f: impl FnOnce() -> Result<T, CpsEvalError>,
) -> (Result<T, CpsEvalError>, Vec<String>) {
    (f(), Vec::new())
}
