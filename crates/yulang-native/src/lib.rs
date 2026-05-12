//! Native backend skeleton for Yulang.
//!
//! This crate starts with a small control IR boundary.  Cranelift codegen will
//! sit behind this boundary later; for now the important behavior is that
//! supported runtime IR lowers explicitly and unsupported runtime IR fails with
//! a structured reason.

pub mod abi;
pub mod abi_eval;
pub mod abi_format;
pub mod abi_lane;
pub mod abi_subset;
pub mod abi_validate;
pub mod closure;
pub mod compare;
pub mod control_ir;
pub mod cps_capture;
pub mod cps_closure;
pub mod cps_compare;
pub mod cps_env;
pub mod cps_eval;
pub mod cps_ir;
pub mod cps_lower;
pub mod cps_repr;
pub mod cps_repr_abi;
pub mod cps_repr_cranelift;
pub mod cps_validate;
pub mod cranelift;
pub mod eval;
pub mod lower;
pub mod native_runtime;
pub mod source;
pub mod value_cranelift;

pub use abi::{
    NativeAbiBlock, NativeAbiFunction, NativeAbiModule, NativeAbiStmt, lower_closure_module_to_abi,
};
pub use abi_eval::{NativeAbiEvalError, NativeAbiEvalResult, eval_abi_module};
pub use abi_format::format_abi_module;
pub use abi_lane::{
    NativeAbiLaneAnalysis, NativeAbiRepr, NativeAbiReprAnalysis, NativeAbiValueLane,
    NativeRuntimePtrKind, analyze_abi_reprs, analyze_abi_value_lanes,
};
pub use abi_subset::{NativeAbiSubsetError, validate_cranelift_prototype_subset};
pub use abi_validate::{NativeAbiValidateError, validate_abi_module};
pub use closure::{
    NativeClosureAbi, NativeClosureBlock, NativeClosureCapture, NativeClosureCodeRef,
    NativeClosureEnvRef, NativeClosureEnvironment, NativeClosureFunction, NativeClosureModule,
    NativeClosureSlot, NativeClosureStmt, closure_convert_module,
};
pub use compare::{
    NativeCompareError, NativeSourceCompareError, compare_module, compare_module_i64,
    compare_source_i64, compare_source_i64_with_options,
};
pub use control_ir::{
    BlockId, NativeBlock, NativeFunction, NativeLiteral, NativeModule, NativeStmt,
    NativeTerminator, ValueId,
};
pub use cps_capture::infer_cps_captures;
pub use cps_closure::{
    CpsClosureContinuation, CpsClosureFunction, CpsClosureModule, closure_convert_cps_module,
};
pub use cps_compare::{
    CpsCompareError, CpsReprI64CompareReport, CpsReprI64RootCompare, compare_cps_module,
    compare_cps_repr_cranelift_i64, compare_cps_repr_cranelift_i64_report,
};
pub use cps_env::{
    CpsContinuationEnvironmentLayout, CpsEnvironmentLayout, CpsEnvironmentSlot,
    CpsFunctionEnvironmentLayout, layout_cps_environments,
};
pub use cps_eval::{CpsEvalError, eval_cps_module};
pub use cps_ir::{
    CpsContinuation, CpsContinuationId, CpsFunction, CpsHandler, CpsHandlerArm,
    CpsHandlerContextId, CpsHandlerId, CpsLiteral, CpsModule, CpsShotKind, CpsStmt, CpsTerminator,
    CpsValueId,
};
pub use cps_lower::{CpsLowerError, CpsLowerResult, lower_cps_module};
pub use cps_repr::{
    CpsReprAbiAnalysis, CpsReprAbiLane, CpsReprContinuation, CpsReprEnvironmentSlot,
    CpsReprEvalError, CpsReprFunction, CpsReprFunctionAbiAnalysis, CpsReprFunctionValueAnalysis,
    CpsReprModule, CpsReprValueAnalysis, CpsReprValueKind, analyze_cps_repr_abi_lanes,
    analyze_cps_repr_values, eval_cps_repr_module, lower_cps_repr_module,
};
pub use cps_repr_abi::{
    CpsReprAbiContinuation, CpsReprAbiEnvironmentSlot, CpsReprAbiFunction, CpsReprAbiHandler,
    CpsReprAbiHandlerArm, CpsReprAbiModule, CpsReprAbiValue, lower_cps_repr_abi_module,
};
pub use cps_repr_cranelift::{
    CpsReprCraneliftError, CpsReprJitModule, CpsReprObjectModule, compile_cps_repr_abi_module,
    compile_cps_repr_abi_module_to_object, compile_runtime_module_to_cps_repr_jit,
    compile_runtime_module_to_cps_repr_object,
};
pub use cps_validate::{CpsValidateError, validate_cps_module};
pub use cranelift::{
    NativeCraneliftError, NativeJitModule, NativeObjectModule, compile_abi_module,
    compile_abi_module_to_object,
};
pub use eval::{NativeEvalError, eval_module};
pub use lower::{NativeLowerError, NativeLowerResult, lower_module};
pub use native_runtime::{
    NativeRuntimeContext, concat_string as native_runtime_concat_string,
    list_empty as native_runtime_list_empty, list_index as native_runtime_list_index,
    list_len as native_runtime_list_len, list_merge as native_runtime_list_merge,
    list_singleton as native_runtime_list_singleton, make_bool as native_runtime_make_bool,
    make_float as native_runtime_make_float, make_int as native_runtime_make_int,
    make_string as native_runtime_make_string, make_unit as native_runtime_make_unit,
    record_empty as native_runtime_record_empty, record_insert as native_runtime_record_insert,
    record_select as native_runtime_record_select, tuple_empty as native_runtime_tuple_empty,
    tuple_push as native_runtime_tuple_push, variant as native_runtime_variant,
    yulang_native_concat_string, yulang_native_context_free, yulang_native_context_new,
    yulang_native_list_empty, yulang_native_list_index, yulang_native_list_len,
    yulang_native_list_merge, yulang_native_list_singleton, yulang_native_make_bool,
    yulang_native_make_float, yulang_native_make_int, yulang_native_make_string,
    yulang_native_make_unit, yulang_native_print_value, yulang_native_record_empty,
    yulang_native_record_insert, yulang_native_record_select, yulang_native_tuple_empty,
    yulang_native_tuple_push, yulang_native_variant,
};
pub use source::{
    NativeSourceError, NativeSourceResult, analyze_source_abi_reprs,
    analyze_source_abi_reprs_with_options, compare_source_cps_repr_i64,
    compare_source_cps_repr_i64_with_options, compile_source, compile_source_object,
    compile_source_object_with_options, compile_source_value_object,
    compile_source_value_object_with_options, compile_source_with_options, eval_source,
    eval_source_cps_repr_i64, eval_source_cps_repr_i64_with_options, eval_source_i64,
    eval_source_i64_with_options, eval_source_value_lane, eval_source_value_lane_with_options,
    eval_source_with_options, native_default_source_options,
    runtime_module_from_source_with_options,
};
pub use value_cranelift::{
    NativeValueCraneliftError, NativeValueJitModule, NativeValueObjectModule,
    compile_value_abi_module, compile_value_abi_module_to_object,
};
