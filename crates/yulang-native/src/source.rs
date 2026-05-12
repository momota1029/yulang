//! Source-string entrypoints for the native backend.
//!
//! The native backend itself still starts from `runtime::Module`.  This module
//! is a thin experimental adapter used by tests and local tooling that want to
//! start from Yulang source text without copying the frontend pipeline.

use std::fmt;
use std::path::PathBuf;

use yulang_infer as infer;
use yulang_runtime as runtime;

use crate::abi::lower_closure_module_to_abi;
use crate::abi_lane::{NativeAbiReprAnalysis, analyze_abi_reprs};
use crate::closure::closure_convert_module;
use crate::control_ir::NativeModule;
use crate::cps_compare::CpsCompareError;
use crate::cps_repr_cranelift::{CpsReprCraneliftError, compile_runtime_module_to_cps_repr_jit};
use crate::cranelift::{
    NativeCraneliftError, NativeObjectModule, compile_abi_module, compile_abi_module_to_object,
};
use crate::eval::{NativeEvalError, eval_module};
use crate::lower::{NativeLowerError, lower_module};
use crate::value_cranelift::{
    NativeValueCraneliftError, NativeValueObjectModule, compile_value_abi_module,
    compile_value_abi_module_to_object,
};

pub type NativeSourceResult<T> = Result<T, NativeSourceError>;

#[derive(Debug)]
pub enum NativeSourceError {
    SourceLoad(infer::SourceLoadError),
    SurfaceDiagnostics(Vec<String>),
    RuntimeLower(runtime::RuntimeError),
    NativeLower(NativeLowerError),
    NativeEval(NativeEvalError),
    Cranelift(NativeCraneliftError),
    ValueCranelift(NativeValueCraneliftError),
    CpsReprCranelift(CpsReprCraneliftError),
    CpsCompare(CpsCompareError),
}

impl fmt::Display for NativeSourceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeSourceError::SourceLoad(error) => write!(f, "{error}"),
            NativeSourceError::SurfaceDiagnostics(messages) => {
                write!(f, "{}", messages.join("\n"))
            }
            NativeSourceError::RuntimeLower(error) => write!(f, "{error}"),
            NativeSourceError::NativeLower(error) => write!(f, "{error}"),
            NativeSourceError::NativeEval(error) => write!(f, "{error}"),
            NativeSourceError::Cranelift(error) => write!(f, "{error}"),
            NativeSourceError::ValueCranelift(error) => write!(f, "{error}"),
            NativeSourceError::CpsReprCranelift(error) => write!(f, "{error}"),
            NativeSourceError::CpsCompare(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for NativeSourceError {}

impl From<infer::SourceLoadError> for NativeSourceError {
    fn from(error: infer::SourceLoadError) -> Self {
        NativeSourceError::SourceLoad(error)
    }
}

impl From<runtime::RuntimeError> for NativeSourceError {
    fn from(error: runtime::RuntimeError) -> Self {
        NativeSourceError::RuntimeLower(error)
    }
}

impl From<NativeLowerError> for NativeSourceError {
    fn from(error: NativeLowerError) -> Self {
        NativeSourceError::NativeLower(error)
    }
}

impl From<NativeEvalError> for NativeSourceError {
    fn from(error: NativeEvalError) -> Self {
        NativeSourceError::NativeEval(error)
    }
}

impl From<NativeCraneliftError> for NativeSourceError {
    fn from(error: NativeCraneliftError) -> Self {
        NativeSourceError::Cranelift(error)
    }
}

impl From<NativeValueCraneliftError> for NativeSourceError {
    fn from(error: NativeValueCraneliftError) -> Self {
        NativeSourceError::ValueCranelift(error)
    }
}

impl From<CpsReprCraneliftError> for NativeSourceError {
    fn from(error: CpsReprCraneliftError) -> Self {
        NativeSourceError::CpsReprCranelift(error)
    }
}

impl From<CpsCompareError> for NativeSourceError {
    fn from(error: CpsCompareError) -> Self {
        NativeSourceError::CpsCompare(error)
    }
}

pub fn compile_source(source: &str) -> NativeSourceResult<NativeModule> {
    compile_source_with_options(source, native_default_source_options())
}

pub fn compile_source_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<NativeModule> {
    let module = runtime_module_from_source_with_options(source, options)?;
    lower_module(&module).map_err(NativeSourceError::from)
}

pub fn eval_source(source: &str) -> NativeSourceResult<Vec<runtime::VmValue>> {
    eval_source_with_options(source, native_default_source_options())
}

pub fn eval_source_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<Vec<runtime::VmValue>> {
    let module = compile_source_with_options(source, options)?;
    eval_module(&module).map_err(NativeSourceError::from)
}

pub fn eval_source_i64(source: &str) -> NativeSourceResult<Vec<i64>> {
    eval_source_i64_with_options(source, native_default_source_options())
}

pub fn eval_source_i64_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<Vec<i64>> {
    let native_module = compile_source_with_options(source, options)?;
    let closure_module = closure_convert_module(&native_module);
    let abi_module = lower_closure_module_to_abi(&closure_module);
    let mut jit = compile_abi_module(&abi_module)?;
    jit.run_roots_i64().map_err(NativeSourceError::from)
}

pub fn compile_source_object(source: &str) -> NativeSourceResult<NativeObjectModule> {
    compile_source_object_with_options(source, native_default_source_options())
}

pub fn compile_source_object_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<NativeObjectModule> {
    let native_module = compile_source_with_options(source, options)?;
    let closure_module = closure_convert_module(&native_module);
    let abi_module = lower_closure_module_to_abi(&closure_module);
    compile_abi_module_to_object(&abi_module).map_err(NativeSourceError::from)
}

pub fn eval_source_value_lane(source: &str) -> NativeSourceResult<Vec<runtime::VmValue>> {
    eval_source_value_lane_with_options(source, native_default_source_options())
}

pub fn eval_source_value_lane_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<Vec<runtime::VmValue>> {
    let runtime_module = runtime_module_from_source_with_options(source, options)?;
    let native_module = lower_module(&runtime_module)?;
    let closure_module = closure_convert_module(&native_module);
    let abi_module = lower_closure_module_to_abi(&closure_module);
    let mut jit = compile_value_abi_module(&abi_module)?;
    jit.run_roots().map_err(NativeSourceError::from)
}

pub fn compile_source_value_object(source: &str) -> NativeSourceResult<NativeValueObjectModule> {
    compile_source_value_object_with_options(source, native_default_source_options())
}

pub fn compile_source_value_object_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<NativeValueObjectModule> {
    let runtime_module = runtime_module_from_source_with_options(source, options)?;
    let native_module = lower_module(&runtime_module)?;
    let closure_module = closure_convert_module(&native_module);
    let abi_module = lower_closure_module_to_abi(&closure_module);
    compile_value_abi_module_to_object(&abi_module).map_err(NativeSourceError::from)
}

pub fn eval_source_cps_repr_i64(source: &str) -> NativeSourceResult<Vec<i64>> {
    eval_source_cps_repr_i64_with_options(source, native_default_source_options())
}

pub fn eval_source_cps_repr_i64_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<Vec<i64>> {
    let runtime_module = runtime_module_from_source_with_options(source, options)?;
    let mut jit = compile_runtime_module_to_cps_repr_jit(&runtime_module)?;
    jit.run_roots_i64().map_err(NativeSourceError::from)
}

pub fn compare_source_cps_repr_i64(source: &str) -> NativeSourceResult<()> {
    compare_source_cps_repr_i64_with_options(source, native_default_source_options())
}

pub fn compare_source_cps_repr_i64_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<()> {
    let runtime_module = runtime_module_from_source_with_options(source, options)?;
    crate::cps_compare::compare_cps_repr_cranelift_i64(&runtime_module)
        .map_err(NativeSourceError::from)
}

pub fn analyze_source_abi_reprs(source: &str) -> NativeSourceResult<NativeAbiReprAnalysis> {
    analyze_source_abi_reprs_with_options(source, native_default_source_options())
}

pub fn analyze_source_abi_reprs_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<NativeAbiReprAnalysis> {
    let runtime_module = runtime_module_from_source_with_options(source, options)?;
    let native_module = lower_module(&runtime_module)?;
    let closure_module = closure_convert_module(&native_module);
    let abi_module = lower_closure_module_to_abi(&closure_module);
    Ok(analyze_abi_reprs(&abi_module))
}

pub fn runtime_module_from_source_with_options(
    source: &str,
    options: infer::SourceOptions,
) -> NativeSourceResult<runtime::Module> {
    let mut lowered = infer::lower_virtual_source_with_options(source, None, options)?;
    let diagnostics = infer::collect_surface_diagnostics(&lowered.state);
    if !diagnostics.is_empty() {
        return Err(NativeSourceError::SurfaceDiagnostics(
            diagnostics
                .into_iter()
                .map(|diagnostic| diagnostic.message)
                .collect(),
        ));
    }
    let program = infer::export_core_program(&mut lowered.state);
    runtime::lower_core_program(program)
        .and_then(runtime::monomorphize_module)
        .map_err(NativeSourceError::from)
}

pub fn native_default_source_options() -> infer::SourceOptions {
    let std_root = default_std_root();
    infer::SourceOptions {
        implicit_prelude: std_root.is_some(),
        std_root,
        search_paths: Vec::new(),
    }
}

fn default_std_root() -> Option<PathBuf> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../lib/std");
    root.is_dir().then_some(root)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::{NativeAbiRepr, NativeAbiValueLane, NativeRuntimePtrKind};

    use super::*;

    #[test]
    fn evals_literal_source_string() {
        let values = eval_source_with_options("41", infer::SourceOptions::default())
            .expect("native source eval");
        assert_eq!(values, vec![runtime::VmValue::Int("41".to_string())]);
    }

    #[test]
    fn evals_literal_source_string_through_cranelift_scalar_path() {
        let values = eval_source_i64_with_options("41", infer::SourceOptions::default())
            .expect("native source jit eval");
        assert_eq!(values, vec![41]);
    }

    #[test]
    fn emits_literal_source_object() {
        let object = compile_source_object_with_options("41", infer::SourceOptions::default())
            .expect("native source object compile");
        assert!(!object.bytes().is_empty());
    }

    #[test]
    fn evals_literal_source_through_cps_repr_cranelift() {
        let values = eval_source_cps_repr_i64_with_options("41", infer::SourceOptions::default())
            .expect("native CPS repr jit eval");
        assert_eq!(values, vec![41]);
    }

    #[test]
    fn evals_prelude_source_through_cps_repr_cranelift() {
        let values = run_with_large_stack(|| {
            eval_source_cps_repr_i64("41").expect("native CPS repr jit eval with prelude")
        });
        assert_eq!(values, vec![41]);
    }

    #[test]
    fn evals_structural_source_through_cps_repr_interpreter() {
        let module = runtime_module_from_source_with_options(
            "(1, 2)\n{x: 1, y: 2}.y\n:label 3",
            infer::SourceOptions::default(),
        )
        .expect("runtime module");
        let cps = crate::cps_lower::lower_cps_module(&module).expect("CPS module");
        crate::cps_validate::validate_cps_module(&cps).expect("valid CPS module");
        let direct = crate::cps_eval::eval_cps_module(&cps).expect("CPS eval");
        let repr = crate::cps_repr::lower_cps_repr_module(&cps);
        let repr_values = crate::cps_repr::eval_cps_repr_module(&repr).expect("CPS repr eval");

        let expected = vec![
            runtime::VmValue::Tuple(vec![
                runtime::VmValue::Int("1".to_string()),
                runtime::VmValue::Int("2".to_string()),
            ]),
            runtime::VmValue::Int("2".to_string()),
            runtime::VmValue::Variant {
                tag: yulang_typed_ir::Name("label".to_string()),
                value: Some(Box::new(runtime::VmValue::Int("3".to_string()))),
            },
        ];
        assert_eq!(direct, expected);
        assert_eq!(repr_values, expected);
    }

    #[test]
    fn compares_source_effect_handler_through_cps_repr_cranelift() {
        compare_source_cps_repr_i64_with_options(
            r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> k x
"#,
            infer::SourceOptions::default(),
        )
        .expect("source CPS repr jit compare");
    }

    #[test]
    fn compares_source_value_handler_arm_through_cps_repr_cranelift() {
        compare_source_cps_repr_i64_with_options(
            r#"catch 31:
    value -> 41
"#,
            infer::SourceOptions::default(),
        )
        .expect("source CPS repr jit compare");
    }

    #[test]
    fn compares_source_resume_result_outside_value_arm_through_cps_repr_cranelift() {
        compare_source_cps_repr_i64_with_options(
            r#"pub act choose:
  pub pick: int -> int

catch choose::pick 31:
    choose::pick x, k -> k x
    value -> 41
"#,
            infer::SourceOptions::default(),
        )
        .expect("source CPS repr jit compare");
    }

    #[test]
    fn compares_prelude_source_effect_handler_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> k x
"#,
            )
            .expect("source CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_multishot_effect_handler_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> k 1 + k 2
"#,
            )
            .expect("source multishot CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_once_branch_tail_effect_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choice:
  pub branch: () -> bool

my once(x: [_] bool): bool = catch x:
    choice::branch (), k -> k true
    v -> v

once { choice::branch () }
"#,
            )
            .expect("source once branch CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_once_branch_match_effect_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choice:
  pub branch: () -> bool

my once(x: [_] int): int = catch x:
    choice::branch (), k -> k true
    v -> v

once { case choice::branch ():
    true -> 1
    false -> 2
}
"#,
            )
            .expect("source once branch match CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_once_dfs_reject_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choice:
  pub branch: () -> bool
  pub reject: () -> never

my once_dfs_int(x: [choice] int): int = catch x:
    choice::branch (), k -> catch k true:
        choice::reject (), _ -> k false
        v -> v
    choice::reject (), _ -> 0
    v -> v

once_dfs_int { case choice::branch ():
    true -> choice::reject ()
    false -> 2
}
"#,
            )
            .expect("source once DFS reject CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_once_finite_list_without_fold_sub_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choice:
  pub branch: () -> bool
  pub reject: () -> never

my once_dfs_int(x: [choice] int): int = catch x:
    choice::branch (), k -> catch k true:
        choice::reject (), _ -> k false
        v -> v
    choice::reject (), _ -> 0
    v -> v

once_dfs_int { case std::list::uncons [1, 2, 3]:
    std::opt::opt::nil -> choice::reject ()
    std::opt::opt::just (x, _) -> case choice::branch ():
        true -> x
        false -> choice::reject ()
}
"#,
            )
            .expect("source once finite-list CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_once_finite_each_function_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choice:
  pub branch: () -> bool
  pub reject: () -> never

my once_dfs_int(x: [choice] int): int = catch x:
    choice::branch (), k -> catch k true:
        choice::reject (), _ -> k false
        v -> v
    choice::reject (), _ -> 0
    v -> v

my each_head(xs: std::list::list int): [choice] int = case std::list::uncons xs:
    std::opt::opt::nil -> choice::reject ()
    std::opt::opt::just (x, _) -> case choice::branch ():
        true -> x
        false -> choice::reject ()

once_dfs_int { each_head [1, 2, 3] }
"#,
            )
            .expect("source once finite each function CPS repr jit compare with prelude");
        });
    }

    #[test]
    #[ignore = "Milestone 6 debug: each_list through CPS eval / repr eval / Cranelift"]
    fn debugs_each_list_recursive_through_cps_stages() {
        let source = r#"pub act choice:
  pub branch: () -> bool
  pub reject: () -> never

my once_dfs_int(x: [choice] int): int = catch x:
    choice::branch (), k -> catch k true:
        choice::reject (), _ -> k false
        v -> v
    choice::reject (), _ -> 0
    v -> v

my each_list(xs: std::list::list int): [choice] int = case std::list::uncons xs:
    std::opt::opt::nil -> choice::reject ()
    std::opt::opt::just (x, rest) -> case choice::branch ():
        true -> x
        false -> each_list rest

once_dfs_int { each_list [1, 2, 3] }
"#;

        run_with_large_stack(|| {
            let module =
                runtime_module_from_source_with_options(source, native_default_source_options())
                    .expect("runtime module");

            let cps = crate::cps_lower::lower_cps_module(&module).expect("CPS lowering");
            crate::cps_validate::validate_cps_module(&cps).expect("CPS validation");

            eprintln!("=== CPS module ===");
            for f in cps.functions.iter().chain(cps.roots.iter()) {
                eprintln!("function: {} params={:?}", f.name, f.params);
                for cont in &f.continuations {
                    eprintln!(
                        "  cont {:?} params={:?} captures={:?}",
                        cont.id, cont.params, cont.captures
                    );
                    for stmt in &cont.stmts {
                        eprintln!("    stmt: {:?}", stmt);
                    }
                    eprintln!("    term: {:?}", cont.terminator);
                }
                for handler in &f.handlers {
                    eprintln!(
                        "  handler {:?} arms={:?}",
                        handler.id,
                        handler
                            .arms
                            .iter()
                            .map(|a| (&a.effect, a.entry))
                            .collect::<Vec<_>>()
                    );
                }
            }

            // Layer 1: CPS eval vs VM
            crate::cps_compare::compare_cps_module(&module).expect("CPS eval == VM");
            eprintln!("Layer 1 (CPS eval): OK");

            // Layer 2: CPS repr eval vs VM
            let repr = crate::cps_repr::lower_cps_repr_module(&cps);
            let repr_values = crate::cps_repr::eval_cps_repr_module(&repr).expect("CPS repr eval");
            let vm_results = runtime::compile_vm_module(module.clone())
                .expect("VM compile")
                .eval_roots()
                .expect("VM eval");
            let vm_value = match &vm_results[0] {
                runtime::VmResult::Value(v) => v.clone(),
                runtime::VmResult::Request(_) => panic!("VM gave request"),
            };
            assert_eq!(repr_values[0], vm_value, "CPS repr eval == VM");
            eprintln!("Layer 2 (CPS repr eval): OK");

            // Layer 3: CPS repr Cranelift vs VM
            compare_source_cps_repr_i64(source).expect("CPS repr Cranelift compare");
            eprintln!("Layer 3 (CPS repr Cranelift): OK");
        });
    }

    #[test]
    #[ignore = "Milestone 7 debug: std::undet.each through CPS eval / repr eval / Cranelift"]
    fn debugs_std_each_with_local_once_dfs_eval_layers() {
        let source = r#"use std::undet::*

my once_dfs_int(x: [std::undet::undet] int): int = catch x:
    branch (), k -> catch k true:
        reject (), _ -> k false
        v -> v
    reject (), _ -> 0
    v -> v

once_dfs_int { each [1, 2, 3] }
"#;

        run_with_large_stack(|| {
            let module =
                runtime_module_from_source_with_options(source, native_default_source_options())
                    .expect("runtime module");

            let cps = crate::cps_lower::lower_cps_module(&module).expect("CPS lowering");
            crate::cps_validate::validate_cps_module(&cps).expect("CPS validation");

            eprintln!("=== CPS module ===");
            for f in cps.functions.iter().chain(cps.roots.iter()) {
                eprintln!("function: {} params={:?}", f.name, f.params);
                for cont in &f.continuations {
                    eprintln!(
                        "  cont {:?} params={:?} captures={:?}",
                        cont.id, cont.params, cont.captures
                    );
                    for stmt in &cont.stmts {
                        eprintln!("    stmt: {:?}", stmt);
                    }
                    eprintln!("    term: {:?}", cont.terminator);
                }
                for handler in &f.handlers {
                    eprintln!(
                        "  handler {:?} arms={:?}",
                        handler.id,
                        handler
                            .arms
                            .iter()
                            .map(|a| (&a.effect, a.entry))
                            .collect::<Vec<_>>()
                    );
                }
            }

            crate::cps_compare::compare_cps_module(&module).expect("CPS eval == VM");
            eprintln!("Layer 1 (CPS eval): OK");

            let repr = crate::cps_repr::lower_cps_repr_module(&cps);
            let repr_values = crate::cps_repr::eval_cps_repr_module(&repr).expect("CPS repr eval");
            let vm_results = runtime::compile_vm_module(module.clone())
                .expect("VM compile")
                .eval_roots()
                .expect("VM eval");
            let vm_value = match &vm_results[0] {
                runtime::VmResult::Value(v) => v.clone(),
                runtime::VmResult::Request(_) => panic!("VM gave request"),
            };
            assert_eq!(repr_values[0], vm_value, "CPS repr eval == VM");
            eprintln!("Layer 2 (CPS repr eval): OK");

            compare_source_cps_repr_i64(source).expect("CPS repr Cranelift compare");
            eprintln!("Layer 3 (CPS repr Cranelift): OK");
        });
    }

    #[test]
    #[ignore = "Phase D: first-class resumption stored in tuple"]
    fn compares_resumption_stored_in_tuple_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choice:
  pub branch: () -> bool

catch choice::branch ():
    choice::branch (), k ->
        my pair = (k, 0)
        case pair:
            (r, _) -> if r true: 1 else: 2
    v -> if v: 10 else: 20
"#,
            )
            .expect("resumption tuple CPS repr jit compare");
        });
    }

    #[test]
    fn compares_resumption_stored_in_list_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choice:
  pub branch: () -> bool

catch choice::branch ():
    choice::branch (), k -> case std::list::uncons [k]:
        std::opt::opt::nil -> 0
        std::opt::opt::just (r, _) -> if r true: 1 else: 2
    v -> if v: 10 else: 20
"#,
            )
            .expect("resumption list CPS repr jit compare");
        });
    }

    #[test]
    #[ignore = "Phase D: first-class closure stored in tuple"]
    fn compares_closure_stored_in_tuple_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"my apply_pair p = case p:
    (f, x) -> f x

apply_pair (\x -> x + 1, 41)
"#,
            )
            .expect("closure tuple CPS repr jit compare");
        });
    }

    #[test]
    #[ignore = "Phase D: first-class closure stored in list"]
    fn compares_closure_stored_in_list_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"case std::list::uncons [\x -> x + 1]:
    std::opt::opt::nil -> 0
    std::opt::opt::just (f, _) -> f 41
"#,
            )
            .expect("closure list CPS repr jit compare");
        });
    }

    #[test]
    #[ignore = "Phase F debug: inspect std::undet.once lowering around loop(k true, queue)"]
    fn debugs_std_undet_once_cps_shape() {
        let source = r#"use std::undet::*

case (each [1, 2, 3]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
"#;

        run_with_large_stack(|| {
            let module =
                runtime_module_from_source_with_options(source, native_default_source_options())
                    .expect("runtime module");

            let cps = crate::cps_lower::lower_cps_module(&module).expect("CPS lowering");
            crate::cps_validate::validate_cps_module(&cps).expect("CPS validation");

            for f in cps.functions.iter().chain(cps.roots.iter()) {
                if !f.name.contains("once")
                    && !f.name.contains("loop")
                    && !f.name.contains("each")
                    && !f.name.contains("root")
                {
                    continue;
                }
                eprintln!("function: {} params={:?}", f.name, f.params);
                for cont in &f.continuations {
                    eprintln!(
                        "  cont {:?} params={:?} captures={:?}",
                        cont.id, cont.params, cont.captures
                    );
                    for stmt in &cont.stmts {
                        eprintln!("    stmt: {:?}", stmt);
                    }
                    eprintln!("    term: {:?}", cont.terminator);
                }
                for handler in &f.handlers {
                    eprintln!(
                        "  handler {:?} arms={:?}",
                        handler.id,
                        handler
                            .arms
                            .iter()
                            .map(|a| (&a.effect, a.entry))
                            .collect::<Vec<_>>()
                    );
                }
            }
        });
    }

    #[test]
    #[ignore = "Phase F debug: std::undet.once layer-by-layer"]
    fn debugs_std_undet_once_scalar_unwrapped_eval_layers() {
        let source = r#"use std::undet::*

case (each [1, 2, 3]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
"#;

        run_with_large_stack(|| {
            let module =
                runtime_module_from_source_with_options(source, native_default_source_options())
                    .expect("runtime module");

            let cps = crate::cps_lower::lower_cps_module(&module).expect("CPS lowering");
            crate::cps_validate::validate_cps_module(&cps).expect("CPS validation");

            crate::cps_compare::compare_cps_module(&module).expect("CPS eval == VM");
            eprintln!("Layer 1 (CPS eval): OK");

            let repr = crate::cps_repr::lower_cps_repr_module(&cps);
            let repr_values = crate::cps_repr::eval_cps_repr_module(&repr).expect("CPS repr eval");
            let vm_results = runtime::compile_vm_module(module.clone())
                .expect("VM compile")
                .eval_roots()
                .expect("VM eval");
            let vm_value = match &vm_results[0] {
                runtime::VmResult::Value(v) => v.clone(),
                runtime::VmResult::Request(_) => panic!("VM gave request"),
            };
            assert_eq!(repr_values[0], vm_value, "CPS repr eval == VM");
            eprintln!("Layer 2 (CPS repr eval): OK");

            compare_source_cps_repr_i64(source).expect("CPS repr Cranelift compare");
            eprintln!("Layer 3 (CPS repr Cranelift): OK");
        });
    }

    #[test]
    fn compares_std_undet_once_scalar_unwrapped_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"use std::undet::*

case (each [1, 2, 3]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
"#,
            )
            .expect("std undet once scalar unwrapped CPS repr jit compare");
        });
    }

    #[test]
    #[ignore = "Phase F: sum_down requires monomorphic int instantiation; ResidualPolymorphicBinding"]
    fn compares_recursive_closure_self_reference_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"my sum_down(n: int): int = if n == 0:
    0
else:
    n + sum_down (n - 1)

sum_down 5
"#,
            )
            .expect("recursive closure self-reference MakeRecursiveClosure patch");
        });
    }

    #[test]
    fn compares_local_choice_callback_rest_through_cps_repr_cranelift() {
        // Test A from write13: closure callback that performs an effect,
        // with caller's post-call cont needing to run inside inner once's H2.
        // Differs from caller_rest_eval by routing the perform through a
        // closure argument (ApplyClosure path) rather than a direct call.
        let source = r#"pub act choice:
  pub branch: () -> bool
  pub reject: () -> never

my call_callback(f: int -> [choice] int): [choice] int = f 0

my once_dfs_int(x: [choice] int): int = catch x:
  choice::branch (), k -> catch k true:
    choice::reject (), _ -> k false
    v -> v
  choice::reject (), _ -> 0
  v -> v

my work(): [choice] int = {
  my n = call_callback: \_ -> case choice::branch ():
    true -> 1
    false -> 2
  if n == 1:
    choice::reject ()
  else:
    n
}

once_dfs_int { work() }
"#;
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(source)
                .expect("local choice callback rest CPS repr jit compare");
        });
    }

    #[test]
    fn compares_local_choice_caller_rest_through_cps_repr_cranelift() {
        // Minimal test for return-frame semantics: choose() performs branch,
        // work() calls choose() and then guards — the resumption k must capture
        // work's post-call continuation so reject inside work lands in the
        // inner catch's handler (H2), not the outer one (H1).
        let source = r#"pub act choice:
  pub branch: () -> bool
  pub reject: () -> never

my choose(): [choice] int = case choice::branch ():
  true -> 1
  false -> 2

my once_dfs_int(x: [choice] int): int = catch x:
  choice::branch (), k -> catch k true:
    choice::reject (), _ -> k false
    v -> v
  choice::reject (), _ -> 0
  v -> v

my work(): [choice] int = {
  my n = choose()
  if n == 1:
    choice::reject ()
  else:
    n
}

once_dfs_int { work() }
"#;
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(source)
                .expect("local choice caller rest CPS repr jit compare");
        });
    }

    #[test]
    #[ignore = "Phase F debug: std::undet.once with reject layer-by-layer"]
    fn debugs_std_undet_once_skip_eval_layers() {
        let source = r#"use std::undet::*

my work(): int = {
    my n = each [1, 2, 3]
    guard: n > 1
    n
}

case work().once:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
"#;

        run_with_large_stack(|| {
            let module =
                runtime_module_from_source_with_options(source, native_default_source_options())
                    .expect("runtime module");

            let cps = crate::cps_lower::lower_cps_module(&module).expect("CPS lowering");
            crate::cps_validate::validate_cps_module(&cps).expect("CPS validation");

            crate::cps_compare::compare_cps_module(&module).expect("CPS eval == VM");
            eprintln!("Layer 1 (CPS eval): OK");

            let repr = crate::cps_repr::lower_cps_repr_module(&cps);
            let repr_values = crate::cps_repr::eval_cps_repr_module(&repr).expect("CPS repr eval");
            let vm_results = runtime::compile_vm_module(module.clone())
                .expect("VM compile")
                .eval_roots()
                .expect("VM eval");
            let vm_value = match &vm_results[0] {
                runtime::VmResult::Value(v) => v.clone(),
                runtime::VmResult::Request(_) => panic!("VM gave request"),
            };
            assert_eq!(repr_values[0], vm_value, "CPS repr eval == VM");
            eprintln!("Layer 2 (CPS repr eval): OK");

            compare_source_cps_repr_i64(source).expect("CPS repr Cranelift compare");
            eprintln!("Layer 3 (CPS repr Cranelift): OK");
        });
    }

    #[test]
    fn compares_std_undet_once_skips_rejected_first_choice_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"use std::undet::*

my mk(): int = {
    my n = each [1, 2, 3]
    guard: n > 1
    n
}

case mk().once:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
"#,
            )
            .expect("std undet once skips rejected first choice");
        });
    }

    #[test]
    fn compares_std_undet_once_all_rejected_explicit_reject_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"use std::undet::*

my mk(): int = {
    my n = each [1, 2, 3]
    if n > 10:
        n
    else:
        reject ()
}

case mk().once:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
"#,
            )
            .expect("std undet once explicit reject all rejected");
        });
    }

    #[test]
    fn compares_std_undet_once_returns_nil_when_all_rejected_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"use std::undet::*

my mk(): int = {
    my n = each [1, 2, 3]
    guard: n > 10
    n
}

case mk().once:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
"#,
            )
            .expect("std undet once nil when all rejected");
        });
    }

    #[test]
    fn compares_std_undet_once_two_nested_choices_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"use std::undet::*

my mk(): int = {
    my a = each [1, 2]
    my b = each [10, 20]
    guard: a + b > 12
    a + b
}

case mk().once:
    std::opt::opt::nil -> 0
    std::opt::opt::just z -> z
"#,
            )
            .expect("std undet once with two nested choices");
        });
    }

    #[test]
    fn compares_std_each_with_local_once_dfs_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"use std::undet::*

my once_dfs_int(x: [std::undet::undet] int): int = catch x:
    branch (), k -> catch k true:
        reject (), _ -> k false
        v -> v
    reject (), _ -> 0
    v -> v

once_dfs_int { each [1, 2, 3] }
"#,
            )
            .expect("std each with local once_dfs CPS repr jit compare");
        });
    }

    #[test]
    fn compares_prelude_source_once_finite_each_list_recursive_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choice:
  pub branch: () -> bool
  pub reject: () -> never

my once_dfs_int(x: [choice] int): int = catch x:
    choice::branch (), k -> catch k true:
        choice::reject (), _ -> k false
        v -> v
    choice::reject (), _ -> 0
    v -> v

my each_list(xs: std::list::list int): [choice] int = case std::list::uncons xs:
    std::opt::opt::nil -> choice::reject ()
    std::opt::opt::just (x, rest) -> case choice::branch ():
        true -> x
        false -> each_list rest

once_dfs_int { each_list [1, 2, 3] }
"#,
            )
            .expect("source once finite each_list recursive CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_opt_just_case_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"case std::opt::opt::just 2:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
"#,
            )
            .expect("source opt::just case CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_std_undet_once_value_arm_only_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"use std::undet::*

case (each [2]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
"#,
            )
            .expect("std undet once value-arm-only CPS repr jit compare");
        });
    }

    #[test]
    fn compiles_std_undet_once_through_cps_repr_object() {
        run_with_large_stack(|| {
            let module = runtime_module_from_source_with_options(
                "each [1, 2, 3] .once",
                native_default_source_options(),
            )
            .expect("std undet once runtime module");
            let object =
                crate::cps_repr_cranelift::compile_runtime_module_to_cps_repr_object(&module)
                    .expect("std undet once CPS repr object");
            assert!(!object.bytes().is_empty());
            assert_eq!(object.roots(), &["root_0".to_string()]);
        });
    }

    #[test]
    fn compares_prelude_source_higher_order_lambda_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"my apply(f: int -> int, x: int): int = f x

apply(\x -> x + 1, 41)
"#,
            )
            .expect("source higher-order lambda CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_direct_call_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

my id x = x

catch choose::pick 41:
    choose::pick x, k -> id (k x)
"#,
            )
            .expect("source handler direct-call CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_block_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k ->
        my y = k x
        y + 1
"#,
            )
            .expect("source handler block CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_effect_inside_primitive_arg_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 1 + 2:
    choose::pick x, k -> k x
"#,
            )
            .expect("source effect-in-primitive CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_value_arm_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> k x
    value -> value + 1
"#,
            )
            .expect("source handler value-arm CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_bool_if_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> if true: k x else: k x + 1
"#,
            )
            .expect("source handler bool-if CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_comparison_if_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> if x < 0: k x else: k x + 1
"#,
            )
            .expect("source handler comparison-if CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_or_if_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> if x < 0 or x == 0: k x else: k x + 1
"#,
            )
            .expect("source handler or-if CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_and_if_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> if x < 0 and x == 0: k x else: k x + 1
"#,
            )
            .expect("source handler and-if CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_not_if_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> if not (x < 0): k x else: k x + 1
"#,
            )
            .expect("source handler not-if CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_nested_if_condition_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k -> if if x < 0: false else: true: k x else: k x + 1
"#,
            )
            .expect("source handler nested-if condition CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_prelude_source_handler_arm_let_condition_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64(
                r#"pub act choose:
  pub pick: int -> int

catch choose::pick 41:
    choose::pick x, k ->
        my c = x < 0 or x == 0
        if c: k x else: k x + 1
"#,
            )
            .expect("source handler let condition CPS repr jit compare with prelude");
        });
    }

    #[test]
    fn compares_std_sub_return_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            compare_source_cps_repr_i64("std::flow::sub::sub { std::flow::sub::return 41 }")
                .expect("std sub return CPS repr jit compare");
        });
    }

    #[test]
    fn evals_mutable_ref_edit_through_cps_repr_cranelift() {
        run_with_large_stack(|| {
            let source = r#"
{
    my $x = 1
    &x = $x + 2
    $x
}
"#;
            let module =
                runtime_module_from_source_with_options(source, native_default_source_options())
                    .expect("mutable ref runtime module");
            let cps = crate::cps_lower::lower_cps_module(&module)
                .expect("mutable ref CPS lowering should preserve recursive thunk calls");
            crate::cps_validate::validate_cps_module(&cps).expect("mutable ref CPS validation");

            let lowered = format!("{cps:#?}");
            assert!(lowered.contains("&x#"));
            assert!(lowered.contains("MakeThunk"));
            assert!(lowered.contains("ForceThunk"));
            assert!(lowered.contains("ResumeWithHandler"));

            compare_source_cps_repr_i64(source).expect("mutable ref CPS repr Cranelift compare");
            let values = eval_source_cps_repr_i64(source).expect("mutable ref CPS repr Cranelift");
            assert_eq!(values, vec![3]);
        });
    }

    #[test]
    fn analyzes_string_source_as_runtime_pointer_lane() {
        let analysis =
            analyze_source_abi_reprs_with_options("\"hello\"", infer::SourceOptions::default())
                .expect("native ABI reprs");

        assert_eq!(
            analysis.function_repr("root_0"),
            Some(&NativeAbiRepr::RuntimeValuePtr(
                NativeRuntimePtrKind::String
            ))
        );
        assert_eq!(
            analysis.function_lane("root_0"),
            Some(NativeAbiValueLane::RuntimeValuePtr)
        );
    }

    #[test]
    fn evals_string_source_through_cranelift_value_lane() {
        let values =
            eval_source_value_lane_with_options("\"hello\"", infer::SourceOptions::default())
                .expect("native value jit eval");

        assert_eq!(
            values,
            vec![runtime::VmValue::String(
                runtime::runtime::string_tree::StringTree::from_str("hello")
            )]
        );
    }

    #[test]
    fn evals_string_concat_source_through_cranelift_value_lane() {
        let value = run_with_large_stack(|| {
            let values = eval_source_value_lane("\"a\" + \"b\"").expect("native value jit eval");
            let [runtime::VmValue::String(value)] = values.as_slice() else {
                panic!("expected one string value");
            };
            value.to_flat_string()
        });

        assert_eq!(value, "ab");
    }

    #[test]
    fn evals_scalar_sources_through_cranelift_value_lane() {
        let values =
            eval_source_value_lane_with_options("true\n()\n1.5", infer::SourceOptions::default())
                .expect("native value jit eval");

        assert_eq!(
            values,
            vec![
                runtime::VmValue::Bool(true),
                runtime::VmValue::Unit,
                runtime::VmValue::Float("1.5".to_string())
            ]
        );
    }

    #[test]
    fn evals_numeric_and_bool_primitives_through_cranelift_value_lane() {
        let values = run_with_large_stack(|| {
            eval_source_value_lane("1 + 2\n5 - 3\n2 * 4\n8 / 2\n1 < 2\nnot false")
                .expect("native value jit eval")
                .into_iter()
                .map(|value| match value {
                    runtime::VmValue::Int(value) => format!("int:{value}"),
                    runtime::VmValue::Bool(value) => format!("bool:{value}"),
                    value => panic!("expected int or bool value, got {value:?}"),
                })
                .collect::<Vec<_>>()
        });

        assert_eq!(
            values,
            vec![
                "int:3".to_string(),
                "int:2".to_string(),
                "int:8".to_string(),
                "int:4".to_string(),
                "bool:true".to_string(),
                "bool:true".to_string(),
            ]
        );
    }

    #[test]
    fn evals_local_and_top_level_bindings_through_cranelift_value_lane() {
        let values = run_with_large_stack(|| {
            eval_source_value_lane(
                r#"
my top = 2
my total = top + 3

{
    my local = total + 4
    {answer: local}.answer
}
"#,
            )
            .expect("native value jit eval")
            .into_iter()
            .map(|value| match value {
                runtime::VmValue::Int(value) => value,
                value => panic!("expected int value, got {value:?}"),
            })
            .collect::<Vec<_>>()
        });

        assert_eq!(values, vec!["9"]);
    }

    #[test]
    fn evals_list_literal_source_through_cranelift_value_lane() {
        let items = run_with_large_stack(|| {
            let values = eval_source_value_lane("[1, 2, 3]").expect("native value jit eval");
            let [runtime::VmValue::List(list)] = values.as_slice() else {
                panic!("expected one list value");
            };
            list.to_vec()
                .into_iter()
                .map(|value| match value.as_ref() {
                    runtime::VmValue::Int(value) => value.clone(),
                    value => panic!("expected int list item, got {value:?}"),
                })
                .collect::<Vec<_>>()
        });

        assert_eq!(items, vec!["1", "2", "3"]);
    }

    #[test]
    fn evals_list_len_and_index_source_through_cranelift_value_lane() {
        let values = run_with_large_stack(|| {
            eval_source_value_lane("[1, 2].len\n[1, 2].index 1")
                .expect("native value jit eval")
                .into_iter()
                .map(|value| match value {
                    runtime::VmValue::Int(value) => value,
                    value => panic!("expected int value, got {value:?}"),
                })
                .collect::<Vec<_>>()
        });

        assert_eq!(values, vec!["2", "2"]);
    }

    #[test]
    fn evals_structural_sources_through_cranelift_value_lane() {
        let values = eval_source_value_lane_with_options(
            "(1, 2)\n{x: 1, y: 2}\n{x: 1, y: 2}.x\nmy get_y p = p.y\nget_y {x: 3, y: 4}\n:label \"send\"",
            infer::SourceOptions::default(),
        )
        .expect("native value jit eval");

        assert_eq!(
            values,
            vec![
                runtime::VmValue::Tuple(vec![
                    runtime::VmValue::Int("1".to_string()),
                    runtime::VmValue::Int("2".to_string())
                ]),
                runtime::VmValue::Record(BTreeMap::from([
                    (
                        yulang_typed_ir::Name("x".to_string()),
                        runtime::VmValue::Int("1".to_string())
                    ),
                    (
                        yulang_typed_ir::Name("y".to_string()),
                        runtime::VmValue::Int("2".to_string())
                    )
                ])),
                runtime::VmValue::Int("1".to_string()),
                runtime::VmValue::Int("4".to_string()),
                runtime::VmValue::Variant {
                    tag: yulang_typed_ir::Name("label".to_string()),
                    value: Some(Box::new(runtime::VmValue::String(
                        runtime::runtime::string_tree::StringTree::from_str("send")
                    )))
                }
            ]
        );
    }

    #[test]
    fn emits_string_source_value_object() {
        let object =
            compile_source_value_object_with_options("\"hello\"", infer::SourceOptions::default())
                .expect("native value object");

        assert!(!object.bytes().is_empty());
        assert_eq!(object.roots(), &["root_0".to_string()]);
    }

    #[test]
    fn analyzes_list_source_element_repr() {
        let analysis = run_with_large_stack(|| {
            analyze_source_abi_reprs("[1, 2, 3]").expect("native ABI reprs")
        });

        assert_eq!(
            analysis.function_repr("root_0"),
            Some(&NativeAbiRepr::List(Box::new(NativeAbiRepr::Int)))
        );
        assert_eq!(
            analysis.function_lane("root_0"),
            Some(NativeAbiValueLane::RuntimeValuePtr)
        );
    }

    #[test]
    fn source_diagnostics_are_reported_before_runtime_lowering() {
        let error = eval_source_with_options("missing_name", infer::SourceOptions::default())
            .expect_err("diagnostic");
        assert!(matches!(error, NativeSourceError::SurfaceDiagnostics(_)));
    }

    fn run_with_large_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(f)
            .expect("spawn native source test thread")
            .join()
            .expect("join native source test thread")
    }
}
