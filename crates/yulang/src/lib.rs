//! 新 `sources` / `infer` / `poly` route を実ファイルから試すための薄い入口。
//!
//! この crate は現行 `yulang` CLI の大きい pipeline から独立した実験用 binary である。

pub mod artifact;
pub mod cache;
mod playground_std;
#[cfg(not(target_arch = "wasm32"))]
pub mod server;
pub mod source;
pub mod stdlib;
mod time;

pub use source::{
    AnalyzeSourceOutput, BuildControlOutput, BuildPolyOutput, CheckPolyOutput, CollectedSource,
    ControlRunTimings, DumpMonoOutput, DumpPolyOutput, IMPLICIT_PRELUDE_IMPORT, RouteError,
    RunControlOutput, RunMonoOutput, SourceDiagnostic, SourceHover, SourceRange, StdSourceOptions,
    analyze_entry_source, analyze_entry_source_with_std_options,
    analyze_source_text_with_embedded_std, build_control_from_collected_sources,
    build_control_from_entry, build_control_from_entry_with_std,
    build_control_from_entry_with_std_options, build_control_from_poly_output,
    build_control_from_source_text_with_embedded_playground_std,
    build_control_from_source_text_with_embedded_std, build_poly_from_collected_sources,
    build_poly_from_loaded_files, build_poly_from_source_text_with_embedded_playground_std,
    build_poly_from_source_text_with_embedded_std, check_poly_from_entry,
    check_poly_from_entry_with_std, check_poly_from_entry_with_std_in_module,
    check_poly_from_entry_with_std_in_module_options, check_poly_from_entry_with_std_options,
    check_poly_from_source_text_with_embedded_std, collect_local_source_text,
    collect_local_source_text_with_std_options, collect_local_sources,
    collect_local_sources_with_std, collect_local_sources_with_std_options,
    collect_source_text_with_embedded_playground_std, collect_source_text_with_embedded_std,
    dump_mono_from_entry, dump_mono_from_entry_with_std, dump_mono_from_entry_with_std_options,
    dump_mono_from_source_text_with_embedded_std, dump_poly_from_entry,
    dump_poly_from_entry_with_std, dump_poly_from_entry_with_std_in_module,
    dump_poly_from_entry_with_std_in_module_options, dump_poly_from_entry_with_std_options,
    dump_poly_from_source_text_with_embedded_std, dump_poly_raw_from_entry,
    dump_poly_raw_from_entry_with_std, dump_poly_raw_from_entry_with_std_in_module,
    dump_poly_raw_from_entry_with_std_in_module_options, dump_poly_raw_from_entry_with_std_options,
    dump_poly_raw_from_source_text_with_embedded_std, find_nearby_std_root, format_run_mono_values,
    hover_entry_source, hover_entry_source_with_std_options,
    load_source_text_with_embedded_playground_std, load_source_text_with_embedded_std,
    run_built_control_program, run_control_from_entry, run_control_from_entry_with_std,
    run_control_from_entry_with_std_options, run_control_from_source_text_with_embedded_std,
    run_mono_from_entry, run_mono_from_entry_with_std, run_mono_from_entry_with_std_options,
};
