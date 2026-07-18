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
mod yumark_eval;
#[cfg(not(target_arch = "wasm32"))]
mod yumark_render_worker;

pub use yumark_eval::{
    YumarkLiteralEvaluationError, evaluate_doc_comment_render_input_markdown_with_embedded_std,
    evaluate_yumark_literal_markdown_with_embedded_std,
};
#[cfg(not(target_arch = "wasm32"))]
pub use yumark_render_worker::{
    DEFAULT_DOC_COMMENT_RENDER_CACHE_CAPACITY, DocCommentRenderWorker, DocCommentRenderWorkerError,
};

pub use source::{
    AnalyzeSourceOutput, BuildControlOutput, BuildPolyAndCompiledUnitOutput, BuildPolyOutput,
    CheckDiagnosticSource, CheckPolyOutput, CollectedSource, DumpMonoOutput, DumpPolyOutput,
    IMPLICIT_PRELUDE_IMPORT, IMPLICIT_STD_SOURCE_PREFIX_LEN, ParseDiagnosticsOutput,
    RealmInstallError, RealmInstallOutput, RouteError, RunMonoOutput, SourceCollectionCache,
    SourceCompilationUnit, SourceCompilationUnits, SourceDefinition, SourceDiagnostic,
    SourceDiagnosticRelatedOrigin, SourceDiagnosticSeverity, SourceHover, SourceLocation,
    SourceRange, SourceRename, SourceTextEdit, StdSourceOptions, analyze_entry_source,
    analyze_entry_source_with_std_options, analyze_source_text_with_embedded_std,
    build_control_from_collected_sources, build_control_from_entry,
    build_control_from_entry_with_std, build_control_from_entry_with_std_options,
    build_control_from_poly_output, build_control_from_source_text_with_embedded_playground_std,
    build_control_from_source_text_with_embedded_std,
    build_poly_and_compiled_unit_from_collected_sources,
    build_poly_and_compiled_unit_from_compiled_unit_prefix_and_collected_sources,
    build_poly_from_collected_sources, build_poly_from_compiled_unit_artifact,
    build_poly_from_compiled_unit_prefix_and_collected_sources,
    build_poly_from_embedded_playground_std_compiled_unit_artifact,
    build_poly_from_embedded_std_compiled_unit_artifact, build_poly_from_loaded_files,
    build_poly_from_source_text_with_embedded_playground_std,
    build_poly_from_source_text_with_embedded_std, check_poly_from_entry,
    check_poly_from_entry_with_std, check_poly_from_entry_with_std_in_module,
    check_poly_from_entry_with_std_in_module_options, check_poly_from_entry_with_std_options,
    check_poly_from_source_text_with_embedded_std, collect_local_source_text,
    collect_local_source_text_with_std_options, collect_local_sources,
    collect_local_sources_with_cache, collect_local_sources_with_std,
    collect_local_sources_with_std_options, collect_local_sources_with_std_options_and_cache,
    collect_source_text_with_embedded_playground_std, collect_source_text_with_embedded_std,
    definition_entry_source, definition_entry_source_with_std_options, dump_mono_from_entry,
    dump_mono_from_entry_with_std, dump_mono_from_entry_with_std_options,
    dump_mono_from_source_text_with_embedded_std, dump_poly_from_entry,
    dump_poly_from_entry_with_std, dump_poly_from_entry_with_std_in_module,
    dump_poly_from_entry_with_std_in_module_options, dump_poly_from_entry_with_std_options,
    dump_poly_from_source_text_with_embedded_std, dump_poly_raw_from_entry,
    dump_poly_raw_from_entry_with_std, dump_poly_raw_from_entry_with_std_in_module,
    dump_poly_raw_from_entry_with_std_in_module_options, dump_poly_raw_from_entry_with_std_options,
    dump_poly_raw_from_source_text_with_embedded_std, find_nearby_std_root, format_run_mono_values,
    format_run_mono_values_with_labels, hover_entry_source, hover_entry_source_with_std_options,
    install_local_realm, load_source_text_with_embedded_playground_std,
    load_source_text_with_embedded_std, parse_diagnostics_from_collected_sources,
    prepare_rename_entry_source, prepare_rename_entry_source_with_std_options,
    references_entry_source, references_entry_source_with_std_options, rename_entry_source,
    rename_entry_source_with_std_options, resolve_std_root_for_entry, run_mono_from_entry,
    run_mono_from_entry_with_std, run_mono_from_entry_with_std_options, source_compilation_units,
    source_text_needs_full_embedded_std_for_playground,
    warm_embedded_playground_std_compiled_unit_artifact_prefix,
    warm_embedded_std_compiled_unit_artifact_prefix,
};
