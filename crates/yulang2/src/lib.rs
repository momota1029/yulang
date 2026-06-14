//! 新 `sources` / `infer` / `poly` route を実ファイルから試すための薄い入口。
//!
//! この crate は現行 `yulang` CLI の大きい pipeline から独立した実験用 binary である。

pub mod artifact;
pub mod source;
pub mod stdlib;

pub use source::{
    BuildControlOutput, CheckPolyOutput, CollectedSource, DumpMonoOutput, DumpPolyOutput,
    IMPLICIT_PRELUDE_IMPORT, RouteError, RunControlOutput, RunMonoOutput, StdSourceOptions,
    build_control_from_entry, build_control_from_entry_with_std,
    build_control_from_entry_with_std_options, check_poly_from_entry,
    check_poly_from_entry_with_std, check_poly_from_entry_with_std_in_module,
    check_poly_from_entry_with_std_in_module_options, check_poly_from_entry_with_std_options,
    collect_local_sources, collect_local_sources_with_std, collect_local_sources_with_std_options,
    dump_mono_from_entry, dump_mono_from_entry_with_std, dump_mono_from_entry_with_std_options,
    dump_poly_from_entry, dump_poly_from_entry_with_std, dump_poly_from_entry_with_std_in_module,
    dump_poly_from_entry_with_std_in_module_options, dump_poly_from_entry_with_std_options,
    dump_poly_raw_from_entry, dump_poly_raw_from_entry_with_std,
    dump_poly_raw_from_entry_with_std_in_module,
    dump_poly_raw_from_entry_with_std_in_module_options, dump_poly_raw_from_entry_with_std_options,
    find_nearby_std_root, run_control_from_entry, run_control_from_entry_with_std,
    run_control_from_entry_with_std_options, run_mono_from_entry, run_mono_from_entry_with_std,
    run_mono_from_entry_with_std_options,
};
