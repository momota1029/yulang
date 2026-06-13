//! 新 `sources` / `infer` / `poly` route を実ファイルから試すための薄い入口。
//!
//! この crate は現行 `yulang` CLI の大きい pipeline から独立した実験用 binary である。

pub mod source;

pub use source::{
    CheckPolyOutput, CollectedSource, DumpMonoOutput, DumpPolyOutput, IMPLICIT_PRELUDE_IMPORT,
    RouteError, check_poly_from_entry_with_std, check_poly_from_entry_with_std_in_module,
    collect_local_sources, collect_local_sources_with_std, dump_mono_from_entry,
    dump_mono_from_entry_with_std, dump_poly_from_entry, dump_poly_from_entry_with_std,
    dump_poly_from_entry_with_std_in_module, dump_poly_raw_from_entry,
    dump_poly_raw_from_entry_with_std, dump_poly_raw_from_entry_with_std_in_module,
    find_nearby_std_root,
};
