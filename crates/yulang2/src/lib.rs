//! 新 `sources` / `infer` / `poly` route を実ファイルから試すための薄い入口。
//!
//! この crate は現行 `yulang` CLI の大きい pipeline から独立した実験用 binary である。

pub mod source;

pub use source::{
    CollectedSource, DumpPolyOutput, IMPLICIT_PRELUDE_IMPORT, RouteError, collect_local_sources,
    collect_local_sources_with_std, dump_poly_from_entry, dump_poly_from_entry_with_std,
    find_nearby_std_root,
};
