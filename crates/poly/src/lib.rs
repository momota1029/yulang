//! `poly` は、型推論が作った結果を載せる最終寄りの多相 IR。
//!
//! この crate の Arena は、名前解決結果・selection 解決結果・式木・型表現を保持する。
//! 一方で、制約伝播中の上下界、未解決 selection の watcher、SCC の open component など、
//! 推論中だけ必要な可変状態はここへ入れない。それらは `infer` 側の作業用 table に置く。
//!
//! 目的は、あとで cache や serialize の境界を考えるときに、`poly` を「結果として読むもの」、
//! `infer` を「結果を作る途中の機械」として分けられるようにすること。

pub mod dump;
pub mod expr;
pub mod types;
