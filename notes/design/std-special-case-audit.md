# Std Special Case Audit

このメモは、`std` path や path suffix で処理系の挙動を分岐している箇所を
洗い出し、どれを消すべきかを追跡するための作業メモ。

基本方針:

- sugar の入口に閉じた `std` 参照は許容する。
  - 例: `for` を `std::flow::loop::for_in` へ展開する入口。
  - 例: `$x` / `&x = v` を `std::var` の synthetic act へ展開する入口。
- sugar 以外で、任意の `std::...` path か末尾名で型・effect・signature を補う
  処理は撤去対象とする。
- `std` を特別扱いする必要がある bootstrap は、散在させず semantic table /
  primitive table / runtime tag へ寄せる。
- 任意 path の `segments.ends_with(...)` は、ユーザー定義との衝突を起こすため
  原則として撤去対象とする。

## Production Hot Spots

### Runtime Monomorphize: Associated Signature Closure

場所:

- `crates/yulang-runtime/src/monomorphize/associated.rs`
- `crates/yulang-runtime/src/monomorphize/check.rs`
- `crates/yulang-runtime/src/monomorphize/emit.rs`
- `crates/yulang-runtime/src/monomorphize/specialize.rs`
- `crates/yulang-runtime/src/monomorphize/solve.rs`

残っている主な path 依存:

- production の target 判定としての `std` exact path / suffix match は撤去済み。
- primitive result type は、既存 signature / runtime type に出ている constructor を
  再利用して閉じる。
  - `associated.rs` は `std::list::list` / `std::list::list_view` /
    `std::opt::opt` / `std::var::ref` を生成しない。
  - `check.rs` / `emit.rs` の list primitive hint も、式自体の result type
    constructor を再利用する。
- test fixture の `std::...` path。

問題:

- monomorphize の型穴閉じ・effect 消費・specialization materialize 判定が
  `std` の exact path に依存していた。
- source std と embedded std artifact のどちらでも動くが、ユーザーが同等の
  protocol を定義しても同じ扱いにならない。
- `std` の名前や配置を変えると runtime 側の複数箇所を同時に直す必要がある。

撤去方針:

- monomorphize は binding shape から `Fold` / `for_in` / handler collection などを
  推測して signature hole を閉じない。
- list / opt / ref の primitive family table は、今後の bootstrap metadata として
  追加する。現時点の monomorphize は、型に現れた constructor を再利用する。
- `associated.rs` は default effect hole closure だけを担当する。

### Runtime Lower

場所:

- `crates/yulang-runtime/src/lower/function.rs`
- `crates/yulang-runtime/src/lower/primitive_types.rs`
- `crates/yulang-runtime/src/lower/lowerer.rs`
- `crates/yulang-runtime/src/lower/evidence.rs`
- `crates/yulang-runtime/src/lower/effects.rs`

残っている主な特例:

- primitive type family は `CoreGraphView::primitive_types` から runtime lower へ
  渡すところまで進んだ。
- graph metadata が欠ける古い artifact / test fixture では、保守的に fixed
  bootstrap table へ fallback する。
- effect operation の path 解決で `#effect` suffix や candidate path suffix を見る。

問題:

- 末尾名だけの判定は、ユーザー定義 `my::list` や `foo::str` と衝突する。
- primitive 型 bootstrap と通常の名前解決が同じ見た目で混ざっている。

撤去方針:

- primitive type family を compiled-unit artifact metadata に載せ、`CoreGraphView`
  と同じ family id / path を artifact import へ渡す。
- `list` / `str` / `int` / `range` の判定は path 文字列ではなく family id で行う。
- effect operation の suffix fallback は、act/effect namespace 由来の構造化解決に
  置き換える。

### Infer / Lower Primitive Bootstrap

場所:

- `crates/yulang-infer/src/lower/primitives/*.rs`
- `crates/yulang-infer/src/lower/expr/literal.rs`
- `crates/yulang-infer/src/lower/expr/list.rs`
- `crates/yulang-infer/src/lower/stmt/patterns/check.rs`

残っている主な特例:

- primitive family は `builtin_types.rs` に集約済みだが、まだ compiled-unit artifact
  由来ではなく固定 bootstrap table。
- `std_ref_paths` / `std_flow_paths` は sugar/bootstrap の標準展開先として
  `std` path を持つ。

問題:

- これは sugar ではなく primitive bootstrap なので、必要ではあるが散在させると
  `std` 固定になる。

撤去方針:

- primitive bootstrap table を 1 箇所に集約する。
- lowering 側は `PrimitiveFamily::{Int, Float, Bool, Str, List, Range, Unit}` の
  ような安定 id を受け取る。
- `std` source 側の companion module は、その primitive family に後から
  method / role impl を足すものとして扱う。

### Role / Effect Suffix Matching

場所:

- `crates/yulang-infer/src/solve/role.rs`
- `crates/yulang-runtime/src/monomorphize/check.rs`

残っている主な特例:

- role method / effect path 比較で `segments.ends_with(...)` を許す。

問題:

- 同じ末尾名の user role / user effect が accidental match する。
- `std` 特例ではないが、同じ構造の path 特例なので撤去対象。

撤去方針:

- import / reexport 後の canonical id で比較する。
- 省略名を許す場合も、名前解決 phase で canonical path に確定させてから
  solve / runtime へ渡す。

## Allowed Or Isolated Cases

### Sugar Entrypoints

現時点で sugar として隔離してよいもの:

- `for` / labelled loop lowering
- `sub` / labelled `sub` lowering
- `$x` / `&x = value` lowering
- list literal / range literal / scalar literal の primitive family 接続

ただし、これらも最終的には path 文字列ではなく semantic table を通す。

### Implicit Prelude

`crates/yulang-sources/src/lib.rs` の `use std::prelude::*` 注入は言語 surface の
仕様として扱う。これは runtime 側の std 特例とは別枠。

### Debug / Diagnostic Only

次は挙動ではなく表示・debug filter なので優先度を下げる:

- `crates/yulang-runtime/src/diagnostic.rs` の std int op 表示名。
- `YULANG_DEBUG_*` 系の target path filter。

ただし、debug filter でも suffix matching は誤診断の原因になるので、挙動判定からは
外していく。

## Recently Removed

- 任意の末尾名 `add` だけで list merge signature closure を入れる処理。
- 任意の末尾名 `fold` / `fold_impl` だけで Fold signature closure を入れる処理。
- `std::fold::Fold::find` exact path だけで Fold find signature closure を入れる処理。
- handler consumed effect は binding body の `handle` 構造から拾う入口を追加した。
  - 残る exact std path は bootstrap fallback として隔離中。
- `AssociatedSignatureKind` と associated demand signature closure を撤去した。
  - `for_in` / `Fold` / `Fold::find` / `ListViewRaw` / handler collection /
    local var ref/run について、binding body/type/primitive/role impl graph から
    target を分類して signature hole を補完する処理は残さない。
  - 既知 target として consumed effect を補う処理も撤去し、pure handler body から
    直接読める consumed effect だけを見る。
- complete principal export から、role requirement の `item` associated type を
  `list` / `range` の path 末尾名で逆算する処理を撤去した。
  - substitution は call slot / exported bounds / expected evidence から取れる情報だけで
    作る。
- runtime effect compatibility から、`std::flow::loop` を含む expected effect が
  任意の actual effect を通す特例を撤去した。
  - effect parent と child operation の prefix match は通常規則として残す。
- core/runtime/infer の numeric widening から、任意 path の末尾名 `int` / `float`
  判定を撤去した。
  - 現時点では context を持たない層なので、bare `int` -> bare `float` の完全一致だけを
    bootstrap fallback として残す。
- runtime VM の int-to-float cast 判定から、任意 path の末尾名 `float` 判定を撤去した。
- monomorphize type normalization から、末尾名 `sub` の effect payload を value type で
  後付け補完する処理を撤去した。
- VM effect operation erase から、consumed effect namespace の末尾名と単一 operation 名が
  一致したとき namespace 自体へ解決する分岐を撤去した。
  - 単一 operation 名は consumed effect namespace に operation 名を足す通常解決だけを使う。
- ordinary role method call resolution から、method 名 `cast` の特別分岐を撤去した。
  - 明示 coercion 用の `resolve_cast_method` は残るが、通常の `.cast` method call は
    他の role method と同じ resolver を通る。
- ref list index projection は compiler export の専用分岐から外し、
  `lib/std/list.yu` の `Index (ref 'e (list 'a)) int` impl へ移した。
  - `&xs[i] = v` は通常の index selection で child ref を得て、通常の ref set export を通る。
  - `foo.index(x)` と suffix `foo[x]` を compiler export が区別して覚える必要はなくなった。
- lower の handle effect operation 解決から、runtime symbol 候補の namespace suffix
  fallback を撤去した。既に `RuntimeSymbolKind::EffectOperation` として登録済みの
  path か、同一 namespace の `#effect` hidden path だけを使う。
- lower/refine/validate の constructor 判定から `nil` / `just` 固定名を外した。
  期待型の親 type path と constructor path の親子関係だけを見る。
- lower の list pattern item 推定から、型 path 末尾 `list` 判定を外した。
  現状は単一 type arg を持つ runtime container shape を見る暫定形。
- monomorphize の `segments.ends_with(...)` 系 helper は exact match または撤去へ
  置き換えた。任意 suffix match は production hot path から外した。
- demand check / associated / emit の list / opt payload 抽出は、`std::list::list` /
  `std::opt::opt` の path ではなく単一 type arg shape を見る。
- demand check / associated の `std::var::ref` / `std::var::ref_update` 再判定は、
  内部 refine では type arg shape を見る。
- debug filter のためだけの `std` target path 判定を撤去した。
- Fold member collection と associated signature closure 用の role impl graph scan を
  撤去した。
- effect path matching から任意 suffix match を外した。
  - `std::flow::sub` と `user::std::flow::sub` は一致しない。
  - parent effect と child operation の prefix 関係だけは残す。
- `Fold::item` の demand closure 自体を撤去した。list/range item を role impl graph
  から推測して callback signature を補う処理は残さない。
- demand unifier の `std::flow::loop::{last,next,redo}` /
  `std::flow::label_loop::{last,next,redo}` family match を撤去した。
- runtime monomorphize / lower / refine / validate の production scan で、
  `path_is(... ["std", ...])` / `path_has_prefix(... ["std", ...])` /
  `ends_with(...)` / `path_ends_with` は検出されない状態にした。
- infer の `std_var_ref_path` / `is_std_var_ref_path` を撤去した。
  - `Infer` が `ref_type_paths` metadata を持つ。
  - selection は path 文字列ではなく `Infer::is_ref_type_path` を見る。
  - `std::var::ref` の path 構築は `std_ref_paths` の sugar/bootstrap 入口へ集約した。
- infer の role method prefix suffix match を撤去し、canonical role path の完全一致にした。
- `for` / `sub` / labelled loop sugar 入口の `std::flow` path 構築を
  `std_flow_paths` へ集約した。
  - lowering 本体は `crate::std_flow_paths::*` を呼ぶ。
  - `std::flow` の文字列は sugar/bootstrap path module だけに置く。
- `associated.rs` / `check.rs` / `emit.rs` の runtime type constructor 生成から
  `std::list` / `std::opt` / `std::var` の直書きを外した。
  - constructor は expected/runtime signature に含まれる `Named` path を再利用する。
- runtime lower の `std_types.rs` を `primitive_types.rs` に置き換え、literal /
  bool / unit の型生成を `PrimitiveTypeFamily` 経由にした。
- runtime lower の `Lowerer` が `RuntimePrimitivePathTable` を持つようにした。
  - expression / pattern / evidence / effect helper は、裸の `bool_type` /
    `unit_type` / literal type helper ではなく `Lowerer` の table を通す。
- `CoreGraphView::primitive_types` に primitive type family metadata を追加した。
  - infer export は `LowerState::primitive_paths` から `PrimitiveTypeGraphNode` を吐く。
  - runtime lower は `RuntimePrimitivePathTable::from_graph` で graph metadata を
    優先し、欠けた family だけ fixed bootstrap path に fallback する。
  - compiled runtime surface merge は primitive metadata を dedupe し、同じ family が
    異なる path を指す場合は conflict として拒否する。
- infer lower の primitive type/value path を `builtin_types.rs` に集約した。
  - `LowerState` は `PrimitivePathTable` を持つ。
  - list literal、list pattern、list primitive installer は `std::list::list` /
    `std::range::range` / `std::list::list_view` を直接組み立てない。
  - string concat は `PrimitiveValueFamily` 経由にし、state の table から path を読む入口を作った。
  - ref list index projection は std の `Index` impl へ移したため、export-time
    `std::list::index_raw` path は不要になった。
- `$x` fallback と var synthetic act helper source は `std_ref_paths` 経由にした。
- `for` / `sub` / labelled loop / `$x` / `&x = v` は Rust の `for in` と同じく、
  標準 protocol への糖衣展開として扱う。ここに新しい compiled artifact
  metadata は導入しない。
- ref field projection selection は `Infer::primary_ref_type_path` を使い、固定
  `std::var::ref` path を推論判定として再生成しない。
- ref field projection export は `std_ref_paths` の標準 path helper へ集約した。
  ref index projection export は撤去し、std の `Index` impl に寄せた。
- runtime symbol export は root binding path だけでなく、lowered program が知る
  effect operation def も `RuntimeSymbolKind::EffectOperation` として出す。
  - std/user module 越しに参照された operation が、root binding でなくても runtime
    lower で束縛済み symbol として扱われる。

## Next Removal Order

1. primitive family table を compiled-unit artifact metadata に渡す。
   - `CoreGraphView` までは family id を明示的に渡せるようになった。
   - `CompiledRuntimeSurface` は `CoreProgram` ごと primitive metadata を保持し、
     merge でも落とさない。
   - 次は persistent artifact の manifest / runtime surface へ同じ metadata を
     入れる。
2. sugar 展開先の `std_ref_paths` / `std_flow_paths` は、当面標準 protocol として
   受け入れる。
   - std source に専用 metadata は持たせない。
   - compiled namespace artifact に ref/flow sugar metadata は載せない。
   - ここを一般化するより、推論・runtime 側の path 判定を減らす作業を優先する。
