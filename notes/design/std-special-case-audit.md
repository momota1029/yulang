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

- `DemandSemantics` に semantic tag を集約する。
- `Fold` member / `Fold::find` は role impl graph から判定する。任意の末尾名
  `fold` / `find` 判定は使わない。
- list / opt / ref の primitive family table は、今後の bootstrap metadata として
  追加する。現時点の monomorphize は、型に現れた constructor を再利用する。
- `associated.rs` は `AssociatedSignatureKind` の dispatch だけを見る形へ寄せる。

### Runtime Lower

場所:

- `crates/yulang-runtime/src/lower/function.rs`
- `crates/yulang-runtime/src/lower/primitive_types.rs`
- `crates/yulang-runtime/src/lower/lowerer.rs`
- `crates/yulang-runtime/src/lower/evidence.rs`
- `crates/yulang-runtime/src/lower/effects.rs`

残っている主な特例:

- primitive type family は `primitive_types.rs` に集約し、`Lowerer` が
  `RuntimePrimitivePathTable` を持つところまで進んだ。ただし、まだ core metadata
  から渡される table ではなく固定 bootstrap table。
- effect operation の path 解決で `#effect` suffix や candidate path suffix を見る。

問題:

- 末尾名だけの判定は、ユーザー定義 `my::list` や `foo::str` と衝突する。
- primitive 型 bootstrap と通常の名前解決が同じ見た目で混ざっている。

撤去方針:

- primitive type family を core metadata に持たせ、`Lowerer` の table 初期化元を
  fixed bootstrap から metadata へ置き換える。
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

- primitive family は `builtin_types.rs` に集約済みだが、まだ std source の import
  artifact 由来ではなく固定 bootstrap table。
- `ref_capability` / `flow_capability` は sugar/bootstrap 入口として `std` path を持つ。

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

`crates/yulang-source/src/lib.rs` の `use std::prelude::*` 注入は言語 surface の
仕様として扱う。これは runtime 側の std 特例とは別枠。

### Debug / Diagnostic Only

次は挙動ではなく表示・debug filter なので優先度を下げる:

- `crates/yulang-runtime/src/diagnostic.rs` の std int op 表示名。
- `YULANG_DEBUG_*` 系の target path filter。

ただし、debug filter でも suffix matching は誤診断の原因になるので最終的には
semantic tag へ寄せる。

## Recently Removed

- 任意の末尾名 `add` だけで list merge signature closure を入れる処理。
- 任意の末尾名 `fold` / `fold_impl` だけで Fold signature closure を入れる処理。
- `std::fold::Fold::find` exact path だけで Fold find signature closure を入れる処理。
  - 現在は `Fold` role impl graph から method path を導出する。
- handler consumed effect は binding body の `handle` 構造から拾う入口を追加した。
  - 残る exact std path は bootstrap fallback として隔離中。
- associated demand signature closure の target 判定は `DemandSemantics` の
  `AssociatedSignatureKind` に集約した。
  - `associated.rs` / `check.rs` / `emit.rs` / `specialize.rs` は、`fold_impl` /
    `for_in` / `view_raw` / range fold helper を直接 path で判定しない。
  - consumed-effect 判定も `AssociatedSignatureKind` を再利用し、同じ target 群を
    別々の path if 列で重複判定しない。
  - `DemandSemantics::from_module` は binding path から
    bootstrap tag を作る互換 fallback をまだ持つ。
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
  entrypoint の semantic kind に任せ、内部 refine では type arg shape を見る。
- debug filter のためだけの `std` target path 判定を撤去した。
- Fold member collection は `std::fold::Fold` path ではなく、role impl graph 上の
  `item` associated type と member surface から拾う。
- production query はまず `associated_signature_kinds` map / role impl graph /
  local synthetic ref metadata を見る。
  - bootstrap classifier は撤去済み。
- effect path matching から任意 suffix match を外した。
  - `std::flow::sub` と `user::std::flow::sub` は一致しない。
  - parent effect と child operation の prefix 関係だけは残す。
- `Fold::item` の demand closure は `std::list::list` / `std::range::range` の
  path 判定から外した。
  - `DemandSemantics` は role impl graph から汎用 `AssociatedTypeProjection` を作る。
  - `associated.rs` は role path を固定せず、`item` associated type projection が
    一意に決まるときだけ問い合わせる。
  - list / range の item は、テスト上も `impl Fold ...: type item = ...` から
    得る形にした。
- `DemandSemantics` の bootstrap classifier を撤去した。
  - `for_in` は binding type の callback effect から `ForIn` tag を作る。
  - `sub` handler は binding body/type の consumed effect から `SubHandler` tag を作る。
  - `std::undet::{list,logic,once}` は pure handler shape と result type shape から
    collection handler として扱う。
  - `fold_impl` は body 内の `ListViewRaw` primitive と function arity から
    thunk-callback fold helper として扱う。
  - `std::list::uncons` / `std::range::{fold_from,fold_ints}` / `std::var::ref`
    exact fallback は撤去した。
- demand unifier の `std::flow::loop::{last,next,redo}` /
  `std::flow::label_loop::{last,next,redo}` family match を撤去した。
- runtime monomorphize / lower / refine / validate の production scan で、
  `path_is(... ["std", ...])` / `path_has_prefix(... ["std", ...])` /
  `ends_with(...)` / `path_ends_with` は検出されない状態にした。
- infer の `std_var_ref_path` / `is_std_var_ref_path` を撤去した。
  - `Infer` が `ref_type_paths` metadata を持つ。
  - selection は path 文字列ではなく `Infer::is_ref_type_path` を見る。
  - `std::var::ref` の path 構築は `ref_capability` の sugar/bootstrap 入口へ集約した。
- infer の role method prefix suffix match を撤去し、canonical role path の完全一致にした。
- `for` / `sub` / labelled loop sugar 入口の `std::flow` path 構築を
  `flow_capability` へ集約した。
  - lowering 本体は `crate::flow_capability::*` を呼ぶ。
  - `std::flow` の文字列は sugar/bootstrap capability module だけに置く。
- `associated.rs` / `check.rs` / `emit.rs` の runtime type constructor 生成から
  `std::list` / `std::opt` / `std::var` の直書きを外した。
  - constructor は expected/runtime signature に含まれる `Named` path を再利用する。
  - `ListViewRaw` は `DemandSemantics` tag に result constructor を持たせる。
- runtime lower の `std_types.rs` を `primitive_types.rs` に置き換え、literal /
  bool / unit の型生成を `PrimitiveTypeFamily` 経由にした。
- runtime lower の `Lowerer` が `RuntimePrimitivePathTable` を持つようにした。
  - expression / pattern / evidence / effect helper は、裸の `bool_type` /
    `unit_type` / literal type helper ではなく `Lowerer` の table を通す。
- infer lower の primitive type/value path を `builtin_types.rs` に集約した。
  - `LowerState` は `PrimitivePathTable` を持つ。
  - list literal、list pattern、list primitive installer は `std::list::list` /
    `std::range::range` / `std::list::list_view` を直接組み立てない。
  - string concat と export-time `std::list::index_raw` は `PrimitiveValueFamily`
    経由にし、state の table から path を読む入口を作った。
  - `$x` fallback と var synthetic act source は `ref_capability` 経由にした。

## Next Removal Order

1. primitive family table を core metadata / compiled-unit artifact に渡す。
   - 今の monomorphize は型 constructor 再利用まで進んだので、次は lower/runtime 間で
     family id を明示的に渡す。
2. infer/runtime の固定 bootstrap table を std source / compiled-unit import artifact
   由来の capability metadata へ置き換える。
3. sugar 入口の `for` / `sub` / labelled loop path 構築を semantic table へ寄せる。
   - 現在は `flow_capability` に集約済み。次は `std` source の import artifact から
     capability を解決する形へ進める。
