# Track 3 (Host / Filesystem Semantics): 完了履歴 (2026-05-14 時点)

`tasks/current.md` Track 3 から退避した完了済み事項の記録。
active な計画は `tasks/current.md` を参照。

## parser / lowering の特例削減

`+` / `-` / `*` / `/` / `==` / `<` / `<=` / `>` / `>=` の role method 直結は
`std::ops` operator 定義へ寄せた。

- `std::ops` 分離、古い `+ -> add` internal-name fallback の撤去、forward direct role method call の constraints import で、operator wrapper 内の未解決 `ref_*` は閉じた。
- `and` / `or` は `lazy` operator へ寄せた。
- 末尾名 `add` / `fold` / `fold_impl` / `find` だけで associated demand signature closure を入れる特例は撤去した。
- `AssociatedSignatureKind` と associated demand signature closure を撤去した。monomorphize は binding body/type/primitive/role impl graph から target を分類して signature hole を補完しない。
- monomorphize の effect path matching から任意 suffix match を外した。effect parent / child operation の prefix 関係だけ残す。
- `Fold::item` の demand closure も撤去した。list/range item を role impl graph から推測して callback signature を補完しない。
- complete principal export からも `item` / `list` / `range` の名前ベース補完を外した。role requirement から型を逆算せず、call slot / exported bounds / expected evidence だけを substitution source にする。
- runtime effect compatibility から、`std::flow::loop` を expected effect に含めると任意の actual effect を通す分岐を外した。
- numeric widening / union join / VM cast は任意末尾名 `int` / `float` を見ない。context を持たない層では bare `int` -> bare `float` の bootstrap fallback だけ残す。
- monomorphize normalization から末尾名 `sub` の payload 後付け補完を外した。
- VM effect operation erase から consumed effect namespace の末尾名に単一 operation を合わせる解決分岐を外した。
- ordinary role method call resolver から `cast` method 名の特別分岐を外した。明示 coercion は専用 entrypoint のまま残す。
- ref list index projection は compiler export の専用分岐を外し、`lib/std/list.yu` の `Index (ref 'e (list 'a)) int` impl へ移した。
- lower / validate / refine の `nil` / `just` / `list` 末尾名判定を減らした。constructor は期待型との親子関係、list pattern は暫定的に単一 type arg shape を見る。
- monomorphize の list / opt payload 抽出、var/ref 内部 refine、debug filter から std path 再判定を減らした。`associated.rs` / `check.rs` / `emit.rs` は、list / opt / ref の result type constructor を直書きせず、既存 signature / runtime type に出ている `Named` constructor を再利用する。runtime monomorphize / lower / refine / validate の production scan では `path_is(... ["std", ...])` / `path_has_prefix(... ["std", ...])` / `ends_with(...)` / `path_ends_with` は検出されない。
- infer の `std_var_ref_path` / `is_std_var_ref_path` は `Infer::ref_type_paths` metadata へ寄せた。selection は `Infer::is_ref_type_path` を見る。
- infer の role method prefix suffix match を外し、canonical role path の完全一致だけにした。
- `for` / `sub` / labelled loop sugar 入口の `std::flow` path 構築は `std_flow_paths` へ集約した。
- runtime lower の `std_types` は `primitive_types` に置き換えた。`Lowerer` は `RuntimePrimitivePathTable` を持ち、literal / bool / unit は expression / pattern / evidence / effect helper まで table 経由で型を作る。
- primitive type family metadata は `CoreGraphView::primitive_types` に載せた。infer export は `LowerState::primitive_paths` から graph node を吐き、runtime lower は graph metadata を優先して table を作る。
- compiled runtime surface merge は primitive metadata を保持し、同じ family が異なる path を指す場合は conflict として拒否する。
- infer primitive bootstrap の型/value path は `builtin_types` に集約した。`LowerState` は `PrimitivePathTable` を持ち、list literal / list pattern / string concat は state table 経由で path を読む。
- `$x` fallback と var synthetic act helper source は `std_ref_paths` 経由にした。
- ref field projection selection は `Infer::primary_ref_type_path` から ref constructor を再利用し、固定 `std::var::ref` path を再生成しない。
- `for` / `sub` / labelled loop / `$x` / `&x = v` は標準 protocol への糖衣展開として扱い、新しい compiled artifact metadata は導入しない。
- 残っている `std` path / `ends_with` / 末尾名判定は `notes/design/std-special-case-audit.md` に洗い出した。sugar 入口以外の挙動特例は primitive family table / canonical id 比較へ寄せて消す。
