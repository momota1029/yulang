# yulang-infer / yulang-monomorphize 引き継ぎメモ 2026-05-26

## 基準点

作業スナップショット:

```text
d80a25f WIP infer monomorphize audit fixes
```

この commit は不完全な WIP。`notes/bugs/yulang-infer-monomorphize-audit-2026-05-26.md`
と、infer / monomorphize / runtime-lower / runtime-refine / VM 周辺の途中差分を含む。

このメモを書き始める直前の作業ツリーは clean。

## ユーザーの直近意図

- infer をこれ以上広く壊したくない。
- `no implicit cast from user_id to int` は、途中で入れた infer 実験の副作用と見てよい。
- いま主に疑うべきは monomorphize / materialize / cast insertion 側。
- ただし、現在の failing canary は surface diagnostic が先に止めているため、次に infer を触るなら広い solver 改変ではなく、その diagnostic の扱いだけを切り分ける。

重要な会話上の前提:

- `Any` は Top、`Never` は Bottom、`Unknown` は唯一の不明型。
- `Any` / `Unknown` の取り違えは仕様ではなくバグ。
- 型推論で fixture 名、path 文字列、特定入力だけを通す分岐は入れない。

## 直近で戻した infer 実験

一度、`ApplicationArgument` と `IfBranch` の cast boundary を infer 側で特別扱いする実験を入れたが、ユーザーの懸念に沿って戻した。

戻したもの:

- `resolve_cast_boundary_method_def`
- `cast_boundary_has_nominal_args`
- `concrete_tv_upper_chain_repr`
- `application_arg_cast_boundary_does_not_pollute_if_branch_actual_type`
- `YULANG_TRACE_CAST_BOUNDARY`

現在残っている infer 側の差分には、既存の `YULANG_TRACE_INFER_ANY_APPLY` instrumentation がある。これは今回の最後の実験由来ではない。

## 現在の主要な未解決 canary

```sh
RUSTC_WRAPPER= cargo test -q -p yulang-vm vm_inserts_cast_at_if_branch_boundary -- --nocapture
```

現在の失敗:

```text
finalized runtime module failed: expected user_id, found int
```

再現 source:

```yulang
struct user_id { raw: int }
cast(x: int): user_id = user_id { raw: x + 10 }
my read(x: user_id) = x.raw
read (if true: 1 else: user_id { raw: 0 })
```

重要な観測:

- `vm_inserts_cast_at_function_argument_boundary` は通る。
- `vm_selects_cast_by_annotation_target` は通る。
- `vm_keeps_open_identity_join_from_using_unrelated_cast` は通る。
- `yulang-infer branch_join_uses_implicit_cast_boundary` は通る。
- `dump --runtime-finalize-ir /tmp/yulang-cast-if.yu` も同じ `expected user_id, found int` で止まる。

つまり、この VM canary は名前に反して、いまは monomorphize の最終出力まで到達していない。`yulang-compile::runtime_module_from_lowered_sources` が `collect_surface_diagnostics` を fatal にしており、surface diagnostic が先に止めている。

## monomorphize 側で入っている直近修正

`crates/yulang-monomorphize/src/solver/materialize.rs`

- `If` materialize 時に `JoinEvidence.result` / 外側 expected runtime を branch expected として流す。
- branch 側で closed expected が分かる場合、`materialize_expr_to_expected` 経由で `Coerce(actual -> expected)` を作る。
- apply argument adaptation と同じ helper に寄せ、value/thunk expected handling を共有した。

`crates/yulang-monomorphize/src/solver/cast.rs`

- closed な `Coerce(A -> B)` は、`Cast A { type to = B }` path が存在すれば semantic cast call へ展開する。
- open endpoint (`Any` / `Unknown` / `Var` / non-closed) は引き続き cast call にしない。
- `int -> float` は VM primitive coercion が持つため semantic cast call へ展開しない。

追加した局所テスト:

- `materialize_if_branches_to_join_result`
- `semantic_cast_normalization_expands_closed_coerce_to_cast_call`

どちらも通過済み。

## 確認済みコマンド

通ったもの:

```sh
RUSTC_WRAPPER= cargo test -q -p yulang-monomorphize materialize_if_branches_to_join_result -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-monomorphize semantic_cast_normalization_expands_closed_coerce_to_cast_call -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-vm vm_inserts_cast_at_function_argument_boundary -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-vm vm_selects_cast_by_annotation_target -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-vm vm_keeps_open_identity_join_from_using_unrelated_cast -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-infer branch_join_uses_implicit_cast_boundary -- --nocapture
RUSTC_WRAPPER= cargo check -q -p yulang-monomorphize
git diff --cached --check
```

落ちているもの:

```sh
RUSTC_WRAPPER= cargo test -q -p yulang-vm vm_inserts_cast_at_if_branch_boundary -- --nocapture
```

失敗は `collect_surface_diagnostics` 由来の `expected user_id, found int`。

## 次に見るべき場所

まず読む場所:

- `crates/yulang-infer/src/lower/expr/control.rs`
  - `lower_if`
  - 最初の branch が `tv <: body.tv` を入れ、各 branch が `body <: tv` expected boundary を持つ。
- `crates/yulang-infer/src/lower/state.rs`
  - `implicit_cast_boundary_with_effects`
  - unresolved cast boundary は、cast role があれば boundary expr を保存するが、同時に `actual <: expected` constraint も入れる。
- `crates/yulang-infer/src/export/expr.rs`
  - `ExprKind::Coerce`
  - `export_user_cast_boundary`
- `crates/yulang-infer/src/surface_diagnostic.rs`
  - `collect_surface_diagnostics`
  - `state.infer.type_errors()` をそのまま surface fatal diagnostic にしている。
- `crates/yulang-compile/src/lib.rs`
  - `runtime_module_from_lowered_sources`
  - surface diagnostics が non-empty なら monomorphize へ進まない。

見方:

- `IfBranch` の preserved cast boundary は core export / monomorphize では意味を持つ。
- しかし solver diagnostic には、boundary を保存していても `actual <: expected` の constructor mismatch が残りうる。
- この false positive を消すには、infer solver 全体を変える前に「expected-edge cast boundary として後段に委ねる不一致」を diagnostic からどう除外するかを見る方が狭い。

## 次の担当へのおすすめ方針

1. `vm_inserts_cast_at_if_branch_boundary` を最初の canary にする。
2. いきなり infer の constraint solver を広く変えない。
3. `collect_surface_diagnostics` に届いている `TypeError` が、どの `ExpectedEdgeId` / `ExpectedEdgeKind` と対応しているかを trace する。
4. 対応する expected edge が `IfBranch` / `ApplicationArgument` で、かつ preserved boundary が export 可能な closed cast なら、surface diagnostic として fatal にすべきかを切る。
5. その場合でも `MissingImpl` / `AmbiguousImpl` は握りつぶさない。
6. monomorphize へ進めた後、finalized IR に `Cast int -> user_id` の apply が入るか確認する。

避けること:

- `Any` を fallback として使う。
- `user_id` / `int` などの path 文字列で分岐する。
- `IfBranch` だけを場当たり的に通す。
- `MissingImpl` を false positive と一緒に消す。

## finalized IR dump

`crates/yulang/src/main.rs` の `dump --finalized-ir` は、`Debug` dump ではなく `print_runtime_module(&output.module, options.verbose_ir)` を使う形になっている。次に monomorphize まで進めたら、まずこの dump で cast call が見えるかを確認するとよい。

## 別系統の未解決

audit note の後半に残っている `materialize.rs` thunk-adaptation regression は、今回の branch cast canary とは別系統。

主な対象:

- `cached_std_finalize_runs_playground_core_examples`
- `cached_std_control_vm_legacy_runtime_and_finalize_match_playground_examples`
- `std_no_cache_finalize_runs_reported_graph_unification_regressions`

`once` / `each` / thunk forcing の問題は、`materialize_thunk_to_value_or_coerce` の force trigger が粗すぎる疑い。apply-spine 側から explicit "force allowed" hint を渡す方向が推奨。

## 追加の注意

`crates/yulang-monomorphize/src/graph.rs` には `YULANG_TRACE_ANY_BOUNDS=1` instrumentation が残っている。`Any` lower bound を追うには有用だが、最終的には整理対象。
