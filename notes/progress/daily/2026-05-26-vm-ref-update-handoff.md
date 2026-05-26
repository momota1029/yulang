# VM ref_update / infer-monomorphize 引き継ぎメモ 2026-05-26

## 目的

`vm_host_flushes_file_handle_string_edits` を canary にして、file handle の `ref '[fs] str` を
line view 経由で編集したときに `ref_update::update` が VM top まで漏れる問題を直す。

ユーザー意図:

- infer / monomorphize を局所的に壊さない。
- `Any` は Top、`Unknown` は唯一の不明型。`Any` を fallback / unknown として使わない。
- path 文字列・fixture 名・特定テスト名で分岐しない。
- 対症療法ではなく、原因に近い層で直す。

## 現在の failing canary

```sh
RUSTC_WRAPPER= cargo test -q -p yulang-vm vm_host_flushes_file_handle_string_edits -- --nocapture
```

現在の失敗:

```text
unexpected request: Path { segments: [Name("std"), Name("var"), Name("ref_update"), Name("update")] }
```

再現 source は `crates/yulang-vm/src/vm/tests.rs` の
`vm_host_flushes_file_handle_string_edits`。手元では同等の一時ファイルとして
`/tmp/yulang-file-handle-lines.yu` を使った。

## finalized-ir で確認したこと

`runtime-finalize-ir` より `finalized-ir` の方が今の症状に近い。

```sh
RUSTC_WRAPPER= cargo run -q -p yulang -- --std-root lib/std dump --finalized-ir /tmp/yulang-file-handle-lines.yu > /tmp/yulang-file-handle-finalized-ir.txt
```

重要な観測:

- `std::str::&impl#272::index::mono4` は `ref<fs, str> -> range -> ref<fs, str>` まで解けている。
- しかし root 側の assignment では、`update_effect::mono5` がまだ
  `ref<[flow::loop; fs], str>` を要求する。
- root に次のような coerce が残る:

```text
coerce[std::var::ref<std::flow::loop, std::str::str>
       => std::var::ref<[std::flow::loop; std::fs::fs], std::str::str>]
__ref_set_ref_t16853
```

つまり最初に疑っていた「`index` が fs を落とす」問題はかなり改善済みで、
残りは assignment / handler / update_effect specialization のどこかで
`loop` を混ぜている。

## VM trace で確認したこと

一時的に VM trace を入れて確認したが、現在は VM 側の trace は削除済み。

trace 結果:

```text
TRACE vm handle_request ... effect=std::var::ref_update::update ... arms=[std::var::ref_update::update]
TRACE vm handle_arm_body_request ... effect=std::var::ref_update::update ...
TRACE vm propagate_no_frame ... effect=std::var::ref_update::update ...
```

意味:

- 最初の `ref_update::update` は handler に届いている。
- blocked guard で handler がスキップされているわけではない。
- arm path mismatch でもない。
- handler arm body の実行中に、resume 側から次の `ref_update::update` が出て top まで漏れる。

この観測から、`&ref = value` 用に infer export が生成する handler が、
`std::var::ref.update` のように recursive に catch し続ける形になっていない疑いが濃い。

## 現在入っている未完の実験

`crates/yulang-infer/src/export/expr.rs`

`export_ref_set` と `export_ref_field_projection` の update handler を、
単発 handler から recursive loop handler に寄せる実験が入っている。

現在の概形:

```text
let __ref_set_loop = fun __ref_set_action -> catch __ref_set_action:
  ref_update::update old, k -> __ref_set_loop (k value)

__ref_set_loop (ref.update_effect ())
```

さらに loop 引数を遅延させるため、generated lambda に
`param_effect_annotation: Some(ParamEffectAnnotation::Wildcard)` を付けた。

しかし canary はまだ同じ `unexpected request ref_update::update` で落ちる。
この変更は未完成で、commit 前に「正しい方向か」「revert すべきか」を判断する必要がある。

疑うべき点:

- generated typed-ir の lambda annotation だけでは、runtime-lower が期待する thunk boundary になっていない可能性。
- finalized-ir では `__ref_set_loop (resume "B\n")` の `resume "B\n"` が、
  loop の handler に入る前に評価されているように見える。
- `typed_ir` export で annotation を手で付けるだけでは expected type が足りず、
  lowering が loop param を `[_]` thunk として扱えない可能性がある。

## monomorphize 側で進んだこと

`crates/yulang-monomorphize/src/solver/apply_spine.rs`

- block の `let` initializer を collect した直後、その solve 結果の `result_type` を
  pattern-local の scrutinee 型として使う経路を追加。
- `__ref_set_ref_t16853` の let-local 登録まで `ref<fs, str>` が届くことを trace で確認済み。
- `ApplyStep::arg_type_and_effect` は local env の closed runtime type を優先し、
  evidence arg は runtime value が `Any` のように不精確な場合だけ override する方向へ寄せた。
- `solve_simple_apply` の result type は stale `expr.ty` ではなく、
  graph で materialize した result value/effect から作るようにした。

追加済み local tests:

- `block_let_local_uses_collected_initializer_result_for_following_apply`
- `root_apply_result_type_bounds_open_return_var`
- `materialize_apply_result_prefers_closed_callee_return_over_result_evidence`

通過確認済み:

```sh
RUSTC_WRAPPER= cargo test -q -p yulang-monomorphize block_let_local_uses_collected_initializer_result_for_following_apply -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-monomorphize root_apply_result_type_bounds_open_return_var -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-monomorphize materialize_apply_result_prefers_closed_callee_return_over_result_evidence -- --nocapture
```

## 残っている未整理 instrumentation

`crates/yulang-monomorphize/src/solver/apply_spine.rs` に残っている。
最終 commit 前に削除対象。

- `YULANG_TRACE_ROOT_SOLUTIONS`
- `format!("{pattern:?}").contains("__ref_set_ref")`

後者は path/name 文字列 trace なので、絶対に製品コードとして残さない。

`crates/yulang-monomorphize/src/graph.rs` の `YULANG_TRACE_ANY_BOUNDS` は以前からの調査用。
これも最終的には整理対象。

## ユーザー側変更として扱うもの

`lib/std/flow.yu` と `crates/yulang-sources/std/flow.yu` はユーザーが直したもの。
戻さない。

```diff
- our for_in(xs: 'container, f: label -> 'item -> ['e; label_loop; loop] _) =
+ our for_in(xs: 'container, f: label -> 'item -> [label_loop, loop] _) =
```

## 次に見る順序

1. `export_ref_set` の recursive handler 実験を続けるか、いったん戻すか決める。
2. 続けるなら、typed-ir export で作った generated lambda が runtime-lower で本当に `[_]` thunk param になっているか、`--runtime-finalize-ir` と `--finalized-ir` の両方で確認する。
3. `resume value` が loop handler の外で先に評価されているなら、export で `loop (thunk ...)` 相当を構造的に表す方法を探す。
4. `std::var::ref.update` の source 由来 export と、generated `export_ref_set` の runtime IR を比較する。
5. `update_effect::mono5` が `flow::loop` を拾う経路はまだ残っているので、handler 問題と別に monomorphize の stale expected / materialize arg adaptation も追う。
6. 修正後に `vm_host_flushes_file_handle_string_edits`、近い ref assignment VM tests、monomorphize local tests を再実行する。

## 注意

VM 側の handler continuation をいじる実験も一度したが、原因に近くないと判断して戻した。
現状の VM 側差分はないはず。

`cargo fmt` は通過済み。
canary はまだ落ちている。
