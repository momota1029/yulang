# Parallel cache / VM flake handoff 2026-05-28

## 目的

`yulang-vm` / `yulang-monomorphize` 周辺の遅さと並列 flake を、単純な直列化ではなく
キャッシュと並列実行に耐える形へ寄せる途中の引き継ぎ。

ユーザー意図:

- テストを直列化して通すだけでは不可。
- キャッシュを使いながら並列化しても壊れない状態を目標にする。
- `lib/std/var.yu` 側が処理系に気を遣う書き方へ逃げるのは不可。
- 原因が分かった後は標準ライブラリの一時変更を戻す。
- 全テスト通過前なので publish / deploy はしない。

## 現在の状態

この handoff 時点では、全テストは通っていない。

通ったもの:

```sh
RUSTC_WRAPPER= cargo test -q -p yulang-vm vm_runs_source_ref_string_range_assignment_example -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-vm vm_std_pipeline_survives_repeated_ref_and_effect_runs_on_one_thread -- --nocapture
```

まだ落ちるもの:

```sh
RUSTC_WRAPPER= cargo test -q -p yulang-vm vm_std_pipeline_survives_parallel_source_ref_runs -- --nocapture
```

`cargo fmt` 後に単発で 1 回通ったが、直後の 10 回反復の 1 回目で再現した。
つまり「常に落ちる」ではなく「同一プロセス内の並列 stress で不安定」。

失敗例:

```text
unexpected request: Path { segments: [Name("&s#1326"), Name("get")] },
blocked_id=None,
blocked_ids=[],
continuation_guard_stack=GuardStack(... id: 5 ...),
frames=["BindHere", "BindHere", "Coerce", "BindHere", ...]
```

単発と一スレッド反復は通るので、VM 意味論だけの単純な常時 failure ではない。
同一テスト内で 4 worker が同時に `eval_source_with_std_inner` を走ると落ちる。

## 今回入っている主な変更

### 1. fresh ID を thread-local scope 化

ファイル:

- `crates/yulang-infer/src/ids.rs`
- `crates/yulang-infer/src/source.rs`

別スレッドの lowering が `DefId` / `RefId` / `TypeVar` の列を共有すると、snapshot /
cache の remap 前提が崩れる。そこで fresh counters を thread-local にし、
`lower_source_set_with_profile` の入口で thread ごとの base block を割り当てる形にした。

cached std state を clone したあとに uncached source を lower する経路では、
既存 state 内の最大 ID を見て counters を進める `reserve_fresh_ids_after_state` を追加した。

注意:

- failing source ref は `&s#101326` のような大きい owner-derived 名になることも、
  `&s#1326` のような小さい owner-derived 名になることもある。
- したがって巨大 ID そのものを原因として見るのは弱い。
- ただし synthetic var act 名と handler arm 名が同一 lowering 内でずれている可能性はまだ残る。

### 2. compiled unit / std graph cache の並列 write を atomic rename 化

ファイル:

- `crates/yulang-infer/src/artifact_cache.rs`
- `crates/yulang-sources/src/lib.rs`

同じ cache key に複数 worker が同時 write しても、読み手が途中の partial file を拾わないように
一時ファイルへ write してから rename する形にした。

`StdGraphCacheFile::matches_file_metadata` は mtime / len だけでなく source hash も読む。
mtime が同じまま中身だけ変わるケースを stale cache として弾くため。

### 3. dependency bundle cache を全依存 artifact が揃う場合だけ読む

ファイル:

- `crates/yulang-runtime-pipeline/src/dependency_cache.rs`

部分的な依存 cache bundle から runtime module を組むと、依存 closure の surface が欠けたまま
進む危険がある。今回は `read_for_manifest` が 1 つでも miss したら bundle miss とする方針に寄せた。

### 4. runtime lowering / VM の thunk arg 境界を `FunctionSigAllowedEffects` まで拡張

ファイル:

- `crates/yulang-runtime-lower/src/lower/lowerer.rs`
- `crates/yulang-runtime-lower/src/lower/evidence.rs`
- `crates/yulang-runtime-lower/src/lower/thunk.rs`
- `crates/yulang-monomorphize/src/solver/materialize.rs`
- `crates/yulang-vm/src/vm/interpreter.rs`
- `crates/yulang-vm/src/vm/control.rs`

`param_effect_annotation` だけでなく、function signature の allowed effects も thunk param として扱う。
これに合わせて VM 側の closure application でも callee の param shape を見て arg を delay する。

この系統の canary は以前通過:

```sh
RUSTC_WRAPPER= cargo test -q -p yulang-runtime-lower inferred_handle_payload -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-vm vm_keeps_for_callback_return_effect_hygienic_across_sub -- --nocapture
```

ただし、最新の `inside_handle` 変更後には crate 全体を回し切れていない。

### 5. VM continuation split の一部修正

ファイル:

- `crates/yulang-vm/src/vm/continuation.rs`
- `crates/yulang-vm/src/vm/tests.rs`

`VmContinuation::inside_handle` は、これまで `drain(..=index)` で対象 handler frame と外側 frame を
まとめて捨てていた。continuation frame は outer-to-inner で並ぶため、shallow resume では
対象 handler 自体だけを外し、外側 handler は残すべき。今は `remove(index)` にしている。

この修正で単発の source ref range assignment は通るが、並列 source ref canary はまだ落ちる。
したがって、これは必要な修正の可能性があるが十分条件ではない。

未確認:

- `crates/yulang-vm/src/vm/control.rs` の `split_handle_continuations` は同じ意味論なら mirror が必要かも。
- 今の failing request では continuation frames に `Handle` が残っていないため、別原因も並行している。

## 戻したもの / 入れていないもの

標準ライブラリの回避策は戻している。

`lib/std/var.yu` は次の形:

```yu
    my var_ref(): ref '[var 't] 't = ref {
        get: \() -> get(),
        update_effect: \() -> set:ref_update::update:get()
    }
```

途中で試した VM 側の `HandleScope` / `HandleArmResult` / handler arm result special-case は削除済み。
次はこの方向へ戻らず、handler / request の生成元に近い層を見る方がよい。

確認用 grep:

```sh
rg -n "HandleScope|HandleArmResult|continue_handle_arm_body_result|handler_should_scope_arm_request|debug_unexpected|EVAL_LOCK|PIPELINE_LOCK|static LOCK|std_source_lower_lock" crates/yulang-vm/src/vm crates/yulang-infer/src/ids.rs
```

この handoff 直前は、今回入れた temporary lock / temporary handler scope 名は残っていない。

## 次に見る順序

1. 並列 source ref canary で、落ちた worker の finalized VM module を dump する。
   - `&s#...::get` request を処理する handler arm が module 内に存在するか。
   - 存在するなら continuation からなぜ消えたか。
   - 存在しないなら lowering / synthetic act copy / monomorphize rewrite 側の path mismatch。
2. `scoped_var_act_name` と `var_ref_acts` の対応を、同一 lowering 内で検査する。
   - `run` / `get` / `set` / `var_ref` が同じ synthetic act 名を使っているか。
   - cached std state clone 後の user source lowering で、owner / DefId がずれていないか。
3. `VmContinuation::inside_handle` の修正が control VM にも必要かを決める。
   - tree VM と control VM で continuation order が同じなら、control 側の inner split も外側 frame を保持する。
4. `callee_expects_thunk_arg` と runtime-lower の `FunctionSigAllowedEffects` 対応が source ref の handler body を過剰に delay していないか見る。
5. 並列 stress は直列 lock で逃げず、以下を繰り返す。

```sh
for i in $(seq 1 10); do
  RUSTC_WRAPPER= cargo test -q -p yulang-vm vm_std_pipeline_survives_parallel_source_ref_runs -- --nocapture || exit 1
done
```

## 既存 debug gate

今回の差分外だが、`crates/yulang-monomorphize/src/solver/apply_spine.rs` には以前から
`YULANG_TRACE_ROOT_SOLUTIONS` と `format!("{pattern:?}").contains("__ref_set_ref")` が残っている。
今回の commit では触っていない。最終整理では path/name 文字列 trace として消す対象。

## publish / deploy

全テスト通過条件を満たしていないため未実施。
