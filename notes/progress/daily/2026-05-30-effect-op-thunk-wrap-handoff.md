# Effect op Thunk wrap — (A) 試行と次の方針 2026-05-30

引き継ぎ元: `2026-05-29-handle-frame-loss-analysis.md`

## TL;DR

並列 flake `vm_std_pipeline_survives_parallel_source_ref_runs` の根本は **「effect 発火が、ある handle scope の外で起きてしまう」** こと。
具体的には `set v, k -> run v: k()` の eval 経路で、`run v` の inner Apply の中で thunk が force され、その時点で外側の handle frame が積まれていないため `propagate.no_handler` になる。

(A) 「effect op の type を `Fun(Value(t), Value(unit))` に正規化して Thunk wrap を剥がす」を試したが、**根本問題は解けず別の場所で同じ性質の panic が出る**ようになった (flake 率 5/10 → 8/10 に悪化)。

→ **Thunk wrap は yulang の意図的設計であり、剥がすと「effect 発火を handler 中まで遅延させる」仕組みが崩れる**。次は (C) Lambda apply の force 経路、または (D) bind_here の Request 継続接続を考える。

## (A) として加えた変更（未 commit ではなく、この commit に含めて残す）

### 変更 1: `crates/yulang-runtime-lower/src/lower/lowerer.rs`

`merge_effect_op_runtime_type` の `(Thunk, sig)` / `(expected, Thunk)` 分岐を「Thunk wrap を剥がして再帰 merge」に変更。effect op の callee.ty を declared 通りの `Fun(Value, Value)` 形に戻すのが狙い。

### 変更 2: `crates/yulang-monomorphize/src/solver/lowered_to_finalized.rs`

`from_lowered_expr` で `LoweredExprKind::EffectOp(_)` のとき、`runtime_type_from_core_value` の出力に `strip_effect_op_thunk_wrap` をかけて Thunk wrap を剥がす。monomorphize 後の Finalized の世界でも Thunk wrap が再付与されないようにするため。

### 変更 3: `crates/yulang-vm/src/vm/interpreter.rs`

`trace_apply_eval_entry` の `arg_tag` に `Coerce / AddId / BindHere / EffectOp / LocalPushId / Pack` の分類を追加（trace 強化のみ）。

### 結果

set effect op の callee_ty は望み通り `Fun(Value(str), Value(unit))` になり、`apply_eval.entry callee_kind=EffectOp(set) arg_kind=Apply delay_arg=false` を確認。delay_arg=false は (A) の目的どおり。

しかし test flake は悪化:

```
run=1 exit=0
run=2 exit=101
run=3 exit=0
run=4 exit=101
run=5..10  ... 5/10 fail (修正前 ~30%, 修正後 ~80%)
```

## 修正後の panic mode

panic effect が `set` から **`std::var::ref_update::update` (or `get`)** に変わった。

```
panicked: unexpected request: Path { ... ref_update::update },
  frames=["BindHere", "BindHere", "Coerce", "BindHere", "BindHere",
          "BindHere", "Coerce", "BindHere", "BindHere", "BindHere",
          "Coerce", "BindHere", "BindHere", "BindHere", "Coerce",
          "ApplyCallee", "ApplyArg"]
```

トレース(抜粋):

```
apply_eval.callee_ty kind=brief ty=Fun { param: Value(str), ret: Value(unit) }   ← (A) の効果で正規化された
apply_eval.entry callee_kind=EffectOp(set) arg_kind=Apply delay_arg=false
apply_eval.callee_ready callee=effect_op
apply_eval.entry callee_kind=EffectOp(update) arg_kind=BindHere delay_arg=false
apply_eval.entry callee_kind=EffectOp(get)   arg_kind=Lit       delay_arg=false
apply.entry callee=effect_op(get) arg=unit
bind_here.entry value=thunk_emit effect=get blocked_count=0
eval_handle.push id=7 effect=get frames_before_push=5            ← handle 7 (r.update の catch) しかいない
handle_request.arm_miss id=7 effect=get
  arms=["std::var::ref_update::update"]                          ← update arm のみ、get で arm_miss
propagate.entry effect=get before=0 frames_len=0 handle_ids=[]   ← outer 空
propagate.no_handler effect=get
```

## なぜ (A) が解にならないか

set の arg を **eager 評価** すると、`set(ref_update::update(get()))` の `get()` が **set 発火前** に evaluate される。その時の continuation frames には:

- handle 7: `r.update` の `catch x:` の handle (これは `loop x:` で start)
- handle 7 の外側にあるべき `&s#run` の handle (handle 4, handle 2 など) は**まだ frames に積まれていない**

handle frame は VM 設計上「eval が Request を return した時点で push」される。eager に外で effect を発火すると、外側の handle はまだ「待機中」で frames には乗ってない → arm_miss → no_handler。

つまり Thunk wrap は **「effect の発火位置を、handler の arm body が active になる scope まで遅延させる」** 機構として機能している。これを剥がすと:

- 修正前: handler の arm body で `run v` の `v=Thunk` を force → bind_here が外側 frame の積まれていない状態で effect 発火 → no_handler
- 修正後 (A): handler に届く前の set 引数 eval 段階で effect 発火 → 外側 frame が一切ない状態で発火 → no_handler

**症状の所在が違うだけで、根本は「handle frame が積まれる前に effect が出る」一点**。

## 設計の整理 (本質の確認)

yulang の runtime type system の中核ルール:

- `effect 列を持つ位置 = Thunk wrap` (`should_thunk_effect(effect) == true` で Thunk{effect, value} を作る)
- `apply(EffectOp(op), arg)` → `Thunk(Emit { effect: op, payload: arg })` を返す
- handler は arm body の eval 中に bind_here で Thunk を展開してその中の effect を出す → 上位 Handle frame が積まれる

「set: 't -> ()」は宣言上は `param: Value, ret: Value` だが、`set(...)` の use site の expr.ty は `Fun(Thunk(['e]t), Thunk(['e]unit))` になる。これは「set 自体が値を計算するときに effect 列を必要とする」という意味であって、payload の表現としては「lazy な計算を Thunk として handler に渡す」設計。

**handler 側で Thunk payload をどう扱うか** が問題の本質:

1. (現状) handler arm の payload pattern bind で Thunk を `As { pattern, name }` で arm_env に insert → 後の Var ref で env_hit → Closure apply 時に `closure_param_forces_thunk_arg=true && arg=Thunk` で force_apply_arg → bind_here で effect 発火 → ❌ ここで上位 frame が無い
2. (A) - 試行済み: 「effect op 自体の type を Value 化して eager eval」→ ❌ もっと早い段階で同じ問題が出る
3. (B) - 候補: handler の `bind_pattern` で payload Thunk を bind_here で force してから insert → handler scope (handle 3 など) は frames にあるはずなので、そこから propagate すれば外側に流せる。**handler の scope が `bind_here` の caller になるか**を要検証
4. (C) - 候補: VM の `apply(Closure(param_ty=Value(_)), Thunk(_))` で force_apply_arg しない経路を作る (Thunk を env にそのまま入れる)。`Var(v)` の eval / Lambda body で参照されたタイミングで force。これは大規模変更
5. (D) - 候補: `force_apply_arg → bind_here` で発生した Request を一段抽象化された Frame で包んで、上位 Frame::Handle が積まれるまで「待つ」ような仕掛けを足す

## 推奨される次の方向

優先順 (実装コスト × 効果):

1. **(B) handler bind 時の payload force を試す**
   - 1 箇所 (`crates/yulang-vm/src/vm/interpreter.rs::handle_request`) のみ修正
   - 「Thunk payload を bind_here で force してから arm_env に insert」
   - `bind_here` が Request を返した場合の継続が「handle scope の中」になっているかを必ず確認
   - もし force した結果が Request になっても、その continuation は handle_request の **handler_guard_stack** にあるので、Handler frame が rebuild される経路を踏むはず → これが (A) より見込みあり
2. **(D) bind_here Request の継続接続を見直す**
   - 修正前の `force_apply_arg → bind_here` で出た Request を 1 段挿入する Frame::Continuation を入れる
   - VM 設計上のインパクトが大きい
3. **(C) Lambda apply で Thunk arg を保存して lazy 化**
   - もっと根本的だが、影響範囲はかなり大きい

## (A) の変更を rollback する場合

```sh
git revert <この commit の hash>
```

ただし、引き継ぎ価値として **「(A) を試して同じ性質の問題が出る」** という結論が本ノートに残るので、commit は残しておく方が次に試した人の二度手間を避けられる。

## 残してある trace 装備

前の commit (`Add trace instrumentation and root-cause notes for set effect Thunk wrap`) で導入したものに加え、本 commit では:

- `interpreter.rs::trace_apply_eval_entry` の `arg_kind` 分類を Coerce / AddId / BindHere / EffectOp / LocalPushId / Pack 対応に拡張
- 環境変数 `YULANG_TRACE_HANDLE=1` で gate されたまま

## 再現コマンド

```sh
# 失敗を 5-8 回/10 程度で再現
for i in $(seq 1 10); do
  cargo test -q -p yulang-vm vm_std_pipeline_survives_parallel_source_ref_runs &> /tmp/yulang-A-$i.log
  echo "run=$i exit=$?"
done

# 失敗時のトレース
YULANG_TRACE_HANDLE=1 cargo test -q -p yulang-vm \
  vm_std_pipeline_survives_parallel_source_ref_runs -- --nocapture &> /tmp/yulang-trace.log

# 失敗時の binding body dump (set arm body の構造を確認)
YULANG_TRACE_HANDLE=1 YULANG_PANIC_DUMP=1 cargo test -q -p yulang-vm \
  vm_std_pipeline_survives_parallel_source_ref_runs -- --nocapture &> /tmp/yulang-dump.log
```

## 関連メモ

- [[project_state_purity]] — state は純粋継続スレッディング実装、Copying GC が直接効く根拠
- [[project_runtime_finalize]] — runtime rewrite。本件で触っている `merge_effect_op_runtime_type` は旧 lowerer 系
- [[project_runtime_ir_parameterization_plan]] — Type::Core の中途半端さの根治予定。本件の Thunk wrap も合わせて整理対象

## 続きの結果 — payload force 後に元 request を再 dispatch

実装結果:

- (A) の effect op type normalization は rollback。
  - `merge_effect_op_runtime_type` は effectful use-site の `Thunk` wrap を保持する形へ戻した。
  - `lowered_to_finalized` の `EffectOp` 専用 `strip_effect_op_thunk_wrap` も削除。
- (B) は「payload を force してそのまま arm body に入る」だと不十分。
  - `set(update(get()))` の payload 内 `get` が old state handler に捕まり、その `get` の継続が **set operation ではなく set arm body** になってしまう。
  - その結果、old state の `run` が set 後の継続を外側から包み、`"abcz"` ではなく `"aあ🙂z"` が返る flake になった。
- 正しい形は、handler が `Thunk` payload を force し、force 中に `Request` が出た場合だけ `HandlePayload` frame を積むこと。
  - `HandlePayload` は payload が値になった時点で arm body へ直接進まず、元の operation request に値 payload を入れて再 dispatch する。
  - これで payload 内 effect の継続は「set arm body」ではなく「値 payload 付きの set request」になり、CBV の operation argument 評価に近い順序へ戻る。
- tree VM と control VM の両方に同じ責務を入れた。
  - control VM は `ControlHandleArm::payload_forces_thunk` を compile 時に持つ。
  - serialized artifact shape が変わるため `CONTROL_VM_ARTIFACT_VERSION` は `13` に更新。

追加した regression:

- `vm_redispatches_effectful_payload_after_forcing_it`
- `control_vm_redispatches_effectful_payload_after_forcing_it`
- `control_vm_runs_source_ref_string_range_assignment_example`

確認済み:

```sh
RUSTC_WRAPPER= cargo test -q -p yulang-vm redispatches_effectful_payload -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-vm source_ref_string_range_assignment_example -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-vm vm_std_pipeline_survives_repeated_ref_and_effect_runs_on_one_thread -- --nocapture
for i in $(seq 1 10); do
  RUSTC_WRAPPER= cargo test -q -p yulang-vm vm_std_pipeline_survives_parallel_source_ref_runs -- --nocapture \
    > /tmp/yulang-final-parallel-source-ref-$i.log 2>&1 || exit 1
done
RUSTC_WRAPPER= cargo test -q -p yulang-runtime-lower inferred_handle_payload -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-vm vm_keeps_for_callback_return_effect_hygienic_across_sub -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-vm
```

`cargo test -q -p yulang-vm` は 235 tests 全通過。
