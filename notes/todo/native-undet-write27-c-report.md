---
title: native-undet-write27-c 実装レポート — JIT に ScopeReturn + route 系統を接続
date: 2026-05-12
---

# native-undet-write27-c 実装レポート

## 結論（先に）

write27-c のうち **c0〜c5 を実装**。Layer 3 (cps_repr_cranelift JIT) に:

- pre_push_count 形の callee initial (c0 HOTFIX)
- `YULANG_CPS_JIT_TRACE` env-guarded trace (c1)
- `NativeCpsI64HandlerFrame` の full fields + `install_handler_full_i64_N`
  family (c2)
- ScopeReturn ベースの Perform 完了パス + outer-stack snapshot/restore
  (c3)
- `route_scope_return_i64` (current handler walk + return-frame walk) (c4)
- 全 sync internal call 経路の post-call SR route (c5)

を入れた。

**c6 (EffectfulApply Resumption helper / anchor merge)** は未着手。

既存 167 tests **pass**。Layer 3 ターゲットテスト
`debugs_std_undet_once_skip_eval_layers` は依然として
`I64Mismatch(vm:2, cps_cranelift:1)`。trace で見た限り、原因は **c6
未実装 + handler stack に synthetic frame が混入する経路** (ForceThunk
内 pending 消費 / resume_with_handler) のいずれか or 両方。

---

## c0 HOTFIX — pre_push_count

`switch_eval_context_for_callee` が push 後 `return_frame_len` を
callee initial にしていた件、引数として `pre_push_count: ir::Value` を
受け取る形に変更。

EffectfulCall / EffectfulForce / EffectfulApply の 3 箇所で `push` の
**前** に `yulang_cps_return_frame_len_i64` を呼んでから
`push_return_frame_for_resume` → `switch_eval_context_for_callee(pre)`
の順に並べた。

効果: `cps_cranelift=0 → 1` に進んだ。F_post が consume されるように
なって、`action=continue` / `action=pre_force` の trace が出るように
なった。

---

## c1 — JIT runtime trace

`YULANG_CPS_JIT_TRACE=1` 環境変数で有効化。`AtomicU8` キャッシュで
hot path は読みだけ 1 回。次の event を `eprintln!` で吐く:

- `push_return_frame` (len_before, len_after, cont, env_len,
  owner_initial, owner_eval, immediate_force)
- `set_eval_context` (eval, initial)
- `return_i64` (value, frame_len, initial, action=noop|pre_force|continue)
- `continue_return_frame` (owner_eval, owner_initial,
  restored_handlers_len, restored_guards_len, value)
- `scope_return_set` (prompt, target, value)
- `scope_return_set (from selected)` / `scope_return_set (perform_finish)`
- `route_scope_return` (prompt, current_eval, initial,
  action=current_handler|frame_walk|propagate, value)
- `perform_select` (handler, prompt, install_eval, synthetic, threshold, idx)
- `install_handler_full` / `install_handler (legacy)`

これで Layer 3 の挙動が一目で追えるようになった。

---

## c2 — Handler frame full fields

`NativeCpsI64HandlerFrame` に Layer 1/2 相当の field を追加:

- `prompt: u64`
- `install_eval_id: u64`
- `inherited: bool`
- `escape_continuation: usize`
- `escape_env: Box<[i64]>`
- `return_frame_threshold: usize`

既存 frame 構築箇所 (`current_native_i64_handler_stack_with_fallback`,
`take_pending_native_i64_handler_frames`,
`yulang_cps_install_handler_i64`, `yulang_cps_resume_with_handler_i64`)
は全部 default 値 (synthetic_eval_id = u64::MAX, escape_cont=0, env=空)
で fill。これで既存 codegen は legacy abort 経路で動き続ける。

新 `install_handler_full_i64_N` (N=0..4) helper を追加。`fresh_prompt`
counter + helper も同時に。

---

## c3 — Perform を ScopeReturn 化 + InstallHandler stmt 切替

### Perform 経路

`lower_selected_handler_return` から legacy `abort_i64` の return
ロジックを除去し、新 `yulang_cps_perform_finish_i64(arm_result)` 一発に
置き換えた:

```rust
extern "C" fn yulang_cps_perform_finish_i64(value: i64) -> i64 {
    // 1. restore outer handler stack from snapshot (select 時に save)
    // 2. selected handler が real なら ScopeReturn { prompt, target=escape, value } を set
    // 3. route_scope_return(value) を呼んで dispatch
    // 4. synthetic handler 経路では legacy abort slot を set して旧 propagate 経路も生かす
}
```

### select_handler の拡張

`yulang_cps_select_handler_i64` を次のとおり拡張:

- 旧: `stack` を `stack[..idx]` に truncate し、`SELECTED_HANDLER_ENVS`
  に matched envs を入れる。
- 新: その前に **pre-truncation stack を `OUTER_HANDLER_SNAPSHOTS` に
  push** + **matched frame の meta を `SELECTED_HANDLER_META` に
  保存**。`perform_select` trace も同時に出す。

これで `perform_finish` の中で:
- snapshot をポップして元の stack を復元 → route の current-handler walk が動く
- meta から prompt/escape を直接読み出して SR を構築

### InstallHandler stmt codegen

`escape_cont.environment.len() <= 4` なら full helper を使う:

```rust
let escape_ptr = func_addr(escape_func_ref)
let threshold  = return_frame_len()
let prompt     = fresh_prompt()
let install_eval = current_eval_id()
install_handler_full_i64_N(handler_id, escape_ptr, threshold, prompt,
                            install_eval, 0, env_slots...)
```

env > 4 のときは legacy `install_handler_i64` にフォールバック (synthetic
扱い)。今のところ env > 4 になる handler は見ていない。

---

## c4 — `route_scope_return_i64(fallback)`

仕様どおりの walk-based dispatch:

```text
1. 現在の handler stack を reverse 走査
   prompt == sr.prompt && install_eval_id == current_eval_id
   match: truncate handler stack to idx, truncate frames to threshold,
          clear sr, call escape(env, sr.value)

2. return_frames[current_initial..] を reverse 走査
   各 frame の handlers を reverse 走査
   prompt == sr.prompt && handler.install_eval_id == frame.owner_eval_id
   match: restore frame.handlers[..hi] / frame.guards / eval_context,
          truncate frames at fi → さらに threshold,
          clear sr, call escape(env, sr.value)

3. no match: leave sr active, return fallback_value
```

`escape_continuation == 0` は synthetic 扱いで raw value を返す。

---

## c5 — sync internal call の post-call route

`return_if_scope_return_active(result)` ヘルパ codegen を追加し、
全 sync internal call の `return_if_abort_active` 直後に **必ず**
emit するようにした:

- `CpsStmt::ForceThunk` (両 path)
- `CpsStmt::DirectCall` (両 path)
- `CpsStmt::ApplyClosure` (両 path)
- `CpsStmt::Resume`
- `CpsStmt::ResumeWithHandler`
- `call_continuation` ヘルパ (continuation 内 tail-call)

挙動: `scope_return_active()` を見て active なら `route_scope_return(result)`
の結果を `return` し、そうでなければ素通り。これで caller チェーンを
SR が伝播する。

注: write27-c notes の「eval context save/restore」は今回見送り。現状
sync call は callee の eval context を caller のまま使い続けるので、
save/restore せずに動いている。EffectfulCall だけが eval id を進める。
必要なら c6 と合わせて再検討する。

---

## テスト結果

```text
cargo test -p yulang-native           => 167 pass / 17 ignored
debugs_local_choice_caller_rest_eval  => pass
debugs_local_choice_callback_rest_eval => pass
debugs_std_undet_once_skip_eval_layers
  => Layer 1 OK / Layer 2 OK
     Layer 3 FAIL: I64Mismatch(vm:2, cps_cranelift:1)
```

`cps_cranelift=1` は「once が 1 個目の branch しか出していない」状態。

---

## 観察された Layer 3 の挙動

`YULANG_CPS_JIT_TRACE=1` で出した trace から:

- 最初の `install_handler_full` 3 回はすべて real frame
  (prompt=1, install_eval=1) (prompt=2, install_eval=2)
  (prompt=3, install_eval=8)。これは期待どおり。

- ところが `perform_select` で選ばれているのは **synthetic frame**:

  ```text
  perform_select: handler=1 prompt=0 install_eval=MAX synthetic=true threshold=0 idx=29
  perform_select: handler=0 prompt=0 install_eval=MAX synthetic=true threshold=0 idx=32
  ```

- handler stack は途中で `restored_handlers_len=14, 28` まで膨らんでいる。
  これは return_frame snapshot から復元された stack。

- snapshot の元になった handler stack は、`install_handler_full` で
  入った real frame と、`take_pending_native_i64_handler_frames` で
  作られた synthetic frame が混在しているらしい。

select_handler は最も内側 (rposition) で handler_id 一致を見るので、
同 handler_id の synthetic frame が real frame の **上** に積まれている
状況だと、synthetic を拾ってしまう。

---

## 残課題

### A. c6: EffectfulApply Resumption helper

未着手。現状 EffectfulApply codegen は Closure 用の
`yulang_cps_apply_closure_i64` を呼ぶだけで、Resumption の場合の
anchor merge + combined_frames + handler merge を行っていない。

write25 で Layer 1/2 では `apply_resumption_inline` 系のロジックで
これが動くようになっている。Layer 3 でも:

```rust
extern "C" fn yulang_cps_effectful_apply_resumption_i64_N(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    immediately_forces: i64,
    env_slots...
) -> i64
```

を新規追加し、Rust 側で:
- F_post を作る
- 現在の return_frames + F_post = new_frames
- resumption.handled_anchor で anchor merge
- adjusted_res_frames = merge_extras_into_frames(...)
- combined_frames = new_frames + adjusted_res_frames
- resumed_handlers = merge_resumption_handlers(...)
- set return frame stack / handler stack / guard stack / eval_context
- call resumption.target

を実装する。

### B. synthetic frame 混入経路の整理

c6 を入れても解決しない可能性のある問題。`take_pending_native_i64_handler_frames`
が synthetic で frame を作るパス（ForceThunk 内、make_resumption capture
時点）、`yulang_cps_resume_with_handler_i64` で push される frame が
すべて synthetic 化されている。

これは Layer 1/2 では問題にならない。なぜなら Layer 1/2 は
`active_handlers` を ref-only に扱い、handler env capture は別ロジック
で行うから。Layer 3 (JIT) では thread_local stack 1 本に env も
prompt も escape も詰める設計なので、pending → handler の遷移時に
prompt/eval/escape の情報を持ち越す必要がある。

対応案 (どれか):
1. capture_handler_envs / install_handler_full 経路を一本化し、
   `take_pending` 時に full info を保持する。
2. `select_handler` で synthetic frame を **skip** する (legacy frame
   は別 path で扱う前提)。
3. ForceThunk 内の `native_i64_handler_stack_for_force` を見直して、
   pending を thread_local stack に extend しない形にする。

(2) は legacy abort path を壊す。(1) は工数大。(3) は影響範囲を
要調査。

### C. eval context save/restore は本当に要らないか

write27-c notes には「sync call も save/restore せよ」とあるが、
今回見送った。問題が残るのは callee 側で EffectfulCall を行って
caller の eval id を上書きするケース。今は callee の Return が
eval_context を `continue_return_frame` 経由で復元するので、純粋な
sync call ではここを通らない（EffectfulCall の post には通る）。

c6 と組み合わせて再検証する。

---

## 触ったファイル

- `crates/yulang-native/src/cps_repr_cranelift.rs`
  - `NativeCpsI64HandlerFrame` 拡張 (c2)
  - `NativeCpsI64SelectedHandlerMeta` 新規 (c3)
  - `NATIVE_CPS_I64_NEXT_PROMPT` / `NATIVE_CPS_I64_OUTER_HANDLER_SNAPSHOTS`
    / `NATIVE_CPS_I64_SELECTED_HANDLER_META` thread_local 追加
  - `jit_trace_enabled()` + 各 helper の trace 出力 (c1)
  - `install_handler_full_i64_N` / `fresh_prompt_i64` helper
    (N=0..4) (c2)
  - `restore_outer_handler_stack_i64` /
    `scope_return_from_selected_handler_i64` /
    `route_scope_return_i64` /
    `perform_finish_i64` helper (c3, c4)
  - `select_handler_i64` を snapshot + meta 保存 + trace に拡張 (c3)
  - `switch_eval_context_for_callee(pre_push_count)` 形に変更 + 3
    呼出側更新 (c0)
  - `return_if_scope_return_active` codegen helper (c5)
  - sync stmt codegen 全箇所に post-call route 挿入 (c5)
  - `lower_selected_handler_return` を perform_finish 呼び出しに置換 (c3)
  - `CpsStmt::InstallHandler` codegen を full helper 経由に切替 (c3)
  - reset_native_i64_cps_state を新 thread_local の clear に対応 (c2,c3)
  - symbol 登録: full install / restore_outer / scope_return_from_selected
    / route_scope_return / perform_finish

---

## 次の作業（write27-d 候補）

1. c6 を完了させる: `effectful_apply_resumption_i64_N` helper + EffectfulApply
   codegen の Resumption 分岐。
2. synthetic 混入経路の対応 (上記 B)。c6 後に再現 trace を見て決める。
3. c6 後の Layer 3 trace を見て、`cps_cranelift = 1 → 2` への frontier を
   特定する。
4. Layer 3 通過後、`Aborted` / `yulang_cps_abort_*` legacy の grep →
   削除可否判定。

---

## ひとこと

`cps:0 → 1` だけだと「ほんの一歩」だけど、write27-b の `todo!` →
`UnsupportedTerminator` → `I64Mismatch(0)` → `I64Mismatch(1)` という
3 段の前進があったあとの 1 だから、JIT 基盤の return-frame と SR が
ようやく繋がった証拠だよ〜。

c6 と synthetic 整理を入れれば、Layer 3 通過の射程内に入ってると思う。
