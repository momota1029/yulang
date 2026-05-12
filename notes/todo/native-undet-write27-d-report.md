---
title: native-undet-write27-d 実装レポート — c6 Resumption helper + sync context + origin trace
date: 2026-05-12
---

# native-undet-write27-d 実装レポート

## 結論（先に）

write27-d で **c6 EffectfulApply(Resumption) helper を含む d1〜d6 を一通り実装**。

- d1: `NativeCpsI64HandlerFrameOrigin` enum + 各 frame 構築箇所に origin
  設定 + `perform_select` trace に origin 表示。
- d2/d3: `NativeCpsI64Resumption` に `return_frames` / `handled_anchor`
  を保持。`make_native_i64_resumption` で current return frames を
  capture。`yulang_cps_set_resumption_anchor_from_selected_i64` 新設
  + Perform codegen が select 直後にこれを呼ぶ。
- d4 (c6 本命): `effectful_apply_resumption_i64_N` (N=0..4) +
  `yulang_cps_is_resumption_i64` predicate を追加。EffectfulApply
  codegen は runtime で Resumption / Closure 分岐し、Resumption
  なら helper に anchor merge + combined_frames + state swap を
  任せる。`merge_resumption_handlers_native` /
  `merge_extras_into_frames_native` を Layer 2 から port。
- d5: 全 sync internal call (`DirectCall` / `ApplyClosure` /
  `ForceThunk` / `Resume` / `ResumeWithHandler` / handler arm call)
  を `enter_callee_eval_context` / `restore_caller_eval_context` で
  囲む。fresh eval id + `initial = return_frame_len` で callee 内で
  push された frame だけ consume できるようにする。
- d6: `select_handler` を 2-pass に。`PendingEnv` 由来の synthetic
  placeholder を実 handler より下げる優先度づけで、handler が
  shadow されないように。

既存 167 tests **pass**。`debugs_local_choice_*` も **pass**。
Layer 3 `debugs_std_undet_once_skip_eval_layers` は
`I64Mismatch(vm:2, cps_cranelift:0)` で fail (write27-c 時点は
`cps_cranelift:1` だった)。これは「synthetic 経由の legacy abort
で偶然 1 を返していた」状態から「Real SR + Resumption + anchor
merge の意味論パスに乗ったが、最終段で state が落ちる」状態への
**code path 移行**を意味していて、後退ではなく前進だよ〜。

---

## 進捗まとめ

```text
write27-c 後:
  Layer 3: cps_cranelift=1  (legacy abort fallback 経由)

write27-d 後:
  Layer 3: cps_cranelift=0  (Real SR / Resumption path に乗った)
  内訳:
    - perform_select は全部 origin=RealInstall を選んでる
    - resumption_anchor が prompt=1 install_eval=3,
      prompt=2 install_eval=6 で正しくセット
    - effectful_apply_resumption が anchor merge + combined frames で動く
    - sub::return SR が route_scope_return で current_handler match
      まで到達
  残課題:
    - SR resolved 後の handler stack truncate で inner once が
      消失し、reject Perform が outer once を拾う (詳細は後述)
```

---

## d1 — HandlerFrameOrigin

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativeCpsI64HandlerFrameOrigin {
    RealInstall,
    LegacyInstall,
    PendingEnv,
    ResumeWithHandler,
    StaticFallback,
}
```

各 frame 構築箇所:

```text
install_handler_full_i64_N         → RealInstall
yulang_cps_install_handler_i64     → LegacyInstall
take_pending_native_i64_handler_frames → PendingEnv
yulang_cps_resume_with_handler_i64 → ResumeWithHandler
current_native_i64_handler_stack_with_fallback (empty fallback) → StaticFallback
```

`perform_select` trace に `origin=...` を表示。trace を見ると、
write27-c では `origin=PendingEnv synthetic=true` がよく拾われていて、
これが Layer 1/2 と乖離する主因の一つと判明した。

---

## d2/d3 — Resumption 拡張

```rust
struct NativeCpsI64Resumption {
    code,
    env,
    handlers,
    guard_stack,
    return_frames: Box<[NativeCpsI64ReturnFrame]>,    // 追加
    handled_anchor: Option<NativeCpsI64HandlerAnchor>, // 追加
}

#[derive(Debug, Clone, Copy)]
struct NativeCpsI64HandlerAnchor {
    prompt: u64,
    install_eval_id: u64,
}
```

`make_native_i64_resumption` で:

- `return_frames`: `NATIVE_CPS_I64_RETURN_FRAMES` の clone。
- `handled_anchor`: 一旦 `None` (capture 時点では select 前)。

select 後に Perform codegen が新 helper を呼んで anchor を埋める:

```rust
extern "C" fn yulang_cps_set_resumption_anchor_from_selected_i64(
    resumption: *mut NativeCpsI64Resumption,
) -> i64 {
    let meta = SELECTED_HANDLER_META.borrow().clone();
    if let Some(meta) = meta {
        if !meta.synthetic && meta.escape_continuation != 0 {
            (*resumption).handled_anchor = Some(NativeCpsI64HandlerAnchor {
                prompt: meta.prompt,
                install_eval_id: meta.install_eval_id,
            });
        }
    }
    0
}
```

trace で `resumption_anchor: prompt=2 install_eval=6` のように出る。

---

## d4 (c6) — EffectfulApply Resumption helper

### runtime predicate

```rust
static NATIVE_CPS_I64_RESUMPTIONS: HashSet<usize>
yulang_cps_is_resumption_i64(value) -> 0/1
```

`make_native_i64_resumption` が pointer を set に挿入。reset 時に clear。

### anchor merge helpers (Layer 2 port)

```rust
fn merge_resumption_handlers_native(captured, current, anchor) -> Vec<...>
fn merge_extras_into_frames_native(frames, current, anchor) -> Vec<...>
fn same_handler_frame_native(a, b) -> bool  // (prompt, install_eval) 一致
```

ロジックは `cps_repr.rs` の `_repr` 変種をそのまま移植。

### effectful_apply_resumption_i64_N

```rust
fn effectful_apply_resumption_native(
    resumption, arg, post_cont, owner_initial, owner_eval,
    immediately_forces, env,
) -> i64 {
    // 1. Build F_post(post_cont, env, handlers snapshot, guards snapshot,
    //    owner_initial, owner_eval, immediately_forces).
    // 2. new_frames = current return_frames + [F_post]
    // 3. anchor merge:
    //    resumed_handlers = merge_resumption_handlers(...)
    //    adjusted_res    = merge_extras_into_frames(...)
    // 4. combined_frames = new_frames ++ adjusted_res
    // 5. swap thread-local state:
    //    return_frames = combined_frames
    //    handlers      = resumed_handlers
    //    guards        = resumption.guard_stack
    //    eval_context  = (fresh_eval, initial=0)
    // 6. (resumption.code)(resumption.env, arg)
}
```

N=0..4 の wrapper を作って IR から呼ぶ。

### EffectfulApply codegen 分岐

```text
is_resumption = is_resumption_i64(callable)
brif:
  closure_block:
    pre_push = return_frame_len()
    push_return_frame_i64_N(post_cont, ...)
    switch_eval_context(fresh, pre_push)
    result = apply_closure_i64(callable, arg)
    return result
  resumption_block:
    result = effectful_apply_resumption_i64_N(callable, arg, post_cont,
                                              current_initial, current_eval,
                                              imm_force, env_slots...)
    return result
```

trace に `effectful_apply_resumption: anchor=... fresh_eval=... combined_frames=... resumed_handlers=...` を出して動作確認。

---

## d5 — sync internal call の eval context save/restore

`enter_callee_eval_context` / `restore_caller_eval_context` 2 つの
codegen helper を新設し、全 sync call を囲む:

```text
let (saved_eval, saved_initial) = enter_callee_eval_context(...)
  // saved_eval     = current_eval_id_i64()
  // saved_initial  = current_initial_frame_count_i64()
  // callee_initial = return_frame_len_i64()
  // callee_eval    = fresh_eval_id_i64()
  // set_eval_context(callee_eval, callee_initial)

let result = call(...)

restore_caller_eval_context(saved_eval, saved_initial)
return_if_abort_active(...)
return_if_scope_return_active(result)
def_var(dest, result)
```

囲んだ箇所:

- `CpsStmt::ForceThunk` (両 path)
- `CpsStmt::DirectCall` (両 path)
- `CpsStmt::ApplyClosure` (両 path)
- `CpsStmt::Resume`
- `CpsStmt::ResumeWithHandler`
- `lower_selected_handler_return` の handler arm call

trace で `set_eval_context: ...` が大量に出るようになる。期待どおり
fresh eval id が割り当たって、`return_i64` の `frame_len <= initial`
判定が正しく動くように。

---

## d6 — `select_handler` の origin priority

trace で `origin=PendingEnv` が Real install を shadow するのを
観測したので、2-pass search に変更:

```rust
chosen = stack.iter().enumerate().rev()
    .find(|f| frame_allowed(f) && !matches!(f.origin, PendingEnv))
    .or_else(|| stack.iter().enumerate().rev().find(|f| frame_allowed(f)));
```

`PendingEnv` だけを2nd pass に降格させた。`LegacyInstall` /
`StaticFallback` はそのまま (legacy abort 経路と互換)。`PendingEnv`
は JIT 固有の補助構造で、Layer 1/2 に対応する概念がないため。

trace で `perform_select: ... origin=RealInstall` が出るように。

---

## テスト結果

```text
cargo test -p yulang-native            => 167 pass / 17 ignored
cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored
  => pass
cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored
  => pass
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored
  => Layer 1 OK / Layer 2 OK
     Layer 3 FAIL: I64Mismatch(vm:2, cps_cranelift:0)
```

---

## 残る Layer 3 のバグ

trace から読み解いた挙動:

```text
1. install handler=1 prompt=1 (outer once)
2. install handler=0 prompt=2 (outer sub::return)
3. push F_work_post (effectful frame for the inner work)
4. perform_select handler=1 prompt=1  ← outer once.branch
5. effectful_apply_resumption (anchor=prompt=1)
6. install handler=1 prompt=3 (inner once)  ← 内側のループ
7. perform_select handler=0 prompt=2  ← sub::return
8. scope_return_set prompt=2 value=1
9. route_scope_return propagates through several frames
10. action=current_handler match at current_eval=6 initial=3
    → handler stack truncated to before outer sub::return
    → **inner once (prompt=3) も一緒に truncate されて消失**
11. escape continuation runs in outer once's context
12. perform_select handler=1 (reject)
    → inner once が無いので OUTER once を拾う (idx=6 install_eval=3)
13. 結果として外側 once の早期終了経路に入り、最終値が 0
```

問題は step 10 の **`route_scope_return` の current_handler match
で handler stack を truncate する際に、selected handler より深く
install された frame (= inner once) も一緒に消える**こと。

Layer 1/2 では `handle_scope_return_repr` が
`active_handlers.truncate(index)` するけど、escape continuation を
call する側が handlers / frames を別経路で構築し直すから問題が
出ない (eval_continuations の再呼び出し)。Layer 3 では escape
continuation を直接 call し、handler stack はそのまま truncated 状態
で進む — ここがミスマッチ。

候補対策:

1. **escape 先で必要な handler を return_frame snapshot から再構築する**。
   現状 `continue_return_frame` が snapshot を復元するが、SR の escape
   call 直後は snapshot 復元せずに truncated state で進んでいる。
   ここで何らかの merge が要る。

2. **Layer 2 の `eval_continuations` のように、SR escape を「elsewhere
   から再 eval」する形に近づける**。これは大改修。

3. **truncate を全部やめて、SR matched frame だけ「scope を抜けたよ」
   フラグを立てる**設計に。Layer 1/2 とはやや乖離するが、JIT 流。

write27-e の方向はこのへんから一つ選ぶ感じになりそう。

---

## 触ったファイル

- `crates/yulang-native/src/cps_repr_cranelift.rs`
  - `NativeCpsI64HandlerFrameOrigin` enum (d1)
  - `NativeCpsI64HandlerFrame.origin` field (d1)
  - `NativeCpsI64HandlerAnchor` struct (d2)
  - `NativeCpsI64Resumption` に return_frames / handled_anchor (d2)
  - `NATIVE_CPS_I64_RESUMPTIONS` set thread_local (d4)
  - `make_native_i64_resumption` に full capture (d2/d3) + set 登録 (d4)
  - `yulang_cps_set_resumption_anchor_from_selected_i64` (d2)
  - `merge_resumption_handlers_native` /
    `merge_extras_into_frames_native` / `same_handler_frame_native` (d4)
  - `effectful_apply_resumption_native` + N=0..4 wrapper (d4)
  - `yulang_cps_is_resumption_i64` (d4)
  - EffectfulApply codegen 分岐 (d4)
  - `enter_callee_eval_context` / `restore_caller_eval_context` (d5)
  - 全 sync stmt + handler arm call を save/restore で囲む (d5)
  - `select_handler` を 2-pass + origin priority (d6)
  - `perform_select` trace に origin (d1)
  - reset/clear に新 thread_local を追加
  - symbol 登録

---

## 次の作業（write27-e 候補）

1. **escape continuation 後の inner-handler 再構築**:
   `route_scope_return` の current_handler match path で truncate する
   handlers をどう保存して escape 先に渡すか設計。たぶん
   matched_frame の snapshot を escape の handler stack として
   採用するのが Layer 1/2 と整合する。

2. **trace の追記**: SR route の current_handler match 後の
   continue_return_frame restore 過程を細かく見る。inner once が
   消えた瞬間を再確認する。

3. Layer 3 通過後、`Aborted` / `yulang_cps_abort_*` legacy の grep
   → 削除可否判定。

---

## ひとこと

write27-c の `cps:0 → 1` のあとに、write27-d で `cps:1 → 0` という
**値だけ見れば後退**になったけど、内容は明確に前進。
synthetic legacy 経路で「たまたま 1 が返っていた」状態から、Real SR
+ Resumption + anchor merge の **正しい意味論ルート**に乗ったから、
残るバグは「ルートのある 1 区間で state が落ちる」だけになっている。

ここからは「SR 解決後の handler 再構築」が決まれば一気に通る射程に
いると思うよ〜。
