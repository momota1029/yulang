---
title: native-undet-write27-a 実装レポート — Cranelift JIT に runtime state foundation
date: 2026-05-12
---

# native-undet-write27-a 実装レポート

## 結論（先に）

write27 は本来「cps_repr_cranelift JIT backend に Layer 1/2 の return-frame
意味論を移植して `debugs_std_undet_once_skip_eval_layers` の Layer 3 を通す」
という大規模 port タスク。

write27 自身が a/b/c に切る案を提示していたので、まず最小の **write27-a:
runtime state foundation** をやった。

- Cranelift JIT 用の **ScopeReturn slot** を追加 (`NATIVE_CPS_I64_SCOPE_RETURN`)。
- **Return frame stack** を追加 (`NATIVE_CPS_I64_RETURN_FRAMES`)。
- **Eval context** (current_eval_id + initial_frame_count) を thread_local に
  (`NATIVE_CPS_I64_EVAL_CONTEXT`)。
- 12 個の新 `extern "C"` helper を追加 + symbol 登録 + reset 統合。
- 既存の abort helper / `Aborted` 系は **そのまま残す**（legacy bridge）。
- codegen 側は **まだ何も書き換えていない**。完全に新規 state のみ。
- 既存 167 tests **pass**、`debugs_local_choice_*` 系も pass。

Layer 3 (`cps_repr_cranelift JIT == VM`) はまだ `todo!` panic のまま。これは
write27-b (EffectfulCall + EffectfulForce codegen) と write27-c
(EffectfulApply Resumption + anchor merge) で順次接続する。

---

## 進捗まとめ

- write26 後: Layer 1 OK + Layer 2 OK + Layer 3 `todo!` panic。
- write27-a 後: 同じ + Layer 3 接続の **runtime infrastructure** が用意完了。
  codegen 側はまだ未接続。

---

## Step 1: ScopeReturn slot

```rust
#[derive(Debug, Clone, Default)]
struct NativeCpsI64ScopeReturn {
    active: bool,
    prompt: u64,
    target: i64,
    value: i64,
}

thread_local! {
    static NATIVE_CPS_I64_SCOPE_RETURN: RefCell<NativeCpsI64ScopeReturn> =
        const { RefCell::new(NativeCpsI64ScopeReturn { ... }) };
}
```

helper 6 個:

- `yulang_cps_scope_return_i64(prompt, target, value) -> i64`
- `yulang_cps_scope_return_active_i64() -> i64`
- `yulang_cps_scope_return_prompt_i64() -> i64`
- `yulang_cps_scope_return_target_i64() -> i64`
- `yulang_cps_scope_return_value_i64() -> i64`
- `yulang_cps_clear_scope_return_i64() -> i64`

意味論：`cps_eval::CpsRuntimeValue::ScopeReturn` /
`cps_repr::CpsReprRuntimeValue::ScopeReturn` の Cranelift 版。

旧 `yulang_cps_abort_*` 系はまだ codegen から呼ばれているので残す。

---

## Step 2: Return frame stack

```rust
#[derive(Clone)]
struct NativeCpsI64ReturnFrame {
    continuation: usize,                      // JIT function pointer
    env: i64,
    handlers: Vec<NativeCpsI64HandlerFrame>,  // snapshot
    guards: Vec<i64>,                          // snapshot
    owner_initial_frame_count: usize,
    owner_eval_id: u64,
}

thread_local! {
    static NATIVE_CPS_I64_RETURN_FRAMES: RefCell<Vec<NativeCpsI64ReturnFrame>> =
        const { RefCell::new(Vec::new()) };
}
```

helper 3 個:

- `yulang_cps_return_frame_len_i64() -> i64`
- `yulang_cps_push_return_frame_i64(continuation, env, owner_initial, owner_eval) -> i64`
- `yulang_cps_pop_return_frame_i64() -> i64` (continuation pointer or -1)

`pop_return_frame` は handler stack / guard stack / eval context の snapshot
を frame から復元してから continuation pointer を返す。実際の continuation
call は codegen 側で行う（後の write27-b で）。

---

## Step 3: Eval context

```rust
#[derive(Debug, Clone, Copy, Default)]
struct NativeCpsI64EvalContext {
    current_eval_id: u64,
    initial_frame_count: usize,
}

thread_local! {
    static NATIVE_CPS_I64_EVAL_CONTEXT: RefCell<NativeCpsI64EvalContext> =
        const { RefCell::new(...) };
    static NATIVE_CPS_I64_NEXT_EVAL_ID: RefCell<u64> = const { RefCell::new(0) };
}
```

helper 4 個:

- `yulang_cps_fresh_eval_id_i64() -> i64`
- `yulang_cps_current_eval_id_i64() -> i64`
- `yulang_cps_current_initial_frame_count_i64() -> i64`
- `yulang_cps_set_eval_context_i64(eval_id, initial) -> i64`

Cranelift の continuation function signature に hidden params を増やさず、
thread_local context として持つ。write27 notes でもこの方針を推奨している。

---

## sentinel 定数

```rust
const NATIVE_CPS_I64_SYNTHETIC_EVAL_ID: u64 = u64::MAX;
const NATIVE_CPS_I64_EXIT_RWH_TARGET: i64 = -1;
```

`cps_eval::SYNTHETIC_EVAL_ID` / `cps_eval::EXIT_RWH_TARGET` の Cranelift 版。

---

## reset 統合

`reset_native_i64_cps_state` で新 state を全部 clear。複数 test の thread_local
汚染を防ぐ。

---

## テスト結果

```text
cargo test -p yulang-native                              => 167 pass / 17 ignored
cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored
  => pass
cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored
  => pass
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored
  => Layer 1 OK / Layer 2 OK / Layer 3 todo! panic (unchanged)
```

8 個の `dead_code` warning が出る。これは新 helper が codegen からまだ呼ばれて
いないため。symbol 登録があるので、JIT linker は解決できる。次の write27-b/c
で codegen から呼ぶようになる。

---

## 触ったファイル

- `crates/yulang-native/src/cps_repr_cranelift.rs`:
  - `NativeCpsI64ScopeReturn`, `NativeCpsI64ReturnFrame`,
    `NativeCpsI64EvalContext` 構造体追加
  - `NATIVE_CPS_I64_SYNTHETIC_EVAL_ID`, `NATIVE_CPS_I64_EXIT_RWH_TARGET`
    sentinel 定数追加
  - thread_local block に 4 個の新 slot 追加 (SCOPE_RETURN, RETURN_FRAMES,
    EVAL_CONTEXT, NEXT_EVAL_ID)
  - reset_native_i64_cps_state に新 state の clear を追加
  - 13 個の `extern "C"` helper 追加
  - 13 個の symbol を `builder.symbol(...)` で登録

---

## 次の作業（write27-b/c）

### write27-b: codegen 接続

1. **Return terminator codegen の更新**:
   - `if return_frame_len() > current_initial_frame_count()`: continue_return_frames
   - else: 通常 Return
   - pre-force v2 (Thunk 値 + top frame's continuation が ForceThunk なら)

2. **DirectCall / ApplyClosure / ForceThunk 後の route_scope_return**:
   - `if scope_return_active(): route_scope_return(); return routed`

3. **EffectfulCall codegen**:
   - `pre_push_count = return_frame_len()`
   - `push_return_frame(resume_cont, resume_env, owner_initial, current_eval)`
   - `set_eval_context(fresh_eval_id(), pre_push_count)`
   - call target → result → route if scope_return_active

4. **EffectfulForce codegen**: 同型

### write27-c: EffectfulApply + walk

5. **EffectfulApply codegen** (Closure + Resumption):
   - Closure: 同型 push frame + tail-call
   - Resumption: helper `yulang_cps_effectful_apply_resumption_i64` を新規追加し、
     anchor merge + combined_frames を Rust 側で計算

6. **route_scope_return helper**:
   - current handler stack で match
   - return frame stack[initial..] を walk
   - match したら handler stack truncate + frame stack truncate + clear sr +
     set eval context + call escape continuation

7. **Perform codegen の ScopeReturn 化**:
   - 旧 `yulang_cps_abort_i64` → 新 `yulang_cps_scope_return_i64`
   - frame_in_active で synthetic 除外
   - handled_anchor 記録

8. **Handler frame の extension**:
   - prompt, install_eval_id, escape, return_frame_threshold, inherited
     fields の追加（既存 handler stack push 側も更新）

---

## りなに渡す質問

1. **Return terminator codegen の詳細**: 現在 Cranelift の Return は単純に
   `ireturn value` っぽい。これを「return frame があれば pop してその
   continuation を call」に変えるのは、JIT codegen として trampoline 的な
   構造が要りそう。Rust helper で完結させる方が安全？それとも codegen 側で
   loop を作る？

2. **continuation function pointer の取得**: `push_return_frame` に渡す
   `continuation_ptr` は、Cranelift で `func_addr` 命令で取得する形になる
   と思う。current function 内の cont id を function pointer に解決する
   仕組みは既存にある？

3. **handler frame の field 拡張**: `NativeCpsI64HandlerFrame` に prompt や
   install_eval_id を足すと、InstallHandler codegen 側の `push` ロジック
   が複雑になる。helper 関数で push する形にした方がいい？

---

## コミット予定

write27-a 完了。
- Cranelift JIT に Layer 1/2 と同型の runtime state infrastructure を追加
- 167 tests pass、local choice 系 pass、regression なし
- Layer 3 はまだ `todo!` panic のまま (write27-b/c で codegen 接続)
