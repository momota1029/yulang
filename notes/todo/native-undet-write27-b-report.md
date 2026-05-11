---
title: native-undet-write27-b 実装レポート — Cranelift JIT 側 Return + Effectful{Call,Force,Apply} codegen
date: 2026-05-12
---

# native-undet-write27-b 実装レポート

## 結論（先に）

write27 を a/b/c に切る計画の **b 段** を実装。write27-a が JIT runtime に
ScopeReturn slot / return frame stack / eval context を「置いた」段だったのに
対して、write27-b はそれを **codegen 側から呼ぶ** 段。

- `yulang_cps_return_i64` を Return terminator codegen に挿入。frame_len <=
  initial の通常ケースでは no-op、effectful 経路では pre-force v2 or
  continue_return_frame に分岐。
- `push_return_frame_i64_N` (N=0..4) family と
  `yulang_cps_continue_return_frame_i64` を helper として実装。
- `EffectfulCall` / `EffectfulForce` / `EffectfulApply (Closure)` の codegen
  を実装。`todo!` panic および直前 commit の `UnsupportedTerminator` Err は
  全て消えた。
- 既存 167 tests **pass**、`debugs_local_choice_*` 系も pass、regression なし。
- `debugs_std_undet_once_skip_eval_layers` の Layer 3 が
  **`UnsupportedTerminator` Err → `I64Mismatch { vm: 2, cps_cranelift: 0 }`**
  に進化。Cranelift JIT が compile + run まで通り、numeric mismatch のみ残る。

`EffectfulApply` の Resumption-callable 分岐と Perform を ScopeReturn 化する
作業は write27-c に持ち越し。

---

## 進捗まとめ

- write26 後: Layer 1 OK + Layer 2 OK + Layer 3 `todo!` panic。
- write27-a 後: 同じ + JIT runtime に foundation (slot/frames/ctx)。
- write27-b prep 後: 同じ + `todo!` → `UnsupportedTerminator` Err。
- **write27-b 後**: Layer 3 が compile + run。`I64Mismatch(vm:2, cps:0)`。
  Cranelift JIT が effectful terminators を実際に処理して、走り切れるように。

---

## Step b1: Return terminator を helper 経由に

### `NativeCpsI64ReturnFrame` の env 型修正

write27-a の `env: i64` は誤り。JIT 続行 (`NativeCpsI64Continuation`) のシグネチャ
が `extern "C" fn(*const i64, i64) -> i64` であることに合わせ、
`env: Box<[i64]>` に変更。`continuation` の呼び出し時に `env.as_ptr()` を渡す。

`Box<[i64]>` は `NativeCpsI64Resumption::env` と同じ表現で、メモリ寿命を
return frame の lifetime に紐づけて安全。

### `push_return_frame_i64_N` (N=0..4)

`yulang_cps_make_resumption_i64_N` と同型の家族。codegen 側は resume continuation
の `environment` slot 数に応じて 5 種類のうちひとつを呼び分ける。

```rust
extern "C" fn yulang_cps_push_return_frame_i64_2(
    continuation: i64,
    owner_initial: i64,
    owner_eval: i64,
    immediately_forces: i64,
    a: i64,
    b: i64,
) -> i64;
```

write27-a の単一 `push_return_frame_i64` は削除した（codegen から使われない）。

### `yulang_cps_continue_return_frame_i64(value)`

write27-a の「pop して continuation pointer を返す」だけの helper を、
**pop + 状態復元 + continuation 呼び出しまで完結する** 形に置き換え。

```rust
extern "C" fn yulang_cps_continue_return_frame_i64(value: i64) -> i64 {
    let frame = pop_innermost();
    restore_handler_stack(frame.handlers);
    restore_guard_stack(frame.guards);
    set_eval_context(frame.owner_eval_id, frame.owner_initial_frame_count);
    let cont: NativeCpsI64Continuation = transmute(frame.continuation);
    cont(frame.env.as_ptr(), value)
}
```

理由は write27-b notes 通り：env / handler snapshot / guard snapshot / eval
context / continuation arity / continuation call、これらを Cranelift IR で
ばらすと事故が増える。Rust helper で atomic にまとめるのが安全。

### `yulang_cps_pre_force_top_frame_i64(value)` (pre-force v2)

write25 の pre-force v2 を JIT 化。**top frame を pop せず retained**、
`current_eval_id = top.owner_eval_id`、`initial_frame_count = retained_len`
に設定して continuation を呼ぶ。

```rust
extern "C" fn yulang_cps_pre_force_top_frame_i64(value: i64) -> i64 {
    let top = peek_innermost();
    restore_handler_stack(top.handlers.clone());
    restore_guard_stack(top.guards.clone());
    set_eval_context(top.owner_eval_id, return_frames.len()); // retained
    let cont: NativeCpsI64Continuation = transmute(top.continuation);
    cont(top.env.as_ptr(), value)
}
```

pre-force 条件 (`immediately_forces_param`) は **codegen 時** に判定して、
push 時の引数として渡す (`NativeCpsI64ReturnFrame.immediately_forces_param`)。
JIT runtime は CpsContinuationId や function body を知らないから、判定は
codegen 側でやるのが正しい設計。

### `yulang_cps_return_i64(value)` — Return terminator 統合 helper

JIT 側の Return terminator が単純に呼ぶだけで意味論を完結する helper：

```rust
extern "C" fn yulang_cps_return_i64(value: i64) -> i64 {
    if frame_len <= initial { return value; }
    if value_is_thunk && top_frame.immediately_forces_param {
        return pre_force_top_frame_i64(value);
    }
    return continue_return_frame_i64(value);
}
```

### Return terminator codegen の変更

```rust
CpsTerminator::Return(value) => {
    let value = read_value(builder, function, *value)?;
    let routed = call_i64_helper(
        module_backend,
        builder,
        "yulang_cps_return_i64",
        &[value],
    )?;
    builder.ins().return_(&[routed]);
}
```

`yulang_cps_return_i64` は frame_len = 0 の一般ケースで no-op なので、effectful
terminators を使わない既存 167 tests には完全に影響なし。

---

## Step b3: Effectful{Call,Force,Apply} codegen

### `lookup_continuation` alias

`lower_effect_terminator` の引数 `continuation: &CpsReprAbiContinuation` が
モジュール関数 `continuation()` を shadow するため、`lookup_continuation` を
別名で用意した。

### `check_resume_continuation_shape`

`make_resumption` と同じ制約: resume continuation の params は 1 つ
(call の result)、environment は最大 4 slot。違反したら既存の
`UnsupportedTerminator` で error。

### `resume_continuation_immediately_forces_param`

cps_eval/cps_repr の `return_frame_immediately_forces_param` の JIT 版。
AST レベルで resume continuation の最初の stmt が `ForceThunk(first_param)`
かを判定。

```rust
fn resume_continuation_immediately_forces_param(
    resume_cont: &CpsReprAbiContinuation,
) -> bool {
    let Some(first_param) = resume_cont.params.first() else { return false; };
    matches!(
        resume_cont.stmts.first(),
        Some(CpsStmt::ForceThunk { thunk, .. }) if *thunk == first_param.value
    )
}
```

### `push_return_frame_for_resume`

resume continuation の env を読み、func_addr で function pointer を取り、
`push_return_frame_i64_N` を呼ぶ codegen sequence を emit。
`make_resumption` の env 取り方と同型。

```rust
let func_ref = continuation_func_ref(..., resume_cont.id, ...)?;
let cont_ptr = builder.ins().func_addr(types::I64, func_ref);
let current_eval = call_i64_helper(..., "yulang_cps_current_eval_id_i64", &[])?;
let current_initial = call_i64_helper(..., "yulang_cps_current_initial_frame_count_i64", &[])?;
let immediate_force_value = builder.ins().iconst(types::I64, immediate_force as i64);
let mut args = vec![cont_ptr, current_initial, current_eval, immediate_force_value];
for slot in &resume_cont.environment {
    args.push(read_value(builder, function, slot.value)?);
}
call_i64_helper(..., "yulang_cps_push_return_frame_i64_N", &args)?;
```

### `switch_eval_context_for_callee`

push 後、callee 側の eval context にスイッチ。fresh eval id + initial =
return_frame_len (push 直後)。

```rust
let fresh_eval = call_i64_helper(..., "yulang_cps_fresh_eval_id_i64", &[])?;
let frame_len = call_i64_helper(..., "yulang_cps_return_frame_len_i64", &[])?;
call_i64_helper(..., "yulang_cps_set_eval_context_i64", &[fresh_eval, frame_len])?;
```

### `EffectfulCall` / `EffectfulForce` / `EffectfulApply` の codegen

3 つとも共通パターン：
1. resume continuation を取り、shape 検査。
2. `immediately_forces_param` 判定。
3. `push_return_frame_for_resume` で F_post push。
4. arg/closure 等の値を read（context switch 前に）。
5. `switch_eval_context_for_callee` で callee context にスイッチ。
6. target を呼ぶ:
   - `EffectfulCall`: `call <target_func>(args)`
   - `EffectfulForce`: `call yulang_cps_force_thunk_i64(thunk)`
   - `EffectfulApply`: `call yulang_cps_apply_closure_i64(closure, arg)`
7. result を return。

target の Return helper が F_post を consume して resume continuation を呼ぶ
ので、ここで戻ってきた値はそのまま意味論的に正しい。

`EffectfulApply` の Resumption-callable は write27-c で別 helper
(`effectful_apply_resumption_i64`) として実装する。anchor merge と
combined_frames を Rust 側で計算する必要があるため。

---

## Layer 3 trace の進化

```text
write27-a 後:
  todo!("Effectful{Call,Apply,Force} in cps_repr Cranelift backend") panic

write27-b prep 後:
  Err(UnsupportedTerminator { function: "work__mono0", kind: "effectful-call" })

write27-b 後:
  Layer 1 (CPS eval): OK
  Layer 2 (CPS repr eval): OK
  CPS repr Cranelift compare: I64Mismatch { vm: 2, cps_cranelift: 0 }
```

つまり：
- compile 成功
- JIT run 成功
- runtime helper が正常に呼ばれる
- ただし結果が 0（おそらく early-escape か empty path）

cps:0 の原因は明確：Perform codegen がまだ **旧 abort helper を発火**しており、
新 ScopeReturn slot を使ってない。だから handler arm の natural return が
正しく routing されない。route_scope_return helper もまだ無い。

これらは write27-c の作業。

---

## テスト結果

```text
cargo test -p yulang-native                              => 167 pass / 17 ignored
cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored
  => pass
cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored
  => pass
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored
  => Layer 1 OK / Layer 2 OK
  => Layer 3 fails with I64Mismatch (vm:2, cps_cranelift:0)
```

write27-b の codegen は既存 167 tests には透明（Return helper は frame_len=0
で no-op、Effectful* codegen path は 167 tests から到達されない）。確認済み。

---

## 触ったファイル

- `crates/yulang-native/src/cps_repr_cranelift.rs`:
  - `NativeCpsI64ReturnFrame.env` を `Box<[i64]>` に変更
  - `NativeCpsI64ReturnFrame.immediately_forces_param: bool` 追加
  - `push_return_frame_i64_N` (N=0..4) helper 群追加
  - `push_native_i64_return_frame_with_env` shared backend
  - `yulang_cps_continue_return_frame_i64` 追加（pop+restore+call）
  - `yulang_cps_top_return_frame_pre_force_i64` 追加
  - `yulang_cps_pre_force_top_frame_i64` 追加
  - `yulang_cps_return_i64` 追加（Return terminator helper）
  - `pop_return_frame_i64` 削除（continue_return_frame に置換）
  - symbol 登録 13 個追加（push N variants + new helpers）
  - `Return` terminator codegen を `yulang_cps_return_i64` 経由に
  - `lookup_continuation` alias 追加
  - `check_resume_continuation_shape` helper 追加
  - `resume_continuation_immediately_forces_param` helper 追加
  - `push_return_frame_for_resume` codegen helper 追加
  - `switch_eval_context_for_callee` codegen helper 追加
  - `EffectfulCall` codegen 実装
  - `EffectfulForce` codegen 実装
  - `EffectfulApply` codegen 実装（Closure 分岐のみ; Resumption は deferred）

---

## write27-c で残ってる作業

### 1. `route_scope_return` Rust helper

```rust
extern "C" fn yulang_cps_route_scope_return_i64() -> i64
```

仕様:
- ScopeReturn slot から prompt / target / value を読む
- current handler stack を `rposition` で walk:
  - `frame.prompt == prompt && frame.install_eval_id == current_eval_id`
- 見つかれば handler stack truncate + return_frames truncate + clear sr +
  set eval_context + call escape continuation
- 見つからなければ `return_frames[current_initial..]` を reverse walk
- それでも見つからなければ slot active のまま value を返す

### 2. `Perform` codegen を ScopeReturn 化

現状 `yulang_cps_abort_i64(value)` で abort slot に書く。これを
`yulang_cps_scope_return_i64(prompt, target, value)` に置き換える。
prompt は selected handler の prompt、target は selected handler の escape
継続。`frame_in_active` 判定（synthetic frame の install_eval ≠ SYNTHETIC）
で wrap or pass-through を決める。

### 3. Handler frame extension

`NativeCpsI64HandlerFrame` に prompt / install_eval_id / escape /
escape_owner / return_frame_threshold / inherited を追加。
install_handler helper を拡張 (もしくは `_full` variant 新設)。

### 4. Sync internal call の eval context save/restore

`DirectCall` / `ApplyClosure` / `ForceThunk` stmt の前後で：

```text
saved_eval = current_eval_id
saved_initial = current_initial
set_eval_context(fresh_eval_id, return_frame_len)
call
set_eval_context(saved_eval, saved_initial)
if scope_return_active: route_scope_return + return
```

### 5. `EffectfulApply` Resumption 用 helper

```rust
extern "C" fn yulang_cps_effectful_apply_resumption_i64(
    resumption: *const NativeCpsI64Resumption,
    arg: i64,
    post_cont: i64,
    post_initial: i64,
    post_eval: i64,
    immediately_forces: i64,
    // env slots...
) -> i64
```

Rust 側で anchor merge + combined_frames を計算してから target を呼ぶ。

---

## りなに渡す質問

1. **route_scope_return helper の戻り値設計**: codegen 側で internal call
   の後に `if scope_return_active: result = route_scope_return(); return result`
   と書く想定。route_scope_return が match して escape を呼んだ場合は
   escape の戻り値、match しなかった場合は元の result を返せばよい？
   `route_scope_return_i64(fallback_value)` のように fallback を取る形が
   いいかな。

2. **Handler frame の field 拡張時、既存 install_handler helper を破壊
   しないか**: 現在の `yulang_cps_install_handler_i64(handler)` を保持しつつ、
   write27-c では新 helper `yulang_cps_install_handler_full_i64(...)`
   を Perform / InstallHandler stmt から呼ぶ形に切り替える方向で OK？

3. **Aborted / abort helper の削除タイミング**: Perform を ScopeReturn 化
   すると、abort helper の使われ方は test や fallback 経路だけになりそう。
   write27-c で完全削除を試すべき？ それとも legacy bridge として残す？

---

## コミット予定

write27-b 完了 (commit `11c6748`)。
- JIT runtime に Return + Effectful*{Call,Force,Apply Closure} を接続
- 167 tests pass、local choice 系 pass、regression なし
- Layer 3: UnsupportedTerminator → I64Mismatch(vm:2, cps:0) に進化
- 残: Perform → ScopeReturn 化 + route_scope_return helper + Handler frame
  extension + EffectfulApply Resumption variant は write27-c
