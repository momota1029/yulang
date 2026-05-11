---
title: native-undet-write22 実装レポート — eval-frame identity を導入
date: 2026-05-11
---

# native-undet-write22 実装レポート

## 結論（先に）

- write22 spec 通り `CpsEvalId` を導入、`CpsHandlerFrame.install_eval_id` /
  `CpsReturnFrame.owner_eval_id` も追加完了
- `handle_scope_return` の判定を write21 の loose check
  (`escape_owner_function == current_function`) から
  **strict check (`install_eval_id == current_eval_id`)** に置き換え
- 既存 167 tests **pass**（regression なし）
- `debugs_local_choice_caller_rest_eval` / `debugs_local_choice_callback_rest_eval`
  も pass
- `debugs_std_undet_once_skip_eval_layers` は **cps:1 → cps:0** に回帰
- ただし回帰の原因は eval_id 機構の不備ではなく、Case 3
  （intermediate handler frame の destruction）が顕在化したため。
  これは write22 のスコープを超える追加設計が必要

write22 は eval frame identity という **正しい基盤** を整備した step。
test 一発で cps:2 まで届かせる single fix にはならなかった。

---

## 進捗まとめ

- write18 後: cps:0 / vm:2
- write21 後: cps:1 / vm:2
- write22 後: **cps:0** / vm:2

数値だけ見ると write21 から後退に見えるが、write21 は loose check で
意味論的に不正確な早期 match を起こしていた。write22 はその hack を撤去
した上で正しい install scope identity (eval_id) を導入。それで露呈した
残バグが Case 3。

---

## step 1: `CpsEvalId` 型と `fresh_eval_id()`

`fresh_prompt()` と同じ thread_local counter 方式で実装。

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CpsEvalId(u64);

thread_local! {
    static EVAL_ID_COUNTER: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

fn fresh_eval_id() -> CpsEvalId {
    EVAL_ID_COUNTER.with(|cell| {
        let id = cell.get();
        cell.set(id + 1);
        CpsEvalId(id)
    })
}

const SYNTHETIC_EVAL_ID: CpsEvalId = CpsEvalId(u64::MAX);
```

`SYNTHETIC_EVAL_ID` は `handler_stack_with_static` の synthetic fallback frame
が ScopeReturn 解決に参加してしまわないようにする番兵。

---

## step 2: `CpsHandlerFrame.install_eval_id`

InstallHandler / ResumeWithHandler / synthetic / pushed 全てで field を埋めた。
新しい doc comment：

```rust
/// Identity of the eval frame that ran `InstallHandler` to create this
/// frame. A `ScopeReturn` only resolves at a handler whose
/// `install_eval_id == current_eval_id`. Function identity is not
/// enough: a multi-shot resumption can run the same CPS function in a
/// fresh eval frame, and that fresh frame must not catch a handler
/// installed by the original eval (write22).
install_eval_id: CpsEvalId,
```

`inherited` フラグは残す。primary check は `install_eval_id` だが、
inherited は trace や Perform handler search の補助情報として有用。

---

## step 3: `CpsReturnFrame.owner_eval_id`

EffectfulCall / EffectfulApply / EffectfulForce の全 push site で
`owner_eval_id: current_eval_id` を埋めた。

```rust
/// Identity of the eval frame that pushed this return frame. When
/// `continue_return_frames` resumes the owner continuation, this id is
/// restored as `current_eval_id` so `ScopeReturn` resolution targets
/// the same eval frame that originally installed the matching handler
/// (write22).
owner_eval_id: CpsEvalId,
```

---

## step 4: `resume_continuation` に `current_eval_id` 引数

```rust
fn resume_continuation(
    ...
    current_eval_id: CpsEvalId,
) -> CpsEvalResult<CpsRuntimeValue> { ... }
```

- `eval_continuations`：エントリで `let current_eval_id = fresh_eval_id();`
  → cross-function call は新しい eval frame
- `continue_return_frames`：`frame.owner_eval_id` を復元 → 元の install
  scope identity が残る
- `force_returned_thunk_before_frame_consumption`（dead code）：
  `top_frame.owner_eval_id` を使う形に更新

---

## step 5: `handle_scope_return` の判定

変更前 (write21)：

```rust
frame.prompt == prompt
    && (!frame.inherited
        || frame.escape_owner_function == current_function)
```

変更後 (write22)：

```rust
frame.prompt == prompt && frame.install_eval_id == current_eval_id
```

`escape_owner_function == current_function` の owner check は残す
（function-local jump target の安全弁）。

trace に `eval=<current_eval_id>` と
`install_eval=<matched_handler.install_eval_id>` を出力するように拡張。

---

## 禁止事項チェック

- ✓ guard lowering を直さない
- ✓ owner check (frame_owner_match) を維持
- ✓ Cranelift backend を触らない
- ✓ initial_frame_count を消さない
- ✓ write17 pre-force は引き続き disabled（dead code）
- ✓ ApplyClosure / ForceThunk の effectful 化はしない
- ✓ return_frame_threshold を消さない

---

## step 6: テスト結果

```text
cargo test -p yulang-native                              => 167 pass / 17 ignored
cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored
  => pass
cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored
  => pass
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored
  => FAIL: ValueMismatch { vm: Int("2"), cps: Int("0") }
```

local choice 系 pass、regression なし。`once_skip_eval_layers` は cps:0
に後退。

---

## trace 上で確認できた eval_id 機構の正しい動作

write22 trace の主要部：

```text
L26 InstallHandler fn=once_mono4 eval=4 cont 3 prompt=0     ← outer once install in eval=4
L34 InstallHandler fn=each_mono1 eval=8 cont 0 prompt=1     ← H_sub install in eval=8
L46 Perform branch each cont 5 active_handlers=[(0,T,1),(1,T,0)]
L55 InstallHandler fn=once_mono4 eval=22 cont 3 prompt=2    ← inner once install in eval=22
L56 Perform sub::return each cont 8 active_handlers=[(0,T,1),(1,T,0),(2,T,1)]

L57 Return each cont 2 ... initial=0    ← arm body Return
L58 ScopeReturnDispatch fn=each eval=24 prompt=1 matched=no Propagate
L59 ScopeReturnDispatch fn=once eval=23 prompt=1 matched=no Propagate
L60 ScopeReturnDispatch fn=once eval=22 prompt=1 matched=no Propagate
L61 ScopeReturnDispatch fn=each eval=17 prompt=1 matched=no Propagate
L62 ScopeReturnDispatch fn=fold_impl eval=10 prompt=1 matched=no Propagate
L63 ScopeReturnDispatch fn=each eval=8 prompt=1 matched=yes install_eval=8 JumpOrExit
   ★ install_eval_id strict 判定が正しく eval=8 で match している ★
L64 Return each cont 2 value=Plain(Int 1)
```

各 InstallHandler の `eval=N` と、最終 dispatch の `install_eval=8 == eval=8`
の一致から、eval_id 機構は **意味論的に正しく動作している**ことが確認できる。

---

## 残バグ：Case 3（intermediate handler eval destruction）

write22 notes が予測していた Case 3 が顕在化：

```text
L65 Return fn=int::gt cont 0 value=Plain(Bool(false))
L66 Return fn=guard__mono3 cont 0 value=Thunk
L67 Perform reject ... active_handlers=[(0,T,1)]    ← outer once H のみ
L70 ScopeReturnDispatch fn=once eval=4 prompt=0 matched=yes install_eval=4 JumpOrExit
L71 Return once cont 5 value=Variant(nil)
```

work cont 1 が n=1 を受け取って continue する時、その eval の active_handlers
に **inner once H (prompt=2) が存在しない**。

### なぜか

SR の伝播は call-stack 経由（`return Ok(SR)` で各 eval loop を抜ける）。
このとき eval=22, eval=23, eval=17 などの **intermediate eval frame が
local 状態（active_handlers を含む）と共に破棄**される。

eval=22 が消滅した時点で inner once H の install scope も消える。eval=22 が
suspended として保存されていれば残せたが、SR Propagate の機構ではそれが
起きない。

eval=8 で match → JumpOrExit → cont 2 Return → 値が bubble up して work
cont 1 の DirectCall dispatch に戻る。work の eval は **inner once が install
されるよりも前から実行中**（work → each → fold_impl 経由で inner once は
作られた）なので、work の local active_handlers には inner once H が
初めから入っていない。

### 期待されていた flow（write22 notes step 8）

```text
8. reject は inner once (prompt=2) に match → reject arm → uncons queue=[k1] →
   k1 false replay → x=2 path → sub::return(2) → just(2)
```

inner once H が work cont 1 の reject perform 時に **生きていなければならない**。

### 構造的な障害

resumption が capture する `return_frames` には `F_each_post` (H_sub install を
含む frame) が **含まれていない**。理由：fold_impl cont 0 が早期に Thunk を
Return してしまい、`continue_return_frames` が `F_each_post` を pop して
eval=8' を cont 12 で復元するため、その後の branch perform 時には
`F_each_post` は既に消費済み。

```text
each cont 0:
  InstallHandler H_sub
  EffectfulCall fold_impl → F_each_post push, tail-call to eval=10
eval=10 (fold_impl cont 0):
  MakeThunk cont 1; Return Thunk    ← own_frames=[F_each_post] consumed
continue_return_frames: pop F_each_post → resume eval=8' at cont 12
                        rest = [] frames
eval=8' (cont 12, restored at eval_id=8):
  ForceThunk sync → 全ての effects がこの sub-eval で発生
  branch perform → resumption.return_frames は sub-eval が push した frames のみ
                   → F_each_post は含まれない
```

つまり walk-frames でも install scope を find できない（F_each_post が
chain に居ない）。

---

## write23 で取るべき方向

write22 followup (write23) で扱う必要のある仕事：

### 案 A：write17 (pre-force) を write22 と組み合わせて再有効化

`fold_impl cont 0 Return Thunk` の段階で `continue_return_frames` を
呼ばずに、`force_returned_thunk_before_frame_consumption` で thunk body を
`F_each_post` を保持したまま `current_eval_id = top_frame.owner_eval_id`
で実行する。

```rust
// Return terminator:
if let CpsRuntimeValue::Thunk(thunk) = &v {
    if let Some(top_frame) = own_frames.last() {
        if return_frame_immediately_forces_param(module, top_frame)? {
            let result = force_returned_thunk_before_frame_consumption(
                module, thunk.clone(), top_frame, own_frames.clone(), initial_frame_count,
            )?;
            // bubble up
        }
    }
}
```

write17 が以前 disabled だった理由は「H_sub が body の eval で resolve
できない」だったが、write22 の `install_eval_id` で
`current_eval_id = F_each_post.owner_eval_id = 8` と
`H_sub.install_eval_id = 8` が一致するので resolve できる。

ただし pre-force だけでは Case 3 は完全には解けない見込み（inner once H が
post-resolution eval に伝わらない問題は残る）。

### 案 B：propagate-via-frames + intermediate handler collection

`Propagate` 時に call-stack ではなく captured frames を walk する。各
popped frame の `active_handlers` から **install_eval == owner_eval** の
handler を accumulator に集める。match した時にその accumulator を
post-jump eval に inject する。

「sibling handler 保存」の機構を builder-pattern で組む形になる。

### 案 C：`inject_extra_handlers` の挿入位置調整

現在 extras は active_handlers の末尾に push（idx=末尾 → 最も innermost）。
これだと truncate(idx of H_sub) で extras が消える。

挿入位置を「H_sub よりも前」（つまり captured chain の handlers よりも前
or 後ろの outer once H よりも前）にすれば truncate されない。ただし
handler search 順が変わるので慎重に。

私の感触では **案 A + 案 B の組み合わせ**が必要。案 C は単独だと
handler search の意味論が崩れる懸念。

---

## 触ったファイル

- `crates/yulang-native/src/cps_eval.rs`:
  - `CpsEvalId` 型 + `fresh_eval_id()` + `SYNTHETIC_EVAL_ID` 追加
  - `CpsHandlerFrame.install_eval_id: CpsEvalId` field 追加
  - `CpsReturnFrame.owner_eval_id: CpsEvalId` field 追加
  - `resume_continuation` に `current_eval_id` 引数
  - `eval_continuations` で `fresh_eval_id()` 発行
  - `continue_return_frames` で `frame.owner_eval_id` 復元
  - `handle_scope_return` の判定を `install_eval_id == current_eval_id` に
  - InstallHandler / ResumeWithHandler / synthetic / pushed の全ての
    handler frame 作成箇所で `install_eval_id` を設定
  - EffectfulCall / EffectfulApply / EffectfulForce の全ての return frame
    作成箇所で `owner_eval_id` を設定
  - trace に `eval=` / `install_eval=` / `owner_eval=` を表示

write22-report.md として記録。

---

## りなに渡す質問

1. **Case 3 の解法方向**：`F_each_post` が fold_impl cont 0 の早期 Thunk
   Return で消費されてしまうので、walk-frames では install scope を
   find できない。案 A (write17 + write22) で `F_each_post` を保持する
   方向で良い？

2. **inner once H の preservation**：sub::return abort 後、work cont 1 が
   reject perform した時、 inner once H が active_handlers に残っている
   必要がある。これは abort の意味論として：
   - 案 A: arm body の eval を「保留」して、abort 後に再開する
     （delimited continuation の本格対応）
   - 案 B: abort 通過時に sibling handler を accumulator に集めて、
     post-jump eval に inject する
   
   どちらの方向が yulang の意図と合う？

3. **`escape_owner_function` owner check**：write22 では `install_eval_id`
   で primary check したあと、`escape_owner_function == current_function`
   は **owner_match 判定** として残している。これで OK？
   それとも eval_id ベースに統一すべき？

---

## コミット予定

write22 完了。
- spec 通り eval-frame identity (`CpsEvalId`) を導入
- 167 tests pass、local choice 系 pass
- 残バグ (cps:0 → cps:2) は Case 3 = intermediate handler destruction
- write23 では案 A (write17 再有効化) + 案 B (handler preservation) の
  組み合わせで進める方向
