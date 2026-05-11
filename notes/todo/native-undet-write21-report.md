---
title: native-undet-write21 実装レポート
date: 2026-05-11
---

# native-undet-write21 実装レポート

## 結論（先に）

- 既存 167 tests **pass**（regression なし）
- `debugs_local_choice_caller_rest_eval` / `debugs_local_choice_callback_rest_eval`
  も pass
- `debugs_std_undet_once_skip_eval_layers` が **cps:0 → cps:1** に前進
- VM:2 までは届かないが、これは CPS eval の問題ではなく **CPS lowering の方の
  bug**（後述）

`cps_eval.rs::handle_scope_return` で 1 行（実質）の修正：inherited フラグの
判定に `escape_owner_function == current_function` を加味することで、
closure 越しに inherited 化されてしまった H_sub が同じ function 内の install
scope として resolve できるようになった。

---

## 進捗まとめ

- write18 後: cps:0 / vm:2
- write21 後: **cps:1** / vm:2

依然差はあるが、確実に「**sub::return(1) が H_sub に正しくマッチして each を抜け、
outer once まで戻る**」経路は動くようになった。第1イテレーションの最初の
sub::return が正しく届く、ここまでは前進。

残差は work body の `guard: n > 1` が CPS で見えない問題（CPS lowering 側）。

---

## step 0-2: baseline と分類（write19/20 の延長）

write20-report と同じく、trace と CPS shape audit で：

- case A 否定：`lower_apply` / `direct_apply` で thunk-typed param は MakeThunk
  wrap されている。CPS shape の `once__mono4 cont 6` でも `MakeThunk(cont 8) +
  EffectfulApply(loop, Thunk, ...)` の形を確認。
- case B 否定：trace `EffectfulApply once cont 9 arg=List(len=1, [Resumption])`
  で queue は正しく構築されている。
- case C 否定：`uncons` の入力時点で既に queue が空。primitive 自体は問題ない。

→ **case D' (intermediate handler eval destruction)** を再確定。

---

## step 3: 根本原因の特定

`cps_eval.rs` を細かく audit して、`active_handlers` の `inherited` フラグが
**closure 越しで意図せず true 化されている流れ**を特定。

### `inherited` フラグの本来の意図（doc comment より）

```rust
/// True iff this frame is part of a resumption snapshot (i.e. the
/// `resumption.handlers` of a `Resume` / `ResumeWithHandler`). Inherited
/// frames can still match `Perform`-time handler search, but must NOT
/// resolve a `ScopeReturn` in the resumed eval — the original install
/// site lives in a parent eval frame, so the abort has to keep
/// propagating up to that parent.
```

つまり「resumption snapshot 由来の frame」だけ inherited であるべき。

### 実際の流れ（trace から再構成）

H_sub は `each__mono1 cont 0` で install され（inherited=false）、その後
fold_impl → each cont 5 closure call の連鎖を通る：

1. `each__mono1 cont 0` で `H_sub` push → active_handlers=[(0,T,1),(1,F,0)]
2. EffectfulCall fold_impl → `eval_continuations` → **into_inherited で全部 true 化**
   → fold_impl eval の active_handlers=[(0,T,1),(1,T,0)]
3. fold_impl が EffectfulApply(each cont 3 closure, Unit) → 同様に into_inherited
4. closure(cont 5)(Int 1) → each cont 5 eval、active_handlers=[(0,T,1),(1,T,0)]
5. `Perform branch` → k1 capture、resumption.handlers=[(0,T,1),(1,T,0)] **両方 inherited**
6. once branch arm → recursive loop → InstallHandler prompt=2 (inherited=false)
7. ForceThunk(k_true_thunk) → `eval_continuations` → **into_inherited で (2,F,1) も
   (2,T,1) に**
8. Resume(k1, true) → `resumed_handlers = capture + extra` → `eval_continuations`
   → into_inherited → all inherited=true
9. each cont 10 → cont 7 → cont 8 で sub::return Perform、
   active_handlers=[(0,T,1),(1,T,0),(2,T,1)] **全部 inherited**
10. `handle_scope_return` は `prompt=1 && !inherited` を探す → **見つからず Propagate**
11. propagate が 6 段の eval frame を unwind し、inner once(prompt=2) も一緒に
    破壊される（write20 で観察した case D'）

問題の本質：H_sub の install eval は `each__mono1 cont 0`、k1 capture eval は
`each__mono1 cont 5`。両者は **同じ function** だが **別 eval frame**。`inherited`
フラグは eval frame ベースなので、closure 経由で「同じ function 内」の handler を
見ても inherited 扱いになってしまう。

algebraic effect の意味論的には「同じ function 内の install scope は inherited で
ない」ように扱うべき。

---

## step 4: 修正

`cps_eval.rs::handle_scope_return` の判定式を：

```rust
.rposition(|frame| frame.prompt == prompt && !frame.inherited)
```

から：

```rust
.rposition(|frame| {
    frame.prompt == prompt
        && (!frame.inherited
            || frame.escape_owner_function == current_function)
})
```

に変更。コメントで write21 の経緯と意図を残した。

### 副作用検討

- prompt は dynamic（`fresh_prompt()` で毎回 fresh）なので、別の install と誤
  マッチすることはない
- `frame_owner_match` の既存 check（L297-298）は維持される。target が
  EXIT_RWH_TARGET でない場合は `escape_owner_function == current_function` も
  チェックされるので、間違った eval で resolve しない
- `inherited=true && owner_match=true` は「同じ function 内の install scope 由来
  だが eval frame が違う」状態を表す。これは algebraic effect の install scope
  semantics で正しくマッチさせるべきケース

### 禁止事項チェック

- handle_scope_return の owner check を緩めない → ✓ owner check は保持し、
  inherited 判定だけ拡張
- write17 pre-force を戻さない → ✓
- ApplyClosure 全体を effectful 化しない → ✓
- ForceThunk 全体を effectful 化しない → ✓
- return_frame_threshold を消さない → ✓
- initial_frame_count 設計を崩さない → ✓
- Cranelift backend を触らない → ✓
- expected value を 0 に変えない → ✓
- failing test を ignore して終わらせない → ✓

---

## step 5: テスト結果

```text
cargo test -p yulang-native                              => 167 pass / 17 ignored
cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored
  => pass
cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored
  => pass
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored
  => FAIL: ValueMismatch { vm: Int("2"), cps: Int("1") }
```

`cps:0 → cps:1` の前進、他 regression なし。

### trace 上で確認できた前進ポイント

```text
L46 Perform branch each cont 5 active_handlers=[(0,T,1),(1,T,0)]
L47 EffectfulApply once cont 6 arg=Thunk(once cont 8)  ← MakeThunk 正しく動作
L55 InstallHandler once cont 3 prompt=2 threshold=1    ← recursive once install
L56 Perform sub::return each cont 8 active_handlers=[(0,T,1),(1,T,0),(2,T,1)]
L58 ScopeReturnDispatch each prompt=1 matched=yes owner_match=yes JumpOrExit
    ← ★ write21 fix がここで効いている。inherited=T でも owner_match で resolve
L59 Return each cont 2 value=Plain(Int 1)
L60 ContinueReturnFrames pop owner=fold_impl cont 10
```

write20 では L58 が `matched=no Propagate` の連鎖 → 6 段全部破壊
だったが、write21 fix で1段目で正しく match し JumpOrExit。

---

## 残るバグ（write22 引き継ぎ）：CPS lowering で `guard: n > 1` が missing

cps:1 が返るのは「最初の sub::return(1) が outer once まで届いている」を意味する。
期待値 2 にするには、x=1 で `guard: n > 1` が false → reject、x=2 で sub::return
する流れが必要。

CPS shape dump（test source を一時書き換え）で確認した結果、`each__mono1` の
closure body `cont 5` は：

```text
cont 5: FreshGuard, Literal Unit, Perform branch(Unit) → cont 10
cont 10: Continue cont 7 with arg 12
cont 7: Branch cond=10 then=cont 8 else=cont 9
cont 8: Perform sub::return(7=arg=elem) → cont 11 → cont 6 Return
cont 9: Unit → cont 6 Return
cont 6: Return
```

**`guard: n > 1` の lowering が一切含まれていない**。`branch → if true:
sub::return n` だけで、`n > 1` の cond チェックも `reject` perform も無い。

source は：
```yulang
my work(): int = {
    my n = each [1, 2, 3]
    guard: n > 1
    n
}
```

期待される lowering：each closure body 内で
- `n` を element に bind
- `guard: n > 1` → `if !(n > 1) perform reject`
- `n` を sub::return

ところが現在の lowering では guard 部分が完全に消えている。

VM は同じ runtime IR を入力に正しく 2 を返すので、runtime IR は guard を含む
はず。**CPS lowering で消えている**可能性が高い。

### 確認ポイント（write22 で見るべき）

- `cps_lower.rs` の closure body lowering：`each__mono1` の callback (cont 3)
  が work body の `guard; n` を含む形に lower されるか
- もしかしたら work body の lowering が `each__mono1` の specialization で
  inline されておらず、each generic body だけが使われている
- runtime IR の段階で work body と each callback がどう構築されているか
  比較する必要

---

## 触ったファイル

- `crates/yulang-native/src/cps_eval.rs`:
  - `handle_scope_return` の inherited 判定に `escape_owner_function ==
    current_function` exception を追加（コメントで write21 の経緯を残す）

なお、`source.rs::debugs_std_undet_once_cps_shape` の source を作業中に一時
書き換えたが、commit 前に元に戻した。

---

## りなに渡す質問

1. **CPS lowering で `guard: n > 1` が消えている問題**：each_mono1 の closure
   body lowering を確認したい。runtime IR vs CPS IR の段階で何が起きているか、
   `cps_lower.rs` のどこを見ればよい？

2. **write21 fix の妥当性**：handle_scope_return で「inherited=true でも
   owner_match なら resolve」する変更。意味論的に：

   - H_sub の install scope は `each__mono1` という function。
   - 同 function 内の別 continuation（cont 5 closure body）から見ても install
     scope は同じ。
   - inherited フラグは eval-frame ベースだが、install scope は function ベース
     で見るのが正しい。

   この理解は yulang の意図と一致する？

3. **`into_inherited` の挙動**：現状 `eval_continuations` の wrapper が常に
   `into_inherited` を呼ぶ。これは「caller 由来の handlers を子 eval から見て
   inherited 扱い」する意図だが、**closure body が install scope と同じ function**
   のケースを区別していない。これを cleanup する方向で良い？

---

## コミット予定

write21 完了。
- 1 行（実質）修正で cps:0 → cps:1 の前進
- 167 tests pass、regression なし
- 残バグ（cps:1 → cps:2）は CPS lowering 側（guard 欠落）

次は write22 で CPS lowering の方を見る。
