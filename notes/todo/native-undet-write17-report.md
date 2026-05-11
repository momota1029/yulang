# native-undet-write17 実装レポート

## 実装したこと（write17 指示ベース）

write17 の指示通り、`Return(Thunk)` の auto-consume 前に top frame の即 ForceThunk を
pre-force する経路を試みた。実装はしたが、別の制約と衝突して escape を起こしたため
**現時点では path を無効化**し、helper / trace は将来の follow-up のためにコメント
付きで残してある。

### 残した助走

- `cps_eval.rs::return_frame_immediately_forces_param`: `frame.continuation` が
  受け取った param を最初の stmt で即 `ForceThunk` するかを判定する helper。
- `cps_eval.rs::force_returned_thunk_before_frame_consumption`: top frame の
  active_handlers / guard_stack を使い `resume_continuation` で thunk body を
  pre-force する helper。
- Return terminator に `value_is_thunk` を含む trace を追加。
- 既存の `Perform` / `EffectfulApply` trace と組み合わせて、escape の経路を観察できる。

### 試した順序

1. **第 1 試行**: `eval_continuations` + `top_frame.active_handlers`
   → `EscapedScopeReturn { prompt: 1, target: cont 2 }`（root へ escape）
2. **第 2 試行**: `eval_continuations` + `current eval's active_handlers`
   → 同じ escape
3. **第 3 試行**: `resume_continuation` + `top_frame.active_handlers`
   → 同じ escape

すべて escape を起こす。

---

## なぜ escape するか — 構造的な制約の確認

trace と CPS dump で挙動を追うと、以下の構造が見える。

### `F_each_post.active_handlers` の中身

`each` の `EffectfulCall fold_impl` で push される `F_each_post.active_handlers` は、
push 時点の each の状態:

```
[ H_once (inherited), H_sub (non-inherited; just installed) ]
```

### `H_sub.escape_owner_function`

`InstallHandler H_sub` は each の cont 0 で行われるので:

```
H_sub.escape_owner_function = "std::undet::undet::each__mono1"
```

### pre-force eval の current_function

私の helper では `thunk.owner_function` を取って `eval_continuations` / 
`resume_continuation` を呼ぶ。fold_impl から返ってきた Thunk なら:

```
current_function = "std::list::fold_impl__mono6"
```

### dispatch_scope_return の owner check

`handle_scope_return` は ScopeReturn を解決するときに:

```rust
let frame_owner_match = target == EXIT_RWH_TARGET
    || frame.escape_owner_function == current_function;
```

を要求する。pre-force eval は current_function = fold_impl のため、
H_sub の escape_owner_function = each__mono1 と**一致しない**。

→ `Propagate` になり、ScopeReturn は eval を抜けて呼び出し元へ。

### 既存のフロー（pre-force なし）が動いていた理由

write17 を入れる前の flow:

1. `fold_impl` Return(Thunk) → F_each_post pop。
2. `continue_return_frames` が **F_each_post.continuation = each cont 12** を
   `resume_continuation` で run。
3. このとき current_function = "each__mono1"。F_each_post.active_handlers が
   そのまま渡される（non-inherited 状態を保つ）ので、H_sub は non-inh のまま。
4. cont 12 の sync `ForceThunk` が thunk body を eval_continuations で実行。
5. body 内で sub::return Perform → arm 完了 → ScopeReturn(H_sub) が伝播。
6. **cont 12 の eval は current_function = each + H_sub non-inh → match!**
   `JumpOrExit` で cont 2 of each に jump して each を Return。

つまり、**`continue_return_frames` を経由して owner_function 文脈に乗り換える
ステップが必要**。pre-force で skip するとこの文脈が得られない。

---

## なぜ既存フローでも `cps:3` なのか — 別の問題

上のフローは「H_sub を cont 12 の eval で正しく resolve」するが、
最終的な値が **3** になっているのは、`once`/`loop` の再帰で resumption replay の
連鎖が想定通りに終わらないため、と推測している。

trace では:
- 第1イテレーション: branch=true → sub::return 1
- guard 1>1 fail → reject
- once の reject arm が k1 false を発行
- … 何度か再帰 …
- 最終的に each が `Plain(Int("3"))` を返す

途中で本来 2 で止まるべきところを通り過ぎているように見える。

ここを追うには別途、resumption replay の chain と loop の queue 状態を
event-by-event で追跡する必要がある。今回の write17 セッションでは
そこまで進めなかった。

---

## テスト状況

- **既存 167 通常テスト** PASS（regression なし）
- **`debugs_local_choice_caller_rest_eval`** (write12) PASS
- **`debugs_local_choice_callback_rest_eval`** (write13 Test A) PASS
- **`debugs_std_undet_once_skip_eval_layers`**: 依然として `cps:3 vs vm:2`

---

## 触ったファイル

- `crates/yulang-native/src/cps_eval.rs`:
  - Return trace を `value_is_thunk` を含む形に拡張
  - `return_frame_immediately_forces_param` helper を追加
  - `force_returned_thunk_before_frame_consumption` helper を追加
  - Return terminator に pre-force 経路を入れて試したあと、disabled へ戻した
    （`let _ = ...;` で dead-code 警告だけ抑える）

---

## りなに渡す質問

1. **pre-force が working するには何が必要か**:
   write17 で「Return(Thunk) の auto consume 前に thunk body を評価する」と
   書いたが、実装してみると body の current_function が `thunk.owner_function`
   (= fold_impl) になり、H_sub の escape_owner check (= each) と一致しなくなる。
   - 案 A: pre-force eval の dispatch_scope_return 側で owner check を緩める
     (= top_frame.owner_function == current_function でも match を許す)。
   - 案 B: ScopeReturn を pre-force helper 内で受け取って top_frame の文脈で
     再 dispatch する。
   - 案 C: そもそも pre-force ではなく、continue_return_frames を経由する必要があり、
     write17 の方針自体を見直す。
   
   このうちどれが妥当？

2. **cps:3 の根本原因**:
   pre-force なしの既存フローでも cps:3 になる。trace では sub::return 1 が
   起きたあとに once の reject backtracking → 何度か iteration → 最終的に
   each が 3 を返す。期待は 2。
   
   - `loop(k true, queue+[k])` の curried apply の途中で何かの replay state が
     ずれている？
   - resumption.return_frames に何か余分なフレームが入っている？
   - return_frame_threshold 経由の truncate が起きないケースがある？

   どこを次に追えばいい？

3. **lower 側でやるべきこと**:
   write17 §9 §C で `fold_impl` の `MakeThunk + Return` 自体を抑制する案が出ていた。
   これはやはり後手にすべき？それとも、pre-force の方向に詰めるより lower 側に
   手を入れたほうが筋がいい？

---

## コミット予定

write17 partial。
- 既存 167 通常テスト PASS（regression なし）
- write12/13 local minimal tests 継続 PASS
- pre-force helper / trace を追加するも、ScopeReturn の escape_owner_function 制約と
  衝突するため当該パスは disabled
- `debugs_std_undet_once_skip_eval_layers` は依然として cps:3 vs vm:2
