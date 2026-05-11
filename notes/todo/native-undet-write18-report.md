# native-undet-write18 実装レポート

## 実装したこと

write18 §6 の指示通り、trace を frame chain 中心に強化して std::undet.once の event
列を追跡。その結果、`cps:3` を発生させる根本原因を特定し、修正できた。

### 1. trace 強化

`cps_eval.rs` に追加:
- `Return`: value を `Plain(VmValue)` / `Thunk` / `Closure` / `Resumption` /
  `Discriminant(...)` で出力
- `ContinueReturnFrames`: pop した frame の owner_function / continuation /
  rest.len / owner_initial を出力
- `ScopeReturnDispatch`: handle_scope_return が `Value` / `JumpOrExit` / `Propagate`
  どれを返したか、prompt / target / owner / threshold を出力

### 2. cps:3 の根本原因

trace で **view_raw が 2 回しか呼ばれない** ことが判明。
`[1,2,3]` = `node([1], [2,3])` の tree iteration が `[2,3]` の右側スパインだけ
辿って leaf(3) で終わっていた。

`fold_impl` cont 6 (node branch):

```text
EffectfulCall fold_impl(LEFT)   → cont 12
cont 12: <ここに force 無し>     ← write15 で消えた
         EffectfulCall fold_impl(RIGHT, z=Thunk_left, f)
cont 14: Continue cont 2 [result]
```

LEFT の `EffectfulCall` は `Thunk` を返すが、その Thunk を **force せずに** RIGHT
の z 引数として渡していた。RIGHT 内では callback が z を使わない設計のため、LEFT
の iteration は事実上 dead code として捨てられて RIGHT 側だけ実行されていた。

元の (write15 前) sync DirectCall stmt では `force_if_non_thunk_demand` が
ForceThunk を挟んでいて、LEFT の Thunk を強制 force していた。write15 で
EffectfulCall に切り替えた際にこの force が失われた。

### 3. 修正

`cps_lower.rs::lower_expr` の direct_apply の higher_order_helper EffectfulCall
パスで、最後に `force_if_non_thunk_demand` を呼ぶようにした:

```rust
if self.higher_order_helper && info_returns_thunk {
    ...
    self.terminate(CpsTerminator::EffectfulCall { ... });
    self.finish_current();
    self.current = ContinuationBuilder::new(post_cont, vec![result]);
    return Ok(self.force_if_non_thunk_demand(result, &expr.ty));  // ← write18
}
```

これで `cont 12` の post-LEFT-call cont の先頭に `ForceThunk(left_thunk) → forced`
が入り、後続の RIGHT EffectfulCall は `z=forced` を渡せるようになる。

---

## テスト状況

- **既存 167 通常テスト** PASS（regression なし）
- **`debugs_local_choice_caller_rest_eval`** (write12) PASS
- **`debugs_local_choice_callback_rest_eval`** (write13 Test A) PASS
- **`debugs_std_undet_once_skip_eval_layers`**:
  - **`cps:3` → `cps:0`** に変化
  - 第 1 イテレーションで `branch → sub::return 1 → each returns 1 → guard reject` が
    正しく動くようになった（trace で `Return: each cont 2 value=Plain(Int("1"))`
    確認）
  - その後の once の reject arm で uncons が `nil` を返している（= queue が空）
  - 次のバグ: queue replay の semantics

---

## 残るバグの観察（write19 への引き継ぎ）

trace の終盤:
```
Perform: guard cont 4 reject
ScopeReturnDispatch: guard prompt=0 ... matched=no Propagate
ScopeReturnDispatch: once prompt=0 ... matched=yes JumpOrExit threshold=1
Return: once cont 5 value=Discriminant(6)   ← Variant (nil?)
ContinueReturnFrames: pop once cont 21
Return: once cont 21 value=Discriminant(6)
Return: root cont 2 value=Plain(Int("0"))
```

once の reject arm (`cont 5`) が `Discriminant(6)` (Variant) を返している。これが
`opt::nil` なら最終的に case の `nil -> 0` 分岐で 0 になる。

期待される queue 状態:
- once の branch arm が k1 を queue にいれて `loop(k1_true_thunk, [k1])` で再帰
- 再帰 loop で reject が来るとき、queue=[k1] のはず

なのに uncons が nil を返している = 再帰 loop の `queue` 環境が壊れている、
または逆に reject が **再帰前** の outer loop で発生して queue=[] のまま。

候補:
1. `loop` の再帰呼び出しが起きていない（callback の sub::return が outer scope に
   直接戻り、recursive loop は呼ばれない）
2. recursive loop の queue param が空になっている
3. reject の Perform 位置が想定と違う

trace に `ApplyClosure` / `EffectfulApply` の closure type と arg 内容を細かく見れば
特定できる。

---

## 触ったファイル

- `crates/yulang-native/src/cps_eval.rs`:
  - `Return` trace を value 表示込みに拡張
  - `ContinueReturnFrames` trace 追加
  - `ScopeReturnDispatch` trace 追加（matched/owner_match/threshold 含む）
- `crates/yulang-native/src/cps_lower.rs`:
  - `direct_apply` higher_order_helper EffectfulCall パスで
    `force_if_non_thunk_demand` を post-cont に追加

---

## りなに渡す質問

1. **once の queue replay**:
   write18 fix で第 1 iteration の branch/sub::return/guard reject までは
   正しく動くようになった。次は once の reject arm で uncons が nil を返す
   のがバグ。これは:
   - case A: recursive loop が呼ばれていない（branch arm 内 `loop(k_true, queue+[k])`
     の apply 経路が壊れている）
   - case B: recursive loop は呼ばれるが queue が空になっている
   - case C: そもそも reject が想定と違う位置で発生

   trace で次に見るべき場所は？

2. **`Resume` / `ResumeWithHandler` / `ApplyClosure(Resumption)` / `EffectfulApply(Resumption)` の
   frame order**:
   write16 で EffectfulApply(Resumption) は `parent + [F_post] + res_frames` 順に修正。
   他の3経路は extras injection を adjusted_frames に入れるだけで F_post を持たない
   (sync semantic)。これで write18 fix 後の queue replay 経路が正しく動くべきか、
   それとも特殊な extension が要る？

---

## コミット予定

write18 完了。
- cps:3 → cps:0 への進歩（規定の vm:2 にはまだ届かない）
- trace 強化
- fold_impl の LEFT 再帰結果 force 修正
