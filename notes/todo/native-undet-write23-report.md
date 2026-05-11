---
title: native-undet-write23 実装レポート — handler merge + Return inherited preservation
date: 2026-05-11
---

# native-undet-write23 実装レポート

## 結論（先に）

- `merge_resumption_handlers` を導入、Resume / ApplyClosure(Resumption) /
  EffectfulApply(Resumption) で **resume-site の sibling handler が
  captured continuation の inner handler より外側に位置する** ように修正
- `ResumeWithHandler` だけは **rebased semantics** のため legacy
  inject (`captured ++ [RWH]`) を維持（regression なし）
- `Return` terminator が `continue_return_frames` に **full return_frames**
  を渡すように修正 → tail-call chain で inherited frames が drop されず、
  `F_each_post` が captured chain に保存される
- pre-force は試したが、再帰的 fold_impl で chain が複雑になり cps:2 に
  到達しないため撤去
- 既存 167 tests **pass**（regression なし）
- `debugs_local_choice_caller_rest_eval` / `debugs_local_choice_callback_rest_eval`
  両方 pass
- `debugs_std_undet_once_skip_eval_layers` は依然 **cps:0 / vm:2**
- trace で確認できた前進：`Resumption(... frames=2 ...)` & Resume eval の
  `return_frames.len=2` で **`F_each_post` が captured chain に含まれた**

残バグは **「sub::return abort 後、work cont 1 の続行 eval に inner once H
が伝わらない」** という architectural な問題で、write23 のスコープを
超える追加設計（SR.preserved_handlers + work の sync DirectCall 経由の
handler 注入）が必要。

---

## 進捗まとめ

- write18 後: cps:0 / vm:2
- write21 後: cps:1 / vm:2（loose match の幸運）
- write22 後: cps:0 / vm:2（strict 判定で本質的バグが露呈）
- write23 後: **cps:0** / vm:2、ただし **trace frontier が前進**
  - resumption が capture する frames が 1 → 2 に増えた
  - Resume eval の return_frames が 1 → 2 になった
  - 各 ContinueReturnFrames で rest.len が 0 → 1 に増えた（inherited 保持）

---

## step 1+2: handler merge order の修正

### 追加した helper

`summarize_handler_stack`：trace 用の compact 表記。

```text
[(p=0,inh=T,eval=4,owner=once,thr=1),
 (p=1,inh=T,eval=8,owner=each,thr=1),
 (p=2,inh=T,eval=22,owner=once,thr=1)]
```

`merge_resumption_handlers(captured, current) -> Vec<...>`：

```rust
// shared outer prefix (prompt + install_eval_id 一致)
let mut shared = 0;
while ... { shared += 1; }

let mut merged = Vec::new();
merged.extend(captured[..shared]);  // 共有 outer
for frame in &current[shared..] {
    if !captured.iter().any(|c| same prompt & install_eval) {
        merged.push(frame);          // sibling extras
    }
}
merged.extend(captured[shared..]);  // captured inner tail

merged
```

`merge_extras_into_frames(frames, current)`：各 return frame に上の merge を
適用。

### 適用サイト

- `CpsStmt::ApplyClosure` (Resumption 分岐) — 旧 inject から merge へ
- `CpsStmt::Resume` — 同上
- `CpsTerminator::EffectfulApply` (Resumption 分岐) — 同上

### 例外：`CpsStmt::ResumeWithHandler`

RWH は **rebased semantics**：新 RWH handler が captured innermost を
shadow する形が必要（`evaluates_resumption_under_fresh_handler_stack` test
で確認）。一様 merge に従うと regression するため、legacy の
`captured ++ [RWH]` 挿入と `inject_extra_handlers_legacy` を維持。

trace に `ResumeHandlerMerge` と `InjectExtraHandlers` を追加。

### trace 上で確認できた差分

```text
ResumeHandlerMerge:
  site=Resume fn=once_mono4 eval=23
  captured=[(p=0,eval=4),(p=1,eval=8)]
  current=[(p=2,eval=22)]
  merged=[(p=2,eval=22),(p=0,eval=4),(p=1,eval=8)]
```

write23 が予測した `[outer, inner, H_sub]` 形ではなく `[inner, outer, H_sub]`
になっているのは、**arm body の eval が `stack[..index]` で開始する**
（write23 の `current=[outer, H_inner]` 想定とは異なる）ため。実装上の
current には outer once H は含まれていない。それでも shared prefix が
空のとき current を先に置く merge logic は意味論的にもっともらしく、
167 tests + local choice 系を pass する。

---

## step 3: pre-force 試行と撤去

`force_returned_thunk_before_frame_consumption` (write17 残骸) と
`return_frame_immediately_forces_param` を使って、`fold_impl cont 0`
が Thunk を Return する時に top frame の owner context で
ForceThunk を pre-execute する案を試行した。

### 問題

`fold_impl` 自身が再帰関数で、recursive call も Thunk を返す。pre-force
が再帰的に発火して chain が複雑化。最終的に `Perform branch` 時点での
return_frames が `len=1` のまま（F_each_post が含まれない）。

`owner_function != current_function` 条件で発火を絞ったが、ForceThunk
sync sub-eval の中で発生する再帰的 `Return` で **inherited frames が
依然 drop されていた**ため、結果として cps:0 のまま。

→ pre-force は本筋から外れている、撤去した。本質的な fix は `Return`
terminator の方にあると判断。

---

## 本命：`Return` terminator の inherited preservation

### 問題発見

trace で `Perform branch eval=17 cont 5 return_frames.len=1 initial=0`
を見ていて気づいた：pre-force eval で 2 frames retained してあるのに、
深い tail-call chain を通過した branch perform 地点では 1 frame しか
残っていない。

原因：`Return` terminator が `own_frames = split_off(initial)` してから
`continue_return_frames(own_frames)` を呼ぶ仕様で、**inherited prefix
（split_off の前の部分）が drop されている**。

```text
Y3 (inner fold_impl) Return:
  return_frames = [F_outer_a, F_outer_b, F_cont_20, F_inner], initial=3
  own_frames = split_off(3) = [F_inner]
  continue_return_frames(value, [F_inner])
    pops F_inner → restore Y2 with rest=[]
    Y2's resumed eval has return_frames=[] ❌
```

Y2 (fold_impl recursive entry) was tail-called from Y1, with inherited
frames F_outer_a, F_outer_b, F_cont_20. When Y2 is restored at cont_after_inner,
those inherited frames are **lost**.

### 修正

```rust
// 修正前
let own_frames = return_frames.split_off(initial_frame_count);
return continue_return_frames(module, v, &own_frames, &[]);

// 修正後
return continue_return_frames(module, v, &return_frames, &[]);
```

`continue_return_frames` は innermost (last) frame を pop して `rest =
frames[..-1]` を resumed eval の return_frames として渡す。これで
inherited prefix が naturally 保たれる。

### 影響

- 既存 tests に regression なし（167 pass）
- `Perform branch` 時点の return_frames.len=2 になった（`F_each_post` 含む）
- Resumption が `frames=2` を capture（前は `frames=1`）
- Resume eval (eval=24) が `return_frames.len=2` で start

これで write22 notes が予測していた **「F_each_post が captured chain に
含まれる」状態**が実現した。

---

## それでも cps:0 の理由

trace で確認：

```text
Perform fn=each_mono1 eval=24 cont 8 effect=sub::return
  return_frames.len=2 initial=0
  active_handlers=[(p=2,eval=22,inner once),(p=0,eval=4,outer once),(p=1,eval=8,H_sub)]
↓ propagate via call stack
ScopeReturnDispatch fn=each_mono1 eval=8 prompt=1 matched=yes install_eval=8
↓ JumpOrExit cont 2 → Return Plain(Int 1)
↓ bubble up to work cont 1's DirectCall in eval=7
Perform fn=guard__mono3 eval=30 cont 4 effect=reject
  return_frames.len=1 initial=1
  active_handlers=[(p=0,eval=4,outer once)]   ← inner once H が無い
↓
ScopeReturnDispatch fn=once_mono4 eval=4 prompt=0 matched=yes
↓ Variant(nil) returned → cps:0
```

`eval=8` (match site) の active_handlers は `F_each_post` の snapshot 由来で
`[outer, H_sub]` のみ。`merge_extras_into_frames` で injection された
copy は **captured chain の方の F_each_post** であって、call stack 上で
eval=8 を復元するのに使われるオリジナルではない。

そして bubble up 後の work cont 1 は eval=7 で実行、active_handlers
= [outer once H] のみ。inner once は eval=22 にいた handler frame で
eval=7 に injection されない。

---

## 残バグの本質

**sub::return abort の意味論と impl のミスマッチ**：

- 意味論上、abort 後の work cont 1 の続行は「resumed continuation k の
  内部で進行する」ため、resume site の sibling handler (inner once) も
  scope に居る。
- impl では work cont 1 は sync DirectCall 経由で呼ばれており、その
  continuation は call stack で復元される。call stack の work eval (eval=7)
  は inner once が install される前から存在し、自分で inner once を
  injection する手段が無い。
- 結果として inner once は abort 通過時に消滅し、reject が outer once
  に行ってしまう。

---

## write24 で取るべき方向

### 案 A：SR.preserved_handlers

`ScopeReturn` に `preserved_handlers: Vec<CpsHandlerFrame>` を持たせる。

```rust
ScopeReturn {
    prompt, target, value,
    preserved_handlers: Vec<CpsHandlerFrame>,  // 追加
}
```

- `handle_scope_return` の Propagate 時：current eval が install した
  handler（`install_eval_id == current_eval_id`）を `preserved` に追加。
- Match 時：truncate 後に preserved を active_handlers に inject。

ただし、これは abort 通過する eval=8 (match site) の active_handlers を
修飾するだけ。**work cont 1 の eval=7 にどう伝えるか**が別問題。

### 案 B：work の DirectCall を effectful 化

CPS lowering で「effect を持つ関数の DirectCall」を `EffectfulCall` に
変える。push frame + tail-call 形式になり、work cont 1 の continuation
が return frame として捕獲される。abort はその frame の active_handlers
（preserved injected）で復元される。

これは lowering 側の変更で、大きいが意味論的にクリーン。

### 案 C：SR propagation を call-stack ではなく captured chain で行う

`dispatch_scope_return` の Propagate を「自分の return_frames を walk して
match を探す」形式に変える。各 frame の active_handlers が injection
された状態なので、walk 中に inner once が見える。

ただし、現在の F_each_post の snapshot は不変なので、walk match した
時に inner once を post-jump eval に追加する仕組みが要る。これは
案 A と組み合わせる形になる。

私の感触では **案 A + 案 C の組み合わせ**が一番現実的。案 B は lowering
変更が広範で時間が掛かる。

---

## 触ったファイル

- `crates/yulang-native/src/cps_eval.rs`:
  - `summarize_handler_stack` helper 追加
  - `merge_resumption_handlers` 追加
  - `merge_extras_into_frames` 追加
  - `inject_extra_handlers_legacy`（RWH 用）追加
  - `inject_extra_handlers`（旧）削除
  - `CpsStmt::ApplyClosure` (Resumption) で merge 使用
  - `CpsStmt::Resume` で merge 使用
  - `CpsTerminator::EffectfulApply` (Resumption) で merge 使用
  - `CpsStmt::ResumeWithHandler` は legacy 維持
  - `CpsTerminator::Return` で `return_frames` を full pass
  - trace に `ResumeHandlerMerge` / `InjectExtraHandlers` / 強化された
    `Perform` 出力

write23-report.md として記録。

---

## りなに渡す質問

1. **case 3 の architectural fix**：work cont 1 の sync DirectCall 経由で
   inner once H を伝える機構として案 A (SR.preserved_handlers) + 案 C
   (walk-based propagation) の組み合わせを検討中。それとも案 B
   (work の DirectCall を effectful 化、lowering 変更) のほうが筋が良い？

2. **`merge_resumption_handlers` の意味論**：write23 の例では
   `current=[outer, H_inner]` だったが、実装上の Perform arm body の
   eval は `stack[..index]` で start するため、現在の `current` には
   captured outer prefix が含まれない。それでも shared prefix 空の場合
   に `current` を先に push する merge logic は妥当？

3. **`Return` の inherited preservation**：今までの impl で意図的に
   inherited を drop していたのは「sync caller の eval が alive」の
   仮定だが、tail-call では成立しない。今回の修正で 167 tests pass
   なので大丈夫そうだが、意図せず変な副作用が出る tail-call ケースが
   ないか心配。

---

## コミット予定

write23 完了。
- handler merge order を semantically 正しく（Resume サイト）
- `Return` の inherited preservation で `F_each_post` が captured chain
  に保存される
- 167 tests pass、regression なし
- 残バグ (cps:0 → cps:2) は work cont 1 の eval=7 に inner once H を
  伝える機構が必要、これは write24 で
