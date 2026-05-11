---
title: native-undet-write24 実装レポート — anchor-based handler merge
date: 2026-05-11
---

# native-undet-write24 実装レポート

## 結論（先に）

- `CpsHandlerAnchor` を導入、`CpsResumption.handled_anchor` に Perform で
  捕まえた handler frame を保存
- `merge_resumption_handlers` を **anchor-based** に書き換え。anchor の
  直後に resume-site siblings を配置することで、stack 順が
  `[outer, inner, H_sub]` になる（write24 の期待通り）
- `merge_extras_into_frames` も anchor を受け取って同じ位置決めで injection
- `PerformHandlerSearch` trace を追加して handler 選択を可視化
- `ResumeWithHandler` は引き続き legacy inject（rebased semantics）
- 既存 167 tests **pass**、`debugs_local_choice_*` 系も pass
- `debugs_std_undet_once_skip_eval_layers` は依然 **cps:0 / vm:2**

Step 4 (targeted EffectfulCall lowering) を試みたが、`info_returns_thunk &&
demand_is_non_thunk` 条件では他テストに 2 件 regression が出たため revert。
write25 でより targeted な発火条件（caller の effect tracking 等）で
再挑戦予定。

---

## 進捗まとめ

- write22 後: cps:0 / vm:2
- write23 後: cps:0 / vm:2 (but resumption frames=2, F_each_post captured)
- write24 後: **cps:0** / vm:2 (anchor merge で eval=24 active_handlers の
  順序が semantically 正しく)

trace frontier 上の前進：

```text
write23 trace (no anchor):
  ResumeHandlerMerge merged=[inner, outer, H_sub]  ← inner が outermost (危険)

write24 trace (anchor=outer):
  ResumeHandlerMerge anchor=Some((0,4))
                     merged=[outer, inner, H_sub]  ← write24 期待通り
```

`PerformHandlerSearch trace` も追加：

```text
PerformHandlerSearch fn=each eval=24 effect=sub::return
  stack=[outer, inner, H_sub]
  matched_index=Some(2) matched_prompt=1 matched_install_eval=8
```

H_sub が正しく見つかっている。

---

## Step 1: anchor-based merge

### 追加した構造

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CpsHandlerAnchor {
    prompt: CpsPromptId,
    install_eval_id: CpsEvalId,
}

struct CpsResumption {
    // ...既存 field...
    handled_anchor: Option<CpsHandlerAnchor>,
}
```

### Perform で anchor を保存

`CpsTerminator::Perform` で `handler_arm_for_stack` から返ってきた `frame`
の prompt/install_eval_id を anchor として保存。`frame_in_active` が false
（synthetic fallback）の場合は `None`。

```rust
let handled_anchor = if frame_in_active {
    Some(CpsHandlerAnchor {
        prompt: frame.prompt,
        install_eval_id: frame.install_eval_id,
    })
} else {
    None
};
```

### merge_resumption_handlers の動作

```rust
fn merge_resumption_handlers(
    captured: &[CpsHandlerFrame],
    current: &[CpsHandlerFrame],
    anchor: Option<CpsHandlerAnchor>,
) -> Vec<CpsHandlerFrame> {
    if let Some(anchor) = anchor {
        if let Some(anchor_index) = captured.iter().position(|f| is_anchor(f, anchor)) {
            let mut merged = Vec::new();
            // captured prefix through anchor (inclusive)
            merged.extend(captured[..=anchor_index].iter().cloned());
            // resume-site siblings (current handlers not in prefix/tail)
            for frame in current { ... merged.push(frame.clone()); }
            // captured continuation inner tail
            merged.extend(captured[anchor_index + 1..].iter().cloned());
            return merged;
        }
    }
    // fallback: shared-prefix merge
    ...
}
```

例：
```text
captured=[outer, H_sub], anchor=outer
captured[..=0] = [outer]
current[0..] = [inner]  (not in prefix, not in tail)
captured[1..] = [H_sub]
merged = [outer, inner, H_sub]  ✓
```

### 適用サイト

- `CpsStmt::Resume`
- `CpsStmt::ApplyClosure` (Resumption 分岐)
- `CpsTerminator::EffectfulApply` (Resumption 分岐)

各サイトで `resumption.handled_anchor` を渡す。

`ResumeWithHandler` は write23 と同じく legacy inject 維持。

### `summarize_handler_stack` の field 拡張

trace で anchor 位置を確認しやすいよう、`escape_owner_function` も表示。

### `PerformHandlerSearch` trace

handler search の結果を可視化する trace を追加。effect, stack, matched
handler の install_eval_id / owner / in_active を出力。

---

## Step 4: targeted EffectfulCall lowering（試行 → revert）

### 試したこと

`cps_lower.rs` の `direct_apply` 経路で、`higher_order_helper` gate を
外して `info_returns_thunk && demand_is_non_thunk` でも EffectfulCall を
使うように変更。

### 結果

`debugs_std_undet_once_skip_eval_layers` の trace では：
- `Perform branch ... return_frames.len=3` (was 2)
- `Resumption(... frames=3 ...)` (was 2)
- F_each_post.threshold=2 (was 1)
- H_sub.threshold=2 (was 1)

つまり F_work_post が captured chain に入った。

しかし：
- regression が 2 件: `compares_prelude_source_once_finite_each_list_recursive_through_cps_repr_cranelift`,
  `evals_mutable_ref_edit_through_cps_repr_cranelift`
- once_skip_eval_layers は依然 cps:0

→ Step 4 を **revert**。

### なぜ Step 4 単体では足りないか

trace 観察：

```text
Perform sub::return eval=24 active_handlers=[outer, inner, H_sub] return_frames.len=3
↓ Propagate via call stack
ScopeReturnDispatch eval=8 prompt=1 matched=yes install_eval=8 JumpOrExit
```

match は eval=8' (cont 12 復元) で起き、その local active_handlers は
F_each_post.active_handlers の **snapshot** 由来で `[outer, H_sub]`。inner
once は含まれない。

eval=24's local return_frames には merge_extras_into_frames で modified された
F_work_post (inner once injected) があるが、**SR の call-stack propagation
は eval=24's local を経由しない** ため、modified frame は使われない。

eval=8' で JumpOrExit → cont 2 Return → continue_return_frames pops
F_work_post (call-stack chain の original, NOT modified) → work_eval at
cont_after_call_each → active_handlers=[outer]。

つまり inner once H が abort を越えて work cont 1 に届かない。

### Step 4 が破壊した tests

なぜ regression が出たかは未検証だが、おそらく：

- `compares_prelude_source_once_finite_each_list_recursive_through_cps_repr_cranelift`:
  recursive list の各 element での `each` 呼び出しが EffectfulCall に
  変わったことで、frame の積み方が想定と変わり、cps_repr 評価との一致が
  崩れた可能性。
- `evals_mutable_ref_edit_through_cps_repr_cranelift`: 同様に sync を
  仮定していた箇所で frame の有無が変わった可能性。

→ Step 4 は targeted condition が必要。

---

## なぜ Step 1 だけでは cps:2 に届かないか

write24 の予測通り、anchor merge は **eval=24 内の handler stack** を
意味論的に正しくしたが、SR の resolution が `call-stack` 経由で eval=8'
に届き、そこで使われる active_handlers は F_each_post の snapshot
（merge 前のオリジナル）。

つまり cps:2 にするには：

```text
1. anchor merge ✓ (write24)
2. captured chain に work cont 1 の post-call cont を入れる (Step 4)
3. SR resolution で modified captured frame を使う (Step 5: walk-based
   propagation, or preserved_handlers)
```

の 3 つが揃う必要。

write24 の note は Step 4 を本線にしていたが、私の試行では Step 4 単体
（targeted lowering）でも (2) は満たすが (3) が無いと cps:2 にならない。

---

## write25 で取るべき方向

### 案 A: Step 4 を targeted condition で実装し直す

- caller が「effect を持つ continuation を call の後に持つ」場合のみ
  EffectfulCall に変える
- 例えば caller の関数本体に `Perform` / handler install / 別の
  EffectfulCall が含まれる場合
- これでも (3) が必要

### 案 B: SR の resolution を walk-based に変更（Step 5 案 A+C）

`handle_scope_return` の Propagate 時に、現在 eval の return_frames を
walk して match を探す。各 frame の active_handlers が modified された
copy（merge inject 済み）なので、walk で match した時にその copy を
使う。

ただし「match した frame を restore して H_sub.escape を呼ぶ」のは
escape 関数の identity が必要で、難しい。

### 案 C: 上記 A+B の組み合わせ

- Step 4 で work's call を EffectfulCall に。
- Step 5 で SR propagation を eval=24's frames から walk。
- eval=24's F_work_post_modified に到達したら、F_work_post.active_handlers
  に inner once 入った状態で restore。

これが理論的には write24 期待の挙動。複雑だが本筋。

私の感触では **案 C が write25 の本線**。

---

## 触ったファイル

- `crates/yulang-native/src/cps_eval.rs`:
  - `CpsHandlerAnchor` 構造追加
  - `CpsResumption.handled_anchor` field 追加
  - `merge_resumption_handlers` を anchor-based に書き換え（fallback として
    shared-prefix merge も残す）
  - `merge_extras_into_frames` に anchor 引数追加
  - `same_handler_frame` helper 追加
  - `summarize_handler_stack` に `escape_owner_function` 追加
  - Perform で anchor 保存 + `PerformHandlerSearch` trace
  - 3 つの Resume サイトで anchor 渡す + `ResumeHandlerMerge` trace 拡張

write24-report.md として記録。

---

## りなに渡す質問

1. **Step 4 の targeted 化方針**：caller の effect tracking が必要。
   どの段階で実装するべき？ (a) lowering 中に caller の continuation を
   先読みして判定、(b) function info の effect annotation を活用、 (c)
   別の方法？

2. **案 C (walk-based propagation) の実装**：SR propagation で eval=24's
   return_frames を walk する場合、modified F_X.active_handlers に
   matching handler が見つかった時、どこで `H_sub.escape` (= each cont 2)
   を実行する？ F_X.owner_function は fold_impl などで違うので、F_X の
   eval を直接使えない。「H_sub.escape は H_sub.install_eval_id の eval
   で実行」というのを別途復元する仕組みが要りそう。

3. **anchor None の場合の挙動**：synthetic fallback frame で perform した
   場合 anchor=None。今は shared-prefix fallback を使うが、これで十分？
   実例は `evaluates_resumption_under_fresh_handler_stack` で問題なく
   動作している。

---

## コミット予定

write24 完了。
- anchor-based handler merge で stack 順序を semantically 正しく
- 167 tests pass、local choice 系 pass
- `PerformHandlerSearch` trace で handler 選択を可視化
- once_skip_eval_layers は依然 cps:0。Step 4 + Step 5 (案 C) が write25 で
