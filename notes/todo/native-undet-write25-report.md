---
title: native-undet-write25 実装レポート — walk-based SR routing + each EffectfulCall + pre-force
date: 2026-05-12
---

# native-undet-write25 実装レポート

## 結論（先に）

- **Layer 1 (cps_eval == VM): 達成！** `debugs_std_undet_once_skip_eval_layers`
  test で `cps:2 == vm:2`！🎊
- write25 が提案した 3 つの fix の組み合わせがすべて必要だった：
  1. **Step 5**: walk-based ScopeReturn routing (`try_route_scope_return_through_return_frames`)
  2. **Step 4 narrow**: `std::undet::undet::each*` を target にした EffectfulCall lowering
  3. **Pre-force** (write17 v2): fold_impl が Thunk を Return する時、F_each_post を
     pop せず each cont 12 を **F_each_post の owner context** (current_eval_id=8) で実行
- 既存 167 tests **pass**、`debugs_local_choice_*` 系も pass
- 唯一の残課題: **Layer 2 (cps_repr interpreter)** が `EffectfulCall` / `EffectfulApply`
  / `EffectfulForce` を未実装で `todo!` panic。これは pre-existing な TODO で、
  Step 4 narrow が initial trigger となった。write26 で対応予定。

---

## 進捗まとめ

- write22 後: cps:0 / vm:2 (Layer 1 fail)
- write23 後: cps:0 / vm:2 (Layer 1 fail, ただし F_each_post が一部 capture)
- write24 後: cps:0 / vm:2 (Layer 1 fail, anchor merge で stack 順正しく)
- write25 後: **cps:2 == vm:2** (Layer 1 達成！) + cps_repr interpreter TODO 露呈

---

## Step 5: walk-based ScopeReturn routing

### `try_route_scope_return_through_return_frames`

`continue_return_frames` の近くに新しい helper を追加。

```rust
fn try_route_scope_return_through_return_frames(
    module: &CpsModule,
    scope_return: &CpsRuntimeValue,
    return_frames: &[CpsReturnFrame],
    initial_frame_count: usize,
) -> CpsEvalResult<Option<CpsRuntimeValue>> {
    // ScopeReturn 以外なら None
    // target == EXIT_RWH_TARGET なら None (call-stack に任せる)
    // return_frames.len() <= initial_frame_count なら None (inherited のみ)
    // innermost からの reverse walk:
    //   for each frame:
    //     if frame.active_handlers has handler matching
    //        (handler.prompt == sr.prompt
    //         && handler.install_eval_id == frame.owner_eval_id):
    //       truncate frame.active_handlers below handler_index
    //       truncate rest_frames at handler.return_frame_threshold
    //       resume_continuation at handler.escape with these
    //       return Some(result)
    //   return None (fall through to call-stack propagation)
}
```

### `dispatch_scope_return!` macro と Perform terminator の Propagate path に組み込み

```rust
ScopeReturnAction::Propagate(v) => {
    if let Some(routed) = try_route_scope_return_through_return_frames(
        module, &v, &return_frames, initial_frame_count,
    )? {
        return Ok(routed);
    }
    return Ok(v);
}
```

### trace 追加

- `ScopeReturnFrameWalk`: walk のエントリポイント。
- `ScopeReturnFrameWalk: check frame_index=...`: 各 frame の検査。
- `FrameWalkMatch`: match した時に handlers_before/after, threshold, rest 等を出力。

---

## Step 4 narrow: `std::undet::undet::each*` を EffectfulCall に

`cps_lower.rs` の `direct_apply` 経路で、`info_returns_thunk` の場合の
EffectfulCall path を、callee が `std::undet::undet::each*` の時も発火するように
拡張。

```rust
let target_is_undet_each =
    target.starts_with("std::undet::undet::each");
if (self.higher_order_helper && info_returns_thunk)
    || (target_is_undet_each && info_returns_thunk)
{
    // EffectfulCall + post_cont with force_if_non_thunk_demand
}
```

write24 の試行 (`info_returns_thunk && demand_is_non_thunk`) は広すぎて 2 regression
が出たため revert したが、`std::undet::undet::each*` だけに絞ると regression なし。

### 効果

`work__mono0` の `DirectCall each__mono1 → ForceThunk` パターンが：

```text
EffectfulCall each__mono1 -> cont_after_each_call
cont_after_each_call(t):
  ForceThunk(t) -> n          (stmt-level、higher_order_helper 既存パターン)
  ... rest (guard; reject) ...
```

に変わる。これで **work の post-call continuation が `F_work_post` という
return frame になり、captured chain に入る**。

---

## Pre-force (write17 v2): `Return` terminator で

write23 から残っていた pre-force のコメントを実装に。

```rust
if let CpsRuntimeValue::Thunk(_) = &v {
    let top_index = return_frames.len() - 1;
    let top_frame = &return_frames[top_index];
    if return_frame_immediately_forces_param(module, top_frame)?
        && top_index >= initial_frame_count
    {
        let top_frame = top_frame.clone();
        let top_owner = function_by_name(module, &top_frame.owner_function)?;
        return resume_continuation(
            module,
            top_owner,
            top_frame.continuation,
            vec![v],
            top_frame.values.as_ref().clone(),
            top_frame.active_handlers.clone(),
            top_frame.guard_stack.clone(),
            return_frames.clone(),          // ← 全 frames 保持、top_frame も含む
            return_frames.len(),            // ← initial = full len で consume 防止
            top_frame.owner_eval_id,        // ← eval=8 復元
        );
    }
}
```

### 重要なポイント

- `top_frame` を `return_frames` に **retained** したまま実行 → F_each_post が
  chain に居続ける。
- `top_owner=each` で `current_eval_id=8` (= F_each_post.owner_eval_id) →
  `H_sub.install_eval_id=8 == current_eval_id` で walk match できる。
- write17 が当時 disable された理由 (current_function=fold_impl で owner check
  fail) は、`top_owner` を使うことで解消。

### Trace

`PreForceResumeTopFrame top_owner=each top_owner_eval=8 top_cont=cont 12` が
fold_impl Return 時に発火する。

---

## 三段の組み合わせがなぜ必要だったか

最終 trace を見ると、bug が消えた理由がはっきり：

```text
Return fold_impl cont 0 value=Thunk
PreForceResumeTopFrame top_owner=each top_owner_eval=8 top_cont=cont 12

(F_each_post が retained のまま each cont 12 が eval_id=8 で実行)

cont 12 ForceThunk sync → fold_impl 本体実行
... 各種 EffectfulApply で frame push ...
Perform branch eval=17 return_frames.len=3 (with F_each_post, F_work_post)
Resumption(... frames=3 ...)

(merge_extras_into_frames で F_each_post に inner once H injection)

Resume k1 true eval=24 active_handlers=[outer, inner, H_sub]
Perform sub::return eval=24 → dispatch matched=no → Propagate

(write25 Step 5 walk fires)

FrameWalkMatch frame_owner=each frame_owner_eval=8
  handler_prompt=1 handler_install_eval=8
  handlers_before=[outer, inner, H_sub] handlers_after=[outer, inner]

(walk が F_each_post で match → 各 cont 2 を eval_id=8 で実行)

Return each cont 2 value=Plain(Int 1)
ContinueReturnFrames pop F_work_post owner_eval=7

(F_work_post.active_handlers = [outer, inner] が work cont_after_each_call に
 propagate)

Perform reject eval=??? active_handlers=[outer, inner]
PerformHandlerSearch matched_prompt=2 (inner once!)
... uncons queue=[k1] → just(k1) → Apply k1 false → x=2 path ...
... sub::return(2) → H_sub abort again → just(2) ...

Layer 1 (CPS eval): OK ✓
```

各 step が組み合わさって：
- Pre-force: F_each_post を chain に保持
- Step 4 narrow: F_work_post も chain に追加
- merge anchor (write24): F_each_post.active_handlers と F_work_post.active_handlers
  に inner once H を正しい位置で injection
- Step 5 walk: F_each_post で match → modified F_each_post.active_handlers を使う
- modified F_work_post: walk match 後、`continue_return_frames` pop で
  work cont_after_each_call に modified active_handlers が伝わる
- reject perform: 正しく inner once H に match

---

## 既存 167 tests の regression なし

- write24 で広い `info_returns_thunk && demand_is_non_thunk` は 2 regression。
- 今回 narrow にして `std::undet::undet::each*` のみ → regression なし。
- pre-force は `return_frame_immediately_forces_param` チェックがあり、適切な
  形のみ発火。
- Step 5 walk は target=EXIT_RWH_TARGET をスキップ、strict match 条件で safe。

---

## Layer 2 (cps_repr interpreter) の残課題

`cps_repr.rs:1736` に既存の `todo!` がある：

```rust
CpsTerminator::EffectfulCall { .. }
| CpsTerminator::EffectfulApply { .. }
| CpsTerminator::EffectfulForce { .. } => {
    todo!("Effectful{{Call,Apply,Force}} in cps_repr eval");
}
```

cps_repr の **interpreter eval** path (`cps_repr::eval_cps_repr_module`) が
effectful terminators を未実装。`Cranelift JIT` path (`compare_cps_repr_cranelift_i64`)
は実装あり (codegen 経由)。

これまでこの test 以外で interpreter path が triggered されていなかったため
潜在 TODO だった。Step 4 narrow で `work` が EffectfulCall を emit するように
なり、この test の Layer 2 で初めて hit。

write26 で：

```text
1. cps_repr interpreter に EffectfulCall/EffectfulApply/EffectfulForce を実装
   - cps_eval の return-frame セマンティクスを port
   - もしくは、 cps_repr では effectful を sync 等価変換するシム
```

を入れて Layer 2 も通す。

---

## Step 4 narrow を将来汎用化する方針

現在 `target.starts_with("std::undet::undet::each")` でハードコード。
write26 以降で：

1. **(b) effect annotation 経由**: callee の effect / handler signature を
   見て、caller の post-call continuation が effect を持つなら EffectfulCall。
2. **(c) function-level analysis**: caller の関数本体に Perform / handler
   install / effectful call があるなら、effect を持つ callee を EffectfulCall。

write24 の質問 Q1 への私の最終回答は **(c) function-level analysis** が
バランス良いと思う。(b) effect annotation は infrastructure 重め。

---

## 触ったファイル

### `crates/yulang-native/src/cps_eval.rs`

- `try_route_scope_return_through_return_frames` helper 追加 (約 100 行)。
- `dispatch_scope_return!` macro の Propagate 分岐で walk を呼ぶ。
- `CpsTerminator::Perform` の handle_scope_return Propagate 分岐でも walk を呼ぶ。
  Propagate 分岐を Perform terminator の match 順序前に移動。
- `CpsTerminator::Return` で write17 pre-force を re-enable
  (`return_frame_immediately_forces_param` + `resume_continuation` with retained
  frames)。
- trace 追加: `ScopeReturnFrameWalk`, `FrameWalkMatch`,
  `PreForceResumeTopFrame`.

### `crates/yulang-native/src/cps_lower.rs`

- `direct_apply` 経路で `target_is_undet_each` 条件を追加。
  `std::undet::undet::each*` callee の場合も EffectfulCall path に進む。

---

## りなに渡す質問

1. **cps_repr interpreter の effectful 実装**：write26 で cps_repr に
   `CpsTerminator::EffectfulCall/Apply/Force` の eval を実装する方針。
   cps_eval の return-frame セマンティクスをそのまま port する形でよい？
   もしくは cps_repr では sync 化する shim approach がある？

2. **Step 4 narrow の generalization**：`std::undet::undet::each` のハードコードを
   将来どう一般化する？ (a) effect annotation、(b) function-level effect tracking、
   (c) ad-hoc whitelist 拡張？

3. **walk 設計の owner check**：今は match 条件として
   `handler.install_eval_id == frame.owner_eval_id` AND
   `handler.escape_owner_function == frame.owner_function` を要求している。
   厳密だが正確。これで OK？

4. **Pre-force の condition**: 現在 `return_frame_immediately_forces_param` のみ。
   将来 other patterns (e.g. EffectfulForce 用意で同等の挙動を狙う) に拡張する
   余地はある？

---

## コミット予定

write25 完了。
- **Layer 1 cps_eval == VM 達成** for `debugs_std_undet_once_skip_eval_layers`
- 167 tests pass、local choice 系 pass
- 残: Layer 2 cps_repr interpreter の `EffectfulCall/Apply/Force` 実装 (write26)
