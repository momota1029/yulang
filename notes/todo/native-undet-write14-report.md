# native-undet-write14 実装レポート

## 実装したこと（write14 指示ベース）

### `initial_frame_count` refactor (cps_eval.rs)

write14 が出した「sync call は親 frames を inherit するが、callee の通常 Return では
consume しない」を実装する中核 refactor。

#### 1. `CpsReturnFrame` に threshold を追加

```rust
struct CpsReturnFrame {
    // ... 既存 ...
    /// Threshold for the owner eval's `initial_frame_count` ...
    owner_initial_frame_count: usize,
}
```

EffectfulCall / EffectfulApply / EffectfulForce が frame を push する時、
push 時点の `initial_frame_count` をここに保存。

#### 2. eval entry points に `initial_frame_count: usize` を追加

```rust
eval_function_with_context(..., initial_frame_count: usize)
eval_continuations(..., initial_frame_count: usize)
resume_continuation(..., initial_frame_count: usize)
```

#### 3. `Return` の新ルール

```rust
if return_frames.len() <= initial_frame_count {
    return Ok(v);
}
let own_frames = return_frames.split_off(initial_frame_count);
return continue_return_frames(module, v, &own_frames, &[]);
```

prefix が inherited、suffix が own。own のみ consume。

#### 4. sync stmt calls を更新

- DirectCall stmt
- ApplyClosure stmt (Closure ケース)
- ForceThunk stmt（loop 内）

すべて parent の `return_frames.clone()` を callee に渡し、
`initial_frame_count = return_frames.len()` を渡す（= 全部 inherited、
callee の Return で何も consume しない）。

#### 5. Effectful terminators を更新

- EffectfulCall / EffectfulApply / EffectfulForce

すべて push 前の `pre_push_count = return_frames.len()` を取って、

- frame に `owner_initial_frame_count = 現在の initial_frame_count` を保存
- callee に渡す `initial_frame_count = pre_push_count`（= 自分が push した
  frame は callee の own になる）

#### 6. Resume / ResumeWithHandler / ApplyClosure(Resumption) を更新

すべて `initial_frame_count = 0` を渡す。captured continuation の replay なので
保存された frames すべて consume してよい。

#### 7. `continue_return_frames` を更新

pop した frame の `owner_initial_frame_count` を `resume_continuation` に渡す
ことで、frame の owner eval が再開時に正しい threshold を復元できる。

```rust
debug_assert!(frame.owner_initial_frame_count <= rest.len());
resume_continuation(..., rest, frame.owner_initial_frame_count)
```

---

## テスト状況

### 通った 🎉

- **既存 170 テスト** すべて PASS（regression なし）
- **`debugs_local_choice_caller_rest_eval`** (write12 minimal) 継続 PASS
- **`debugs_local_choice_callback_rest_eval`** (write13 Test A) **新規 PASS**
  - `call_callback(f) = f 0` の callback 内 `branch()` から outer の reject まで
    正しく caller continuation を辿れるようになった
  - cps:2 / vm:2 一致

### まだ通らない

- **`debugs_std_undet_once_skip_eval_layers`** (cps:0 vs vm:2)
  - write14 が予告通り「`fold_impl` 内の非 tail `ApplyClosure` の local rest が
    resumption に入らない」次段階の問題
  - `initial_frame_count` refactor は outer return frames の継承を直したが、
    `fold_impl` 内で `f z x` の post-call cont を resumption に含めるには
    targeted EffectfulApply lowering が必要

その他の ignored test (8件) は全て write14 以前から `#[ignore = "Phase D/F: ..."]`
の known failures。新規 regression なし。

---

## 実装の要点（write14 が強調してくれた箇所）

### 「inherit するが consume しない」分離

これが本質的だった。今までは sync stmt call に `Vec::new()` を渡していて、
callee の Perform が caller の post-call cont を捕まえられなかった。

```text
sync call:
  callee に return_frames を渡す      ← Perform が拾える
  initial = return_frames.len()      ← Return では消費しない
```

### Effectful terminator の `pre_push_count` vs `initial_frame_count`

ここを混同すると即座に壊れる。write14 が「強く言っておくといいねぇ」と言っていた箇所。

```text
frame.owner_initial_frame_count = 現在の eval の initial_frame_count
callee.initial_frame_count      = push 前の return_frames.len()
```

両者は別の値。前者は「自分が再開時に戻すべき threshold」、後者は「callee が
自分の own frame として何個目から扱えるか」。

### Resume は sync call ではない

`Resume(k, arg)` / `ResumeWithHandler` は captured continuation の replay なので
`initial = 0`。captured frames すべてが own = consume できる。

ここを sync call と同じ初期値にすると、resumption が再開時に F_work_post 等を
消費できなくなり、Test A も通らない。

---

## 次段階の課題（write14 §13 で予告）

`debugs_std_undet_once_skip_eval_layers` を通すには:

1. **trace で `fold_impl` の callback apply を確認**
   - branch Perform inside fold callback の `return_frames.len()`
   - outer frame は入っているか、fold の「次の要素へ進む rest」が入っているか
2. **欠けている continuation を特定**
   - もし outer frame は入っているが local rest が無いなら、`fold_impl` 内の
     `f z x` を `EffectfulApply` terminator にする targeted lowering が必要
3. **Cranelift backend との衝突を避ける**
   - `Stmt::Expr` split / global EffectfulApply 化は既存 Cranelift regression を
     起こすので、targeted な範囲のみ
4. **その時点で cps_repr / Cranelift の扱いも決める**

---

## コミット予定

write14 の `initial_frame_count` refactor を `cps_eval.rs` のみで実装。
IR・lowering・cps_repr・cps_repr_cranelift は無変更。

170 既存 + 2 新規 ignore PASS = 172 通り。次の write15（仮）で
`std::undet.once` の local rest を扱う方針を相談したい。
