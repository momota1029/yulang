---
title: native-undet-write26 実装レポート — cps_repr interpreter に return-frame semantics を port
date: 2026-05-12
---

# native-undet-write26 実装レポート

## 結論（先に）

- **Layer 2 (cps_repr interpreter == VM): 達成！** `debugs_std_undet_once_skip_eval_layers`
  test で **Layer 1 OK + Layer 2 OK**！🎊
- write26 の方針通り、cps_eval の effectful terminator / ScopeReturn / eval_id /
  walk routing / pre-force / Return inherited preservation の意味論を
  **cps_repr interpreter に port** した。
- 既存 167 tests **pass**、`debugs_local_choice_*` 系も pass。
- 残: Layer 3 (cps_repr_cranelift JIT backend) は同じく effectful terminators
  に対する `todo!` panic がある。write27 で codegen 側の port が必要。

---

## 進捗まとめ

- write25 後: Layer 1 OK, Layer 2 `todo!` panic。
- write26 後: **Layer 1 OK + Layer 2 OK** ✓。Layer 3 (cranelift) `todo!` panic
  が新しい front frontier。

---

## Step 1: Runtime types を Layer 1 と揃える

### 追加した型

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CpsReprPromptId(u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CpsReprEvalId(u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CpsReprHandlerAnchor {
    prompt: CpsReprPromptId,
    install_eval_id: CpsReprEvalId,
}

const REPR_SYNTHETIC_EVAL_ID: CpsReprEvalId = CpsReprEvalId(u64::MAX);
const REPR_EXIT_RWH_TARGET: CpsContinuationId = CpsContinuationId(usize::MAX);
```

それぞれ `cps_eval::{CpsPromptId, CpsEvalId, CpsHandlerAnchor, SYNTHETIC_EVAL_ID,
EXIT_RWH_TARGET}` の repr 版。thread_local counter `fresh_repr_prompt()` /
`fresh_repr_eval_id()` も。

### `CpsReprRuntimeValue` に `ScopeReturn` variant

```rust
ScopeReturn {
    prompt: CpsReprPromptId,
    target: CpsContinuationId,
    value: Box<CpsReprRuntimeValue>,
}
```

既存 `Aborted` は legacy として残し、Perform terminator が legacy Aborted を
受けたら ScopeReturn に変換する形に。

### `CpsReprHandlerFrame` 拡張

```rust
struct CpsReprHandlerFrame {
    prompt: CpsReprPromptId,
    handler: CpsHandlerId,
    guard_stack: Vec<CpsReprGuardEntry>,
    envs: Vec<CpsReprEvaluatedHandlerEnv>,
    escape: CpsContinuationId,
    escape_owner_function: String,
    return_frame_threshold: usize,
    inherited: bool,
    install_eval_id: CpsReprEvalId,
}
```

### `CpsReprReturnFrame` 新規追加

```rust
struct CpsReprReturnFrame {
    owner_function: String,
    continuation: CpsContinuationId,
    values: Rc<HashMap<CpsValueId, CpsReprRuntimeValue>>,
    active_handlers: Vec<CpsReprHandlerFrame>,
    guard_stack: Vec<CpsReprGuardEntry>,
    owner_initial_frame_count: usize,
    owner_eval_id: CpsReprEvalId,
}
```

### `CpsReprResumption` 拡張

```rust
struct CpsReprResumption {
    // ...既存 field...
    return_frames: Vec<CpsReprReturnFrame>,
    handled_anchor: Option<CpsReprHandlerAnchor>,
}
```

---

## Step 2: eval signatures を更新

`eval_function`, `eval_function_with_context`, `eval_continuations` のシグネチャ
を Layer 1 と揃え、`return_frames`, `initial_frame_count`, `current_eval_id`
を threading。

```rust
fn eval_continuations(...) -> ... {
    let current_eval_id = fresh_repr_eval_id();
    resume_continuation(..., into_inherited_repr(active_handlers), ..., current_eval_id)
}

fn resume_continuation(
    module: &CpsReprModule,
    function: &CpsReprFunction,
    entry: CpsContinuationId,
    args: Vec<CpsReprRuntimeValue>,
    values: HashMap<CpsValueId, CpsReprRuntimeValue>,
    active_handlers: Vec<CpsReprHandlerFrame>,
    guard_stack: Vec<CpsReprGuardEntry>,
    return_frames: Vec<CpsReprReturnFrame>,
    initial_frame_count: usize,
    current_eval_id: CpsReprEvalId,
) -> CpsReprEvalResult<CpsReprRuntimeValue> { ... }
```

`into_inherited_repr` は handler frame の `inherited` flag を全部 true に。

---

## Step 3: helper 関数を port

`cps_eval` から repr 版を port：

- `same_handler_frame_repr` — (prompt, install_eval_id) 一致判定
- `merge_resumption_handlers_repr` — anchor-based merge with shared-prefix fallback
- `merge_extras_into_frames_repr` — 各 return frame に merge を適用
- `continue_return_frames_repr` — innermost frame pop + resume
- `return_frame_immediately_forces_param_repr` — pre-force 条件
- `try_route_scope_return_through_return_frames_repr` — walk-based ScopeReturn routing
- `handle_scope_return_repr` + `ScopeReturnActionRepr` enum

---

## Step 4: Effectful terminators

`CpsTerminator::EffectfulCall / EffectfulApply / EffectfulForce` を実装。
それぞれ `cps_eval` の同名 terminator の意味論を port：

- `EffectfulCall`: push F (with owner_eval=current) tail-call eval_function_with_context。
- `EffectfulForce`: thunk force 時に push F + tail-call thunk body。
- `EffectfulApply`: Closure/Resumption 分岐。Resumption の場合 anchor merge +
  combined_frames で再生。

`callee initial_frame_count = pre_push_count` (push 後 len ではなく push 前 len)
で post-call frame を callee の own_frames にする。Layer 1 と同じ semantics。

---

## Step 5: `Perform` を ScopeReturn ベースに

handler arm body の natural return を ScopeReturn { prompt, target=frame.escape,
value } に wrap。frame_in_active=false (synthetic) の場合は wrap せず raw 値
を返す。

```rust
let frame_in_active = active_handlers
    .iter()
    .any(|f| f.prompt == frame_prompt)
    && frame.install_eval_id != REPR_SYNTHETIC_EVAL_ID;
```

`install_eval_id != REPR_SYNTHETIC_EVAL_ID` チェックは、captured chain で synthetic
frame が混入した場合に Aborted-style の値返しを保つため
（`skips_handler_frame_blocked_by_guard_snapshot` test で必要）。

`handled_anchor` 保存も同様：

```rust
let handled_anchor = if frame_in_active {
    Some(CpsReprHandlerAnchor {
        prompt: frame.prompt,
        install_eval_id: frame.install_eval_id,
    })
} else {
    None
};
```

その後 ScopeReturn を `handle_scope_return_repr` に渡して dispatch。Propagate
時には walk → call-stack の fallback。

---

## Step 6: 各 stmt の dispatch macro 化

`dispatch_scope_return_repr!` macro を resume_continuation 内に定義し、
`DirectCall / ApplyClosure / ForceThunk / Resume / ResumeWithHandler` の各
stmt で sub-eval 結果を dispatch。JumpOrExit (with target/EXIT) / Propagate
(with walk) を Layer 1 と同じパターンで処理。

---

## Step 7: Return terminator with pre-force v2

```rust
CpsTerminator::Return(value) => {
    let v = read_value(function, &values, *value)?;
    if return_frames.len() <= initial_frame_count {
        return Ok(v);
    }
    // pre-force v2: top frame's continuation immediately ForceThunks?
    if let CpsReprRuntimeValue::Thunk(_) = &v {
        let top_index = return_frames.len() - 1;
        let top_frame = &return_frames[top_index];
        if return_frame_immediately_forces_param_repr(module, top_frame)?
            && top_index >= initial_frame_count
        {
            // resume_continuation in top frame's owner context with frames retained
            ...
        }
    }
    return continue_return_frames_repr(module, v, &return_frames, &[]);
}
```

`return_frames` を full pass し、`split_off(initial)` しない。Layer 1 と同じ
inherited preservation。

---

## Step 8: RWH を local-push パターンで

Legacy `handler_stack_with_pushed` 用法では install_eval=SYNTHETIC になり
ScopeReturn match できないため、Layer 1 と同じ「local active_handlers に
inline で push (install_eval=current_eval_id) + inner_handlers = captured ++ [RWH inherited]」
に書き換え。

```rust
let pushed_prompt = fresh_repr_prompt();
active_handlers.push(CpsReprHandlerFrame {
    prompt: pushed_prompt,
    handler: *handler,
    ...
    escape: REPR_EXIT_RWH_TARGET,
    escape_owner_function: function.name.clone(),
    return_frame_threshold: return_frames.len(),
    inherited: false,
    install_eval_id: current_eval_id,
});
let inner_handlers = {
    let mut stack = resumption.handlers.clone();
    let mut owned = active_handlers.last().cloned().expect(...);
    owned.inherited = true;
    stack.push(owned);
    stack
};
```

その後 dispatch macro を使い、value-flow path で RWH frame を pop。

---

## Step 9: ForceThunk stmt の nested-Thunk loop

cps_eval の ForceThunk stmt は Thunk → Thunk → ... のチェーンを loop で繰り返し
force する。cps_repr の従来実装は **single-force のみ** で、nested Thunk を
処理できていなかった。

```rust
let mut result = read_value(...)?;
loop {
    match result {
        CpsReprRuntimeValue::Thunk(thunk) => {
            ...
            result = eval_continuations(...)?;
            if matches!(result, CpsReprRuntimeValue::ScopeReturn { .. }) {
                break;
            }
        }
        _ => break,
    }
}
```

これがないと `once cont 3` の sync ForceThunk が work_thunk を1段しか force
できず、work cont 1 を実行しないまま終わってしまい、`once cont 3` の eval=4
での dispatch チェーンを構築できない。**Layer 2 を OK にする決定的な fix**。

---

## Step 10: List primitives 拡張

cps_repr の primitive eval が ListLen / ListIndex / ListIndexRangeRaw を
未対応だった。cps_eval から port：

- `cps_repr_value_to_usize` helper 追加。
- `PrimitiveOp::ListLen` 実装。
- `PrimitiveOp::ListIndex` 実装。
- `PrimitiveOp::ListIndexRangeRaw` 実装。

これらは std::list::uncons など内部で使われる。once の reject arm が
uncons を呼ぶため必須。

---

## 細かい修正

- `cps_repr_value_to_vm` の match に `ScopeReturn { .. }` を追加（None を返す）。
- `handler_stack_with_static` / `handler_stack_with_pushed` (legacy) の
  synthetic frame に新 field をデフォルト値 (SYNTHETIC) で埋める。

---

## Layer 3 (cps_repr_cranelift) — write27 へ持ち越し

`cps_repr_cranelift.rs:1344` に `todo!("Effectful{Call,Apply,Force} in cps_repr
Cranelift backend")` がある。write27 では Cranelift JIT backend に同じ意味論
を codegen で実装する必要。これは codegen 作業で、interpreter ほど直接的な
port にはならないが、Layer 1+2 の意味論を機械語へ落とす形になる。

優先順位的には：
1. **Layer 1+2 が通った** ← 現状の write26 で完了。
2. Layer 3 (cranelift) の codegen が次。

---

## テスト結果

```text
cargo test -p yulang-native                              => 167 pass / 17 ignored
cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored
  => pass
cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored
  => pass
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored
  => Layer 1 (CPS eval): OK
  => Layer 2 (CPS repr eval): OK
  => Layer 3 (CPS repr cranelift): todo! panic
```

---

## 触ったファイル

- `crates/yulang-native/src/cps_repr.rs`:
  - 新規型: `CpsReprPromptId`, `CpsReprEvalId`, `CpsReprHandlerAnchor`,
    sentinels (`REPR_SYNTHETIC_EVAL_ID`, `REPR_EXIT_RWH_TARGET`)
  - 新規 variant: `CpsReprRuntimeValue::ScopeReturn`
  - 新規 struct: `CpsReprReturnFrame`
  - 拡張 struct: `CpsReprHandlerFrame` (prompt, escape, escape_owner_function,
    return_frame_threshold, inherited, install_eval_id)
  - 拡張 struct: `CpsReprResumption` (return_frames, handled_anchor)
  - 新規 helper: `same_handler_frame_repr`, `merge_resumption_handlers_repr`,
    `merge_extras_into_frames_repr`, `continue_return_frames_repr`,
    `return_frame_immediately_forces_param_repr`,
    `try_route_scope_return_through_return_frames_repr`,
    `handle_scope_return_repr` + `ScopeReturnActionRepr`,
    `into_inherited_repr`, `fresh_repr_prompt`, `fresh_repr_eval_id`,
    `cps_repr_value_to_usize`
  - eval signatures に return_frames / initial_frame_count / current_eval_id
    を threading
  - `resume_continuation` 内に `dispatch_scope_return_repr!` macro
  - 各 stmt (DirectCall, ApplyClosure, ForceThunk, Resume, ResumeWithHandler)
    で dispatch macro 使用
  - ForceThunk stmt に nested-Thunk loop 追加
  - 3 つの effectful terminators (EffectfulCall, EffectfulForce, EffectfulApply)
    を実装
  - Perform terminator を ScopeReturn ベース + anchor 記録に
  - Return terminator に inherited preservation + pre-force v2
  - List primitives 拡張 (ListLen, ListIndex, ListIndexRangeRaw)
  - `cps_repr_value_to_vm` の match に ScopeReturn を追加

---

## りなに渡す質問

1. **Layer 3 (cps_repr_cranelift) の port 方針**: Cranelift codegen で
   effectful terminators を実装する必要。これは interpreter と違って
   コードを生成する形になる。具体的にどう codegen するべきか方針が
   欲しい。push frame は値を保存する命令列、tail-call は jump、と
   素直に対応できる？

2. **Aborted variant の deprecation**: cps_repr の `Aborted` variant は
   ほぼ使われなくなった (legacy fallback のみ)。Perform の bridge:
   `Aborted(inner) => ScopeReturn { prompt, target, value: inner }`。
   完全に削除する方向で良い？

3. **ForceThunk nested-Thunk loop の発見**: これは cps_eval にあったが
   cps_repr に欠けていた。両者の整合性を保つメカニズムを将来作るか？
   （例：共有 enum と eval trait みたいな抽象化）

---

## コミット予定

write26 完了。
- cps_repr interpreter に Layer 1 の return-frame 意味論を移植
- ScopeReturn / eval_id / walk routing / pre-force / anchor merge 全て port
- ForceThunk の nested-Thunk loop 追加（決定的な fix）
- List primitives 拡張
- Layer 1 + Layer 2 OK
- 167 tests pass、local choice 系 pass
- 残: Layer 3 (cps_repr_cranelift JIT) の effectful terminators codegen は write27
