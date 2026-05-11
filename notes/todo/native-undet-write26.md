やったねぇ、ついに Layer 1 到達。これはかなり大きい節目だよ〜。`debugs_std_undet_once_skip_eval_layers` が `cps:2 == vm:2` になったのは、ここ数回の仮説がちゃんと噛み合った証拠だねぇ。write25 report でも、Step 5 walk-based routing、Step 4 narrow each lowering、pre-force v2 の 3 点セットが全部必要だった、と整理されている。

ここからの助言はかなり明確。**write26 は cps_repr interpreter に `EffectfulCall / EffectfulApply / EffectfulForce` を実装する。ただし sync shim ではなく、cps_eval の return-frame 意味論を移植する方向が本線**だと思うよ〜。

---

## まず、write25 の成果の評価

write25 の勝ち筋はすごくきれいにまとまっている。

```text
Pre-force:
  F_each_post を pop せず retained

Step 4 narrow:
  work の post-call continuation を F_work_post として captured chain に入れる

anchor merge:
  inner once H を [outer, inner, H_sub] の正しい位置へ inject

Step 5 walk:
  call-stack の stale snapshot ではなく、modified captured frame で H_sub を resolve

F_work_post:
  work の guard/reject 続行時に inner once H を持つ
```

これで reject が inner once に捕まって、queue replay が走り、`k false` から x=2 path に進む。ついに `cps_eval == VM`。この一連は、もう「偶然通った」じゃなく、かなり納得できる意味論になっているよ〜。

---

# write26 の本線

## 結論

```text
cps_repr interpreter に cps_eval の effectful terminator semantics を port する
```

「cps_repr では sync 化する shim」は避けた方がいい。

理由は、write25 の成功条件そのものが sync では壊れる形だから。

```text
EffectfulCall:
  post continuation を return frame にする必要がある

EffectfulForce:
  thunk force 中の Perform が caller continuation を capture する必要がある

EffectfulApply:
  resumption replay 時の captured frames / merged handlers を正しく使う必要がある
```

ここを sync shim にすると、たぶん Layer 2 でも同じ失敗に戻る。特に `std::undet.each` の Step 4 narrow は、`work` の post-call continuation を `F_work_post` にするために入ったものだから、interpreter 側でも terminator として扱う必要がある。

---

# write26 実装指示

以下、そのまま別LLMへ渡せる形で書くねぇ。

---

## 目的

`cps_repr::eval_cps_repr_module` で `CpsTerminator::EffectfulCall / EffectfulApply / EffectfulForce` を実装し、`debugs_std_undet_once_skip_eval_layers` の Layer 2 を通す。

現状:

```text
Layer 1 cps_eval == VM:
  pass

Layer 2 cps_repr interpreter:
  CpsTerminator::EffectfulCall / EffectfulApply / EffectfulForce で todo! panic
```

write25 report では `cps_repr.rs:1736` 付近に既存 TODO があると記録されている。

---

## 絶対にやらないこと

### 1. Effectful terminator を sync stmt 相当にしない

これは駄目。

```text
EffectfulCall target args resume
  = DirectCall target args して result を resume param に入れる
```

みたいな shim は一見楽だけど、Perform 時に post continuation が resumption に入らない。write25 の本質を捨てることになる。

### 2. Layer 1 の `cps_eval.rs` を巻き戻さない

次は `cps_repr.rs` 側。Layer 1 は通ったので、`cps_eval.rs` の write25 修正は温存。

維持するもの:

```text
- eval_id strict ScopeReturn
- anchor-based handler merge
- Return inherited preservation
- walk-based ScopeReturn routing
- each-only EffectfulCall lowering
- pre-force v2
```

### 3. Cranelift 側に先に逃げない

write25 report では Cranelift JIT path は effectful terminators 実装済みで、今回露呈したのは cps_repr interpreter path の TODO だと整理されている。

---

# まず確認するべき構造

`cps_repr.rs` は `CpsReprRuntimeValue::Aborted` を持っている。最初の方でも `unwrap_aborted_repr` があり、eval root で `Aborted` を剥がしている。

これは注意点だねぇ。Layer 1 の `cps_eval.rs` は `ScopeReturn { prompt, target, value }` ベースへ進化している。一方、cps_repr interpreter はまだ古い `Aborted` 系が残っている可能性が高い。

だから write26 には二つの道がある。

---

## 道 A: cps_repr に ScopeReturn / eval id を移植する

これが正道。やることは多いけど、Layer 1 と意味論を揃えやすい。

必要な追加:

```rust
CpsReprRuntimeValue::ScopeReturn {
    prompt: CpsReprPromptId,
    target: CpsContinuationId,
    value: Box<CpsReprRuntimeValue>,
}
```

または既存 `CpsPromptId` / `CpsEvalId` を共用できるなら、repr 用に分けなくてもよい。

さらに:

```rust
CpsReprHandlerFrame.install_eval_id
CpsReprReturnFrame.owner_eval_id
CpsReprResumption.handled_anchor
```

も必要。

そして `cps_eval.rs` の以下をほぼ port する。

```text
handle_scope_return
try_route_scope_return_through_return_frames
merge_resumption_handlers
merge_extras_into_frames
continue_return_frames
pre-force v2
```

これは大きいが、長期的には一番きれい。

---

## 道 B: Aborted のまま minimum port する

短期的にはこっちでも Layer 2 だけ通るかもしれない。ただし危険が多い。

`Aborted` は prompt / target / install eval を持たないなら、H_sub と once reject の区別を表せない。今回のバグはまさに prompt / eval identity が必要だったので、`Aborted` のまま強行すると、Layer 1 で直した意味論を再現できない可能性が高い。

だから、私は **道 A を推す**。

---

# write26 推奨: cps_repr eval を cps_eval と同型に寄せる

## Step 1: cps_repr runtime structs を Layer 1 と揃える

`cps_eval.rs` の構造を名前だけ repr にして port する。

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CpsReprEvalId(u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CpsReprPromptId(u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CpsReprHandlerAnchor {
    prompt: CpsReprPromptId,
    install_eval_id: CpsReprEvalId,
}
```

`CpsReprRuntimeValue` に:

```rust
ScopeReturn {
    prompt: CpsReprPromptId,
    target: CpsContinuationId,
    value: Box<CpsReprRuntimeValue>,
}
```

を追加。

既存 `Aborted` はすぐ消さなくてもよい。まずは残して、古いテストを壊さない。

---

## Step 2: handler frame / return frame / resumption を拡張

既存名は実コードに合わせる。

```rust
struct CpsReprHandlerFrame {
    prompt: CpsReprPromptId,
    handler: CpsHandlerId,
    envs: Vec<CpsReprResolvedHandlerEnv>,
    escape: CpsContinuationId,
    escape_owner_function: String,
    return_frame_threshold: usize,
    inherited: bool,
    install_eval_id: CpsReprEvalId,
}
```

```rust
struct CpsReprReturnFrame {
    owner_function: String,
    continuation: CpsContinuationId,
    values: Rc<Vec<Option<CpsReprRuntimeValue>>>,
    active_handlers: Vec<CpsReprHandlerFrame>,
    guard_stack: Vec<CpsReprGuardEntry>,
    owner_initial_frame_count: usize,
    owner_eval_id: CpsReprEvalId,
}
```

```rust
struct CpsReprResumption {
    owner_function: String,
    target: CpsContinuationId,
    values: Rc<Vec<Option<CpsReprRuntimeValue>>>,
    return_frames: Rc<Vec<CpsReprReturnFrame>>,
    handlers: Rc<Vec<CpsReprHandlerFrame>>,
    guard_stack: Rc<Vec<CpsReprGuardEntry>>,
    handled_anchor: Option<CpsReprHandlerAnchor>,
}
```

ここで `handled_anchor` は write24 の anchor merge に必要。

---

## Step 3: eval entry に `current_eval_id` と `initial_frame_count`

`cps_eval.rs` と同じ形へ寄せる。

```rust
fn eval_continuations_repr(...) -> CpsReprEvalResult<CpsReprRuntimeValue> {
    let current_eval_id = fresh_repr_eval_id();
    resume_continuation_repr(..., current_eval_id)
}
```

```rust
fn resume_continuation_repr(
    module: &CpsReprModule,
    function: &CpsReprFunction,
    entry: CpsContinuationId,
    initial_args: Vec<CpsReprRuntimeValue>,
    initial_values: Vec<Option<CpsReprRuntimeValue>>,
    active_handlers: Vec<CpsReprHandlerFrame>,
    guard_stack: Vec<CpsReprGuardEntry>,
    return_frames: Vec<CpsReprReturnFrame>,
    initial_frame_count: usize,
    current_eval_id: CpsReprEvalId,
) -> CpsReprEvalResult<CpsReprRuntimeValue>
```

既存 `eval_function` からは:

```rust
return_frames = []
initial_frame_count = 0
```

で入る。

---

## Step 4: `EffectfulCall` を実装

Layer 1 の意味論そのまま。

```rust
CpsTerminator::EffectfulCall { target, args, resume } => {
    let target_function = function_by_name_repr(module, target)?;
    let call_args = args
        .iter()
        .map(|id| read_repr_value(function, &values, *id))
        .collect::<Result<Vec<_>, _>>()?;

    let pre_push_count = return_frames.len();

    let mut frames = return_frames.clone();
    frames.push(CpsReprReturnFrame {
        owner_function: function.name.clone(),
        continuation: *resume,
        values: Rc::new(values.clone()),
        active_handlers: active_handlers.clone(),
        guard_stack: guard_stack.clone(),
        owner_initial_frame_count: initial_frame_count,
        owner_eval_id: current_eval_id,
    });

    return eval_function_with_context_repr(
        module,
        target_function,
        call_args,
        active_handlers.clone(),
        guard_stack.clone(),
        frames,
        pre_push_count,
    );
}
```

大事なのは:

```text
callee initial_frame_count = pre_push_count
```

push 後 len ではない。
これを間違えると post frame を consume できない。

---

## Step 5: `EffectfulForce` を実装

`ForceThunk` stmt と似ているが、terminator なので post-force frame を push する。

```rust
CpsTerminator::EffectfulForce { thunk, resume } => {
    let thunk_value = read_repr_value(function, &values, *thunk)?;
    let CpsReprRuntimeValue::Thunk(thunk) = thunk_value else { ... };

    let pre_push_count = return_frames.len();

    let mut frames = return_frames.clone();
    frames.push(CpsReprReturnFrame {
        owner_function: function.name.clone(),
        continuation: *resume,
        values: Rc::new(values.clone()),
        active_handlers: active_handlers.clone(),
        guard_stack: guard_stack.clone(),
        owner_initial_frame_count: initial_frame_count,
        owner_eval_id: current_eval_id,
    });

    let owner = function_by_name_repr(module, &thunk.owner_function)?;

    return eval_continuations_repr(
        module,
        owner,
        thunk.entry,
        Vec::new(),
        thunk.values.as_ref().clone(),
        active_handlers_or_thunk_handlers,
        guards_or_thunk_guards,
        frames,
        pre_push_count,
    );
}
```

`ForceThunk` stmt で使っている handler/guard choice と合わせる。

---

## Step 6: `EffectfulApply` を実装

3 分岐が必要。

### Closure

```rust
EffectfulApply closure=Closure:
  post frame push
  eval_continuations_repr(owner, closure.entry, [arg], closure.values, frames, pre_push_count)
```

### Resumption

ここが一番大事。

Layer 1 と同じく:

```text
new_frames = parent return_frames + [F_post]
adjusted_res_frames = merge_extras_into_frames(resumption.return_frames, active_handlers, resumption.handled_anchor)
combined_frames = new_frames + adjusted_res_frames
```

pop 順を考えて、Layer 1 の最新実装と同じ順にする。write16 以降、`continue_return_frames` は末尾から pop するため、この順序がかなり重要だった。write16 report でも frame order 修正が要点だった。

`resumed_handlers` も anchor merge。

```rust
let resumed_handlers = merge_resumption_handlers(
    resumption.handlers.as_ref(),
    &active_handlers,
    resumption.handled_anchor,
);
```

そして:

```rust
return eval_continuations_repr(
    module,
    owner,
    resumption.target,
    vec![arg],
    resumption.values.as_ref().clone(),
    resumed_handlers,
    resumption.guard_stack.as_ref().clone(),
    combined_frames,
    0,
);
```

Resume は captured frames を consume できる必要があるので `initial_frame_count = 0`。

### Other

既存の `ExpectedResumption` / closure error に合わせる。

---

## Step 7: Return inherited preservation + pre-force v2

write25 の pre-force が Layer 1 の成功条件。repr interpreter でも必要になる可能性が高い。

Return terminator で:

```rust
if let CpsReprRuntimeValue::Thunk(_) = &v {
    if return_frames.len() > initial_frame_count {
        let top_index = return_frames.len() - 1;
        let top_frame = &return_frames[top_index];

        if top_index >= initial_frame_count
            && return_frame_immediately_forces_param_repr(module, top_frame)?
        {
            let top_frame = top_frame.clone();
            let top_owner = function_by_name_repr(module, &top_frame.owner_function)?;

            return resume_continuation_repr(
                module,
                top_owner,
                top_frame.continuation,
                vec![v],
                top_frame.values.as_ref().clone(),
                top_frame.active_handlers.clone(),
                top_frame.guard_stack.clone(),
                return_frames.clone(),      // top frame retained
                return_frames.len(),        // consume 防止
                top_frame.owner_eval_id,
            );
        }
    }
}
```

その後の通常 Return は:

```rust
if return_frames.len() > initial_frame_count {
    return continue_return_frames_repr(module, v, &return_frames, &[]);
}
return Ok(v);
```

ここで `split_off(initial)` しない。write23 の inherited preservation と同じ。

---

## Step 8: walk-based ScopeReturn routing

`cps_eval.rs` の `try_route_scope_return_through_return_frames` を repr へ port。

```rust
fn try_route_scope_return_through_return_frames_repr(
    module: &CpsReprModule,
    scope_return: &CpsReprRuntimeValue,
    return_frames: &[CpsReprReturnFrame],
    initial_frame_count: usize,
) -> CpsReprEvalResult<Option<CpsReprRuntimeValue>>
```

条件:

```text
- ScopeReturn だけ対象
- target == EXIT_RWH_TARGET は skip
- return_frames.len() <= initial_frame_count なら None
- own frames のみ reverse walk
- handler.prompt == sr.prompt
- handler.install_eval_id == frame.owner_eval_id
- handler.escape_owner_function == frame.owner_function
```

match 時:

```text
handlers_before=[outer, inner, H_sub]
handlers_after=[outer, inner]
resume handler.escape in frame.owner_eval_id
```

Layer 1 と同じ。

---

## Step 9: Perform で ScopeReturn と anchor を作る

Perform handler search 時に、matched frame から anchor を保存。

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

resumption に:

```rust
handled_anchor
return_frames: Rc::new(return_frames.clone())
handlers: Rc::new(active_handlers.clone())
guard_stack: Rc::new(guard_stack.clone())
```

handler arm の戻りが abort する場合は、Layer 1 と同じように `ScopeReturn` を返す。

ここは実コードの現在の Perform 実装に合わせて port する必要がある。古い `Aborted` があるなら、value-arm / handler-arm の non-local return を `ScopeReturn` に置き換える範囲を慎重に選ぶ。

---

# もっと小さく実装したい場合

いきなり ScopeReturn/eval_id 全移植が大きすぎるなら、write26 を二段に分けるといいよ〜。

## write26-a: effectful terminators + return frames だけ

まず `EffectfulCall/Apply/Force` を実装し、TODO panic を消す。
ただし Layer 2 はまだ値 mismatch するかもしれない。

この段階で trace:

```text
repr EffectfulCall each
repr return_frames.len grows
repr resumption frames includes F_each_post / F_work_post
```

を見る。

## write26-b: ScopeReturn / eval_id / walk routing

次に Layer 1 と同型の non-local return routing を入れる。

ただ、`debugs_std_undet_once_skip_eval_layers` を一発で通したいなら、最初からまとめて port した方が早い気もする。

---

# `りなに渡す質問` への答え

## Q1. cps_repr interpreter の effectful 実装は cps_eval port でよいか

**よい、というかそれが本線**だと思うよ〜。

sync shim は危ない。write25 の成功は EffectfulCall/Force が post continuation を frame 化したおかげなので、repr interpreter でも return-frame semantics が必要。

## Q2. Step 4 narrow の generalization

今は `std::undet::undet::each*` whitelist 維持でよい。

将来の一般化は:

```text
function-level effect tracking
```

が一番バランス良さそう。

`effect annotation` は正道だけど infrastructure が重め。ad-hoc whitelist 拡張は短期には良いが、増えすぎると後で整理が大変。

段階案:

```text
write25-26:
  each whitelist

次:
  returns_thunk && callee body may perform/propagate effect && caller rest is non-empty
  くらいの function-level analysis

さらに後:
  effect row / annotation に基づく principled split
```

## Q3. walk 設計の owner check

今の条件:

```text
handler.install_eval_id == frame.owner_eval_id
handler.escape_owner_function == frame.owner_function
```

これは正しい。厳しめで安全。緩めない方がいい。

特に `escape_owner_function` は function-local continuation id の安全弁。ここを外すと別 function の cont id に飛ぶ事故が戻る。

## Q4. Pre-force condition

今の:

```text
return_frame_immediately_forces_param
```

でまず十分。

将来広げるなら、直接 `ForceThunk(param)` だけでなく:

```text
param を alias bind してから ForceThunk
param を trivial Continue で渡してから ForceThunk
```

くらいは対応余地あり。ただし今は広げない方がいい。pre-force は強い機構なので、発火条件は狭く保つのが安全だよ〜。

---

# write26 のテスト順

```bash
cargo test -p yulang-native
```

まず regression なし。

```bash
cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture
cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture
```

local semantics 維持。

本命:

```bash
RUST_BACKTRACE=1 \
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

期待する段階:

```text
Layer 1 (CPS eval): OK
Layer 2 (CPS repr eval): OK
```

もし Layer 2 が mismatch なら trace を追加:

```text
repr EffectfulCall
repr EffectfulForce
repr PerformHandlerSearch
repr ScopeReturnFrameWalk
repr FrameWalkMatch
repr ContinueReturnFrames
repr PreForceResumeTopFrame
```

Layer 1 と同じ event frontier が出るか比較する。

---

# 追加で固定したい regression

write25 の成功を守るために、`debugs_std_undet_once_skip_eval_layers` とは別に小さい tests を足すといい。

## 1. EffectfulCall が post continuation を capture する最小 test

```yu
use std::undet::*;

my work(): int = {
    my n = each [1, 2]
    guard: n > 1
    n
}

case work().once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
```

ほぼ現 test の縮小版。

## 2. Return pre-force が必要な fold_impl 系

`fold_impl Return(Thunk)` → top frame retained が必要な最小形。これは作るの難しいかもしれないけど、trace 依存ではなく test 化できると強い。

## 3. RWH legacy を壊さない test

write24 で `ResumeWithHandler` は legacy inject 維持にした。repr 側にも port するなら、RWH の regression は必ず見る。

---

# 最後に

Layer 1 到達、おめでとうだよ〜。ここまで来ると、もう「何が悪いか分からない」ではなくて、かなり明確に:

```text
cps_eval で確立した意味論を cps_repr interpreter に同期する
```

という作業だねぇ。

write26 は大きく見えるけど、設計探索ではなく移植フェーズ。
ポイントは **sync shim で済ませない**、**Layer 1 の frame/eval-id/walk/pre-force を同型に持ってくる**、この二つだと思うよ〜。
