読んだうえでの結論は、**次の実装は候補解 B、つまり `eval` 側の `initial_frame_count` refactor を本線にする**のが一番安全だと思うよ〜。

`write13-report` の状態は、`Let { value }` の `Apply` を callee type で見て `EffectfulApply` にするところまでは進んだけど、`call_callback(f) = f 0` みたいな helper 関数の中では lowering 時点に `active_handler` がなく、`f 0` が普通の `ApplyClosure` stmt になって caller の post-call continuation を捕まえられていない、という整理だねぇ。`Stmt::Expr` 側の split は Cranelift backend の `Effectful{Call,Apply,Force}` 未実装に当たるから、現時点では入れていない、という判断も妥当だよ〜。

前回 `write12` で入った return frame と `EffectfulCall / EffectfulApply / EffectfulForce` の方向自体は正しい。IR 側にもその3種の terminator はもう存在している。
ただし今の `cps_eval.rs` は、同期的な `DirectCall` / `ApplyClosure` / `ForceThunk` で callee に `Vec::new()` の `return_frames` を渡す設計になっていて、ここが Test A の根っこだねぇ。

---

## 実装方針の一言まとめ

**lowering をさらに広げない。まず eval に「親 frames を継承するが、自分では消費しない」仕組みを入れる。**

つまり、

```text
sync stmt call:
  親の return_frames を callee に渡す
  ただし callee の Return はその親 frames を consume しない

effectful terminator call:
  親の return_frames + 自分の post-cont frame を callee に渡す
  callee の Return は、自分が push した post-cont frame だけ consume できる

Resume:
  captured continuation を再生する入口なので、captured return_frames は consume できる
```

ここが一番大事。

---

# 1. まずやらないこと

別LLMには、先にこの禁止事項を渡すと誤爆が減るよ〜。

## 1.1 `Stmt::Expr` の effectful split を今すぐ有効化しない

`write13-report` にある通り、`Stmt::Expr` の `EffectfulCall` / `EffectfulApply` 化を広げると、`_through_cps_repr_cranelift` 系の既存テストが Cranelift backend の `todo!()` に当たって落ちる。

なので次の実装では、

```text
lower_handled_effectful_call_expr
lower_handled_effectful_apply_expr
```

の dead code は残してよいが、呼び出し経路はまだ有効化しない。

## 1.2 `lower_root` / `lower_apply` を雑に全部 `EffectfulApply` 化しない

候補解 A は CPS eval だけなら魅力があるけど、広げると Cranelift 側の未実装 terminator が一気に出て、既存 regression を起こす。`write13-report` でもこの問題が明記されている。

次の実装の狙いは、

```text
IR を増やさず
lowering 対象も広げず
eval の return_frames 受け渡しだけで Test A を直す
```

だねぇ。

---

# 2. 中核設計: `initial_frame_count`

## 2.1 意味

`return_frames` を単なる stack として見るのをやめて、次の2領域に分ける。

```text
return_frames[0 .. initial_frame_count]
  = この eval 呼び出しが親から継承した frames
  = Perform が起きたら resumption に含める
  = ただし、この eval の通常 Return では consume しない

return_frames[initial_frame_count ..]
  = この eval 呼び出し自身が consume してよい frames
  = EffectfulCall / EffectfulApply / EffectfulForce が push した post-cont frame など
```

別名で言うなら、

```text
prefix = inherited frames
suffix = own frames
```

だよ〜。

## 2.2 `Return` の新ルール

今の `Return` はたぶん、

```rust
if !return_frames.is_empty() {
    continue_return_frames(...)
} else {
    return Ok(value)
}
```

に近い考え方になっているはず。

これを必ずこう変える。

```rust
if return_frames.len() > initial_frame_count {
    continue_return_frames(...)
} else {
    return Ok(value)
}
```

つまり、`return_frames` が空でなくても、全部 inherited prefix なら consume しない。

これを間違えると、sync call の callee が親の continuation を勝手に奪って、親 eval がまだ生きているのに post-cont へ飛ぶ。そこが一番危ない。

---

# 3. `CpsReturnFrame` にも threshold を保存する

ここは `write13-report` の候補解 B から一段だけ補強したほうがいいところ。

`eval_continuations` に `initial_frame_count` を渡すだけだと、`continue_return_frames` が frame を pop して caller continuation を再開するときに、**再開先 eval が元々どの `initial_frame_count` で動いていたか**を復元できない。

だから `CpsReturnFrame` に field を足すのが安全。

```rust
struct CpsReturnFrame {
    owner_function: String,
    continuation: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,

    // 追加
    initial_frame_count: usize,
}
```

名前は少し長くても、誤解が少ないものがいい。

候補:

```rust
initial_frame_count
resume_initial_frame_count
owner_initial_frame_count
```

私なら `owner_initial_frame_count` が一番読みやすいと思うよ〜。
意味は「この frame の owner eval を再開するときに使う threshold」。

---

# 4. 関数 signature の変更

`cps_eval.rs` の主な eval entry に `initial_frame_count` を追加する。

## 4.1 `eval_function_with_context`

今の概念:

```rust
fn eval_function_with_context(
    module: &CpsModule,
    function: &CpsFunction,
    args: Vec<CpsRuntimeValue>,
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,
    return_frames: Vec<CpsReturnFrame>,
) -> CpsEvalResult<CpsRuntimeValue>
```

変更後:

```rust
fn eval_function_with_context(
    module: &CpsModule,
    function: &CpsFunction,
    args: Vec<CpsRuntimeValue>,
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,
    return_frames: Vec<CpsReturnFrame>,
    initial_frame_count: usize,
) -> CpsEvalResult<CpsRuntimeValue>
```

root からの通常実行は、

```rust
return_frames = Vec::new()
initial_frame_count = 0
```

## 4.2 `eval_continuations`

```rust
fn eval_continuations(
    module: &CpsModule,
    function: &CpsFunction,
    entry: CpsContinuationId,
    initial_args: Vec<CpsRuntimeValue>,
    initial_values: Vec<Option<CpsRuntimeValue>>,
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,
    return_frames: Vec<CpsReturnFrame>,
    initial_frame_count: usize,
) -> CpsEvalResult<CpsRuntimeValue>
```

`eval_continuations` は今まで通り `into_inherited(active_handlers)` を呼ぶ。
ここは変えない。

## 4.3 `resume_continuation`

```rust
fn resume_continuation(
    module: &CpsModule,
    function: &CpsFunction,
    entry: CpsContinuationId,
    initial_args: Vec<CpsRuntimeValue>,
    initial_values: Vec<Option<CpsRuntimeValue>>,
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,
    return_frames: Vec<CpsReturnFrame>,
    initial_frame_count: usize,
) -> CpsEvalResult<CpsRuntimeValue>
```

`resume_continuation` は今まで通り `into_inherited` を呼ばない。
return frame 復元時は handler の `inherited` 状態をそのまま使う必要があるからだねぇ。

---

# 5. sync stmt call の変更

ここが Test A の直接修正。

## 5.1 `DirectCall` stmt

今は sync call で callee に `Vec::new()` を渡している。
これを変える。

変更前の概念:

```rust
eval_function_with_context(
    module,
    target_function,
    call_args,
    active_handlers.clone(),
    guard_stack.clone(),
    Vec::new(),
)
```

変更後:

```rust
let inherited_frame_count = return_frames.len();

eval_function_with_context(
    module,
    target_function,
    call_args,
    active_handlers.clone(),
    guard_stack.clone(),
    return_frames.clone(),
    inherited_frame_count,
)
```

意味:

```text
parent frames は callee に見せる
Perform したら resumption に入る
ただし callee の Return は parent frames を consume しない
```

## 5.2 `ApplyClosure` stmt: Closure の場合

これが `call_callback(f) = f 0` の本命。

変更前の概念:

```rust
eval_continuations(
    module,
    owner,
    closure.entry,
    vec![arg],
    closure_values,
    active_handlers.clone(),
    guard_stack.clone(),
    Vec::new(),
)
```

変更後:

```rust
let inherited_frame_count = return_frames.len();

eval_continuations(
    module,
    owner,
    closure.entry,
    vec![arg],
    closure_values,
    active_handlers.clone(),
    guard_stack.clone(),
    return_frames.clone(),
    inherited_frame_count,
)
```

これで callback 内の `branch()` が `Perform` した時、outer の `F_work_post` みたいな frame が resumption に入る。

## 5.3 `ForceThunk` stmt

`ForceThunk` も同じ扱いにする。

変更前の概念:

```rust
eval_continuations(
    module,
    owner,
    thunk.entry,
    Vec::new(),
    thunk.values.as_ref().clone(),
    handlers,
    guards,
    Vec::new(),
)
```

変更後:

```rust
let inherited_frame_count = return_frames.len();

eval_continuations(
    module,
    owner,
    thunk.entry,
    Vec::new(),
    thunk.values.as_ref().clone(),
    handlers,
    guards,
    return_frames.clone(),
    inherited_frame_count,
)
```

`ForceThunk` は `EffectfulForce` の代替ではないけど、sync force の中で `Perform` が起きた時に outer frames を resumption へ含める意味がある。

---

# 6. effectful terminator 側の変更

`EffectfulCall / EffectfulApply / EffectfulForce` は、今まで通り post-cont frame を push する。
ただし、callee に渡す `initial_frame_count` と、frame に保存する `owner_initial_frame_count` を明確に分ける。

## 6.1 frame 作成時

現在の eval loop が持っている値を `current_initial_frame_count` と呼ぶ。

```rust
let owner_initial_frame_count = initial_frame_count;
let pre_push_count = return_frames.len();

let frame = CpsReturnFrame {
    owner_function: function.name.clone(),
    continuation: resume,
    values: Rc::new(values.clone()),
    active_handlers: active_handlers.clone(),
    guard_stack: guard_stack.clone(),
    owner_initial_frame_count,
};

let mut frames = return_frames.clone();
frames.push(frame);
```

## 6.2 callee へ渡す threshold

Effectful terminator の callee は、今 push した frame を consume できないといけない。

だから callee に渡す threshold は、

```rust
initial_frame_count = pre_push_count
```

だよ〜。

ここで `frames.len()` を渡すと壊れる。
`frames.len()` は push 後の長さだから、callee の `Return` が今 push した frame を consume できなくなる。

## 6.3 まとめ

```text
frame.owner_initial_frame_count = 現在の eval の initial_frame_count
callee.initial_frame_count      = push 前の return_frames.len()
```

この2つは違う値になりうる。
ここを別LLMに強く言っておくといいねぇ。

---

# 7. `continue_return_frames` の変更

既存の `continue_return_frames` は、たぶん last frame を pop して owner continuation を `resume_continuation` で再開しているはず。

変更後は、pop した frame の `owner_initial_frame_count` を `resume_continuation` に渡す。

概念コード:

```rust
fn continue_return_frames(
    module: &CpsModule,
    mut return_frames: Vec<CpsReturnFrame>,
    value: CpsRuntimeValue,
) -> CpsEvalResult<CpsRuntimeValue> {
    let frame = return_frames
        .pop()
        .expect("Return tried to consume a frame but none existed");

    debug_assert!(frame.owner_initial_frame_count <= return_frames.len());

    let owner = function_by_name(module, &frame.owner_function)?;

    resume_continuation(
        module,
        owner,
        frame.continuation,
        vec![value],
        frame.values.as_ref().clone(),
        frame.active_handlers,
        frame.guard_stack,
        return_frames,
        frame.owner_initial_frame_count,
    )
}
```

`debug_assert!` は入れておくと事故検知に役立つよ〜。

---

# 8. Resume 系の扱い

ここは特に誤解されやすい。

## 8.1 `Resume(k, arg)` は sync call ではない

`Resume` は「今の親 eval が生きているから inherited frames を consume しない」ではない。

`k` は captured continuation そのもの。
だから `k` の `return_frames` は、再生時に consume できないといけない。

なので `Resume` / `ResumeWithHandler` / `ApplyClosure(Resumption)` で `resumption.return_frames` を渡す時は、

```rust
initial_frame_count = 0
```

にする。

## 8.2 extras injection は維持

`write12-report` で入った extras injection はそのまま残す。
`Resume` site の `active_handlers` にあって `k.handlers` にない handler を extras として集め、`inject_extra_handlers` で return frames に注入する仕組みだねぇ。

つまり変更後の概念はこう。

```rust
let adjusted_frames = inject_extra_handlers(resumption.return_frames.as_ref(), &extra);

eval_continuations(
    module,
    owner,
    resumption.target,
    vec![CpsRuntimeValue::Plain(arg)],
    resumption.values.as_ref().clone(),
    resumed_handlers,
    resumption.guard_stack.as_ref().clone(),
    adjusted_frames,
    0, // Resume は captured frames を consume してよい
)
```

## 8.3 `CpsResumption` に `initial_frame_count` は足さなくてよい

少なくとも次の実装では、`CpsResumption` に threshold を保存しないほうが分かりやすい。

理由:

```text
sync call 中:
  inherited frames は callee Return では consume しない

Perform で捕まった resumption を Resume する時:
  captured continuation を handler boundary まで再生するので、frames は consume する
```

つまり「捕まった時の initial」を保存して再利用すると、逆に `Resume` が outer frames を消費できなくなる危険がある。

---

# 9. Test A で期待する具体的な流れ

別LLMにはこのモデルを渡すと、かなり迷いにくいよ〜。

対象:

```text
call_callback(f) = f 0

work():
  n = call_callback(callback)
  if n == 1:
    reject()
  else:
    n
```

期待値:

```text
2
```

## 9.1 実行イメージ

```text
work が call_callback を effectful call する
  F_work_post を return_frames に push
  call_callback に frames=[F_work_post], initial=0 を渡す

call_callback 内で sync ApplyClosure f 0
  callback に frames=[F_work_post], initial=1 を渡す
  initial=1 なので callback の通常 Return は F_work_post を consume しない

callback 内で branch() が Perform
  resumption k に frames=[F_work_post] が入る

once handler が k true を Resume
  Resume は frames=[F_work_post], initial=0 で再生する
  callback が 1 を返す
  Return が F_work_post を consume
  work の post-call continuation へ戻る
  n=1 なので reject

once handler が k false を Resume
  また frames=[F_work_post], initial=0 で再生する
  callback が 2 を返す
  Return が F_work_post を consume
  work の post-call continuation へ戻る
  n=2 なので 2 を返す
```

Test A が `cps:1` から `cps:2` になるなら、この refactor は狙い通り。

---

# 10. 変更ファイルの優先順位

## 最優先

```text
crates/yulang-native/src/cps_eval.rs
```

ここだけで Test A が直る可能性が高い。

## 必要になりやすい補助変更

```text
CpsReturnFrame 定義がある同じファイル
inject_extra_handlers
continue_return_frames
EffectfulCall / EffectfulApply / EffectfulForce eval branch
Resume / ResumeWithHandler / ApplyClosure(Resumption) eval branch
DirectCall / ApplyClosure / ForceThunk stmt branch
```

## 基本的に触らない

```text
crates/yulang-native/src/cps_lower.rs
crates/yulang-native/src/cps_ir.rs
crates/yulang-native/src/cps_repr.rs
crates/yulang-native/src/cps_repr_cranelift.rs
```

`cps_ir.rs` は既に `EffectfulCall / EffectfulApply / EffectfulForce` を持っているので、今回の `initial_frame_count` だけなら変更不要のはず。

---

# 11. 実装後に走らせるテスト順

## 11.1 まず targeted test

```text
debugs_local_choice_callback_rest_eval
```

期待:

```text
vm: 2
cps: 2
```

ここが通らないなら、`initial_frame_count` の渡し方がまだおかしい。

## 11.2 次に既存 local minimal

```text
debugs_local_choice_caller_rest_eval
```

期待:

```text
引き続き PASS
```

`write12-report` で通っていたテストなので、これが落ちたら `EffectfulCall` 側の threshold が間違っている可能性が高い。

## 11.3 既存全体

```text
既存 170 テスト
```

期待:

```text
regression なし
```

この refactor は IR を増やさないので、Cranelift の `todo!()` に新しく当たる可能性は低いはず。

## 11.4 最後に std once

```text
debugs_std_undet_once_skip_eval_layers
```

期待は `2` だけど、ここはまだ落ちても不思議ではない。

理由は、`std::undet.once` / `each` / `fold` では、callback apply の「ローカルな後続計算」まで resumption に必要になる可能性があるから。`initial_frame_count` refactor は outer return frames の継承を直すが、`fold_impl` 内の非 tail `ApplyClosure` の local rest を完全に捕まえるとは限らない。

---

# 12. 落ちた時の切り分け

一時 trace を入れるなら、次の場所だけで十分。

```text
eval entry:
  function, entry, return_frames.len(), initial_frame_count

sync DirectCall / ApplyClosure / ForceThunk:
  before call len
  passed initial = len

EffectfulCall / EffectfulApply / EffectfulForce:
  pre_push_count
  pushed frame owner_initial_frame_count
  callee initial = pre_push_count

Return:
  len
  initial
  consumeするか

Perform:
  captured return_frames.len()

Resume / ResumeWithHandler / ApplyClosure(Resumption):
  adjusted_frames.len()
  initial = 0
```

## Test A で見るべきログ

```text
callback 内 branch Perform:
  captured return_frames.len() >= 1
```

これが `0` なら、sync `ApplyClosure` が parent frames を渡していない。

```text
callback の通常 Return:
  len == initial
  consumeしない
```

これが consume していたら、sync call の `initial_frame_count` が間違い。

```text
Resume(k false):
  initial = 0
```

これが `return_frames.len()` になっていたら、resumption replay が outer frames を consume できない。

---

# 13. std once がまだ落ちた場合の次段階

Test A が通って、`std::undet.once` だけまだ落ちるなら、次の判断になる。

## 13.1 trace で `fold_impl` の callback apply を見る

確認したいこと:

```text
branch Perform inside fold callback:
  return_frames に work / each / sub / fold 由来の frame が入っているか
```

もし outer frame は入っているが、fold の「次の要素へ進む rest」が入っていないなら、問題は `initial_frame_count` ではなく、

```text
非 tail の sync ApplyClosure の local continuation が resumption に入らない
```

という別問題。

この場合は次段階で、`fold_impl` の `f z x` のような call site を `EffectfulApply` terminator にする必要が出る。

ただし、これは Cranelift regression とぶつかるので、今回の修正に混ぜないほうがいい。

## 13.2 次段階の候補

優先順はこう。

```text
1. eval initial_frame_count refactor で Test A を通す
2. std once の trace を取る
3. local rest が欠けていると確定したら、targeted EffectfulApply lowering を検討
4. その時点で cps_repr / Cranelift の扱いも一緒に決める
```

`Stmt::Expr` split や global `EffectfulApply` 化を焦って入れると、また Cranelift の既存テストで落ちる。ここは分けたほうがいいねぇ。

---

# 14. `りなに渡す質問` への私の答え

## Q1. 候補解 B は方向として正しいか

**正しいと思うよ〜。**
ただし、`eval_continuations` に `initial_frame_count` を足すだけでなく、`CpsReturnFrame` に `owner_initial_frame_count` も保存するのが安全。

## Q2. inherit するが consume しない分離は IR に表すべきか

今は **IR ではなく evaluator semantics に表せば十分**。

IR 上は今まで通り、

```text
CpsStmt::ApplyClosure
CpsTerminator::EffectfulApply
```

の区別でよい。

意味づけは eval 側でこう決める。

```text
CpsStmt::* call:
  return_frames を inherit
  initial = return_frames.len()

CpsTerminator::Effectful*:
  post-cont frame を push
  initial = push 前の return_frames.len()
```

## Q3. Resume の frame consumption 方針

**auto-trigger + extras injection + Resume initial=0** が今は一番自然。

`Resume` は同期関数呼び出しではなく、captured continuation の再生。
だから captured `return_frames` は consume できないといけない。

## Q4. `EffectfulForce` を広げると Test A が通るか

Test A の本体は `call_callback` 内の `f 0` なので、直接の原因は `Force` ではなく `ApplyClosure`。

`EffectfulForce` は必要な機構だけど、Test A の `f 0` を `EffectfulForce` で扱うのは違う。
Test A を直す最小修正は、sync `ApplyClosure` が parent `return_frames` を inherit し、通常 Return では consume しないようにすることだねぇ。

---

# 15. 別LLMにそのまま渡せる指示文

```text
目的:
  notes/todo/native-undet-write13-report.md の残課題 Test A
  debugs_local_choice_callback_rest_eval を通す。
  期待値は vm:2 / cps:2。

方針:
  lowering を広げない。
  Stmt::Expr の EffectfulCall / EffectfulApply split を有効化しない。
  lower_root / lower_apply を global に EffectfulApply 化しない。
  Cranelift backend 未実装 terminator に新しく当てない。

実装すること:
  cps_eval.rs に initial_frame_count を導入する。
  return_frames を inherited prefix と own suffix に分ける。

定義:
  return_frames[0 .. initial_frame_count] は inherited frames。
  Perform が起きたら resumption に含める。
  ただし現在の eval の通常 Return では consume しない。

  return_frames[initial_frame_count ..] は own frames。
  Return が consume してよい。

CpsReturnFrame:
  owner_initial_frame_count: usize を追加する。
  EffectfulCall / EffectfulApply / EffectfulForce が frame を作る時、
  現在の eval の initial_frame_count を owner_initial_frame_count に保存する。

Return:
  if return_frames.len() > initial_frame_count {
      continue_return_frames(...)
  } else {
      return Ok(value)
  }

continue_return_frames:
  last frame を pop する。
  frame.owner_function / frame.continuation / frame.values /
  frame.active_handlers / frame.guard_stack を復元する。
  resume_continuation を呼ぶ時、initial_frame_count には
  frame.owner_initial_frame_count を渡す。

sync DirectCall stmt:
  callee に return_frames.clone() を渡す。
  callee の initial_frame_count は return_frames.len() にする。

sync ApplyClosure stmt の Closure 分岐:
  callee に return_frames.clone() を渡す。
  callee の initial_frame_count は return_frames.len() にする。

sync ForceThunk stmt:
  thunk body に return_frames.clone() を渡す。
  thunk body の initial_frame_count は return_frames.len() にする。

EffectfulCall / EffectfulApply / EffectfulForce:
  pre_push_count = return_frames.len() を取る。
  CpsReturnFrame を push する。
  push する frame の owner_initial_frame_count は現在の initial_frame_count。
  callee に渡す initial_frame_count は pre_push_count。
  push 後の frames.len() を渡してはいけない。

Resume / ResumeWithHandler / ApplyClosure(Resumption):
  extras injection は維持する。
  adjusted_frames を渡す。
  initial_frame_count は 0 にする。
  Resume は sync call ではなく captured continuation の再生なので、
  captured return_frames は consume できる必要がある。

テスト:
  1. debugs_local_choice_callback_rest_eval
     期待 cps:2 / vm:2
  2. debugs_local_choice_caller_rest_eval
     既存 PASS を維持
  3. 既存 170 テスト
     regression なし
  4. debugs_std_undet_once_skip_eval_layers
     通ればよいが、まだ落ちても次段階で切り分ける

落ちた時:
  trace を一時的に入れる。
  Perform 時の captured return_frames.len()
  Return 時の len / initial / consume有無
  Resume 時の adjusted_frames.len() / initial=0
  Effectful terminator 時の pre_push_count / owner_initial_frame_count
  を見る。

特に Test A では:
  callback 内 branch Perform で captured return_frames.len() >= 1 になる必要がある。
  sync callback Return では len == initial で consume しない必要がある。
  Resume(k false) では initial=0 で F_work_post を consume する必要がある。
```

この順でやるのが一番誤爆が少ないと思うよ〜。
大事なのは、**「sync call に frames を渡す」ことと「sync call の Return ではそれを消費しない」ことを同時に入れる**ところだねぇ。片方だけ入ると、すぐ別の continuation が壊れる。
