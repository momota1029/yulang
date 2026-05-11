見たよ〜。write24 はまた一段かなり進んでる。特に **anchor-based merge で `[outer, inner, H_sub]` の順序まで直った**のは大きいねぇ。`PerformHandlerSearch` trace でも `sub::return` が `[outer, inner, H_sub]` の stack から H_sub を拾っているので、handler order の問題はほぼ片付いたと見ていいと思うよ〜。

ただし、write24 自身の観察通り、まだ `cps:0 / vm:2`。理由はもう「merge order」ではなく、**ScopeReturn が call-stack で eval=8 へ戻るせいで、eval=24 側にある modified return frame が使われない**ところだねぇ。Step 4 の targeted EffectfulCall 試行で `F_work_post` は captured chain に入ったのに、それでも cps:0 のままだったのは、この診断をかなり強く支持している。

## 結論

write25 は、私はこう進めるのが一番安全だと思う。

```text
1. Step 5: ScopeReturn を current eval の own return_frames から walk して解決する機構を先に入れる
2. その機構が動く trace を確認する
3. その後で Step 4 targeted EffectfulCall lowering を、std::undet.each 周辺に強く絞って再投入する
4. SR.preserved_handlers はまだ入れない
```

write24 report は「案 C = Step 4 + walk-based propagation」を本線に見ているけど、実装順としては **walk-based propagation 先** がよさそうだよ〜。Step 4 は regression が出て revert されているから、まず evaluator 側に「modified frame を実際に使える経路」を作ってから、狭い lowering を戻す方が切り分けやすい。

---

# 現状で確定したこと

## 1. eval id / strict ScopeReturn は維持

write22 の `install_eval_id == current_eval_id` は正しい土台。現コードでも `handle_scope_return` は prompt と eval id の一致で match している。ここは戻さない。

```rust
frame.prompt == prompt && frame.install_eval_id == current_eval_id
```

write21 の `escape_owner_function == current_function` loose check は、早すぎる H_sub match を起こした原因だから戻さない。

## 2. Return inherited preservation も維持

write23 で `Return` が full `return_frames` を `continue_return_frames` へ渡すようになり、F_each_post が captured chain に入った。これで resumption frames が 1 → 2 に増えた。これは正しい修正だねぇ。

## 3. anchor-based merge も維持

write24 で `CpsHandlerAnchor` / `CpsResumption.handled_anchor` が入り、`captured=[outer,H_sub]`, `current=[inner]`, `anchor=outer` から `merged=[outer,inner,H_sub]` が作れるようになった。`PerformHandlerSearch` も H_sub match を確認している。

ここまでの 3 つは積み上げとして残す。

---

# いま本当に足りないもの

問題はこの一点。

```text
eval=24 の return_frames には modified frame がある
でも ScopeReturn は call-stack Propagate で eval=8 へ戻る
その eval=8 が使う active_handlers は original snapshot
だから modified F_work_post / modified F_each_post が使われない
```

write24 の trace 解釈にある通り、Step 4 試行では `return_frames.len=3` / `Resumption(... frames=3 ...)` まで行き、F_work_post が captured chain に入った。それでも `ScopeReturnDispatch eval=8` で match してしまい、eval=24 側の modified frame を使わない。

だから write25 の中核は、**ScopeReturn propagation を call-stack だけに頼らず、current eval の own return_frames を見に行く**ことだよ〜。

---

# write25 実装案：walk-based ScopeReturn routing

## 方針

`dispatch_scope_return!` の `Propagate(v)` 分岐で、すぐ `return Ok(v)` しない。

まず:

```text
現在 eval の return_frames[initial_frame_count..] を innermost から outermost へ walk
```

して、`ScopeReturn(prompt=p)` を解決できる frame があるか探す。

重要なのは **inherited prefix は walk しない** こと。

```text
return_frames[0..initial_frame_count]
  = sync call から見えているだけの inherited frames
  = 現在 eval が勝手に consume / route してはいけない

return_frames[initial_frame_count..]
  = 現在 eval 自身が持つ own frames
  = Resume eval なら captured chain と post frames
  = ここは walk してよい
```

これは write14/write23 の `initial_frame_count` 意味論と揃う。

---

## 追加 helper の形

```rust
fn try_route_scope_return_through_return_frames(
    module: &CpsModule,
    scope_return: CpsRuntimeValue,
    return_frames: &[CpsReturnFrame],
    initial_frame_count: usize,
) -> CpsEvalResult<Option<CpsRuntimeValue>> {
    // ScopeReturn 以外なら None
    // match できなければ None
    // match できたら routed result を Some(result) で返す
}
```

`CpsRuntimeValue::ScopeReturn` の中身を取り出す。

```rust
let CpsRuntimeValue::ScopeReturn { prompt, target, value } = scope_return else {
    return Ok(None);
};
```

`return_frames[initial_frame_count..]` を reverse walk する。

```rust
for frame_index in (initial_frame_count..return_frames.len()).rev() {
    let frame = &return_frames[frame_index];

    // この frame を復元した時の current_eval_id は frame.owner_eval_id
    let frame_eval_id = frame.owner_eval_id;
    let frame_function = &frame.owner_function;

    let mut handlers = frame.active_handlers.clone();

    if let Some(handler_index) = handlers.iter().rposition(|handler| {
        handler.prompt == prompt
            && handler.install_eval_id == frame_eval_id
    }) {
        ...
    }
}
```

この `handler.install_eval_id == frame.owner_eval_id` が大事。

eval=24 の local `return_frames` に modified F_each_post があるなら:

```text
frame.owner_function = each
frame.owner_eval_id = 8
frame.active_handlers = [outer, inner, H_sub]
H_sub.install_eval_id = 8
```

なのでここで H_sub を拾える。

---

## owner check

既存の owner check と同じ考えでよい。

```rust
let owner_match =
    target == EXIT_RWH_TARGET || handler.escape_owner_function == frame.owner_function;
```

ただし、write25 初手では `EXIT_RWH_TARGET` は無理に walk routing しなくていいと思う。まず H_sub の通常 escape を通す。

```rust
if target == EXIT_RWH_TARGET {
    trace_cps("ScopeReturnFrameWalk", "skip EXIT_RWH_TARGET for now");
    continue;
}
```

今回の本命は `H_sub.escape = each cont 2` だから、ここで十分。

---

## match した時の frame 復元

match したら、handler より内側の handlers を捨てる。

```rust
let matched_handler = handlers[handler_index].clone();
handlers.truncate(handler_index);
```

`[outer, inner, H_sub]` なら truncate 後:

```text
[outer, inner]
```

これが狙い。H_sub で abort した後も inner once が残る。

次に return frames を切る。

```rust
let mut rest_frames = return_frames[..frame_index].to_vec();
if rest_frames.len() > matched_handler.return_frame_threshold {
    rest_frames.truncate(matched_handler.return_frame_threshold);
}
```

ただし、ここは trace で確認しながら少し慎重に。`return_frame_threshold` が frame-local か global stack length かでズレる可能性がある。最初は両方 trace する。

```text
FrameWalkMatch:
  frame_index=<i>
  rest_before=<len>
  threshold=<handler.return_frame_threshold>
  rest_after=<len>
```

---

## escape continuation を走らせる

`handler.escape_owner_function` の function を取り、`handler.escape` へ jump する。

```rust
let owner = function_by_name(module, &matched_handler.escape_owner_function)?;

let result = resume_continuation(
    module,
    owner,
    matched_handler.escape,
    vec![*value],
    frame.values.as_ref().clone(),
    handlers,
    frame.guard_stack.clone(),
    rest_frames,
    frame.owner_initial_frame_count,
    frame.owner_eval_id,
)?;
```

ここで `owner` は `frame.owner_function` と一致するはず。H_sub なら each。

念のため debug assert:

```rust
debug_assert_eq!(matched_handler.escape_owner_function, frame.owner_function);
debug_assert_eq!(matched_handler.install_eval_id, frame.owner_eval_id);
```

この assert が落ちるなら、frame walk が「handler の install eval を復元できない frame」で match している。そこでは処理しない方が安全。

---

## dispatch_scope_return! への組み込み

今の macro は `Propagate(v) => return Ok(v)` だと思う。そこをこうする。

```rust
ScopeReturnAction::Propagate(v) => {
    if let Some(routed) = try_route_scope_return_through_return_frames(
        module,
        v.clone(),
        &return_frames,
        initial_frame_count,
    )? {
        return Ok(routed);
    }
    return Ok(v);
}
```

`v.clone()` が重いなら match で所有権を渡して、失敗時に返す形にする。

### 重要な gate

```rust
if return_frames.len() <= initial_frame_count {
    return Ok(v);
}
```

sync callee が inherited frames しか持っていない時は walk しない。ここを守らないと、親 eval が alive なのに子 eval が勝手に親 frames を consume する。

---

# trace 期待値

write25 Step 5 だけを入れた状態で、まず trace を見る。

```text
Perform sub::return eval=24
  active_handlers=[outer, inner, H_sub]
  return_frames.len=2 or 3
  initial=0

ScopeReturnDispatch eval=24 prompt=1 matched=no Propagate
ScopeReturnFrameWalk eval=24 prompt=1 own_frames=...
FrameWalkMatch frame_owner=each owner_eval=8 handler=H_sub
  handlers_before=[outer, inner, H_sub]
  handlers_after=[outer, inner]
  action=JumpOrExit escape=each cont2
```

ここまで見えれば、call-stack の eval=8 original snapshot を使わずに、eval=24 local modified frame を使えている。

---

# Step 5 だけで cps:2 になるか

たぶん **まだならない**可能性が高い。

理由は write24 report の通り、F_work_post は Step 4 試行時だけ captured chain に入った。revert 後の現状は frames=2 で、work の post-call continuation は sync DirectCall の親 eval=7 に残っている。

ただし Step 5 を先に入れる価値は大きい。

```text
Step 5 なし:
  Step 4 で F_work_post を入れても modified frame を使えない

Step 5 あり:
  Step 4 を戻した時、modified F_work_post を使える可能性が出る
```

なので Step 5 は「単独で final fix」ではなく、「Step 4 を意味あるものにする基盤」だねぇ。

---

# Step 4 targeted lowering の再投入方針

Step 5 が trace 上で動いたら、Step 4 を戻す。ただし write24 の広い条件は駄目。

write24 の試行条件:

```text
info_returns_thunk && demand_is_non_thunk
```

これは広すぎて regression 2 件が出た。

## 最初の再投入は std::undet.each に絞る

最初は汎用 effect tracking をやらない方がいい。

```rust
let target_is_std_undet_each =
    path_name(&target).contains("std::undet::undet::each");
```

実際の monomorphized name に合わせる。`each__mono` でもよい。

条件:

```text
target is std::undet::undet::each*
and info_returns_thunk
and demand_is_non_thunk
```

これで work の:

```text
DirectCall each -> ForceThunk -> guard
```

だけを effectful split する。

### なぜこの狭さでよいか

この bug は `std::undet.each` + `std::undet.once` の統合バグ。すでに `std::list::fold_impl` や `std::undet::once` には targeted helper が入っている流れがある。ここで最初から汎用化しようとすると、write24 と同じ regression が出やすい。

## split 形

現在:

```text
DirectCall each(args) -> t
ForceThunk(t) -> n
rest: guard; return n
```

期待:

```text
EffectfulCall each(args), resume=cont_after_each_call

cont_after_each_call(t):
  EffectfulForce t, resume=cont_after_each_force

cont_after_each_force(n):
  rest: guard; return n
```

ここで `F_work_post` が return frame になる。

期待 trace:

```text
Perform branch ... return_frames.len=3
Resumption(... frames=3 ...)
Resume eval=24 return_frames.len=3
FrameWalkMatch H_sub in F_each_post modified
ContinueReturnFrames pop F_work_post modified
work cont_after_each_force active_handlers=[outer, inner]
Perform reject matched_prompt=inner once
```

これが見えれば `cps:2` へかなり近い。

---

# 汎用 effect tracking は後

write24 の質問では `(a) lowering 中に caller continuation を先読み`, `(b) function info の effect annotation`, `(c) 別方法` が挙がっている。

私の答えは:

```text
write25 では (c) path-targeted gate
write26 以降で (b) effect annotation
```

が良いと思う。

理由:

* `(a)` continuation 先読みは lowering 中の state と相性が悪く、誤判定しやすい
* `(b)` effect annotation は正道だけど、今入れるには範囲が広い
* 今必要なのは `std::undet.each` の direct thunk call を 1 箇所 return-frame 化すること

後で汎用化する時は、runtime type/effect の情報から:

```text
callee returns Thunk with residual effect E
caller rest may perform / handle E
```

を見て EffectfulCall にするのが筋だねぇ。

---

# SR.preserved_handlers はまだ入れない

write23/write24 で何度か出ている `SR.preserved_handlers` は、まだ後回しでいいと思う。

理由:

```text
eval=24 local return_frames に modified copy がもうある
なら、その modified copy を walk して使う方が直接的
```

`preserved_handlers` は call-stack propagation に handler delta を載せる設計で、広く効きすぎる可能性がある。まずは `return_frames` に既に入っている modified frame を使うだけに絞る方が安全。

---

# 実装LLMに渡す短い指示文

```text
write24 の anchor-based handler merge は維持する。
write22 の eval_id strict ScopeReturn check も維持する。
Return inherited preservation も維持する。
write21 loose match / write17 pre-force は戻さない。

write25 の最初の実装は walk-based ScopeReturn routing。

dispatch_scope_return! で handle_scope_return が Propagate を返した時、
すぐ return Ok(ScopeReturn) しない。
現在 eval の return_frames[initial_frame_count..] を innermost から walk し、
frame.owner_eval_id と handler.install_eval_id が一致する handler frame を探す。

match 条件:
  handler.prompt == prompt
  handler.install_eval_id == frame.owner_eval_id
  target != EXIT_RWH_TARGET
  handler.escape_owner_function == frame.owner_function

match したら:
  frame.active_handlers を clone
  handler_index で truncate して handler より内側を捨てる
  rest_frames = return_frames[..frame_index]
  return_frame_threshold に従って rest_frames を truncate
  handler.escape_owner_function の function を取り、
  resume_continuation(
      owner,
      handler.escape,
      vec![value],
      frame.values,
      truncated_handlers,
      frame.guard_stack,
      rest_frames,
      frame.owner_initial_frame_count,
      frame.owner_eval_id,
  )
  を呼ぶ。

sync call 由来の inherited prefix は walk しない。
return_frames.len() <= initial_frame_count ならそのまま Propagate。

trace:
  ScopeReturnFrameWalk
  FrameWalkMatch
  handlers_before/after
  frame_owner / frame_owner_eval
  threshold / rest_before / rest_after

この Step 5 を入れた後、targeted EffectfulCall lowering を再投入する。
ただし write24 の info_returns_thunk && demand_is_non_thunk は広すぎるので使わない。
最初は target が std::undet::undet::each* の direct call に限定する。
DirectCall each -> ForceThunk を EffectfulCall -> EffectfulForce に split し、
work の guard 以降を F_work_post として captured chain に入れる。
```

---

# 成功判定

## Step 5 成功

```text
ScopeReturnFrameWalk eval=24 prompt=1
FrameWalkMatch frame_owner=each owner_eval=8
handlers_before=[outer, inner, H_sub]
handlers_after=[outer, inner]
```

この時点で「modified F_each_post を使える」ことが確定。

## Step 4 再投入後の成功

```text
Perform branch return_frames.len=3
Resumption(... frames=3 ...)
Resume eval=24 return_frames.len=3

FrameWalkMatch H_sub in each frame
ContinueReturnFrames pop F_work_post with active_handlers=[outer, inner]

Perform reject effect=reject
PerformHandlerSearch matched_prompt=2 matched_owner=once
```

ここまで行けば、あとは queue=[k1] の replay に進むはず。

---

# 最後の見立て

write24 で「handler stack の順序」は片付いた。
write23 で「F_each_post capture」も片付いた。
残りは **ScopeReturn routing が modified captured frames を使っていない**ことと、**work の post-call continuation が frame 化されていない**こと。

だから write25 はこの二段構えだねぇ。

```text
Step 5 walk-based routing
→ narrow Step 4 std::undet.each-only EffectfulCall lowering
```

この順が一番、regression を見ながら進めやすいと思うよ〜。
