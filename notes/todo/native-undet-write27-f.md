読んだよ〜。これはかなり決定的な前進だねぇ。write27-d の `cps_cranelift=0` は「inner once が消えて意味論が崩れる」だったけど、write27-e は **SR / resumption / anchor merge の本筋を抜けて、最後に heap pointer が返っている**状態。つまり frontier が effect handler 意味論から value/codegen 側へ移った、と見てよさそう。report でも handler stack 膨張の根治、`apply_closure_i64` / `force_thunk_i64` / `resume_i64` の Layer 2 整合、そして `frame_walk match` まで到達したことが整理されている。

ただ、次の一手は少し慎重に切り分けたい。report は「外側 case の `just v -> v` で v を取り出すところで詰まっている感じ」と読んでいるけど、私はまずこう見る。

> 最終 heap pointer は「Variant unwrap codegen が壊れている」だけとは限らない。
> `opt::just 2` を値として返す ScopeReturn が、outer case の continuation まで route されず root へ propagate している可能性も高い。

つまり write27-f は、いきなり `VariantPayload` を直すより、まず **heap pointer が outer case continuation に渡っているのか、それとも ScopeReturn として root まで逃げているのか** を切り分けるのが良いよ〜。

---

# 今回の到達点

write27-e で直ったこと:

```text
- apply_closure_i64 が closure.handlers を append して stack 膨張していた問題を修正
- force_thunk_i64 も Layer 2 と同じ「caller stack があれば caller 優先」へ修正
- resume_i64 に anchor merge + return_frames merge を導入
- PendingEnv synthetic shadow のような症状から、RealInstall path へ移行
- sub::return value=1 / value=2 が SR で走り、frame_walk match まで到達
```

これはかなり大きい。特に `route_scope_return action=frame_walk` が出ているのは、Layer 1/2 の勝ち筋と揃っている。

残り:

```text
Layer 3 result = heap pointer
VM result = 2
```

この heap pointer が何者かを特定するのが write27-f の最初の仕事だねぇ。

---

# 最初にやる切り分け

## A. 純粋な variant case が JIT で通るか

まず effect なしで `Variant` / `VariantTagEq` / `VariantPayload` が壊れていないかを見る。

source 案:

```yu
case std::opt::opt::just 2:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
```

これが `cps_repr_cranelift=2` なら、variant destructuring codegen は基本的に生きている。
これが heap pointer を返すなら、`VariantPayload` / case lowering / payload representation が本体。

さらに標準 opt を避けた最小形も欲しい。

```yu
case :just 2:
    :nil -> 0
    :just v -> v
```

もし syntax 的に通るなら、std の `opt` constructor wrapper を除外できる。

## B. effect なしで `once` の value arm だけ通るか

`branch/reject/each/sub` を外して、`once` の value arm が `just v` を返し、外側 case が unwrap できるかを見る。

```yu
use std::undet.*

case ({ 2 }).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
```

または syntax に合わせて:

```yu
use std::undet.*

case (2).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
```

ここが heap pointer なら、`once` value arm の `ScopeReturn(value=just 2)` が outer case へ正しく route されていない疑いが強い。

## C. `each [2]` + once で guard なし

```yu
use std::undet.*

case (each [2]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
```

これで heap pointer なら、handler/value-arm/SR/outer-case の interaction が本体。
これが 2 なら、guard/reject/backtrack 後の最後の route だけが壊れている。

---

# trace を足す場所

## 1. variant helper trace

JIT helper に `YULANG_CPS_JIT_TRACE=1` で出す。

```text
variant_new:
  tag=<tag_id or name>
  payload=<i64>
  result_ptr=<ptr>

variant_tag_eq:
  value=<ptr>
  expected_tag=<tag>
  actual_tag=<tag>
  result=<0/1>

variant_payload:
  value=<ptr>
  payload=<i64>
```

特に最後の heap pointer について:

```text
value_describe:
  ptr=<heap_ptr>
  kind=Variant
  tag=std::opt::opt::just
  payload=<payload>
```

みたいな helper があると最高。
`scope_return_set value=<heap_ptr>` の value が本当に `opt::just 2` なのか、`opt::just (heap-wrapped 2)` なのか、あるいは別 variant なのかを見たい。

## 2. outer case continuation trace

`VariantTagEq` / `VariantPayload` の codegen だけでなく、outer case の branch continuation が実行されているかを見る。

```text
ContinuationEnter:
  function=root or work caller
  cont=<id>
  env=<...>
  arg=<...>

Branch:
  cond=<0/1>
  then=<cont>
  else=<cont>
```

もし `scope_return_set value=<heap_ptr>` の後に outer case の `VariantTagEq` trace が出ないなら、variant codegen ではなく **ScopeReturn が outer case continuation まで届いていない**。

## 3. route_scope_return の no-match 理由

最後の heap pointer の `scope_return_set` で:

```text
route_scope_return action=propagate
```

とある。ここが一番怪しい。

route の no-match 時に、候補を全部出す。

```text
route_scope_return.propagate:
  sr_prompt=<p>
  sr_value=<heap_ptr>
  current_eval=<eval>
  current_handlers=[
    idx=0 h1(p=..., ev=..., origin=..., escape=...)
    ...
  ]
  return_frames=[
    fi=0 owner_eval=... handlers=[...]
    ...
  ]
  reason:
    no prompt match | prompt match but eval mismatch | escape_cont=0 | synthetic
```

これで、`opt::just` を返す once handler の ScopeReturn がなぜ handler prompt に match しないのか見える。

---

# 私の本命仮説

現時点の最有力はこれ。

```text
final opt::just 2 は正しく構築されている。
でも、その value-arm natural return を表す ScopeReturn が、
outer case の post-continuation まで route されず、root まで propagate している。
そのため root が opt::just heap pointer を i64 として返している。
```

理由は、report の最後に:

```text
scope_return_set value=<heap pointer>
route_scope_return action=propagate
```

とあるから。

もし外側 case が本当に走っていて `VariantPayload` が壊れているなら、`scope_return_set` ではなく `variant_payload` の payload が heap pointerになる trace が出るはず。

だから write27-f の第一目標は:

```text
final heap pointer が root value として返る直前に、
outer case の continuation が実行されたか？
```

を確定することだよ〜。

---

# ありそうな具体バグ

## 1. value arm の ScopeReturn prompt が synthetic / stale prompt

`once` の value arm `v -> just v` の natural return は、handler install prompt に対する ScopeReturn になるはず。

もし JIT の `perform_finish` や handler value completion で:

```text
prompt=selected prompt
```

ではなく、古い selected meta / outer snapshot / synthetic prompt を使っていると、route できず propagate する。

見る trace:

```text
scope_return_set:
  prompt=<p>
  value=<opt just ptr>
  selected_meta=<...>
  handler stack has p?
```

## 2. handler value arm の return_frame_threshold が違う

ScopeReturn match しても threshold truncate が outer case frame を落としている可能性。

trace:

```text
scope_return_set value=just
route_scope_return current/frame walk:
  matched? no
  if matched before:
    threshold=<...>
    frames_before=<...>
    frames_after=<...>
```

もし `F_outer_case_post` が threshold で消えているなら、outer case が走らない。

## 3. `Return` helper が RuntimeValuePtr を scalar Int と区別しない

JIT scalar path は最終値を i64 として返す。heap pointer も i64 なので、型上は区別できない。

もし root continuation の ABI lane が `RuntimeValuePtr` / `OpaqueI64` に上がっているのに `compare_cps_repr_cranelift_i64` が raw i64 を比較しているなら、codegen というより lane analysis / final unwrapping の問題。

見るべき trace / dump:

```text
root return lane
continuation return lane
value lane for outer case result
```

期待は最終 root return lane が `ScalarI64`。
もし `RuntimeValuePtr` なら、outer case の payload extraction が lane analysis 上も伝播していない。

---

# write27-f 実装順

## Step 1: pure variant regression を追加

まず小さい test。

```text
compares_prelude_source_opt_just_case_through_cps_repr_cranelift
```

source:

```yu
case std::opt::opt::just 2:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
```

期待:

```text
VM=2
CPS repr Cranelift=2
```

この test が失敗するなら、handler から離れて variant codegen を直す。
この test が通るなら、handler value arm / ScopeReturn route を追う。

## Step 2: once value-arm-only regression

```yu
use std::undet.*

case ({ 2 }).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
```

期待 2。

これが heap pointer なら、`once` value arm natural return → outer case continuation が壊れている。

## Step 3: trace helpers

次を入れる。

```text
variant_new / variant_tag_eq / variant_payload
scope_return_set with value description
route_scope_return propagate reasons
continuation_enter for root/case continuations
return_i64 final value with describe
```

## Step 4: 原因別 fix

### pure variant case が fail

`VariantPayload` helper が nested payload を返していないか、tag constructor が payload layout を間違えている。

修正候補:

```text
- yulang_cps_variant_payload_i64 が Some(Box(value)) 相当の payload を返すか
- opt::just payload が tuple wrapping されているなら TupleGet が必要か
- Pattern lowering が `just v` に対して VariantPayload → maybe TupleGet を期待しているか
```

ここは Layer 2 の `CpsReprRuntimeValue::Variant { tag, value }` と同じ layout に合わせる。

### pure variant は pass、once value arm が fail

ScopeReturn route が本体。

修正候補:

```text
- handler value arm / perform_finish の prompt selection を修正
- route_scope_return の frame_walk 範囲を修正
- handler install full frame の escape_cont / escape_env を確認
- return_frame_threshold が outer case frame を落としていないか修正
```

### once value arm は pass、guard/backtrack case だけ fail

最後の nested once から outer case へ出る SR route が本体。
`effectful_apply_resumption` 後の return_frames / handler stack snapshot をさらに追う。

---

# Aborted / abort helper はまだ消さない

write27-e でも frontier はまだ Layer 3 mismatch。`Aborted` / `abort_*` 削除はまだ早い。
Layer 3 が 2 になってから grep で消すのが安全。

---

# 具体的な trace の期待形

最終的に欲しい trace:

```text
scope_return_set value=<ptr opt::just 2> prompt=<once prompt>
route_scope_return action=frame_walk or current_handler
  matched handler=<once>
  call escape continuation=<outer case post-cont>

ContinuationEnter root/case cont:
  arg=<ptr opt::just 2>

variant_tag_eq:
  tag=just result=1

variant_payload:
  value=<ptr opt::just 2>
  payload=2

return_i64:
  value=2
  action=noop
```

今はおそらく:

```text
scope_return_set value=<ptr opt::just 2>
route_scope_return action=propagate
return_i64 value=<ptr>
```

この差分を埋める。

---

# report の「値表現の差」について

私は「値表現の差」と言い切る前に、**ScopeReturn route の最後の propagate**を疑う方がいいと思うよ〜。report 自身も `scope_return_set value=<heap pointer>` と `route_scope_return action=propagate` を書いている。

つまり問題は:

```text
heap pointer が variant payload として間違っている
```

よりも、

```text
heap pointer opt::just が outer case へ渡されず root へ漏れている
```

の可能性が高い。

もちろん純粋 variant case が落ちたら前者だけど、まずはここを切り分けると無駄が少ない。

---

# 別LLMへ渡す短い指示文

```text
write27-f の目的:
  Layer 3 が heap pointer を返す原因を切り分ける。
  いきなり VariantPayload を直さず、
  outer case continuation が実行されているかを確認する。

まず pure variant case test を追加:
  case std::opt::opt::just 2:
    nil -> 0
    just v -> v
これが fail なら Variant/VariantPayload/VariantTagEq codegen を直す。

次に once value-arm-only test:
  case ({ 2 }).once:
    nil -> 0
    just v -> v
これが fail なら handler value arm ScopeReturn → outer case route が壊れている。

JIT trace を追加:
  variant_new
  variant_tag_eq
  variant_payload
  continuation_enter
  scope_return_set with value describe
  route_scope_return propagate reason
  final return_i64 value describe

本命 trace:
  scope_return_set value=<opt::just ptr>
  route_scope_return action=propagate
なら、variant codegen ではなく SR route leak。
handler prompt / install_eval / escape_cont / return_frame_threshold /
return_frames[current_initial..] の no-match reason を直す。

Aborted/abort helper はまだ削除しない。
Layer 3 が 2 になってから grep して削除判断。
```

---

# 最後に

write27-e はかなり良い報告だよ〜。ここまで来ると、もう nondet / resumption の大物はだいたい越えている。次は「最終 `opt::just 2` を outer case がちゃんと開けるか」という、かなり局所的な frontier。

私なら write27-f は **variant pure test → once value-arm-only test → final heap pointer route trace** の順で攻める。これで「値表現 codegen」か「最後の ScopeReturn route leak」か、かなりはっきり分かるはずだねぇ。
