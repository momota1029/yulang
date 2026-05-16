かなり前進してる。
今の状態は、**型・render leak の山は越えていて、残りは control/value routing の山**に見えるよ〜。

## まず結論

1. **`open Cast` を即時 runtime adapter にしない方針は妥当**。ただし「消す」ではなく「未確定 evidence として保持、または identity として確定」のどちらかに分けるのが安全。
2. **`JoinEvidence` で thunk arm を force する方針も妥当**。これは cast ではなく、semantic value boundary の処理だねぇ。
3. 残った `["1"]` は、もう render-sink leak ではなく、**junction handler の結果、または junction 内部の値が、`if` の condition continuation を飛ばして root/display 側へ漏れている**と読むのが自然。
4. まず疑うべき境界は、**junction handler の value-arm exit / `sub::return` route / fold callback return prompt**。次に **shallow resume 時の handler stack 再導入**。
5. `["1"]` は `each [3,4,5]` の最初の値ではなく、**`all ... < any ...` 側の `true`、または左 junction の最初の要素 `1` が早く root に出ている**可能性が高い。

---

# 1. 今の `open Cast` / `JoinEvidence force` の切り分け

これは `answer-1.md` の invariant と整合してると思うよ〜。

特にこのログは決定的だねぇ。

```text
runtime implicit cast
  source   = JoinEvidence
  actual   = Var(t2988)
  expected = Var(t2988)
  cast     = std::prelude::&cast#765::cast
```

これは完全におかしい。

```text
Var(t2988) -> Var(t2988)
```

の open identity join に対して、

```text
Cast path -> bytes
```

由来の role method が選ばれている。
なので、ここで runtime expr に `Cast` を即時挿入しないのは正しい。

ただし invariant はこう切るのが安全。

```text
Open Cast は runtime adapter に即時 lowering しない。

ただし、
  identity / compatible と確定できるものは no-op evidence
  まだ非 identity になりうるものは delayed evidence
  lowering 完了時点でも未解決なら diagnostic
```

つまり、**skip ではなく classify** だねぇ。

## `JoinEvidence force` は cast とは別物

ここも大事。

```text
JoinEvidence:
  branch arm を semantic value として観測する境界

Cast evidence:
  semantic type A を semantic type B へ変換する境界
```

この 2 つを混ぜると、今回のように「force が必要だから cast を巻く」みたいな事故が起きる。

なので今の整理はこうでよさそう。

```text
open Cast:
  型変換 evidence としてはまだ runtime expr へ落とさない

JoinEvidence:
  選択済み branch arm が effect thunk なら force する
  ただし bytes/unit への cast は選ばない
```

一点だけ注意。
`JoinEvidence force` は **選ばれた arm だけ**にかかる必要がある。
effectful branch で両 arm を eager に force すると別の意味破壊になるから、invariant はこう。

```text
branch join force は selected arm の value boundary でだけ起きる。
unselected arm は force しない。
```

---

# 2. 残りの `["1"]` は render leak ではないか

ほぼそう見ていいと思う。

前の失敗はこれだった。

```text
branch result type mismatch: expected unit, got std::bytes::bytes
```

これは型 validation の段階で、`bytes` が semantic branch result に混ざっていた症状。

今は validation が通って、その後に

```text
unexpected CPS eval display result: ["1"]
```

になる。
これは **型の混線ではなく、正しくない semantic value が root/display へ届いた**という形だねぇ。

このプログラムの期待パスはこう。

```text
.once installs undet-once handler

block body:
  evaluate if condition:
    all [1,2,3] < any [2,3,4]
    => true

  then branch:
    y = each [3,4,5]
    .once chooses first y = 3

  point { x: 3, y: 3 }.norm2
    => 3*3 + 3*3
    => 18

display:
  "18"
```

でも実際は

```text
"1"
```

が出ている。

これはかなり自然に、

```text
if condition result true
```

または

```text
junction/all 側の最初の値 1
```

が、その後の

```text
if condition continuation
then branch
let y binding
point construction
.norm2
.once finalization
```

を飛ばして root に漏れている、と読める。

---

# 3. まず疑うべき境界

優先順はこれがよさそう。

## 第一候補: junction handler の value-arm exit / `sub::return` route

今回一番怪しいのはここ。

```text
junction handler / fold callback 内で得た値 1 or true
  ↓
本来は fold / junction / if condition continuation へ戻る
  ↓
でも native CPS では root/display 側へ出ている
```

特に `all` / `any` は短絡評価を持つはずだから、内部で

```text
std::flow::sub::return
```

的な制御を使っているなら、そこがかなり疑わしい。

期待する route はこう。

```text
sub::return inside fold callback
  -> callback の lexical sub-return prompt
  -> fold step continuation
  -> junction accumulator/result
  -> if condition continuation
```

危ない route はこう。

```text
sub::return inside fold callback
  -> junction method の外側 prompt
  -> .once body prompt
  -> root/display prompt
```

以前の native CPS JIT の scope-return routing が直っていても、
**handler resume 後の fold callback / nested handler stack 上で return prompt がズレる**のは別バグとして残りやすい。

なのでまず見るべき invariant はこれ。

```text
sub::return の target prompt は lexical function/callback の sub prompt でなければならない。
effect handler prompt, .once prompt, root prompt を target にしてはいけない。
```

---

## 第二候補: perform capture 時の continuation segment

junction effect の `perform` 時に、capture される continuation が短すぎる可能性もある。

本来、junction handler の結果は最終的に

```text
IfCond continuation
```

へ渡る必要がある。

つまり、handler の外側 continuation はこうであるべき。

```text
junction result bool
  -> if condition consumer
  -> selected branch
  -> let y
  -> norm2
  -> .once result
```

危ない形はこれ。

```text
junction result bool
  -> root/display
```

なので `perform` capture の trace では、

```text
この handler の handled-expression exit continuation は何か
```

を出すといい。
captured segment の中に `IfCond` が入るかどうかは handler の置き方次第だけど、少なくとも **handler value arm の exit 先**は root ではなく condition consumer でないとおかしい。

---

## 第三候補: shallow handler resume 時の handler stack 再導入

`all` / `any` / `junction` と `.once` が同居するので、ここも怪しい。

特に shallow handler だと、

```text
resume continuation
```

のときに同じ handler を再導入するかどうかが実装上の分岐になる。
ただし shallow/deep の違いがあっても、外側 handler は消えてはいけない。

このプログラムでは、then branch に入ったあと

```yulang
each [3, 4, 5]
```

が外側の `.once` に捕まる必要がある。

だから resume 後の stack invariant はこう。

```text
junction handler の resume 後も、外側の .once handler は残る。
junction handler は、自分の shallow/deep policy に従って再導入される。
関係ない effect handler が消えたり、順序が反転したりしない。
```

危ない形はこれ。

```text
resume 後の stack から .once が消える
resume 後の stack で root/display が .once より内側に来る
junction handler の value result が .once body result として扱われる
```

---

## 第四候補: fold callback continuation

`all` / `any` が fold で実装されているなら、callback の return continuation も見る価値が高い。

期待形はこう。

```text
fold callback returns step value
  -> fold step consumes it
  -> accumulator updates / short-circuit checks
  -> fold result
  -> junction result
```

危ない形はこう。

```text
fold callback returns 1
  -> callback return prompt missing
  -> outer handler/root consumes 1 as whole expression result
```

特に native CPS で callback thunk を force するなら、

```text
force thunk
return from callback
resume fold continuation
```

の 3 点を同じ trace id で結ぶと見えやすい。

---

# 4. 次に入れる trace / invariant

候補に挙げているものは全部筋がいい。
優先順位をつけるならこう。

## A. root display に届いた値の producer trace

まずこれを入れたい。

```text
RootDisplay {
  value,
  raw_type,
  raw_tag,
  producer_expr,
  producer_function,
  producer_cont,
  current_handler_stack,
}
```

`["1"]` だけだと、

```text
Bool(true) が Display で "1" になった
Int(1) がそのまま "1" になった
junction element 1 が漏れた
```

が区別できない。

なので display 前の raw value が必要。

```text
raw_tag = Bool(true)
```

なら condition result leak。

```text
raw_tag = Int(1)
producer = all list element
```

なら junction element leak。

```text
raw_tag = Int(3)
```

なら each leakだけど、今の表示とは合わない。

---

## B. handler install / perform / capture / resume trace

形式はこれくらい欲しい。

```text
HandlerInstall {
  prompt,
  kind,              // Junction, UndetOnce, SubReturn, Root, ...
  function,
  lexical_scope,
  shallow_or_deep,
  stack_depth,
  parent_prompt,
}

Perform {
  effect,
  op,
  selected_prompt,
  function,
  expr,
  stack_before,
}

Capture {
  selected_prompt,
  captured_segment_id,
  captured_frames,
  handler_exit_cont,
  stack_prefix,
}

Resume {
  captured_segment_id,
  resume_value,
  restored_stack,
  reintroduced_handlers,
  next_cont,
}
```

ここで見る invariant はこれ。

```text
junction perform の selected_prompt は junction handler。
undet.each perform の selected_prompt は .once handler。

junction handler の exit continuation は IfCond consumer。
root/display ではない。
```

もう一つ。

```text
resume 後の restored_stack には外側 .once が残る。
```

---

## C. `std::flow::sub::return` route trace

これはかなり重要。

```text
SubReturn {
  value,
  source_function,
  source_callback,
  source_expr,
  target_prompt,
  target_prompt_kind,
  target_lexical_scope,
  popped_frames,
  next_cont,
  stack_before,
  stack_after,
}
```

invariant はこう。

```text
target_prompt_kind == SubReturn
target_lexical_scope == source の lexical return scope
```

特に fold callback ではこれ。

```text
sub::return inside fold callback
  must target callback return prompt
  must not target junction handler prompt
  must not target undet.once prompt
  must not target root/display prompt
```

今回の `["1"]` は、ここで一発で見つかる可能性が高い。

---

## D. fold callback / thunk force trace

```text
ThunkForce {
  thunk_id,
  origin,             // branch arm, fold callback, handler value arm, ...
  expected_boundary,  // JoinEvidence, FoldStep, Resume, ...
  force_cont,
  return_to,
}

FoldCallbackEnter {
  fold_id,
  callback_id,
  accumulator,
  item,
  handler_stack,
  return_prompt,
}

FoldCallbackReturn {
  fold_id,
  callback_id,
  value,
  consumed_by,
  next_cont,
}
```

invariant はこれ。

```text
FoldCallbackReturn.consumed_by == FoldStep
```

root/display や `.once` が callback return を直接 consume したらアウト。

---

## E. `.once` の undet perform trace

これも強い切り分けになる。

```text
UndetPerform {
  op = each,
  values = [3,4,5],
  selected_prompt,
  captured_cont,
}

OnceChoose {
  chosen_value,
  resume_cont,
}

OnceCommit {
  final_value,
  producer,
}
```

このテストで期待する順番はこう。

```text
junction condition finishes with true
if enters then branch
UndetPerform(each [3,4,5])
OnceChoose(3)
norm2 returns 18
OnceCommit(18)
RootDisplay(18)
```

もし bad trace で

```text
RootDisplay(1)
```

が `UndetPerform(each [3,4,5])` より前に出ているなら、
`each` の continuation ではなく、condition/junction 側が早漏れしている。

---

# 5. `["1"]` は何が漏れているか

自然なのは **junction condition 側の値が root へ漏れている**だねぇ。

この 2 つのどちらか。

```text
Bool(true) display => "1"
```

または

```text
all [1,2,3] の最初の element Int(1) が漏れた
```

一方で、

```yulang
each [3, 4, 5]
```

の最初の値が漏れているなら、普通は

```text
["3"]
```

になりそう。
`point.norm2` まで進んだなら

```text
["18"]
```

になる。
`y = 1` として誤って進んだなら

```text
3*3 + 1*1 = 10
```

なので

```text
["10"]
```

になりやすい。

だから `["1"]` は、then branch の `each` より前、つまり

```text
all [1,2,3] < any [2,3,4]
```

の評価中または handler exit 中に漏れていると見るのが自然。

ただし `Bool(true)` と `Int(1)` は display 上で潰れる可能性があるから、raw tag trace で分けたい。

---

# すぐ切れる小さい regression

この 4 つを native CPS eval に足すと、かなり場所が絞れると思うよ〜。

## A. junction condition が if continuation に戻るか

```yulang
({
    if all [2] < any [3]:
        18
    else:
        2
}).once
```

期待:

```text
["18"]
```

bad が

```text
["1"]
```

なら、`each` は関係なく、junction result が `if` を飛ばしている。

---

## B. Bool leak か element leak か分ける

```yulang
({
    if all [7] < any [8]:
        18
    else:
        2
}).once
```

結果の読み方:

```text
["1"]  -> Bool(true) leak が濃い
["7"]  -> all 側 element leak が濃い
["18"] -> pure junction + if は通る
```

---

## C. `.once` なしで junction + if が通るか

```yulang
if all [2] < any [3]:
    18
else:
    2
```

これが通って、`.once` ありだけ落ちるなら、

```text
outer .once handler があると junction handler exit/resume stack が壊れる
```

方向。

これも落ちるなら、

```text
junction handler -> if condition continuation
```

自体の native CPS bug。

---

## D. junction を消して once + each が通るか

```yulang
({
    my y = if true:
        each [3, 4, 5]
    else:
        2

    point { x: 3, y: y } .norm2
}).once
```

これが通るなら、`.once` と `each` 単体はかなり白い。
既存の once/open range guard が通っているなら、おそらくここも通るはず。

---

# 追加で置きたい assert

## handler value arm の exit assert

```text
A non-root handler value arm must not deliver its result to RootDisplay
unless the handled expression itself is the root expression.
```

今回なら junction handler は condition subexpression の中にいるので、

```text
junction value result -> IfCondCont
```

でないとおかしい。

---

## effect kind routing assert

```text
junction effect is handled only by junction handler
undet effect is handled only by undet.once handler
sub::return is handled only by sub-return prompt
```

特に `sub::return` が effect handler prompt に吸われると、かなり壊れ方が似る。

---

## continuation ownership assert

各 continuation frame に owner を持たせると見やすい。

```text
owner = IfCondition(expr_id)
owner = LetBinding(y)
owner = MethodCall(norm2)
owner = FoldStep(fold_id)
owner = HandlerValueArm(prompt)
owner = OnceFinalize(prompt)
owner = RootDisplay
```

そして value delivery 時にこう出す。

```text
DeliverValue {
  value,
  from_owner,
  to_owner,
}
```

このプログラムで見たい happy path はこう。

```text
junction result true
  -> IfCondition

then branch y thunk/value
  -> LetBinding(y)

each chosen 3
  -> LetBinding(y)

norm2 result 18
  -> OnceFinalize

once result 18
  -> RootDisplay
```

bad path ではたぶんこう出る。

```text
junction result true or element 1
  -> RootDisplay
```

または、

```text
fold callback return 1
  -> RootDisplay
```

---

# 今の trace tail について

```text
HandlerEnvRead { layer: CpsEval, function: "std::junction::junction::any__mono7", handler: 4, entry: 18, values: [] }
HandlerEnvRead { layer: CpsEval, function: "std::junction::junction::junction__mono3", handler: 0, entry: 4, values: [] }
HandlerEnvRead { layer: CpsEval, function: "std::junction::junction::all__mono6", handler: 3, entry: 18, values: [] }
HandlerEnvRead { layer: CpsEval, function: "std::junction::junction::junction__mono3", handler: 0, entry: 5, values: [] }
```

これは少なくとも、最後に動いているのが `each` / `.once` / `norm2` ではなく、`junction` 系であることを示している。
なので `["1"]` はやっぱり junction 側の値っぽい。

`values: []` 自体は、handler env が本当に free value を持たないなら問題とは限らない。
でも次の 2 点は見たい。

```text
handler = 0/3/4 がどの prompt kind か
entry = 4/5/18 がどの continuation owner か
```

特に `entry = 18` が root/display 系ならかなり怪しい。
`entry = IfCond` や `FoldStep` なら次の return route が怪しい。

---

# まとめ

今の修正方針はかなり妥当。

```text
open Cast は runtime adapter にしない
JoinEvidence は cast ではなく value boundary として force する
```

残りの `["1"]` は、render/cast ではなく control routing の値違いとして扱うのがよさそうだねぇ。

一番疑う場所はここ。

```text
junction/fold callback 内の sub::return
  または
junction handler value arm の exit continuation
```

次に見る場所はここ。

```text
shallow handler resume 時の restored handler stack
```

そして `["1"]` の読みはこれ。

```text
then branch の each(3) が漏れたというより、
if condition 側の true / junction element 1 が root に早く漏れている
```

まず入れる trace は、

```text
RootDisplay raw producer
SubReturn route
Handler perform/capture/resume stack
Handler value arm exit continuation
UndetPerform(each) が RootDisplay より前に起きたか
```

この順が一番切れ味ありそうだよ〜。
