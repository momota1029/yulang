# junction method + undet once routing leak

2026-05-16 時点の相談メモ。

## 現象

次の regression がまだ落ちる。

```bash
cargo test -q -p yulang-compile runs_junction_method_undet_once_through_cps_repr -- --nocapture
```

対象コード:

```yulang
use std::undet::*

struct point { x: int, y: int } with:
    our p.norm2: int = p.x * p.x + p.y * p.y

({
    my y = if all [1, 2, 3] < any [2, 3, 4]:
        each [3, 4, 5]
    else:
        2

    point { x: 3, y: y } .norm2
}).once
```

期待:

```text
:just 18
```

実際:

```text
CPS primitive BoolNot cannot accept value Unit
```

## 直前に直ったもの

次は通るようになった。

```bash
cargo test -q -p yulang-compile runs_junction_condition_once_through_cps_repr -- --nocapture
cargo test -q -p yulang-compile runs_junction_condition_without_once_through_cps_repr -- --nocapture
cargo test -q -p yulang-compile runs_undet_once_if_true_branch_through_cps_repr -- --nocapture
cargo test -q -p yulang-compile runs_simple_undet_list_through_cps_repr -- --nocapture
```

修正内容は native/JIT 側で、target prompt を見つけた後の result を
`Global` / plain `Aborted(value)` として root display へ流さず、
`NativeCpsI64Abort::RoutedJump` として保持するもの。
さらに `RoutedJump` の escape continuation 実行中は外側 `.once` の
`PromptExit` frame をすぐ消費しないよう、pending return frames として退避し、
normal return 側で復元するようにした。

この修正で、以前の `["1"]` は消えた。

## 観測

`YULANG_CPS_TRACE_FRAMES=1` で見ると、method 版では `all/any` の再帰 junction 内で
`Unit` が返り、それが最終的に `BoolNot` の入力へ流れているように見える。

重要そうな trace:

```text
PerformHandlerSearch:
  fn=std::junction::junction::all__mono6
  effect=std::junction::junction::and
  matched_prompt=1
  matched_owner=std::junction::junction::junction__mono3

ResumeHandlerMerge:
  site=Resume
  fn=std::junction::junction::junction__mono3
  anchor=Some((1, 6))
  captured=[root, junction prompt 1, all prompt 2]
  current=[root, fresh junction prompt 6]
  merged=[root, old junction prompt 1, fresh junction prompt 6, all prompt 2]

Return:
  fn=std::junction::junction::all__mono6
  cont=8
  value=Unit

Return:
  fn=std::junction::junction::junction__mono3
  cont=31
  value=Unit

FrameWalkMatch:
  frame_owner=std::junction::junction::junction__mono3
  handler_prompt=1
  handlers_after=[root]
  threshold=4
  rest_after=4

Return:
  fn=std::junction::junction::junction__mono3
  cont=2
  value=Unit
```

後半にも同じ形がある。

```text
PerformHandlerSearch:
  fn=std::junction::junction::any__mono7
  effect=std::junction::junction::or
  matched_prompt=7

ResumeHandlerMerge:
  anchor=Some((7, 59))
  captured=[root, outer junction prompt 1, junction prompt 7, any prompt 8]
  current=[root, fresh junction prompt 10]
  merged=[root, outer junction prompt 1, junction prompt 7, fresh junction prompt 10, any prompt 8]

Return:
  fn=std::junction::junction::any__mono7
  cont=8
  value=Unit

Return:
  fn=std::junction::junction::junction__mono3
  cont=18
  value=Unit

FrameWalkMatch:
  frame_owner=std::junction::junction::junction__mono3
  handler_prompt=7
  threshold=0
  rest_after=0

Return:
  fn=std::junction::junction::junction__mono3
  cont=2
  value=Unit
```

`root_0` では condition continuation は bool を要求する。

```text
root_0:
  ...
  CpsContinuationId(25):
    make thunk for all/any expression
    DirectCall junction__mono3
    ForceThunk
    Continue 27(value)

  CpsContinuationId(27):
    Branch cond=value
```

落ちる時はこの value が `Unit` になっている。

## CPS dump 上の気になる点

`std::junction::junction::junction__mono3` の handler shape はこう。

```text
InstallHandler {
  handler: 0,
  value: 1,
  escape: 2,
}
```

handler value arm:

```text
cont 1(x):
  UninstallHandler 0
  Continue 2(x)
```

`and` arm っぽい箇所:

```text
cont 4(_, k):
  UninstallHandler 0
  Continue 8()

cont 8:
  thunk = k true
  DirectCall junction__mono3(thunk)
  ForceThunk result
  Branch result then 14 else 16

cont 14:
  true -> cont 12

cont 16:
  Continue 15()

cont 15:
  thunk = k false
  DirectCall junction__mono3(thunk)
  ForceThunk result
  Continue 12(result)

cont 12(result):
  Continue 2(result)
```

ただし `cont 7` がある。

```text
cont 7:
  Literal Unit
  Continue 2(Unit)
```

`or` arm 側にも似た `Unit` fallback があり、trace ではこの `Unit` 系の
continuation が再帰 junction の exit へ流れているように見える。

## 暫定仮説

前回の `["1"]` は root display への早漏れだったが、今回は少し違う。

今は condition continuation までは戻っている。ただし nested junction の handler
arm / recursive junction value arm のどこかで、resume した suffix の boolean result
ではなく、handler arm の「失敗・fallthrough 用 Unit continuation」が
`junction__mono3` の escape result として採用されている。

疑っている境界:

1. `ResumeHandlerMerge` で、captured handler stack と fresh recursive junction handler
   の順序が間違い、outer `junction` と inner `all/any` の prompt が見えすぎている。
2. `UninstallHandler` 後の `Continue 8()` / `Continue 21()` のような handler arm body が
   `Unit` を返す経路と、`Resume k true/false` の raw subcontinuation result が混ざっている。
3. `handler value arm` と `handler escape` がどちらも `cont 2` に集約されているため、
   shallow handler の body-answer と handler-answer の境界がまた潰れている。
4. `threshold = 0` の recursive junction prompt では frame-walk が `rest_after=0` になり、
   caller continuation を完全に捨てて `Unit` をそのまま escape に流している。

## 質問

この failure は、どこを主犯として見るべきかなぁ。

- `ResumeHandlerMerge` の handler stack composition が悪いのか。
- `junction__mono3` の CPS lowering が `and/or` arm の fallthrough `Unit` を
  handler result として流しうる形になっているのか。
- それとも前回同様、`PromptExit(P)` / `EscapeTarget(P)` / ordinary return frame の
  分離がまだ足りず、recursive handler の value arm と old handler の escape が
  同じ `cont 2` へ潰れているのか。

もし直すなら、局所的な `Unit` guard ではなく、どの invariant を立てるべきか知りたい。

候補:

```text
I1. junction handler expression result is always the thunk body answer type,
    never the handler arm statement/fallthrough unit.

I2. Resume(k, true/false) inside junction and/or arms must return raw body answer;
    recursive junction's value arm may convert that answer, but the old prompt's
    value/escape arm must not run again.

I3. A prompt-targeted frame-walk match with threshold=0 still must preserve the
    lexical caller continuation if the handler expression has a caller; threshold=0
    is not proof that the handler result is the final answer.
```

