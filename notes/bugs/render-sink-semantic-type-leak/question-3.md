# question-3: junction handler result leaks past if continuation

`answer-1.md` / `answer-2.md` を受けて、いったん render-sink / open cast
側は山を越えたように見える。残っているのは native CPS eval の control/value
routing っぽい。

## 現状

直近の修正で以下は入った。

- open な `Cast` / identity join を即時 runtime adapter にしない。
- `JoinEvidence` は semantic value boundary として、open result でも selected
  branch arm の thunk を force する。
- `my choose x = if true: x else: x; choose ()` は VM regression で通る。

ただし、次の小さい regression がまだ CPS eval で壊れる。

```yul
use std::undet::*

if all [2] < any [3]:
    18
else:
    2
```

期待値:

```text
18
```

実際:

```text
["1"]
```

`.once` を付けても同じ系統で壊れる。

```yul
use std::undet::*

({
    if all [2] < any [3]:
        18
    else:
        2
}).once
```

期待値:

```text
:just 18
```

実際:

```text
["1"]
```

一方で、junction を消した次の regression は通る。

```yul
use std::undet::*

struct point { x: int, y: int } with:
    our p.norm2: int = p.x * p.x + p.y * p.y

({
    my y = if true:
        each [3, 4, 5]
    else:
        2

    point { x: 3, y: y } .norm2
}).once
```

期待通り `:just 18`。

なので `.once` / `each` そのものより、`junction` handler の result が `if`
condition continuation へ戻らず、root display 側へ早く漏れているように見える。

## CPS dump の形

`root_0` はおおむねこういう形。

```text
cont0:
  MakeThunk condition_thunk(entry=cont5)
  DirectCall std::junction::junction::junction__mono3(thunk)
  ForceThunk result
  Continue cont2(result)

cont2:
  Branch condition -> cont3 / cont4

cont3:
  Return 18 through cont1

cont4:
  Return 2 through cont1

cont5..cont9:
  condition thunk:
    all [2]
    any [3]
    std::int::lt
    Return Bool(true) to junction handler
```

つまり source-level CPS だけ見ると、`junction(thunk)` の結果は `root_0::cont2`
へ入り、そこで `if` branch を選ぶはず。

`std::junction::junction::junction__mono3` は概念的にこう。

```text
cont0:
  InstallHandler(value=cont1, escape=cont2)
  EffectfulForce thunk resume=cont3

cont3:
  Return forced thunk result

cont1:
  UninstallHandler
  Continue cont2(value)

handler arms:
  and/or を捕捉し、k true / k false を再帰的に junction へ渡す
```

## trace で見えていること

`YULANG_CPS_TRACE_FRAMES=1` で見ると、condition thunk 内では `Bool(true)` が一度
`root_0` 側の continuation へ戻っている。

```text
Return: fn=root_0 cont=8 value=Plain(Bool(true)) return_frames.len=2 initial=1
ContinueReturnFrames pop owner=root_0 cont=9 ...
Return: fn=root_0 cont=9 value=Plain(Bool(true)) return_frames.len=1 initial=0
ContinueReturnFrames pop owner=std::junction::junction::junction__mono3 cont=3 ...
```

その後、nested `junction` 側の continuation/value-arm が `Bool(true)` を処理する。

```text
Return: fn=std::junction::junction::junction__mono3 cont=3 value=Plain(Bool(true))
Return: fn=std::junction::junction::junction__mono3 cont=10 value=Plain(Bool(true))
ContinueReturnFrames pop owner=std::junction::junction::junction__mono3 cont=11
```

最後に outer `junction` prompt の `ScopeReturn` が frame-walk で routing される。

```text
ScopeReturnDispatch:
  fn=std::junction::junction::all__mono4
  eval=11
  prompt=0
  target=2
  matched=no
  action=Propagate

FrameWalkMatch:
  frame_owner=std::junction::junction::junction__mono3
  frame_owner_eval=1
  handler_prompt=0
  ...
```

ここまでは「対象 prompt を見つけた」ように見えるが、最終的に `root_0::cont2`
ではなく root display が `1` を見てしまう。

## 怪しいコード

`crates/yulang-native/src/cps_eval.rs` の
`try_route_scope_return_through_return_frames` が特に怪しい。

```rust
let result = resume_continuation(
    module,
    owner,
    matched_handler.escape,
    vec![*value.clone()],
    frame.values.as_ref().clone(),
    post_handlers,
    frame.guard_stack.clone(),
    rest_frames,
    frame.active_blocked.clone(),
    owner_initial,
    frame.owner_eval_id,
)?;
if frame_index < initial_frame_count {
    return Ok(Some(CpsRuntimeValue::Aborted(Box::new(result))));
}
return Ok(Some(result));
```

`eval_cps_module` は root result で `unwrap_aborted` する。
そのため、`frame_index < initial_frame_count` のときに handler escape result を
`Aborted` に包むと、call-site continuation を飛ばして root answer になるように見える。

以前の `sub::return` / handler routing の修正では「現在 activation より外側の
frame に target があるなら abort lane で返す」という意図だったと思う。
ただ、junction handler の value-arm exit では、target が見つかった後の result は
「最終 answer」ではなく「call site の continuation に渡す handler expression result」
ではないか、という疑いがある。

## 聞きたいこと

1. この状況で `frame_index < initial_frame_count` を理由に
   `CpsRuntimeValue::Aborted(result)` へ包むのは意味論的に正しいか。

2. `Aborted` が次の二つを混ぜてしまっていないか。

   ```text
   A. prompt target はまだ未解決なので caller activation へ伝播する
   B. prompt target は見つかり、handler escape continuation に jump した後の result
   ```

   B はもう abort 中ではなく、普通の handler expression result として外側 continuation
   へ戻すべきではないか。

3. shallow handler の value-arm / escape routing では、`handler.escape(value)` の
   result をどの continuation に戻すべきか。

   今の CPS では `junction(thunk)` の call-site resume は `root_0::cont2`。
   `ScopeReturn(prompt=0)` が `junction__mono3` の handler escape を見つけたあと、
   `root_0::cont2` に戻るためには、どの return frame segment を保持すべきか。

4. `PromptExit(P)` を入れた後の eval model として、`Aborted` / `ScopeReturn`
   だけで十分か。それとも、以前相談したように次のような状態分離が必要か。

   ```rust
   enum Flow {
       Value(v),
       PromptReturn { prompt, value },
       RoutedJump { eval, cont, value, restored_frames },
       GlobalAbort(value),
   }
   ```

5. もし `frame_index < initial_frame_count` を単純に外すと、`sub::return` や
   var handler 更新で再発しそうな既存 invariant は何か。外すのではなく、
   handler kind / return reason / prompt ownership で分岐すべきか。

## こちらの暫定仮説

今の `["1"]` は render leak ではなく、`junction` handler 内部の値が
`if` condition continuation を飛ばして root/display に届く control routing bug。

特に、

```text
target found by frame walk
  -> resume handler.escape
  -> frame_index < initial_frame_count
  -> Aborted(result)
  -> root unwrap_aborted
  -> display result too early
```

という経路で、handler expression result が call-site continuation に戻らず、
top-level answer として扱われているように見える。

