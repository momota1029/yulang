うん、この暫定仮説はかなり当たってると思うよ〜。
貼ってくれた `question-3` の情報を見る限り、`["1"]` はもう render / cast 由来ではなく、**`junction` の handler result が `if` condition continuation を飛ばして root display に届いている control routing bug** と見るのが自然だねぇ。

特に、小さい regression がこれになったのが決定的。

```yul
if all [2] < any [3]:
    18
else:
    2
```

ここには literal `1` がない。
それでも `["1"]` が出るなら、かなり高確率で

```text
Bool(true) が display layer で "1" として出ている
```

だねぇ。
つまり漏れているのは `each` の値でも、list element でもなく、**condition の boolean result**。

---

# 1. `frame_index < initial_frame_count` で `Aborted(result)` に包むのは正しいか

このケースでは、**正しくない**と思う。

もう少し正確に言うと、

```rust
if frame_index < initial_frame_count {
    return Ok(Some(CpsRuntimeValue::Aborted(Box::new(result))));
}
```

という条件分岐自体が完全にダメというより、
**target を見つけて `matched_handler.escape` を実行した後の `result` を `Aborted` に包むのが危ない**。

ここで区別すべきものが 2 つある。

```text
A. まだ target prompt が見つかっていない ScopeReturn
B. target prompt は見つかった。handler escape continuation へ jump した後の結果
```

A は abort / propagate lane に乗せていい。
でも B はもう abort ではない。

B は意味論的には、

```text
handler expression の result
```

だねぇ。

今回なら、

```text
junction(thunk) の result = Bool(true)
```

であって、それは root answer じゃない。
その値は次に

```text
root_0::cont2
```

へ渡って、`if` の branch selection に使われる必要がある。

だから、target が見つかった後に `resume_continuation(...)` して得た結果を、単に `Aborted(result)` に包むと、

```text
Bool(true)
  -> root unwrap_aborted
  -> display
  -> "1"
```

という経路になりやすい。

まさに今の症状だねぇ。

---

# 2. `Aborted` が A/B を混ぜているか

混ぜている可能性がかなり高い。

今の `Aborted` は、たぶん少なくともこの 3 つを同じ箱に入れている。

```text
1. 未解決の prompt return を caller activation へ伝播したい
2. target prompt を見つけたので、そこへ jump したい
3. jump 後に得た普通の値を、現在の activation から外へ返したい
```

でも、この 3 つは意味が違う。

特に今回壊れているのは、

```text
target found
  -> handler.escape(value) を実行
  -> その結果を Aborted に包む
```

のところ。

`handler.escape(value)` を実行した後の値は、もう

```text
ScopeReturn in flight
```

ではない。
それは普通の値、あるいは次の control flow だねぇ。

だから model としてはこう分けたい。

```rust
enum Flow {
    Value(CpsRuntimeValue),

    // まだ target を探している
    PromptReturn {
        prompt: PromptId,
        value: CpsRuntimeValue,
        reason: ReturnReason,
    },

    // target は見つかった。指定 cont へ jump する必要がある
    RoutedJump {
        owner: FunctionId,
        eval_id: EvalId,
        cont: ContId,
        args: Vec<CpsRuntimeValue>,
        env_values: Vec<CpsRuntimeValue>,
        handlers: HandlerStack,
        guard_stack: GuardStack,
        return_frames: Vec<ReturnFrame>,
        active_blocked: ActiveBlocked,
        reason: ReturnReason,
    },

    // 本当に top-level answer / fatal escape
    GlobalAbort(CpsRuntimeValue),
}
```

名前は何でもいいけど、重要なのはこれ。

```text
PromptReturn != RoutedJump != GlobalAbort
```

今の `Aborted` がこの 3 つをまとめているなら、今回みたいに root display へ早漏れする。

---

# 3. shallow handler の value-arm / escape routing ではどこへ戻すべきか

今回の構造では、`junction__mono3` の handler escape はこう戻るべき。

```text
ScopeReturn(prompt=0, value=true)
  -> matching junction handler prompt を見つける
  -> matched_handler.escape(true) を実行
  -> junction(thunk) call-site の continuation へ戻る
  -> root_0::cont2(true)
  -> if true then cont3 else cont4
  -> cont3
  -> 18
  -> root display
```

つまり、`handler.escape(value)` の result を直接 root answer にしてはいけない。
それは **handler expression の result** であって、**caller continuation の input** だねぇ。

今回なら call-site resume はこれ。

```text
root_0::cont2
```

なので、frame walk で target handler を見つけたあとに保持すべき frame segment は、

```text
matched prompt より外側の return frames
```

だよ〜。

典型的にはこう。

```text
younger / inner frames:
  prompt の内側なので捨てる、または handler op resume 用に capture

matched frame:
  handler prompt と handler env を持つ frame
  escape continuation を取り出す

older / outer frames:
  handler expression の外側
  ここに root_0::cont2 が入っている必要がある
  これは保持する
```

疑似的にはこういう分割。

```rust
let inner_frames   = frames[..frame_index].to_vec();       // discard/capture
let matched_frame  = frames[frame_index].clone();          // handler lives here
let outer_frames   = frames[frame_index + 1..].to_vec();   // keep
```

そして、

```rust
resume_continuation(
    module,
    owner,
    matched_handler.escape,
    vec![value],
    matched_frame.values.clone(),
    post_handlers,
    matched_frame.guard_stack.clone(),
    outer_frames,
    matched_frame.active_blocked.clone(),
    owner_initial,
    matched_frame.owner_eval_id,
)
```

のように、**outer frames に `root_0::cont2` が残っている**必要がある。

もし `outer_frames` が空、または root display だけ、または `Aborted` unwrap で無視されるなら、`Bool(true)` が `if` に届かず display される。

ここに assert を入れると強い。

```text
When handling junction prompt in this regression:
  kept outer return frames must contain root_0::cont2.
```

もう一つ強い invariant はこれ。

```text
A non-root handler escape result must not be consumed by RootDisplay
unless its kept outer continuation segment is empty by construction.
```

今回、empty ではないはず。
`root_0::cont2` があるからねぇ。

---

# 4. `PromptExit(P)` 後の eval model は `Aborted` / `ScopeReturn` だけで足りるか

この症状を見る限り、足りていないと思う。

最低でも、今の `Aborted` に相当する状態を分けたほうがいい。

## 必須の分離

```text
PromptReturn:
  target prompt を探している途中

RoutedJump:
  target prompt は見つかった
  どの owner/eval/cont/rest_frames で再開するかも決まった

Value:
  普通の値

GlobalAbort:
  本当に top-level に出す値、または uncaught control
```

このうち、今回の frame-walk match 後は `PromptReturn` ではなく `RoutedJump`。

さらに `RoutedJump` を実行したあとに得たものは、

```text
Value
PromptReturn
RoutedJump
GlobalAbort
```

のどれかになりうる。
でも少なくとも、無条件に `GlobalAbort` 相当へ格上げしてはいけない。

## 現実的な小さめ変更

大改造が重いなら、まず `Aborted` に reason を付けるだけでもかなり切れる。

```rust
enum AbortKind {
    UnresolvedPromptReturn,
    RoutedJumpToOuterActivation,
    GlobalAnswer,
}

struct Aborted {
    kind: AbortKind,
    payload: Box<CpsRuntimeValue>,
}
```

ただ、これはまだ少し危ない。
本当は `payload` が値なのか jump 命令なのかを型で分けたい。

なので理想はこう。

```rust
enum EvalResult {
    Value(CpsRuntimeValue),

    PromptReturn {
        prompt: PromptId,
        target: ContId,
        value: CpsRuntimeValue,
        reason: ReturnReason,
    },

    RoutedJump {
        owner: FunctionId,
        eval_id: EvalId,
        cont: ContId,
        args: Vec<CpsRuntimeValue>,
        env_values: Vec<CpsRuntimeValue>,
        handlers: HandlerStack,
        guard_stack: GuardStack,
        return_frames: Vec<ReturnFrame>,
        active_blocked: ActiveBlocked,
        reason: ReturnReason,
    },

    GlobalAbort(CpsRuntimeValue),
}
```

ここまで分けると、`unwrap_aborted` みたいな処理が危険だと型で見える。

---

# 5. `frame_index < initial_frame_count` を単純に外すと何が再発しそうか

単純に外すのは危ないと思う。
たぶん以前直した `sub::return` / var handler 更新系が再発する可能性がある。

理由はこれ。

```text
frame_index < initial_frame_count
```

は、おそらく

```text
target が現在 activation の外側にある
```

ことを検出するために入っている。

この場合、current activation の残りを普通に続けるとまずい。
たとえば `sub::return` なら、

```text
return した後に、本来捨てるべき callee continuation を続ける
```

みたいな事故が起きる。

なので、外すべきなのは条件そのものではなく、

```text
target found 後の result を Aborted(value) にする
```

という扱い。

正しい分岐はたぶんこう。

```text
target not found:
  PromptReturn を caller へ propagate

target found in current activation:
  execute RoutedJump normally

target found in outer / initial frame:
  current activation は abort する
  ただし payload は final value ではなく RoutedJump
```

つまり、

```text
Aborted(result)
```

ではなく、

```text
Aborted(RoutedJump { ... })
```

または、

```text
Flow::RoutedJump { ... }
```

だねぇ。

`sub::return` で守りたい invariant はこう。

```text
sub::return は target lexical return prompt までの frames を破棄する。
破棄された frames の continuations は再開しない。
target より外側の frames は保持する。
guard/uninstall/active_blocked cleanup は一度だけ走る。
```

var handler 更新で守りたい invariant はこう。

```text
handler env / active_blocked / guard_stack は target frame の snapshot で再開する。
inner handler の env を outer continuation に漏らさない。
outer handler の env を落とさない。
```

だから分岐条件は、`frame_index < initial_frame_count` だけではなく、

```text
target found?
return reason?
target prompt kind?
jump result or unresolved propagation?
kept outer frames are present?
```

を見るべきだと思うよ〜。

---

# 今回の直接バグとして一番ありそうな経路

貼ってくれた仮説のこの経路はかなり説得力がある。

```text
target found by frame walk
  -> resume handler.escape
  -> frame_index < initial_frame_count
  -> Aborted(result)
  -> root unwrap_aborted
  -> display result too early
```

このとき `result` が `Bool(true)` なら、display で `["1"]` になる。
`if` の then/else には一切入らない。

つまり bad path はこう。

```text
condition thunk result true
  -> junction handler escape
  -> Aborted(true)
  -> root display
  -> ["1"]
```

happy path はこう。

```text
condition thunk result true
  -> junction handler escape
  -> root_0::cont2(true)
  -> root_0::cont3
  -> 18
  -> root display
```

---

# まず入れるべき trace

次の trace を入れるのが一番早そう。

## 1. frame-walk match 時の segment dump

```text
FrameWalkMatch {
  prompt,
  reason,
  frame_index,
  initial_frame_count,

  inner_frames: [
    { owner, cont, eval_id, kind }
  ],

  matched_frame: {
    owner,
    eval_id,
    handler_prompt,
    handler_escape,
    handler_value,
  },

  outer_frames: [
    { owner, cont, eval_id, kind }
  ],

  action,
}
```

この regression では、match 時の `outer_frames` に

```text
root_0::cont2
```

が見えないとおかしい。

---

## 2. `Aborted` を作る瞬間の reason

```text
MakeAborted {
  reason,
  payload_kind,
  payload_value,
  payload_flow_kind,
  frame_index,
  initial_frame_count,
  target_found,
}
```

ここでこう出たらアウト。

```text
MakeAborted {
  reason = target_found_escape_result,
  payload_value = Bool(true)
}
```

`target_found_escape_result` を global abort にしているからねぇ。

---

## 3. root display の producer

```text
RootDisplay {
  value = Bool(true),
  producer = junction__mono3.escape,
  last_flow = Aborted,
  saw_if_cont2 = false,
}
```

これが出れば確定。

逆に happy path ではこう。

```text
DeliverValue {
  value = Bool(true),
  to = root_0::cont2,
}

Branch {
  condition = Bool(true),
  selected = root_0::cont3,
}

RootDisplay {
  value = Int(18),
}
```

---

## 4. `resume_continuation` の entry/exit flow

```text
ResumeContinuationEnter {
  owner,
  cont,
  args,
  return_frames_summary,
}

ResumeContinuationExit {
  owner,
  cont,
  result_flow_kind,
  result_value,
  remaining_return_frames_summary,
}
```

特に `matched_handler.escape` の呼び出しで、

```text
return_frames_summary contains root_0::cont2
```

を確認したい。

もし含んでいるのに `Bool(true)` が root へ出るなら、`Aborted` unwrap が原因。
含んでいないなら、frame segment の切り出しが原因。

---

# 入れるべき invariant

## invariant A: junction result must reach if continuation

この小 regression 専用でもいい。

```text
For an if condition expression E:
  result of E must be consumed by Branch/IfCondition continuation,
  not RootDisplay.
```

汎用化するとこう。

```text
A subexpression result may be consumed only by its lexical consumer continuation,
unless a nonlocal control transfer explicitly targets an outer prompt.
```

今回の `Bool(true)` は lexical consumer が `root_0::cont2`。

---

## invariant B: target-found flow is not global abort

```text
After a prompt target is found,
the routed result must not be converted to GlobalAbort
only because frame_index < initial_frame_count.
```

より具体的にはこう。

```text
if target_found && matched_handler.escape != root_escape:
    produced flow must be RoutedJump or Value-through-kept-frames,
    not GlobalAbort.
```

---

## invariant C: kept frames must contain call-site continuation

この test ではこう。

```text
handling prompt 0 in junction__mono3:
  kept_outer_frames contains root_0::cont2
```

一般にはこう。

```text
When handling a prompt return for expression call C,
the continuation frame for C's result must be in the kept outer frame segment.
```

---

## invariant D: `Bool(true)` cannot be displayed before branch

これも小 regression 用に強い。

```text
RootDisplay(Bool(true)) is invalid
if there is an outstanding IfCondition consumer for that value.
```

実装上は `value_id` / `producer_expr_id` が必要だけど、trace だけでも十分。

---

# パッチ方針

まず小さく直すなら、`try_route_scope_return_through_return_frames` の該当箇所をこういう思想に変える。

今の形:

```rust
let result = resume_continuation(...)?;

if frame_index < initial_frame_count {
    return Ok(Some(CpsRuntimeValue::Aborted(Box::new(result))));
}

return Ok(Some(result));
```

方向性:

```rust
let jump = RoutedJump {
    owner,
    eval_id: frame.owner_eval_id,
    cont: matched_handler.escape,
    args: vec![*value.clone()],
    env_values: frame.values.as_ref().clone(),
    handlers: post_handlers,
    guard_stack: frame.guard_stack.clone(),
    return_frames: rest_frames,
    active_blocked: frame.active_blocked.clone(),
    reason,
};

if frame_index < initial_frame_count {
    // current activation はここで止める。
    // でも payload は final value ではなく jump command。
    return Ok(Some(Flow::RoutedJump(jump)));
}

return execute_routed_jump(jump);
```

もし既存 enum を大きく変えたくないなら、一時的には

```rust
CpsRuntimeValue::AbortedJump(Box<RoutedJump>)
```

みたいな別 variant を作るのもあり。

大事なのは、

```text
Aborted(Value(true))
```

を作らないこと。

作るなら、

```text
Aborted(RoutedJump(... root_0::cont2 ...))
```

にする。

---

# `handler kind / return reason / prompt ownership` で分岐すべきか

分岐は入れていいけど、根本 invariant は handler kind 依存にしすぎないほうがいいと思う。

おすすめはこう。

```text
prompt ownership decides target
return reason decides cleanup/capture policy
target-found decides RoutedJump
target-not-found decides PromptReturn propagation
```

つまり、

```text
junction handler だから Aborted しない
sub::return だから Aborted する
```

ではなく、

```text
target not found -> propagate
target found -> routed jump
current activation must stop -> return jump to caller
```

という形。

`sub::return` も target が見つかった後は、本質的には routed jump だねぇ。
違うのは、どの prompt を target にするか、どの frames を捨てるか、cleanup をどう走らせるか。

---

# `["1"]` の読み

今回の追加 regression によって、かなり確定寄り。

```text
["1"] = Bool(true) from all [2] < any [3]
```

だと思うよ〜。

理由は単純で、

```yul
if all [2] < any [3]:
    18
else:
    2
```

には `1` という int value がない。
`each [3,4,5]` もない。
それでも `["1"]` なら、`Bool(true)` の display 表現が `1` になっていると読むのが一番自然。

だから疑う対象は、

```text
each continuation
```

ではなく、

```text
junction(thunk) result true
  -> if condition cont2
```

の間。

より具体的には、

```text
ScopeReturn(prompt=0)
  -> matched_handler.escape
  -> result Bool(true)
  -> root_0::cont2 を経由せず root display
```

の経路だねぇ。

---

# 最終判断

質問への答えを短くまとめるとこう。

```text
1. このケースで Aborted(result) に包むのは意味論的に不正寄り。
   current activation を止める必要はあっても、result を global answer にしてはいけない。

2. Aborted は未解決 prompt propagation と target-found 後の result を混ぜている可能性が高い。
   B は普通の handler expression result、または RoutedJump として扱うべき。

3. handler.escape(value) は root display ではなく、handler expression の call-site continuation へ戻す。
   今回なら root_0::cont2。保持すべき segment は matched prompt より外側の return frames。

4. Aborted / ScopeReturn だけだと足りない。
   PromptReturn / RoutedJump / Value / GlobalAbort を分けるのが筋。

5. frame_index 条件を単純に外すのは危険。
   sub::return などで「捨てるべき activation を続ける」再発がありうる。
   外すのではなく、target-found 後の payload を Value ではなく RoutedJump として扱うのがよさそう。
```

この次の一手は、`try_route_scope_return_through_return_frames` で **`Aborted(Bool(true))` が作られているか**を trace で確定することだねぇ。
それが出たら、かなり勝ち筋が太い。
