まず大事な前提を置くねぇ。

私が参照できる `momota1029/yulang` の `main` では、`notes/todo/native-undet-write18-report.md` が最新で、`notes/todo/native-undet-write19-report.md` は検索でも直接取得でも見つからなかった。だから以下は、**write18-report までの実装済み状態を基準にした「write19で実行すべき手順」**としてまとめるよ〜。

# 最重要結論

次の実装LLMがまずやるべきことは、**`std::undet.once` の branch arm で `loop(k true, queue + [k])` が本当に「再帰 loop を先に立ててから `k true` を force する」形になっているかを trace で証明すること**だねぇ。

write18 で古い `cps:3` の根本原因、つまり `fold_impl(left)` の返した Thunk が force されず、左側の iteration が捨てられる問題は修正済み。修正後は `debugs_std_undet_once_skip_eval_layers` が **`cps:3` から `cps:0`** に変わり、第一イテレーションの `branch → sub::return 1 → guard reject` までは正しく進む。その後、`once` の reject arm で `queue` が空扱いになり、`uncons` が `nil` を返すのが現在の主バグだよ〜。

つまり、もう「3 まで行ってしまう」問題を第一候補にしない方がいい。今は **「queue に k1 が入っているはずなのに、reject 時に queue が空に見える」問題**に変わっている。

`std::undet.once` の定義はこうで、branch arm は `k` を queue に積んでから再帰 loop へ入る意味を持つ。`reject` では queue を `uncons` し、あれば `k false` で replay する。

```yu
pub once(x: [_] _) = loop x [] with:
    our loop(x: [_] _, queue) = catch x:
        branch(), k -> loop(k true, std::list::append queue [k])
        reject(), _ -> case std::list::uncons queue:
            std::opt::opt::nil -> std::opt::opt::nil
            std::opt::opt::just (k, queue) -> loop(k false, queue)
        v -> std::opt::opt::just v
```

ここで一番怪しいのは、**`loop` の第一引数 `x: [_] _` に渡すべき `k true` が Thunk として渡らず、再帰 loop の handler が install される前に eager に replay されている**ケースだねぇ。もしそうなら、`guard reject` は再帰 loop の `queue=[k1]` ではなく、outer loop の `queue=[]` で捕まり、write18-report の観察どおり `uncons nil` になる。

# 触らない方がいいもの

この作業で雑に触ると、かなり壊れやすい場所がある。

* `handle_scope_return` の owner check は緩めない
* write17 の `Return(Thunk)` pre-force path は再有効化しない
* `return_frame_threshold` は外さない
* `ApplyClosure` 全体を global に `EffectfulApply` 化しない
* `ForceThunk` 全体を global に `EffectfulForce` 化しない
* Cranelift backend は同時に直そうとしない
* `fold_impl` の write18 fix は戻さない

理由はかなり明確。write17 で pre-force を試した結果、thunk body が `fold_impl` の `current_function` で走り、`each` 側で install された `H_sub.escape_owner_function` と一致せず、`ScopeReturn` が root へ escape した。既存 flow は `continue_return_frames` 経由で `each` の continuation に戻るから owner check を満たせる。ここは壊さない方がいい。

# 現状の設計整理

TODO 索引上、native backend track は CPS / control IR、Cranelift backend、VM と native の比較を進める主線に置かれている。ただし今の `std::undet.once` は Cranelift より前に CPS eval semantics を固める段階だねぇ。

CPS IR には、通常 stmt として `ForceThunk` / `ApplyClosure` / `Resume` / `ResumeWithHandler` があり、terminator として `EffectfulCall` / `EffectfulApply` / `EffectfulForce` がある。terminator 側は「post-call continuation を return frame として積む」目的のものだよ〜。

write15 では、`std::list::fold_impl`、`std::undet::undet::each`、`std::undet::undet::once` が `higher_order_helper` として扱われ、内部の effectful call/apply を targeted に `EffectfulCall` / `EffectfulApply` 化した。さらに `return_frame_threshold` が入り、handler install 後に積まれた frames を non-local exit 時に切る設計が入っている。

write16 では `std::undet::undet::once` 内の closure apply を無条件 `EffectfulApply` 化し、`EffectfulApply(Resumption)` の frame order も修正済み。`continue_return_frames` は末尾 pop なので、`[parent_frames..., F_post, resumption_frames...]` の順で積み、captured frames を先に pop する形に直っている。

write18 では、`fold_impl` の node branch で `fold_impl(left)` の Thunk を force せずに `fold_impl(right, z=Thunk_left, f)` へ渡していた問題を修正した。具体的には `cps_lower.rs` の `higher_order_helper && info_returns_thunk` な `EffectfulCall` path で、post-cont の result に `force_if_non_thunk_demand(result, &expr.ty)` をかけるようにした。

# 実装LLMへの作業指示

## 0. baseline を固定する

まず作業前にこの4本を走らせる。

```bash
cargo test -p yulang-native

cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

write18 後の期待値はこれ。

```text
cargo test -p yulang-native
  => pass

debugs_local_choice_caller_rest_eval
  => pass

debugs_local_choice_callback_rest_eval
  => pass

debugs_std_undet_once_skip_eval_layers
  => fail
  => cps:0 vs vm:2
```

ここで `cps:3 vs vm:2` なら write18 fix が入っていない可能性が高い。
ここで local choice 系が落ちるなら、`initial_frame_count` / return frame の土台が壊れている。

## 1. trace を増やす

既存の `YULANG_CPS_TRACE_FRAMES` を使っていいけど、出力が多すぎるなら `YULANG_CPS_TRACE_UNDET` を追加して、関数名を次に絞ると読みやすい。

```text
std::undet::undet::once
std::undet::undet::each
std::list::fold_impl
root
work
guard
```

追加する trace helper は、巨大な `Debug` dump ではなく、短い summary にする。

```rust
fn value_summary(value: &CpsRuntimeValue) -> String
fn handlers_summary(handlers: &[CpsHandlerFrame]) -> String
fn frames_summary(frames: &[CpsReturnFrame]) -> String
fn arg_summary(value: &CpsRuntimeValue) -> String
```

`value_summary` は最低限これを区別する。

```text
Plain(Int("1"))
Plain(Bool(true))
Plain(Bool(false))
Plain(Unit)
Thunk(owner=..., entry=...)
Closure(owner=..., entry=...)
Resumption(owner=..., target=..., frames.len=...)
Variant(tag=..., has_payload=...)
List(len=..., item_kinds=[Resumption, ...])
ScopeReturn(prompt=..., target=...)
```

特に `List` は重要。queue が `List([Resumption(k1)])` なのか、`List([])` なのか、VM value に落ちて resumption を失っているのかを見る。

## 2. trace を入れる場所

### `CpsStmt::InstallHandler`

handler install 時点の threshold を見る。

```text
InstallHandler:
  fn
  cont
  handler id
  escape
  return_frames.len
  threshold = return_frames.len
  active_handlers before/after
```

### `CpsTerminator::Perform`

resumption snapshot がどう捕まっているかを見る。

```text
Perform:
  fn
  cont
  effect path
  payload summary
  handler id
  blocked
  resume continuation
  return_frames.len
  initial_frame_count
  active_handlers summary
  captured resumption:
    owner_function
    target
    values summary if cheap
    handlers summary
    guard_stack summary
    return_frames summary
```

### `CpsTerminator::EffectfulApply`

ここが最重要。`once` の branch arm と reject arm の curried apply を追う。

```text
EffectfulApply:
  fn
  cont
  callable kind = Closure | Resumption | Other
  arg summary
  resume continuation
  pre_push_count
  new frame = owner fn / resume cont / owner_initial
  return_frames before
  return_frames after push

if Closure:
  closure owner
  closure entry
  passed initial_frame_count
  closure captured values summary

if Resumption:
  resumption owner
  resumption target
  resumption return_frames summary
  extra handlers summary
  combined_frames summary
  passed initial_frame_count
```

`EffectfulApply(Resumption)` では、combined frame の順序を必ず出す。期待は write16 の通り。

```text
combined_frames = parent_frames + [F_post] + adjusted_resumption_frames
pop order       = adjusted_resumption_frames first, then F_post, then parent
```

### `CpsStmt::ApplyClosure`

write16 後でも sync `ApplyClosure(Resumption)` が残っていないかを確認する。

```text
ApplyClosure:
  fn
  cont
  callable kind
  arg summary
  return_frames.len
  initial_frame_count

if Resumption:
  adjusted_frames summary
  passed initial_frame_count
```

### `CpsStmt::ForceThunk`

`loop` に渡された `x: [_] _` がいつ force されるかを見る。

```text
ForceThunk:
  fn
  cont
  thunk summary
  active_handlers summary
  return_frames.len
  initial_frame_count
  selected handlers source = current | thunk snapshot
  selected guards source = current | thunk snapshot
  owner function
  passed initial_frame_count
```

### `CpsTerminator::Return`

Return が frame を consume するかを見る。

```text
Return:
  fn
  cont
  value summary
  return_frames.len
  initial_frame_count
  will_consume_frames = return_frames.len > initial_frame_count
```

### `continue_return_frames`

どの frame に戻るかを見る。

```text
ContinueReturnFrames:
  value summary
  frames.len before
  popped owner_function
  popped continuation
  rest.len
  owner_initial_frame_count
  owner_initial_after_clamp
  popped active_handlers summary
```

### `handle_scope_return`

owner mismatch と threshold truncate を見る。

```text
ScopeReturnDispatch:
  current_function
  prompt
  target
  matched yes/no
  matched frame owner
  inherited
  owner_match yes/no
  return_frame_threshold
  return_frames.len before truncate
  return_frames.len after truncate
  action = Value | JumpOrExit | Propagate
```

### CPS list primitives

queue は resumption を含むので、VM primitive に落ちると壊れる。`ListLen` / `ListIndex` / `ListIndexRangeRaw` / `merge` / `append` 相当の箇所で、最低限これを見る。

```text
ListPrimitive:
  op
  arg summaries
  result summary
```

`std::list::uncons` は `len`, `index_raw`, `index_range_raw` を使う。queue が resumption-bearing list のまま維持されるかが大事だよ〜。

## 3. trace 実行

```bash
YULANG_CPS_TRACE_FRAMES=1 \
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

出力が多すぎるならこう。

```bash
YULANG_CPS_TRACE_UNDET=1 \
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

# 判定表

## Case A: recursive `loop(k true, queue+[k])` が呼ばれていない

症状はこれ。

```text
x=1 branch true
once branch arm に入る
queue + [k] は作る、または作る前に
k true が eager に replay される
recursive loop の InstallHandler が出ない
guard reject が outer loop の queue=[] で処理される
uncons nil
```

これは今の trace 観察に一番合う。

この場合の修正候補は `cps_lower.rs::lower_apply` / `lower_expr_as_call_arg` 側。`once` の `loop` 第一引数は `x: [_] _` なので、`k true` は **Thunk value として渡る必要がある**。再帰 loop が handler を install したあと、その catch body の中で `x` が force されるべきだねぇ。

要するに、branch arm は意味的にこうでないといけない。

```text
let x_thunk = thunk { k true }
let queue2 = append queue [k]
loop(x_thunk, queue2)
```

ダメな形はこれ。

```text
let x_value = k true        // ここで eager replay
let queue2 = append queue [k]
loop(x_value, queue2)
```

この eager replay が起きると、再帰 loop の `queue=[k1]` がまだ存在しないので、後続 reject が outer queue `[]` で捕まる。

### Case A の修正手順

1. `FunctionLowerer::lower_apply` を読む。
2. `let arg = self.lower_expr_as_call_arg(&callee.ty, arg)?;` が、`force_effectful_apply` の有無に関係なく、callee の第一引数型を正しく見ているか確認する。
3. `callee.ty` が `Fun` なら第一引数型を取り出す。
4. 第一引数型が `Thunk { .. }` なら、`arg` は必ず `lower_expr_as_thunk_value(arg)` で lowering する。
5. `force_effectful_apply` は「apply を terminator にする」だけに限定し、**引数を eager に評価する理由にしない**。
6. `loop(k true, queue+[k])` の CPS dump を取り、`k true` が `MakeThunk` の body に入っていることを確認する。
7. その thunk body の中で `k true` を replay する apply/resume が現れるのはOK。外側の branch arm 本体で先に replay されるのはNG。

もし `callee.ty` が curried partial のせいで `unknown` や plain `Fun/Core` になって第一引数型が取れないなら、次のどちらかにする。

```text
優先: closure value に param type を持たせる / FunctionInfo から local function param type を引く
暫定: std::undet::undet::once の local loop に限定して第一引数を Thunk lowering する
```

暫定策を入れる場合も、continuation id や mono 番号に依存しない方がいい。`std::undet::undet::once` 内の local recursive `loop` で、第一引数の source type が `[_] _` であることを使うのが安全だねぇ。

## Case B: recursive loop は呼ばれるが、queue が空

症状。

```text
once branch arm:
  recursive loop InstallHandler は出る
  loop に渡る x は Thunk
  でも queue arg summary が List(len=0)
```

この場合、`std::list::append queue [k]` の lowering / primitive eval / argument order が怪しい。

見る場所。

```text
queue + [k] の構築
std::list::append / merge
CpsRuntimeValue::List の item kind
Tuple/List/Variant 経由で Resumption が VM value に落ちていないか
curried apply の第二引数が本当に queue2 か
```

修正は `eval_cps_primitive` の list ops か、lowering の引数順ミスになる可能性が高い。

期待 trace。

```text
branch arm before append:
  queue = List(len=0)

after append queue [k]:
  queue2 = List(len=1, item_kinds=[Resumption])

recursive loop apply:
  arg2 = List(len=1, item_kinds=[Resumption])
```

## Case C: queue は len=1 だが `uncons` が nil

症状。

```text
recursive loop:
  queue = List(len=1, item_kinds=[Resumption])

reject arm:
  std::list::uncons queue
  len op returns 0
  or Variant nil returned
```

これは list primitive 側のバグ。resumption-bearing list が `runtime::VmValue` に変換できず、途中で空扱いになっている可能性がある。

見る場所。

```text
eval_cps_primitive:
  ListLen
  ListIndex
  ListIndexRangeRaw

cps_value_to_vm:
  Resumption を含む List を VM value に落としていないか

std::list::uncons lowering:
  len / index_raw / index_range_raw が CPS-domain で処理されるか
```

この場合は、queue に resumption が入っている限り、必ず `CpsRuntimeValue::List` domain のまま処理する。VM primitive fallback に流すと壊れる。

## Case D: queue replay は正しいが `sub::return 2` 後に戻り先が違う

症状。

```text
k1 false replay
x=2 branch Perform
branch true
sub::return 2
でも once value arm の just 2 に到達しない
または fold/each の rest が残る
```

この場合は `return_frame_threshold` / `ScopeReturnDispatch` / frame order を疑う。

ただし今の write18 観察とは少し遠い。第一候補ではないよ〜。

見る場所。

```text
H_sub install 時の threshold
sub::return 2 ScopeReturnDispatch
truncate 前後の return_frames.len
ContinueReturnFrames の pop owner
once value arm の Return
```

# もっとも可能性の高い修正

私の読みでは、最初に狙うべき修正はこれ。

> `std::undet.once` の recursive `loop` 第一引数 `x: [_] _` に渡る `k true` / `k false` が、常に thunk-typed call arg として lower されるようにする。

write16 で `once` 内 apply は無条件 `EffectfulApply` 化済みだけど、それは「post frame を積む」修正であって、「thunk-typed 引数を thunk として渡す」修正とは別物だねぇ。`force_effectful_apply` が立っていても、引数 lowering は callee の param type を尊重する必要がある。

`cps_lower.rs` では、direct call の引数は `FunctionInfo` の params を見て `lower_expr_as_thunk_value` / `force_if_non_thunk_demand` を選ぶ流れがある。一方 closure apply は `callee.ty` から引数型を推定する必要がある。ここで curried partial / local recursive closure / mono 化後の型が不安定だと、`k true` が eager lowering されやすい。

実装LLMには、まずここを audit させるのが良い。

```text
crates/yulang-native/src/cps_lower.rs

確認対象:
- FunctionLowerer::lower_apply
- lower_expr_as_call_arg
- lower_expr_as_thunk_value
- force_effectful_apply
- higher_order_helper
- direct_apply_path / FunctionInfo params を使う direct call path
```

期待する lowering の形はこれ。

```text
once branch arm:
  k_true_thunk = MakeThunk { body: EffectfulApply/Resume k true }
  queue2 = append queue [k]
  EffectfulApply loop k_true_thunk -> post
  EffectfulApply post queue2 -> ...
```

避けたい lowering はこれ。

```text
once branch arm:
  EffectfulApply k true -> result
  queue2 = append queue [k]
  EffectfulApply loop result -> ...
```

後者だと recursive loop の handler が入る前に `k` が replay される。

# 成功条件

最終的にこの状態を満たす。

```text
cargo test -p yulang-native
  => pass

cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture
  => pass

cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture
  => pass

cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
  => CPS eval: 2 / VM: 2
```

trace 上の成功条件はこれ。

```text
x=1:
  branch true
  once branch arm stores k1
  recursive loop starts with queue=[k1]

guard reject:
  reject is caught by recursive loop, not outer loop
  uncons queue returns just(k1, [])

k1 false:
  x=2 path resumes

x=2:
  branch true
  sub::return 2
  once value arm returns just 2
  root returns 2
```

# 実装LLMに渡す短い指示文

そのまま渡すなら、これでよさそうだよ〜。

```text
目的:
debugs_std_undet_once_skip_eval_layers を CPS eval:2 / VM:2 に一致させる。

現在の基準:
write18 後。fold_impl LEFT recursion の Thunk force 漏れは修正済み。
現状は cps:0 vs vm:2。
第一イテレーションの branch/sub::return/guard reject は正しく動く。
残バグは once reject arm で queue が空扱いになり uncons nil になること。

絶対にやらないこと:
- handle_scope_return の owner check を緩めない。
- write17 の Return(Thunk) pre-force helper を有効化しない。
- return_frame_threshold を外さない。
- ApplyClosure / ForceThunk を global に effectful 化しない。
- Cranelift backend を同時に直さない。

最初にやること:
YULANG_CPS_TRACE_FRAMES または YULANG_CPS_TRACE_UNDET で、
once branch arm の loop(k true, queue+[k]) と reject arm の uncons queue を追う。

trace 必須項目:
- InstallHandler: handler, escape, return_frames.len, threshold
- Perform: effect, payload, resume, captured return_frames, captured handlers
- EffectfulApply: Closure/Resumption, arg summary, new frame, combined_frames
- ApplyClosure: Closure/Resumption, arg summary
- ForceThunk: thunk owner, selected handlers, return_frames, initial
- Return: value summary, will_consume_frames
- ContinueReturnFrames: popped owner/cont/rest.len/owner_initial
- ScopeReturnDispatch: matched, owner_match, threshold, truncate 前後
- List primitives: queue len と item kind

判定:
A. recursive loop が呼ばれず outer queue=[] で reject される
   => k true が eager replay されている可能性が高い。
      lower_apply / lower_expr_as_call_arg を直し、
      loop 第一引数 x: [_] _ に渡る k true を MakeThunk 化する。

B. recursive loop は呼ばれるが queue=[]
   => queue+[k] の lowering / arg order / append の CPS-domain 処理を直す。

C. queue=len1 だが uncons nil
   => ListLen/ListIndex/ListIndexRangeRaw が resumption-bearing List を VM fallback に落としている。
      CpsRuntimeValue::List domain のまま処理する。

D. queue replay 後に sub::return 2 が wrong extent
   => return_frame_threshold / EffectfulApply(Resumption) frame order を trace で見る。

最有力修正:
std::undet.once の local recursive loop は第一引数が x: [_] _。
branch arm の loop(k true, queue+[k]) では、
k true を eager に resume せず、Thunk value として loop に渡す。
force_effectful_apply は apply terminator 化だけを担い、引数 thunking を潰さない。
```

この順でやるのが一番安全だと思うよ〜。今の残バグは「resumption frame order」単体より、**recursive loop の handler が install される前に `k true` を走らせているかどうか**が分水嶺に見えるねぇ。
