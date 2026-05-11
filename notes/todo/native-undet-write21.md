まず正直な前提から置くねぇ。

接続できた `momota1029/yulang` の `main` では、`notes/todo/native-undet-write20-report.md` は見つからなかった。`native-undet-write19*` も検索・直接 fetch ともに見えなかったよ〜。見える最新は `native-undet-write18-report.md` だった。だから以下は **write18-report までの実資料 + 現在見えるコード + 過去チャット文脈** に基づく、実装LLM向けの手順だよ。もし実装LLM側の作業ツリーに `write19-report` / `write20-report` が実在するなら、まずそれを読んで「現状結果」と「既に入った修正」を上書きしてねぇ。

---

# 結論

次にやるべき本筋はこれ。

> **`std::undet.once` の queue replay がなぜ空 queue になるかを、`ApplyClosure` / `EffectfulApply` / resumption replay / recursive `loop` call の順で trace し、`loop(k true, queue + [k])` が「queue=[k] を持つ再帰 loop」として成立する前に `k true` 側の effectful computation が走っていないかを確定する。**

write18 後の重要な現状は、`fold_impl` の左部分木が捨てられるバグは直っていて、`cps:3` は `cps:0` に変わった。ただしこれは成功ではなく、1回目の `branch -> sub::return 1 -> guard reject` までは正しく進んだあと、`once` の reject arm で `uncons queue` が `nil` になって最終値 0 へ落ちている状態だねぇ。期待では queue に `k1` が入っているはず、というのが write18-report の引き継ぎ。

---

# 現在地の整理

Native Backend track 全体では、VM を oracle にして CPS / native 側を広げる方針で、`std::undet` 系 finite nondet は early target として扱われている。つまりここは「後で触る難物」ではなく、CPS semantics の中核 regression として見るべき場所だねぇ。

CPS IR には、通常 statement の `ApplyClosure` / `Resume` / `ResumeWithHandler` と、terminator 側の `EffectfulCall` / `EffectfulApply` / `EffectfulForce` がある。今回の問題はほぼこの境界にあるよ〜。

これまでの流れはこう。

| 段階      | 入ったもの                                                                                     | 結果                                                            |
| ------- | ----------------------------------------------------------------------------------------- | ------------------------------------------------------------- |
| write14 | `initial_frame_count`。sync call は caller frames を inherit するが通常 `Return` では consume しない設計 | local callback test が通る。`std::undet.once` はまだ `cps:0 vs vm:2` |
| write15 | `fold_impl` / `each` / `once` 向け targeted `EffectfulCall/Apply`、`return_frame_threshold`  | `cps:0 -> cps:3`。探索は動くが 2 で止まらず 3                             |
| write16 | `once` 内の apply を全部 `EffectfulApply` 化、`EffectfulApply(Resumption)` の frame order 修正      | まだ `cps:3`                                                    |
| write17 | `Return(Thunk)` pre-force を試す                                                             | `escape_owner_function` と衝突。無効化が正解                            |
| write18 | `fold_impl` の LEFT result を demand-side force                                             | `cps:3 -> cps:0`。1回目は正しいが queue が空                            |

write14 の `initial_frame_count` は壊さない。sync call が frames を渡すが consume しない、Effectful terminator は post frame を push して callee に `initial_frame_count = pre_push_count` を渡す、Resume 系は captured frames を consume するため `initial=0`、という区別が土台だよ。

write17 の pre-force は戻さない。`fold_impl` thunk body を `current_function = fold_impl` で走らせると、`each` 側に install された `H_sub.escape_owner_function = each` と合わず、`ScopeReturn` が解決されず escape する。`handle_scope_return` の owner check を緩めるのも危ない。

---

# 最優先で疑う場所

一番ありそうなのはここ。

```text
once branch arm:

branch(), k -> loop(k true, queue + [k])
```

write16 で `std::undet.once` 内の apply は全部 `EffectfulApply` 化された。これは当時は必要だったけど、write18 後の残バグでは **広すぎる可能性** がある。特に `k true` が recursive `loop` の第1引数として渡される前に、`EffectfulApply(k, true)` として即実行されると、`queue + [k]` を持つ再帰 `loop` が立つ前に `sub::return 1` / guard reject が走る可能性がある。

そうなると、reject が発生した時点の `queue` は outer loop の `[]` のままになる。write18-report の「recursive loop が呼ばれていない、または reject が再帰前に発生している」という候補とぴったり合うねぇ。

ただし決め打ちで修正しない。まず trace で確定する。

---

# 実装LLMに渡す手順

## Step 0: baseline を固定する

作業前にこの4本を走らせる。

```bash
cargo test -p yulang-native

cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

write18 時点の期待値はこれ。

```text
cargo test -p yulang-native
  => pass

debugs_local_choice_caller_rest_eval
  => pass

debugs_local_choice_callback_rest_eval
  => pass

debugs_std_undet_once_skip_eval_layers
  => fail
  => CPS eval: 0
  => VM:       2
```

もし `cps:3` なら write18 fix が入っていない。もし local callback tests が落ちるなら write14/15 系の frame semantics が壊れている。そこで止めて差分を先に見る。

---

## Step 1: trace を増やす

`cps_eval.rs` には `YULANG_CPS_TRACE_FRAMES` で有効になる trace がある。write18 で `Return` / `ContinueReturnFrames` / `ScopeReturnDispatch` は強化済みだけど、今回必要なのは **queue と recursive loop の値の流れ** だよ。

追加する helper はこの粒度で十分。

```rust
fn fmt_cps_value_short(value: &CpsRuntimeValue) -> String {
    match value {
        CpsRuntimeValue::Plain(runtime::VmValue::Int(n)) => format!("Int({n})"),
        CpsRuntimeValue::Plain(runtime::VmValue::Bool(b)) => format!("Bool({b})"),
        CpsRuntimeValue::Plain(runtime::VmValue::Unit) => "Unit".to_string(),
        CpsRuntimeValue::Plain(v) => format!("Plain({v:?})"),
        CpsRuntimeValue::Thunk(t) => {
            format!("Thunk(owner={}, entry={:?})", t.owner_function, t.entry)
        }
        CpsRuntimeValue::Closure(c) => {
            format!("Closure(owner={}, entry={:?})", c.owner_function, c.entry)
        }
        CpsRuntimeValue::Resumption(r) => {
            format!(
                "Resumption(owner={}, target={:?}, frames={})",
                r.owner_function,
                r.target,
                r.return_frames.len()
            )
        }
        CpsRuntimeValue::Variant { tag, value } => {
            match value {
                Some(v) => format!("Variant({tag:?}, {})", fmt_cps_value_short(v)),
                None => format!("Variant({tag:?})"),
            }
        }
        CpsRuntimeValue::Tuple(items) => {
            let items = items.iter().map(fmt_cps_value_short).collect::<Vec<_>>();
            format!("Tuple({})", items.join(", "))
        }
        CpsRuntimeValue::List(items) => {
            let preview = items.iter().take(4).map(fmt_cps_value_short).collect::<Vec<_>>();
            format!("List(len={}, [{}])", items.len(), preview.join(", "))
        }
        CpsRuntimeValue::ScopeReturn { prompt, target, value } => {
            format!(
                "ScopeReturn(prompt={}, target={:?}, value={})",
                prompt.0,
                target,
                fmt_cps_value_short(value)
            )
        }
    }
}
```

同じく frames / handlers 用も作る。

```rust
fn fmt_handlers_short(handlers: &[CpsHandlerFrame]) -> String {
    handlers
        .iter()
        .map(|h| {
            format!(
                "(prompt={}, handler={:?}, inherited={}, owner={}, threshold={})",
                h.prompt.0,
                h.handler,
                h.inherited,
                h.escape_owner_function,
                h.return_frame_threshold
            )
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn fmt_frames_short(frames: &[CpsReturnFrame]) -> String {
    frames
        .iter()
        .enumerate()
        .map(|(i, f)| {
            format!(
                "#{i}(owner={}, cont={:?}, owner_initial={}, handlers=[{}])",
                f.owner_function,
                f.continuation,
                f.owner_initial_frame_count,
                fmt_handlers_short(&f.active_handlers)
            )
        })
        .collect::<Vec<_>>()
        .join(" | ")
}
```

巨大 dump ではなく、値の種類・owner・continuation・queue length が見えれば十分。

---

## Step 2: trace point を入れる

### 2.1 `Perform`

`branch` / `reject` / `sub::return` の順番を見る。

出す情報。

```text
Perform:
  fn
  cont
  effect path
  payload
  blocked
  resume cont
  return_frames.len
  initial_frame_count
  active_handlers
  captured resumption frames
```

ここで見たい事実はこれ。

```text
1回目 branch が起きる
k1 が queue に追加される
sub::return 1 が起きる
guard reject が起きる
その reject が outer loop queue=[] で処理されているのか、
recursive loop queue=[k1] で処理されているのか
```

### 2.2 `EffectfulApply`

write16 で一番大事になった場所。特に `callable=Resumption` と `callable=Closure` の両方を出す。

```text
EffectfulApply:
  fn
  cont
  callable kind
  callable short
  arg short
  resume cont
  pre_push_count
  new_frames = parent + F_post
  if resumption:
    resumption owner
    resumption target
    resumption frames
    combined_frames
    initial passed to replay
```

write16 では `EffectfulApply(Resumption)` の frame order を `parent + [F_post] + res_frames` に直している。`continue_return_frames` は末尾 pop だから、captured frames が先に走る順序が必要、という修正だねぇ。

### 2.3 `ApplyClosure`

これも必須。surface 上は closure apply でも runtime value が `Resumption` になることがある。`cps_eval.rs` もその分岐を持っている。

```text
ApplyClosure:
  fn
  cont
  callable kind
  callable short
  arg short
  return_frames.len
  initial_frame_count
  adjusted_frames if Resumption
```

`once` 内は多くが `EffectfulApply` になっているはずだけど、reject arm の queue から取り出した continuation apply が stmt path に残る可能性は潰しておく。

### 2.4 `InstallHandler`

recursive `loop` が本当に新しい queue を捕まえた scope を作ったかを見る。

```text
InstallHandler:
  fn
  cont
  handler id
  escape cont
  prompt
  return_frame_threshold
  active_handlers before/after
```

ここで、recursive loop が呼ばれていないなら install 自体が出ない。呼ばれているのに queue が空なら、closure capture / parameter binding / handler env が怪しい。

### 2.5 `Return` / `continue_return_frames` / `ScopeReturnDispatch`

write18 で既に入っているけど、値表示に `Variant(nil/just)` と `List(len=...)` を出す。

特に見るところ。

```text
ScopeReturnDispatch:
  prompt
  target
  owner_match
  threshold
  return_frames.len before truncate
  return_frames.len after truncate
```

`return_frame_threshold` は消さない。壊れているなら「どの handler install の threshold が何フレームを消したか」を見てから直す。

### 2.6 `eval_cps_primitive` の list/uncons 系

`std::list::uncons` が primitive で処理されるなら、そこにも trace を足す。

```text
Primitive ListUncons:
  input = List(len=N, ...)
  output = Variant(nil) / Variant(just, Tuple(head, tail))
```

write18 の終盤では `once cont 5` が `Discriminant(6)` を返していて、おそらく `opt::nil` だと読まれている。ここを曖昧にしない。

---

## Step 3: CPS shape dump を先に見る

この ignored debug test が既にある。`source.rs` には `debugs_std_undet_once_cps_shape` があり、`once` / `loop` / `each` / `root` の CPS を dump する用途になっている。

実行する。

```bash
cargo test -p yulang-native debugs_std_undet_once_cps_shape -- --ignored --nocapture \
  2>&1 | tee /tmp/once-shape.log
```

探す形はこれ。

```text
std::undet::undet::once...
  branch arm
    k true
    queue + [k]
    loop (k true) (queue + [k])
```

CPS がこうなっていたら要注意。

```text
EffectfulApply { closure: k, arg: true, resume: ... }
... later ...
build queue + [k]
... later ...
call loop
```

この順序だと、`k true` の resumption replay が recursive loop call より先に走る可能性がある。

望ましい形は概念的にはこう。

```text
make/delay first argument for loop = thunk/resumption application k true
build queue2 = queue + [k]
call loop with x = delayed(k true), queue = queue2
```

`k true` の中身が effectful でも、「recursive loop の queue 環境」が先に成立していないと reject arm が空 queue を見る。

---

## Step 4: trace 実行

```bash
YULANG_CPS_TRACE_FRAMES=1 \
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture \
  2>&1 | tee /tmp/once-trace.log
```

ログはこの順で読む。

```text
1. 最初の branch Perform
2. once branch arm に入る
3. k1 が queue に追加される値が作られるか
4. recursive loop call が起きるか
5. recursive loop の InstallHandler が起きるか
6. sub::return 1 が each に戻るか
7. guard reject がどの loop scope で処理されるか
8. reject arm の uncons queue が nil か just か
```

期待される健全なイベント列はこう。

```text
branch x=1
once branch arm receives k1
queue2 = [k1]
recursive loop starts with queue2
sub::return 1
guard reject
once reject arm uncons queue2 -> just(k1, [])
resume k1 false
x=2 path starts
branch x=2
sub::return 2
once value arm -> just 2
root case just x -> 2
```

現在の壊れ方はおそらくこう。

```text
branch x=1
once branch arm receives k1
EffectfulApply(k1, true) runs immediately
sub::return 1
guard reject
reject arm sees outer queue=[]
uncons [] -> nil
root case nil -> 0
```

この違いが見えれば勝ちだよ〜。

---

# 分岐別の修正方針

## Case A: `k true` が recursive loop call より前に実行されている

これが本命。

### 症状

trace にこう出る。

```text
once branch arm
EffectfulApply callable=Resumption(k1) arg=true
...
Perform sub::return 1
...
reject arm uncons queue len=0
...
queue + [k1] / recursive loop call がまだ起きていない
```

### 修正方針

write16 の `force_effectful_apply` を狭める。

現在の方針は、`std::undet::undet::once` 内の全 `ApplyClosure` を無条件 `EffectfulApply` 化するものだった。これは curried `k true`, `loop k`, `(loop k) queue+[k]` の型判定漏れを補うためだったけど、今の段階では **`k true` を eager に走らせすぎる** 可能性が高い。

実装LLMに伝えるべき修正案はこれ。

```text
- once 内の ApplyClosure を全て EffectfulApply にする blanket rule をやめる。
- 少なくとも「関数呼び出しの thunk 引数として lower される apply」は、先に EffectfulApply として実行しない。
- `loop(k true, queue + [k])` の `k true` は、recursive loop の第1引数として渡す delayed computation として lower する。
- recursive loop call が queue=[k] を持つ scope を作った後、その body の中で k true が force/evaluate される形にする。
```

具体的には `cps_lower.rs` でこの周辺を読む。

```rust
FunctionLowerer::lower_apply
FunctionLowerer::lower_expr_as_call_arg
FunctionLowerer::lower_expr_as_thunk_value
FunctionLowerer::force_effectful_apply
FunctionLowerer::higher_order_helper
```

修正の形はこう。

```text
should_emit_effectful_apply(expr, callee, arg, context) を作る。

true:
  - handler scope 内で、その apply の post-cont を resumption に捕捉する必要がある
  - apply result をその場で computation として進める

false:
  - apply result が callee の Thunk 引数として渡される
  - 特に once branch arm の `k true` が recursive `loop` の第1引数になる
```

最小パッチは `lower_expr_as_call_arg(expected_ty, arg)` 側で、`expected_ty` が `Thunk` の場合に `lower_expr_as_thunk_value(arg)` を優先し、`force_effectful_apply` による即 `EffectfulApply` を避けること。write15 で call arg の demand-side forcing が入っているので、その経路を丁寧に読む必要がある。

### 成功条件

CPS shape がこう変わる。

```text
branch arm:
  build delayed x = thunk/resumption application k true
  build queue2 = queue + [k]
  call loop delayed_x queue2
```

trace では、guard reject の時点で reject arm の queue が `List(len=1, [Resumption(k1)])` になる。

---

## Case B: recursive loop は呼ばれるが queue param が空

### 症状

trace にこう出る。

```text
recursive loop call appears
InstallHandler for recursive loop appears
but loop param queue is List(len=0)
```

### 修正方針

closure capture / curried apply の引数束縛を見る。

読む場所。

```text
CpsStmt::MakeClosure
CpsStmt::MakeRecursiveClosure
CpsStmt::ApplyClosure(Closure)
assign_continuation_args
lower_apply の curried apply lowering
```

見ること。

```text
- `queue + [k]` の結果 value id が recursive loop の第2引数に渡っているか
- partial apply `loop k_true` の closure values に古い queue=[] が captured されていないか
- `MakeRecursiveClosure` の `recursive_self` 注入で values snapshot が古いままになっていないか
```

この場合、`EffectfulApply` の eager 問題ではなく、closure snapshot または continuation args の値流れが壊れている。

---

## Case C: queue は `[k1]` なのに `uncons` が `nil`

### 症状

trace にこう出る。

```text
recursive loop queue = List(len=1)
reject arm reads queue = List(len=1)
Primitive/ListUncons returns Variant(nil)
```

### 修正方針

これは value representation / primitive eval の問題。`CpsRuntimeValue::List` と `VmValue::List` の往復、`eval_cps_primitive` の list operation、`Variant` / `TupleGet` / `VariantPayload` を見る。

ただし可能性は低そう。write18-report の観察では queue が空に見えているので、まず Case A/B を優先する。

---

## Case D: `sub::return 1` 後の `return_frame_threshold` が recursive loop frame を捨てる

### 症状

trace にこう出る。

```text
recursive loop queue=[k1] is established
then sub::return 1 ScopeReturnDispatch
return_frames.truncate(threshold)
recursive loop / once branch post frame disappears
guard reject occurs in outer scope
```

### 修正方針

`return_frame_threshold` の値を修正する。ただし絶対に消さない。

見る場所。

```text
InstallHandler:
  return_frame_threshold = return_frames.len()

ScopeReturnDispatch:
  threshold
  before truncate len
  after truncate len
```

`return_frame_threshold` は handler install 後に積まれた frames を non-local exit で捨てるために必要な仕組みだよ。write15 で入って、local tests を壊さず `std::undet.once` を前進させている。

もし threshold が recursive loop の外側まで切っているなら、handler install のタイミングか、resumption replay 時に frame に入っている active_handlers snapshot が古い。

---

## Case E: `k false` replay の frame order が違う

### 症状

```text
reject arm uncons queue -> just(k1, [])
k1 false replay starts
but x=2 branch へ戻らない
または post frame が captured frames より先に走る
```

### 修正方針

resumption replay の全経路を横並びで audit する。

```text
CpsTerminator::EffectfulApply(Resumption)
CpsStmt::ApplyClosure(Resumption)
CpsStmt::Resume
CpsStmt::ResumeWithHandler
inject_extra_handlers
continue_return_frames
```

`EffectfulApply(Resumption)` は write16 で `parent + [F_post] + adjusted_res` に修正済み。`continue_return_frames` は末尾から pop するので、captured frames が末尾側に必要だねぇ。

`ApplyClosure(Resumption)` / `Resume` / `ResumeWithHandler` は F_post を持たない sync replay なので、基本は `adjusted_res` を `initial=0` で渡す。ただし extra handlers injection が frames 内の handlers を壊していないかは見る。

---

# やってはいけない修正

ここは実装LLMに強めに渡していい。

```text
- handle_scope_return の owner check を緩めない。
- write17 の Return(Thunk) pre-force path を再有効化しない。
- global に ApplyClosure 全体を EffectfulApply 化しない。
- global に ForceThunk 全体を EffectfulForce 化しない。
- return_frame_threshold を削除しない。
- initial_frame_count の基本設計を崩さない。
- Cranelift 対応を同時に進めない。
- expected value を 0 に変えない。
- failing debug test を ignore して終わらせない。
```

特に owner check は危ない。`target` の continuation id は function-local だから、`fold_impl` 文脈で `each` の escape continuation を直接解決するのは意味的に壊れている。write17 がそこを実験で踏んでいる。

---

# 最終的な成功条件

まず Layer 1 の CPS eval を VM に合わせる。

```bash
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

期待。

```text
CPS eval: 2
VM:       2
```

そのあと必ず回す。

```bash
cargo test -p yulang-native

cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture
```

trace 上の成功条件はこれ。

```text
1. x=1 branch で k1 が once branch arm に渡る
2. queue2 = [k1] が作られる
3. recursive loop が queue2 を持って始まる
4. sub::return 1 後の guard reject が recursive loop の reject arm に届く
5. reject arm uncons queue2 -> just(k1, [])
6. k1 false replay により x=2 側へ進む
7. x=2 が value arm を通って just 2 になる
8. その後に余計な queue replay で x=3 へ進まない
```

---

# 実装LLMへそのまま渡す指示文

```text
目的:
debugs_std_undet_once_skip_eval_layers を CPS eval:2 / VM:2 に一致させる。

現状:
write18 後の見える最新状態では、fold_impl の LEFT recursion result force は修正済み。
これにより cps:3 は cps:0 に変わった。
第1 iteration の branch -> sub::return 1 -> guard reject までは正しく進む。
しかし once の reject arm で uncons queue が nil になり、root は nil -> 0 を返す。

最重要仮説:
once branch arm の `loop(k true, queue + [k])` で、
`k true` が recursive loop call / queue+[k] の成立より前に EffectfulApply として実行されている。
そのため guard reject 時に recursive loop の queue=[k] ではなく outer loop の queue=[] を見ている可能性が高い。

作業順:
1. baseline test を取る。
   cargo test -p yulang-native
   cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture
   cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture
   cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture

2. cps_eval.rs に値・frame・handler を短く表示する trace helper を追加する。
   表示対象:
   - CpsRuntimeValue: Int/Bool/Unit/Variant tag/List len/Thunk owner/Closure owner/Resumption owner+target
   - CpsReturnFrame: owner_function/continuation/owner_initial_frame_count/active handlers
   - CpsHandlerFrame: prompt/inherited/escape_owner_function/return_frame_threshold

3. 以下の場所に YULANG_CPS_TRACE_FRAMES guard 付き trace を入れる。
   - Perform
   - EffectfulApply
   - ApplyClosure
   - Resume
   - ResumeWithHandler
   - InstallHandler
   - Return
   - continue_return_frames
   - ScopeReturnDispatch / return_frames.truncate
   - list uncons primitive if applicable

4. CPS shape dump を取る。
   cargo test -p yulang-native debugs_std_undet_once_cps_shape -- --ignored --nocapture

   once branch arm の `loop(k true, queue + [k])` がどう lower されているかを見る。
   特に `EffectfulApply(k, true)` が queue+[k] / recursive loop call より前に出ていないかを見る。

5. trace 実行。
   YULANG_CPS_TRACE_FRAMES=1 \
   cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture

6. 分類する。
   A. k true が recursive loop call より前に走る
      -> once の blanket force_effectful_apply を狭める。
         thunk引数として渡される apply は即 EffectfulApply にしない。
         `loop(k true, queue+[k])` では、queue+[k] を持つ recursive loop scope を先に作る。
   B. recursive loop は始まるが queue param が []
      -> closure capture / curried apply / assign_continuation_args を修正する。
   C. queue は [k] なのに uncons が nil
      -> CpsRuntimeValue::List / VmValue::List / primitive uncons / VariantPayload を修正する。
   D. ScopeReturn truncate で recursive loop frame が消える
      -> return_frame_threshold の install 時点と frame snapshot を修正する。
         threshold は削除しない。
   E. k false replay が x=2 に戻らない
      -> EffectfulApply(Resumption), ApplyClosure(Resumption), Resume, ResumeWithHandler の frame order と extra handler injection を audit する。

7. 禁止:
   - handle_scope_return owner check を緩めない。
   - write17 pre-force を戻さない。
   - global ApplyClosure/ForceThunk effectful 化をしない。
   - Cranelift を同時に直さない。
   - return_frame_threshold を消さない。

成功条件:
- debugs_std_undet_once_skip_eval_layers が CPS eval:2 / VM:2
- cargo test -p yulang-native が pass
- debugs_local_choice_caller_rest_eval が pass
- debugs_local_choice_callback_rest_eval が pass
- trace 上、reject arm の uncons queue が nil ではなく just(k1, []) になる
- 2 が返った後に余計な replay で 3 へ進まない
```

---

# 私の推し修正順位

1. **trace で `k true` が早すぎるかを見る**
2. 早すぎるなら **`force_effectful_apply` を blanket から context-aware に狭める**
3. `lower_expr_as_call_arg` / `lower_expr_as_thunk_value` で **Thunk 引数は delayed に渡す** 原則を守る
4. それでも queue が空なら **closure capture / recursive loop arg binding** を見る
5. それでも駄目なら **threshold truncate / resumption frame order** を見る

いきなり evaluator の `handle_scope_return` をいじるのは沼だねぇ。今回の臭いは evaluator の owner check より、`once` branch arm の「再帰 loop を作る前に resumption を走らせている」順序問題に寄っていると思うよ〜。
