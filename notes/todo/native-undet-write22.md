手元のローカルには repo が見えなかったから、GitHub 側の `momota1029/yulang` を読んだよ〜。`cps_eval.rs` はツール表示が後半で切れる箇所があったけど、`handle_scope_return`・`eval_continuations`・`resume_continuation` の入口周辺、`ForceThunk` / `DirectCall` の return-frame 継承、関連レポート群までは読めている。結論はかなりはっきりしているよ〜。

## 結論

次に実装する本線は **CPS lowering ではなく `crates/yulang-native/src/cps_eval.rs` の eval-frame identity 導入**だねぇ。

`write21-report` の「`guard: n > 1` が CPS lowering で消えている」は、`write21-followup` で明確に訂正されている。`work__mono0` と `guard__mono3` の lowering は正しく、`guard(false)` は `perform reject` に落ちている。残りの本当の問題は、`handle_scope_return` が **同じ function 名なら同じ install scope と見なしてしまう**ことだよ〜。

今の `handle_scope_return` は write21 fix として、`frame.prompt == prompt && (!frame.inherited || frame.escape_owner_function == current_function)` でマッチしている。これにより `Resume(k1, true)` の中で走る `each__mono1` eval が、元の `each__mono1` eval に install された `H_sub` を早すぎる場所で拾ってしまう。コード上もその条件が入っている。

だから次は、**function identity ではなく eval-frame identity で ScopeReturn を解決する**。具体的には、各 eval 実行に `eval_id` を与え、`CpsHandlerFrame` に `install_eval_id`、`CpsReturnFrame` に `owner_eval_id` を持たせる。`ScopeReturn(prompt=p)` は、`prompt` だけでなく `install_eval_id == current_eval_id` の handler だけを解決対象にする。

---

## 何が壊れているか

期待する流れはこうだねぇ。

```text
1. work が each [1,2,3] を force
2. each の中で H_sub が install される
3. branch perform で k1 を capture
4. once branch arm が queue=[k1] で recursive once を起動
5. inner once prompt=2 が install される
6. Resume(k1, true) で x=1 path を再生
7. sub::return(1) は Resume eval では H_sub に match しない
8. 保存されている元 each の return frame まで戻って、そこで H_sub に match
9. work の続きに 1 が入り、guard false → reject
10. reject は inner once prompt=2 に捕まる
11. queue=[k1] から k1 false を再生
12. x=2 path が通り、結果は just(2)
```

でも write21 fix 後の実際はこう。

```text
Resume(k1, true) の中で each__mono1 が走る
  ↓
current_function == "each__mono1"
H_sub.escape_owner_function == "each__mono1"
  ↓
function 名が同じなので H_sub に即 match
  ↓
work の guard まで戻らず、Resume の返り値が Plain(Int 1)
  ↓
once が just(1) を返す
```

つまり `cps:0 → cps:1` の前進はあったけど、`cps:2` に届かない理由は **H_sub を拾う場所が早すぎる**ことだねぇ。`write20` / `write19` でも case A/B/C は否定されていて、根は ScopeReturn propagation と intermediate handler eval の扱いに絞られている。

---

## 実装LLMに渡す指示

ここから下は、そのまま別LLMへ渡せる形で書くねぇ。

---

# 目的

`debugs_std_undet_once_skip_eval_layers` を `VM: 2 / CPS: 2` に近づける。

現状は write21 後で:

```text
cargo test -p yulang-native
  => pass

cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored
  => pass

cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored
  => pass

cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored
  => fail
     vm:  Int("2")
     cps: Int("1")
```

`guard` lowering は疑わない。`work__mono0` / `guard__mono3` は正しい。直す場所は `cps_eval.rs` の ScopeReturn routing だよ〜。

---

# 絶対にやらないこと

## 1. `guard` lowering を直そうとしない

`write21-followup` で、`work__mono0` に `n > 1` と `guard__mono3` 呼び出しが正しく入っていることが確認済み。`guard__mono3` も false branch で `perform reject` する。ここを触ると遠回りだよ〜。

## 2. `handle_scope_return` の owner check を外さない

この check は function-local continuation id に飛ぶ安全弁だねぇ。

```rust
let frame_owner_match =
    target == EXIT_RWH_TARGET || frame.escape_owner_function == current_function;
```

これは残す。`target != EXIT_RWH_TARGET` の時に別 function の continuation id へ飛ぶと壊れる。

## 3. `escape_owner_function == current_function` だけで解決しない

これが write21 の semantic gap。**同じ function を別 eval frame で走らせている**状況を区別できない。

```text
元 each eval:
  H_sub を install した本物の scope

Resume eval:
  同じ each__mono1 の continuation を走らせているだけ
  H_sub の install scope ではない
```

function 名一致は必要条件にすらならない。ScopeReturn 解決には **eval-frame identity** が必要。

## 4. Cranelift / CPS repr に進まない

Layer 1 の `cps_eval` が VM と一致していない。Cranelift 側へ意味論を移す段階ではない。

## 5. `initial_frame_count` を消さない

write12/write14 の設計で、`return_frames[0..initial_frame_count]` は inherited prefix、`return_frames[initial_frame_count..]` は現在 eval が consume できる suffix、という分離になっている。sync call は親 frames を見せるが consume しない、Resume は captured frames を consume する、という重要な区別だよ〜。

---

# 本線の修正方針

## 方針名

**eval-frame identity による ScopeReturn 解決**

## 要点

```text
InstallHandler した eval frame だけが、
その prompt の ScopeReturn を解決できる。
```

同じ function 名では駄目。
同じ continuation id でも駄目。
同じ dynamic prompt を持ち、かつ `install_eval_id == current_eval_id` の handler frame だけが解決できる。

---

# Step 1: eval id 型を追加する

`cps_eval.rs` に evaluator-local な eval id を追加する。

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct CpsEvalId(u64);
```

eval id の発行は、既存の `fresh_prompt()` があるなら、その方式に合わせる。もし prompt が global atomic なら、eval id も同じ方式でよい。ただし一番きれいなのは evaluator run ごとの state だねぇ。

推奨形:

```rust
#[derive(Debug, Default)]
struct CpsEvalRunState {
    next_eval_id: u64,
}

impl CpsEvalRunState {
    fn fresh_eval_id(&mut self) -> CpsEvalId {
        let id = self.next_eval_id;
        self.next_eval_id += 1;
        CpsEvalId(id)
    }
}
```

その場合、`eval_cps_module` から `eval_function` / `eval_function_with_context` / `eval_continuations` / `resume_continuation` / `continue_return_frames` に `&mut CpsEvalRunState` を渡す。

もし変更量が大きすぎるなら、一時的に atomic でもよい。ただし prompt と同じく「同時 test で ID が一意ならよい」以上の意味を持たせない。

---

# Step 2: `CpsHandlerFrame` に `install_eval_id` を追加する

`CpsHandlerFrame` は `cps_eval.rs` 内にあるはず。そこに field を足す。

```rust
struct CpsHandlerFrame {
    prompt: CpsPromptId,
    handler: CpsHandlerId,
    envs: Vec<CpsResolvedHandlerEnv>,
    escape: CpsContinuationId,
    escape_owner_function: String,
    return_frame_threshold: usize,
    inherited: bool,

    // 追加
    install_eval_id: CpsEvalId,
}
```

名前は `install_eval_id` が一番誤解が少ない。

意味:

```text
この handler frame を InstallHandler で作った eval frame の ID
```

この field は ScopeReturn 解決用だよ〜。Perform handler search には使わない。

---

# Step 3: `CpsReturnFrame` に `owner_eval_id` を追加する

return frame は「どの eval frame の continuation を後で再開するか」を持っている。そこへ eval id も保存する。

```rust
struct CpsReturnFrame {
    owner_function: String,
    continuation: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,
    owner_initial_frame_count: usize,

    // 追加
    owner_eval_id: CpsEvalId,
}
```

もし `owner_initial_frame_count` の名前が実コードで違うなら、既存名に合わせる。

意味:

```text
この frame を pop して owner continuation を再開するとき、
current_eval_id として復元する ID
```

ここが急所。`CpsReturnFrame` に eval id を保存しないと、元の `each` eval を復元できず、H_sub の install frame まで戻っても `install_eval_id == current_eval_id` が成り立たない。

---

# Step 4: `resume_continuation` に `current_eval_id` を渡す

`resume_continuation` は「実際に今 eval loop を走らせる関数」なので、ここが current eval id を保持する。

概念:

```rust
fn resume_continuation(
    state: &mut CpsEvalRunState,
    module: &CpsModule,
    function: &CpsFunction,
    entry: CpsContinuationId,
    initial_args: Vec<CpsRuntimeValue>,
    initial_values: Vec<Option<CpsRuntimeValue>>,
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,
    return_frames: Vec<CpsReturnFrame>,
    initial_frame_count: usize,
    current_eval_id: CpsEvalId,
) -> CpsEvalResult<CpsRuntimeValue>
```

`resume_continuation` の中では、新しい eval id を発行しない。
渡された `current_eval_id` をそのまま使う。

理由:

```text
continue_return_frames で元 eval frame を再開するとき、
新しい ID を発行したら install_eval_id と一致しなくなる。
```

---

# Step 5: `eval_continuations` は fresh eval id を発行する

`eval_continuations` は cross-function call / thunk force / closure apply の入口。ここは新しい eval frame なので fresh id を発行する。

```rust
fn eval_continuations(...) -> CpsEvalResult<CpsRuntimeValue> {
    let current_eval_id = state.fresh_eval_id();

    resume_continuation(
        state,
        module,
        function,
        entry,
        initial_args,
        initial_values,
        into_inherited(active_handlers),
        guard_stack,
        return_frames,
        initial_frame_count,
        current_eval_id,
    )
}
```

`into_inherited(active_handlers)` は残す。
ただし `into_inherited` は `install_eval_id` を変えない。

```rust
fn into_inherited(mut handlers: Vec<CpsHandlerFrame>) -> Vec<CpsHandlerFrame> {
    for frame in &mut handlers {
        frame.inherited = true;
        // install_eval_id は触らない
    }
    handlers
}
```

---

# Step 6: `continue_return_frames` は `owner_eval_id` を復元する

`continue_return_frames` が return frame を pop したら、その frame が保存していた `owner_eval_id` を `resume_continuation` に渡す。

概念:

```rust
fn continue_return_frames(
    state: &mut CpsEvalRunState,
    module: &CpsModule,
    mut return_frames: Vec<CpsReturnFrame>,
    value: CpsRuntimeValue,
) -> CpsEvalResult<CpsRuntimeValue> {
    let frame = return_frames
        .pop()
        .expect("Return tried to consume a frame but none existed");

    let owner = function_by_name(module, &frame.owner_function)?;

    resume_continuation(
        state,
        module,
        owner,
        frame.continuation,
        vec![value],
        frame.values.as_ref().clone(),
        frame.active_handlers,
        frame.guard_stack,
        return_frames,
        frame.owner_initial_frame_count,
        frame.owner_eval_id,
    )
}
```

ここで fresh id を発行しない。
`frame.owner_eval_id` を必ず使う。

---

# Step 7: `InstallHandler` で `install_eval_id = current_eval_id`

`CpsStmt::InstallHandler` の処理で handler frame を push するとき、現在の eval id を入れる。

概念:

```rust
active_handlers.push(CpsHandlerFrame {
    prompt,
    handler: *handler,
    envs: resolved_envs,
    escape: *escape,
    escape_owner_function: function.name.clone(),
    return_frame_threshold: return_frames.len(),
    inherited: false,
    install_eval_id: current_eval_id,
});
```

trace も増やすとよい。

```rust
trace_cps(
    "InstallHandler",
    format!(
        "fn={} eval={} cont={:?} handler={:?} prompt={} escape={:?} threshold={} handlers.now={}",
        function.name,
        current_eval_id.0,
        current,
        handler,
        prompt.0,
        escape,
        return_frames.len(),
        summarize_handler_stack(&active_handlers),
    ),
);
```

---

# Step 8: return frame 作成時に `owner_eval_id = current_eval_id`

`EffectfulCall` / `EffectfulApply` / `EffectfulForce` は post-cont frame を push する。その frame は「現在の eval を後で再開する」ためのものだから、`owner_eval_id` は `current_eval_id`。

概念:

```rust
let frame = CpsReturnFrame {
    owner_function: function.name.clone(),
    continuation: resume,
    values: Rc::new(values.clone()),
    active_handlers: active_handlers.clone(),
    guard_stack: guard_stack.clone(),
    owner_initial_frame_count: initial_frame_count,
    owner_eval_id: current_eval_id,
};
```

この値は `continue_return_frames` で復元される。

---

# Step 9: sync call は fresh eval id を使うが、親 frames は inherit する

write14 の設計は維持する。sync call は親の `return_frames` を callee に渡すが、callee の通常 Return はそれを consume しない。

## DirectCall stmt

```rust
let inherited = return_frames.len();

let result = eval_function_with_context(
    state,
    module,
    target_function,
    call_args,
    active_handlers.clone(),
    guard_stack.clone(),
    return_frames.clone(),
    inherited,
)?;
```

`eval_function_with_context` → `eval_continuations` で fresh eval id が発行される。

## ApplyClosure stmt の Closure 分岐

```rust
let inherited = return_frames.len();

let result = eval_continuations(
    state,
    module,
    owner,
    closure.entry,
    vec![arg],
    closure.values.as_ref().clone(),
    active_handlers.clone(),
    guard_stack.clone(),
    return_frames.clone(),
    inherited,
)?;
```

## ForceThunk stmt

既に見えているコードでは、`ForceThunk` は `return_frames.clone()` と `inherited = return_frames.len()` を渡している。ここは設計として正しい。fresh eval id 発行だけ `eval_continuations` 側に任せる。

---

# Step 10: Resume 系の扱い

ここは特に大事。

## Resume は fresh eval id でよい

`Resume(k, arg)` は captured continuation の再生入口だねぇ。Resume eval 自体は新しい eval frame なので fresh id でよい。

ただし、`resumption.return_frames` の中に保存されている `owner_eval_id` はそのまま残す。これにより、captured frame を pop した時に元 eval id が復元される。

## Resume は `initial_frame_count = 0`

write14 の方針通り、Resume は captured frames を consume できる必要がある。

```rust
eval_continuations(
    state,
    module,
    owner,
    resumption.target,
    vec![arg],
    resumption.values.as_ref().clone(),
    resumed_handlers,
    resumption.guard_stack.as_ref().clone(),
    adjusted_frames,
    0,
)
```

`eval_continuations` が fresh eval id を発行する。
その fresh id は Resume eval 用。
captured return frame を pop すると、`owner_eval_id` によって元 eval id へ戻る。

## `inject_extra_handlers` は `install_eval_id` を勝手に変えない

extras は resume site 側の handler。たとえば inner once prompt=2 は inner once eval で install された handler だよ〜。captured frames に inject して Perform search から見えるようにするのは必要だけど、`install_eval_id` を captured frame の `owner_eval_id` に書き換えてはいけない。

```text
Perform search:
  extras を見えるようにする

ScopeReturn resolution:
  extras の本当の install eval まで戻って解決する
```

この分離を守る。

---

# Step 11: `handle_scope_return` を eval id ベースに変える

今の write21 条件を置き換える。

変更前の概念:

```rust
frame.prompt == prompt
    && (!frame.inherited
        || frame.escape_owner_function == current_function)
```

変更後:

```rust
frame.prompt == prompt
    && frame.install_eval_id == current_eval_id
```

関数 signature も変える。

```rust
fn handle_scope_return(
    result: CpsRuntimeValue,
    active_handlers: &mut Vec<CpsHandlerFrame>,
    current_function: &str,
    current_eval_id: CpsEvalId,
) -> ScopeReturnAction
```

owner check は残す。

```rust
let frame_owner_match =
    target == EXIT_RWH_TARGET || frame.escape_owner_function == current_function;
```

全体の形:

```rust
if let Some(index) = active_handlers.iter().rposition(|frame| {
    frame.prompt == prompt
        && frame.install_eval_id == current_eval_id
}) {
    let frame = &active_handlers[index];

    let frame_owner_match =
        target == EXIT_RWH_TARGET || frame.escape_owner_function == current_function;

    if !frame_owner_match {
        return ScopeReturnAction::Propagate(CpsRuntimeValue::ScopeReturn {
            prompt,
            target,
            value,
        });
    }

    let threshold = frame.return_frame_threshold;
    active_handlers.truncate(index);

    ScopeReturnAction::JumpOrExit {
        target,
        value: *value,
        return_frame_threshold: threshold,
    }
} else {
    ScopeReturnAction::Propagate(CpsRuntimeValue::ScopeReturn {
        prompt,
        target,
        value,
    })
}
```

`dispatch_scope_return!` の呼び出し側も変える。

```rust
match handle_scope_return(
    result,
    &mut active_handlers,
    &function.name,
    current_eval_id,
) {
    ...
}
```

## コメントも書き換える

write21 のコメントはもう古い。残すと次のLLMが誤解する。

新しいコメント案:

```rust
// A ScopeReturn is resolved only by the eval frame that installed the
// matching handler prompt. Function identity is not enough: a multi-shot
// resumption can run the same CPS function in a fresh eval frame, and that
// fresh frame must not catch a handler installed by the original eval.
// Return frames preserve owner_eval_id so the original eval identity is
// restored when the captured continuation is resumed.
```

コメント文は英語のままでよい。既存コードの文体に合わせる。

---

# Step 12: trace を増やす

`YULANG_CPS_TRACE_FRAMES=1` の時だけ出す。

## Eval entry

```text
EvalEntry:
  fn=<function>
  entry=<cont>
  eval=<current_eval_id>
  frames=<return_frames.len>
  initial=<initial_frame_count>
  handlers=<summary>
```

## InstallHandler

```text
InstallHandler:
  fn=<function>
  eval=<current_eval_id>
  prompt=<prompt>
  escape=<escape>
  threshold=<return_frames.len>
  inherited=false
```

## ScopeReturnDispatch

```text
ScopeReturnDispatch:
  fn=<function>
  eval=<current_eval_id>
  prompt=<prompt>
  target=<target>
  matched=<yes/no>
  matched_install_eval=<id if yes>
  inherited=<bool if yes>
  owner=<escape_owner_function if yes>
  owner_match=<yes/no if yes>
  action=<JumpOrExit/Propagate>
```

## ContinueReturnFrames

```text
ContinueReturnFrames:
  pop owner=<owner_function>
  cont=<continuation>
  owner_eval=<owner_eval_id>
  rest.len=<return_frames.len after pop>
  owner_initial=<owner_initial_frame_count>
```

この trace があれば、今回の修正が効いているか一発で分かる。

---

# Step 13: 期待する trace

`debugs_std_undet_once_skip_eval_layers` で見るべき形。

## 期待パターン

```text
Perform sub::return in Resume eval
ScopeReturnDispatch fn=each eval=<resume_eval_id> prompt=1 matched=no Propagate
```

ここで match してはいけない。
write21 の `cps:1` はここで match したせい。

次に、return frame を辿って元 each eval が復元される。

```text
ContinueReturnFrames pop owner=each cont=<...> owner_eval=<original_each_eval_id>
ScopeReturnDispatch fn=each eval=<original_each_eval_id> prompt=1 matched=yes owner_match=yes JumpOrExit
```

ここで match するのが正しい。

その後:

```text
Return each ... value=Plain(Int 1)
work computes n > 1 => false
Perform reject
active_handlers includes inner once prompt=2
```

そして:

```text
once reject arm sees queue=List(len=1, [Resumption])
Resume(k1, false)
...
Return root value=Plain(Int 2)
```

---

# Step 14: テスト順

## 1. まず通常テスト

```bash
cargo test -p yulang-native
```

期待:

```text
pass
```

## 2. local choice の regression

```bash
cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture
```

期待:

```text
pass
```

write12/write13 由来の return-frame semantics が壊れていないかを見る。

## 3. 本命

```bash
YULANG_CPS_TRACE_FRAMES=1 \
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

期待:

```text
VM:  Int("2")
CPS: Int("2")
```

もしまだ落ちるなら、次の切り分けへ進む。

---

# 失敗時の切り分け

## Case 1: まだ `cps:1`

症状:

```text
ScopeReturnDispatch fn=each eval=<resume_eval_id> prompt=1 matched=yes
```

原因候補:

```text
handle_scope_return がまだ function identity で match している
install_eval_id が current_eval_id と誤って同じになっている
return frame / resumption replay 時に eval id を fresh にせず使い回している
```

見る場所:

```text
eval_continuations が fresh_eval_id を発行しているか
resume_continuation が勝手に fresh_eval_id を発行していないか
InstallHandler の install_eval_id が current_eval_id になっているか
```

## Case 2: ScopeReturn が root まで逃げる

症状:

```text
EscapedScopeReturn prompt=1
```

原因候補:

```text
CpsReturnFrame.owner_eval_id を保存していない
continue_return_frames で owner_eval_id を復元していない
H_sub を含む active_handlers が return frame に保存されていない
```

見る場所:

```text
EffectfulCall fold_impl 時に作る F_each_post の owner_eval_id
Perform branch 時に capture される return_frames
ContinueReturnFrames で復元された eval id
restored frame の active_handlers に H_sub があるか
```

## Case 3: `sub::return(1)` は正しく work に戻るが、reject が outer once に行く

症状:

```text
work guard false
Perform reject
active_handlers=[outer once only]
```

原因候補:

```text
inner once prompt=2 の extra handler が captured return frames に inject されていない
EffectfulApply(Resumption) の frame order が崩れている
inject_extra_handlers が handler stack を落としている
```

見る場所:

```text
EffectfulApply(Resumption)
combined_frames order
inject_extra_handlers
active_handlers in F_each_post after injection
```

write16 の修正では、`continue_return_frames` が末尾から pop するため、`combined_frames = new_frames + adjusted_res` が正しいと整理されている。ここを逆順へ戻さない。

## Case 4: reject は inner once に行くが queue が空

症状:

```text
Perform reject active_handlers includes prompt=2
once reject arm uncons queue=[]
```

原因候補:

```text
branch arm の queue=[k1] が inner once の handler env に保存されていない
ListSingleton/ListMerge の CPS value handling が壊れている
recursive loop call の arg binding がずれている
```

ただし write20 では queue=[Resumption] の構築と recursive loop 起動は確認されていて、list primitive bug は一度否定されている。だから優先度は低めだねぇ。

---

# なぜ案1を推すか

`write21-followup` は候補として:

```text
案1: handler frame に install eval id を持たせる
案2: resumption.return_frames から H_sub を復元
案3: frame stack を見て decide
```

を挙げている。私の判断では、**案1を拡張して `CpsReturnFrame.owner_eval_id` まで入れる**のが一番よい。

## 案2が駄目な理由

Resume eval に H_sub を直接 inject して match させると、write21 の早すぎる match と同じ系統のバグになる。H_sub は Resume eval の handler ではない。

## 案3が弱い理由

`return_frames` の中に同じ function の F_post があるかを見る heuristic は、今回の形には効きそう。でも「同じ function が複数 eval frame で走る」問題を根本的に解いていない。nested resume / recursive same-function eval が増えるとまた崩れる可能性がある。

## eval id が強い理由

`InstallHandler` の動的 scope は function でも continuation でもなく **eval frame** に属する。
なら、その identity をデータとして持つのが自然だよ〜。

---

# 実装後に残すべきコメントの意図

`CpsHandlerFrame::inherited` の既存 doc は、おそらくこういう意図だねぇ。

```text
inherited frame は Perform search には使える
でも ScopeReturn resolution には使わない
```

eval id を入れると、より精密にこう言える。

```text
ScopeReturn resolution は inherited かどうかではなく、
install_eval_id == current_eval_id で決める。

inherited は「fresh eval に持ち込まれた frame」という補助情報として残す。
Perform search / trace / extras 判断にはまだ意味がある。
```

なので `inherited` を消す必要はない。
ただし `handle_scope_return` の主判定からは外してよい。

---

# まとめ

次の実装でやることは一つに絞るとよさそうだねぇ。

```text
cps_eval.rs に eval-frame identity を入れて、
ScopeReturn(prompt) を「その prompt を install した eval frame」でだけ解決する。
```

これにより:

```text
Resume eval の each__mono1:
  H_sub を拾わない

元 each eval の return frame:
  H_sub を拾う

inner once eval:
  reject handler の ScopeReturn を拾う
```

という、本来の delimited continuation の流れに近づくはずだよ〜。
`std::undet.once` は設計メモ上でも hard integration target 扱いだから、ここで大きめの eval identity 修正を入れる価値がある。
