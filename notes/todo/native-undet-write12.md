うん、これはかなり大変な状況だと思う。
でも同時に、かなり大事なところまで来ているねぇ。ここで見えてきた問題は、`std::undet.once` の局所バグではなくて、**今の CPS runtime が「関数呼び出しをまたいだ delimited continuation」をまだ本当に表現できていない** という話だと思う。

報告書の分析はかなり正しい。`Aborted` を `ScopeReturn { prompt, target, value }` にしたのは良い前進だし、`sub::return` が root まで飛びすぎる問題を「handler scope で止める」方向へ直している。ただし、残った `vm:2, cps:0` は、さらに深い問題で、**resumption が caller の残り計算を含んでいない** ことが原因に見えるよ〜。報告書でも、`Resume(k_true_thunk, true)` の eval frame が `sub::return` 後に exit し、`work` の `reject` が inner once の H2 ではなく outer once H1 に流れてしまう、と整理されている。

---

# まず結論

## `ResumeWithHandler(k, true, H2)` だけでは足りない

報告書の候補 A は「最も現実的」と書かれているけど、りなはここを少し警戒してる。
**H2 を resume scope に入れるだけでは、`work` の残り計算そのものが resumption に入っていない問題は解決しない** 可能性が高い。

今回必要なのはこれ。

```text
branch の k は、
  each の中の branch 後の継続
だけでなく、
  each が work に返った後の guard / n / work return
まで含む必要がある。
```

つまり、`k true` を再開したら、

```text
each returns 1
→ work receives n = 1
→ guard n > 1
→ reject
→ inner once H2 handles reject
→ queue から k false
→ each returns 2
→ work receives n = 2
→ guard passes
→ work returns 2
```

までが **inner once の handler scope の内側** で走らないといけない。

今の実装は、おそらくこうなっている。

```text
k true
→ each returns 1
→ resumed eval exits
→ inner once H2 eval frame is gone
→ work's later reject is handled by outer H1 or nil path
```

だから `0` になる。これは report の説明と一致している。

---

# いま直すべき本質

## handler stack ではなく「call continuation stack」が足りない

ここが一番大事。

これまで直してきたものは主に、

```text
active handler stack
guard stack
handler env
prompt-aware ScopeReturn
first-class resumption/list/tuple/variant
```

だった。

でも今回足りないのは、

```text
callee が effect を perform したとき、
caller の「call の後の残り計算」を resumption に含める
```

こと。

つまり、`DirectCall` / `ApplyClosure` / `ForceThunk` をまたぐときに、単に `active_handlers` を渡すだけでは足りない。
**「この callee が戻ってきたら、caller のどの continuation に値を渡して続けるのか」** という return frame を resumption に入れる必要がある。

---

# 今の設計で起きていること

たとえば `work` がこうだとする。

```yulang
my work(): int = {
    my n = each [1, 2, 3]
    guard: n > 1
    n
}
```

CPS 的には本来、

```text
call each
then continue with n:
    guard n > 1
    n
```

という「post-call continuation」がある。

しかし現在は、`each` の中で `branch` が perform したとき、resumption `k` がたぶん **`each` の内部 continuation だけ** を持っている。
それだと `k true` は `each` を `1` で終わらせるだけで、`work` の `guard` まで含まない。

これが今回の核心だと思う。

---

# `ScopeReturn` は正しい。でもそれだけでは足りない

`ScopeReturn` 自体は良い方向だよ〜。
最新コミットでも、`Aborted` を `ScopeReturn { prompt, target, value }` に置き換え、dynamic prompt id と `InstallHandler.escape` を導入している。これは nested once を区別するために必要な変更だと思う。

ただし `ScopeReturn` は、

```text
handler arm body の戻り値を、どの handler scope で止めるか
```

の問題を解くもの。

今回さらに必要なのは、

```text
resumption がどの caller continuation まで含むか
```

の問題。

つまり今の分解はこう。

```text
ScopeReturn:
  handler scope の出口制御

ReturnFrame / continuation stack:
  関数呼び出しをまたぐ「残り計算」の捕捉
```

この2つは両方必要。

---

# 修正方針: `return frame` を resumption に持たせる

## 追加する概念

`CpsResumption` に、呼び出し元の残り計算 stack を入れる。

イメージ:

```rust
#[derive(Debug, Clone, PartialEq)]
struct CpsReturnFrame {
    owner_function: String,
    continuation: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
    active_handlers: Rc<Vec<CpsHandlerFrame>>,
    guard_stack: Rc<Vec<CpsGuardEntry>>,
}
```

そして `CpsResumption` をこうする。

```rust
struct CpsResumption {
    owner_function: String,
    target: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
    handlers: Rc<Vec<CpsHandlerFrame>>,
    guard_stack: Rc<Vec<CpsGuardEntry>>,
    return_frames: Rc<Vec<CpsReturnFrame>>,
}
```

CPS repr 側にも同じものを持たせる。

---

# でも、その前に IR 側で「post-call continuation」が必要

ここが実装上の山だねぇ。

現在の `DirectCall` はおそらく statement になっている。

```rust
CpsStmt::DirectCall {
    dest,
    target,
    args,
}
```

この形だと、callee が perform したときに、caller の「DirectCall の後の残り statements」を resumption に入れづらい。
なぜなら、残り statements は continuation として明示されていないから。

なので、effectful call については、**statement ではなく terminator 的に split** する必要がある。

---

# 新しい IR 追加案

## 1. effectful direct call 用 terminator

```rust
enum CpsTerminator {
    ...
    DirectCall {
        target: String,
        args: Vec<CpsValueId>,
        resume: CpsContinuationId,
    },
}
```

`resume` continuation は、callee の戻り値を1つ受け取って、caller の残り処理を続ける。

例:

```text
my n = each [1,2,3]
guard n > 1
n
```

はこうなる。

```text
cont_before:
    DirectCall each(args..., resume = cont_after_each)

cont_after_each(n):
    guard n > 1
    return n
```

こうなっていれば、`each` の中で branch が perform したとき、resumption `k` に `cont_after_each` を return frame として入れられる。

## 2. effectful apply closure 用 terminator

```rust
CpsTerminator::ApplyClosure {
    closure: CpsValueId,
    arg: CpsValueId,
    resume: CpsContinuationId,
}
```

`std::fold` の callback や local recursive closure では `ApplyClosure` が多いので、DirectCall だけでは足りない。

## 3. effectful force thunk 用 terminator

```rust
CpsTerminator::ForceThunk {
    thunk: CpsValueId,
    resume: CpsContinuationId,
}
```

`catch x:` / `loop(k true, queue)` で thunk を force するところも、perform が起きる入口なので return frame を持てる必要がある。

---

# 既存 `CpsStmt::DirectCall` は残していい

全部の call を terminator にする必要はない。

```text
pure call:
  CpsStmt::DirectCall のまま

effectful / handler scope 内の call:
  CpsTerminator::DirectCall { resume }
```

でいいと思う。

まずは conservative に、

```text
active_handler がある場所での DirectCall / ApplyClosure / ForceThunk
```

を effectful terminator にしてもいい。
少し冗長になるけど、正しさ優先。

---

# lowering の具体方針

## `lower_handled_block` を拡張する

今すでに `lower_handled_block` は、block 内に effect operation があると rest-of-computation を continuation に切っているはず。
同じことを effectful call にもする。

### 対象

```rust
runtime::Stmt::Let { pattern, value }
```

で `value` が以下のどれか。

```text
- direct call to function that may perform effect
- ApplyClosure whose callee may perform effect
- thunk force / thunk-typed computation
```

### 変換

```text
current:
    lower value
    bind pattern
    lower rest

new:
    create post_cont(result)
    lower pattern binding in post_cont
    lower rest in post_cont
    current terminates with EffectfulCall(value, resume = post_cont)
```

擬似コード:

```rust
fn lower_handled_let_with_effectful_call(
    &mut self,
    pattern: &runtime::Pattern,
    value: &runtime::Expr,
    rest: &[runtime::Stmt],
    tail: Option<&runtime::Expr>,
    expected_effects: &[core_ir::Path],
    handler: CpsHandlerId,
    value_cont: Option<CpsContinuationId>,
) -> CpsLowerResult<core_ir::Path> {
    let post_cont = self.fresh_continuation();
    let result = self.fresh_value();

    // current continuation terminates with effectful call
    self.lower_effectful_call_terminator(value, post_cont)?;
    self.finish_current();

    // post continuation receives call result
    self.current = ContinuationBuilder::new(post_cont, vec![result]);
    self.bind_pattern(pattern, result)?;
    self.lower_handled_block(rest, tail, expected_effects, handler, value_cont)
}
```

このような構造にする。

---

# evaluator の具体方針

## eval_continuations に return_frames を渡す

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
) -> CpsEvalResult<CpsRuntimeValue>
```

最初は `return_frames` を `Rc<Vec<_>>` にしてもいい。

## effectful DirectCall terminator の評価

```rust
CpsTerminator::DirectCall { target, args, resume } => {
    let target_function = function_by_name(module, target)?;
    let args = read_values(...)?;

    let frame = CpsReturnFrame {
        owner_function: function.name.clone(),
        continuation: *resume,
        values: Rc::new(values.clone()),
        active_handlers: Rc::new(active_handlers.clone()),
        guard_stack: Rc::new(guard_stack.clone()),
    };

    let mut frames = return_frames.clone();
    frames.push(frame);

    return eval_function_with_context(
        module,
        target_function,
        args,
        active_handlers.clone(),
        guard_stack.clone(),
        frames,
    );
}
```

ただし、callee が普通に値を返したら、その値を return frame に渡して caller の continuation を続ける必要がある。

なので、`eval_function_with_context` の戻りを直接返すのではなく、こういう helper が必要。

```rust
fn continue_return_frames(
    module: &CpsModule,
    mut value: CpsRuntimeValue,
    mut frames: Vec<CpsReturnFrame>,
) -> CpsEvalResult<CpsRuntimeValue> {
    while let Some(frame) = frames.pop() {
        let function = function_by_name(module, &frame.owner_function)?;
        value = eval_continuations(
            module,
            function,
            frame.continuation,
            vec![value],
            frame.values.as_ref().clone(),
            frame.active_handlers.as_ref().clone(),
            frame.guard_stack.as_ref().clone(),
            frames.clone(),
        )?;
    }
    Ok(value)
}
```

実際には `ScopeReturn` が返った場合は、frame 内の handler stack で解決できるか見てから進む必要がある。
ただし最初の実装は `eval_continuations` 側の `handle_scope_return` に任せる形でよいと思う。

---

# Perform で resumption に return_frames を入れる

今の `Perform` で resumption を作るところを変える。

```rust
let resumption = CpsRuntimeValue::Resumption(Rc::new(CpsResumption {
    owner_function: function.name.clone(),
    target: *resume,
    values: Rc::new(values.clone()),
    handlers: Rc::new(handler_stack.clone()),
    guard_stack: Rc::new(guard_stack.clone()),
    return_frames: Rc::new(return_frames.clone()),
}));
```

これが核心。

`branch` が `each` の中で perform されたとき、`return_frames` に `work` の post-call continuation が入っていれば、`k true` が `each` を返したあと `work.guard` に進める。

---

# Resume の評価

現在の `Resume` は、resumption target を eval して値を返しているはず。
これを、target eval 後に return frames を続けるようにする。

```rust
CpsStmt::Resume { dest, resumption, arg } => {
    let resumption = read_resumption(...)?;
    let arg = read_plain_value(...)?;

    let owner = function_by_name(module, &resumption.owner_function)?;

    let result = eval_continuations(
        module,
        owner,
        resumption.target,
        vec![CpsRuntimeValue::Plain(arg)],
        resumption.values.as_ref().clone(),
        resumption.handlers.as_ref().clone(),
        resumption.guard_stack.as_ref().clone(),
        resumption.return_frames.as_ref().clone(),
    )?;

    let result = continue_return_frames(
        module,
        result,
        resumption.return_frames.as_ref().clone(),
    )?;

    dispatch_scope_return!(... result ...)
}
```

ただし、`eval_continuations` 自体が return_frames を消費する設計なら、二重に consume しないよう注意。
実装しやすい形を選んでねぇ。

---

# active_handlers の扱い

ここで report の `inherited` flag が効いてくる。

今は `eval_continuations` の先頭で inherited にしている。
この考え方は悪くない。子 eval が親の prompt を勝手に解決しないためだねぇ。

ただし return frame を導入したら、return frame に保存された `active_handlers` は **元の install site の eval に戻るためのもの** なので、その frame で再開するときは inherited にしすぎてはいけない。

具体的には、

```text
callee に渡す active_handlers:
  inherited = true にしてよい

return frame で caller continuation を再開するときの active_handlers:
  保存時の inherited 状態を復元する
  H2 は non-inherited のままであるべき
```

これが超重要。

今の bug は「H2 eval frame が終わる」ことなので、return frame 再開時に H2 を non-inherited として復元すれば、`work` の `reject` は H2 に届くはず。

---

# Candidate A への回答

> `once` の branch 腕内で `k` を resume するときに H2 を明示的に渡す lowering は正しい方向か？

**部分的には正しい。でも単独では足りない。**

`k true` を H2 の handler scope で動かすことは必要。
でも `k` が caller continuation を持っていないなら、H2 の下で動くのは `each` の残りだけで、`work.guard` には届かない。

だから候補 A を採用するなら、こういう意味でなければいけない。

```text
ResumeWithHandler(k, true, H2)
=
resumption target を H2 で走らせるだけでなく、
resumption に保存された caller return frames も H2 の下で再開する
```

もし実装が単に handler stack に H2 を足すだけなら、たぶんまた壊れる。

---

# Candidate B への回答

> eval レイヤーの捕捉範囲を広げるべきか？

**はい。これが本命。**

ただし「eval レイヤーだけ」でやると Cranelift に移植しづらい。
だから、CPS IR 上に post-call continuation を明示する方がよいと思う。

つまり、

```text
DirectCall as stmt
```

だけではなく、

```text
EffectfulCall as terminator with resume continuation
```

を作る。

これなら CPS eval / CPS repr eval / Cranelift の全てで同じ意味にできる。

---

# 具体的な実装順

## Step 0: 今の ScopeReturn 実装は残す

`ScopeReturn { prompt, target, value }` は正しい方向。
消さない。

ただし、今の `inherited` の扱いは return frame 導入後に見直す可能性がある。

## Step 1: 最小 failing test を追加する

`std::undet.once` は大きすぎる。まずこれを追加してほしい。

```yulang
pub act choice:
  pub branch: () -> bool
  pub reject: () -> never

my choose(): [choice] int = case choice::branch ():
    true -> 1
    false -> 2

my once_dfs_int(x: [choice] int): int = catch x:
    choice::branch (), k -> catch k true:
        choice::reject (), _ -> k false
        v -> v
    choice::reject (), _ -> 0
    v -> v

my work(): [choice] int = {
    my n = choose()
    if n == 1:
        choice::reject ()
    else:
        n
}

once_dfs_int { work() }
```

期待値は `2`。

これは `std::undet.each` / `sub::return` / list queue を使わずに、

```text
callee performs branch
caller has rest computation after call
resumption must capture caller rest
```

だけを見るテストになる。

これが通らないなら、`std::undet.once` に戻らない。

## Step 2: CPS eval 用に return frame を入れる

まず CPS eval だけ。

```rust
struct CpsReturnFrame {
    owner_function: String,
    continuation: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
    active_handlers: Rc<Vec<CpsHandlerFrame>>,
    guard_stack: Rc<Vec<CpsGuardEntry>>,
}
```

`CpsResumption` に `return_frames` を追加。

```rust
return_frames: Rc<Vec<CpsReturnFrame>>
```

`eval_continuations` に `return_frames` 引数を追加。

## Step 3: effectful call を continuation split する

CPS lowering で、handler scope 内の potentially-effectful DirectCall / ApplyClosure / ForceThunk を、

```text
stmt call + rest
```

ではなく、

```text
terminator call with resume continuation
```

にする。

ここは作業量がある。
でもこれをしないと、caller の残り計算を resumption に入れられない。

## Step 4: Perform が resumption に return_frames を入れる

```rust
CpsResumption {
    ...
    return_frames: Rc::new(return_frames.clone()),
}
```

## Step 5: Resume が return_frames を再開する

`Resume(k, arg)` が target function だけで終わらず、return frame stack を続ける。

## Step 6: `work` 最小テストを通す

まず local `choice` test。
それから `std::undet.once skip first reject`。

## Step 7: CPS repr eval

CPS eval が通ったら、CPS repr eval に同じ仕組みを移植。

## Step 8: Cranelift

最後に Cranelift。
これは大きいので、今はまだ触らない。

---

# Cranelift に入る前に更新すべき設計メモ

これは必ず書いた方がいい。

```text
Resumption extent invariant:

A resumption captures:
- the local function continuation where the operation performed;
- the value snapshot of that continuation;
- handler/guard stack snapshots;
- the return-frame stack back to the nearest handling prompt.

Resuming a resumption:
- resumes the local continuation;
- when that continuation returns normally, continues through captured return frames;
- any effects during those frames are handled by the handler stack restored in the corresponding frame.
```

これを `native-undet-plan.md` か新規 `cps-resumption-extent.md` に入れておくと、次の作業者が迷いにくい。

---

# 触らない方がいいもの

## 1. `ResumeWithHandler` の静的 handler id だけで直すこと

これは危ない。
recursive once では同じ handler id が何度も install されるので、static id だけだと内側・外側を取り違える。

使うなら **dynamic prompt / frame** が必要。

## 2. `inherited` を雑に外すこと

`inherited` を全部 false にすると、子 eval が親の ScopeReturn を勝手に解決して別のバグが戻る可能性がある。
return frame の復元時だけ non-inherited を戻す、という方向がよい。

## 3. Cranelift を先に触ること

今は semantics が未確定。
CPS eval → CPS repr eval → Cranelift の順でいくべき。

---

# 彼への直接指示

このまま渡していいよ〜。

```text
write11 の ScopeReturn(prompt,target,value) は正しい方向です。
ただし今の vm:2 cps:0 は、ScopeReturn だけでは解けない問題です。

根本原因:
- resumption k が callee 内の continuation しか持っていない。
- branch が each/choose の中で perform したとき、k true は callee の残りだけを再開し、caller work の「call 後の guard/n/return」まで含んでいない。
- そのため inner once H2 の下で work の reject が起きず、outer once H1 に流れて nil/0 になる。

やるべきこと:
1. ResumeWithHandler(k,true,H2) だけで直そうとしない。
   それは H2 を callee に足すだけで、caller の残り計算を捕まえない。
2. resumption に return frame stack を追加する。
   CpsReturnFrame { owner_function, continuation, values, active_handlers, guard_stack }
3. handler scope 内の effectful DirectCall / ApplyClosure / ForceThunk を
   stmt ではなく「resume continuation 付き terminator」に split する。
4. Perform が resumption を作るとき、現在の return_frames を保存する。
5. Resume は resumption.target を実行した後、保存された return_frames を順に再開する。
6. return frame 再開時には保存した active_handlers を復元する。
   inner once H2 は non-inherited のまま復元される必要がある。
7. まず std::undet ではなく local choice の最小テストで確認する:
   choose() が branch を perform し、work() が choose() の後で reject するケース。
   期待値は 2。
8. CPS eval が通ってから CPS repr eval。
9. Cranelift は最後。

禁止:
- static handler id だけで ResumeWithHandler を足す
- inherited flag を雑に消す
- eval_function root で ScopeReturn を unwrap する
- Cranelift から先に直す
```

---

# りなの最終判断

はい、かなり大変な状況だと思う。
でも、ここで見つかったのは「壊滅的」ではなく、**CPS backend が本物の delimited continuation に近づくために避けられない壁**だねぇ。

今までは、

```text
handler stack を渡す
resumption を値にする
ScopeReturn を prompt-aware にする
```

まで来た。

次に必要なのは、

```text
resumption が caller continuation stack を持つ
```

こと。

ここを入れれば、`std::undet.once` の reject/backtracking だけでなく、将来の `.list` / `.logic` / user-defined handlers もかなり自然に動くようになると思うよ〜。
