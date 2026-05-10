読んだよ〜。
これはかなり本質的。しかも、いまの report はかなり良いところまで切り分けられてると思う。

結論から言うと、**return frame 機構の方向は正しい**。`debugs_local_choice_caller_rest_eval` が通ったなら、「resumption が caller の post-call continuation を持つ」という中核は動き始めている。だけど `std::undet.once` がまだ `0` を返すのは、たぶん **return frame を作るべき呼び出し点がまだ DirectCall の一部に限られていて、`fold` が使う closure application / non-binding expression / method wrapper 経由で return frame が切れている** からだと思う。

報告にも、`lower_handled_effectful_call_let` は DirectCall のみで、`ApplyClosure` や `Stmt::Expr` の direct call は未対応、`each` や `fold` は closure application を多用する、と書かれているねぇ。これはかなり核心だと思うよ〜。`std::undet.each` は `fold` と `sub::return` を使う実装で、`fold` の callback は `\() x -> if branch() { sub::return x } else ()` だから、callback の `ApplyClosure` をまたぐ return frame が絶対に必要になる。 また `list.fold` は `fold_impl` 内で `f z x` を呼ぶ構造なので、ここが普通の同期 `ApplyClosure` のままだと、callback 内の `branch` / `sub::return` が caller の残り計算を正しく捕まえられない。

---

# まず現在地の評価

## 正しい方向に進んだところ

今回の実装で、かなり重要なものが入っている。

```text
- CpsResumption に return_frames
- EffectfulCall / EffectfulApply / EffectfulForce terminator
- Return 時の automatic return frame consumption
- Resume / ResumeWithHandler / ApplyClosure(Resumption) 時の extra handler injection
- DirectCall let-binding を EffectfulCall に split
- EffectfulForce が必要だと判明
```

特に、local choice の最小テストが通ったのはかなり大きい。
つまり、

```text
callee が effect を perform
caller の post-call cont を resumption が捕まえる
resume 後に caller の残り計算が走る
```

という核は成立している。これは設計が間違っていない証拠だねぇ。

## まだ足りないところ

`std::undet.once` は direct call だけではない。
この chain を踏む。

```text
once
  -> each
    -> sub::sub
      -> xs.fold
        -> fold_impl
          -> f z x      // ApplyClosure
             -> branch()
             -> sub::return x
```

`fold_impl` は `list_view` を見て `f z x` する。list の std 実装にも `fold_impl xs z f = ... leaf x -> f z x ... node -> fold_impl(right, fold_impl left z f, f)` とある。
つまり、**EffectfulApply が本命** だと思う。

---

# 大きな設計判断

## 「active_handler.is_some() のときだけ effectful terminator」は足りない

報告では、`lower_handled_block` の `Let { pattern, value }` で、

```text
active_handler.is_some() && direct_apply(value)
```

のときだけ `EffectfulCall` にしている。

でも `fold_impl` は std library function として別関数に lower される。
その関数定義の lowering 時点では `active_handler` がない可能性が高い。にもかかわらず、実行時には `sub::sub` や `once` の handler stack の下で動く。

だから判定条件を変えたほうがいい。

```text
旧:
  active_handler.is_some() && direct_apply(value)

新:
  expression / callee type が effectful な call/apply/force である
  OR callee/callback が effect row を持つ
  OR 現段階では保守的に ApplyClosure は effectful terminator にする
```

最初はやや保守的にしていい。
CPS IR が少し大きくなっても、ここは correctness 優先だねぇ。

---

# 直すべきもの一覧

## 1. EffectfulApply を本実装する

今は `EffectfulApply` terminator があるけど、std once でまだ壊れるなら、おそらく lowering の対象が狭い。

### どこで必要か

以下をすべて疑う。

```text
- lower_handled_block の let value が ApplyClosure
- lower_handled_block の expr statement が ApplyClosure
- lower_expr 内で ApplyClosure が handler scope / effectful context に出る場合
- std fold_impl 内の `f z x`
- curried apply の中間結果
```

### 実装の考え方

`ApplyClosure` を同期 stmt として出すと、callee/callback が perform したときに caller の rest が return frame に入らない。
だから effectful な apply は terminator にする。

```rust
CpsTerminator::EffectfulApply {
    closure: CpsValueId,
    arg: CpsValueId,
    resume: CpsContinuationId,
}
```

評価時はこう。

```rust
EffectfulApply { closure, arg, resume } => {
    let closure_value = read_value(... closure ...);
    let arg_value = read_value(... arg ...);

    let frame = CpsReturnFrame {
        owner_function: function.name.clone(),
        continuation: resume,
        values: Rc::new(values.clone()),
        active_handlers: active_handlers.clone(),
        guard_stack: guard_stack.clone(),
    };

    let mut frames = return_frames.clone();
    frames.push(frame);

    eval_apply_closure_with_context(
        closure_value,
        arg_value,
        active_handlers.clone(),
        guard_stack.clone(),
        frames,
    )
}
```

そして closure body が普通に return したら、`Return` terminator が `continue_return_frames` で `resume` に戻す。
`branch` や `sub::return` で resumption が作られると、その resumption にこの frame stack が入る。

---

## 2. `EffectfulApply` をどの範囲で使うか

質問 1 への答えはこう。

> **ApplyClosure は、少なくとも CPS lowering が effectful になりうると判断できる場所では EffectfulApply にするべき。現段階ではかなり保守的にしてよい。**

判定候補はこの順。

### A. callee の型に effect row があるなら effectful

`runtime::Type::Fun` に effect 情報があるなら、

```rust
fn function_type_may_perform(ty: &runtime::Type) -> bool
```

を作る。

```rust
'a -> ['e] 'b
```

の `'e` が空でない、または未知なら effectful とする。

std fold の role signature は `our container.fold: 'acc -> ('acc -> ['e] item -> ['e] 'acc) -> ['e] 'acc` で、callback が effectful になれる設計になっている。
この情報が runtime type に残っているなら使う。

### B. callee type が unknown なら effectful 扱い

高階関数の callback は型が完全に見えないことが多いので、unknown を pure 扱いしない。
特に CPS backend prototype では、

```text
Unknown / Opaque / type var function call = potentially effectful
```

が安全。

### C. handler scope 内の ApplyClosure は effectful

これはいまの active_handler based 判定に近い。

### D. std fold_impl のような callback apply は effectful

もし型情報で拾えないなら、当面は `ApplyClosure` 全般を effectful terminator にするのもあり。
CPS eval だけなら多少重くても構わない。あとで最適化すればいい。

---

# 3. `Stmt::Expr` も terminator split する

質問 2 への答え。

> **はい。`Stmt::Expr` も必要。結果を捨てるだけでも、effectful call/apply/force なら post-cont を作る必要がある。**

たとえば `std::undet.each` の実装には、

```yulang
xs.fold (): \() x -> if branch() { sub::return x } else ()
reject()
```

がある。`xs.fold ...` は結果を捨てる expr statement として現れる可能性がある。報告でも、以前 `xs.fold(...)` between `sub::sub { ... }` and `reject()` を force する話が出ていた。
この `fold` の中で `sub::return` が起きたら、後続の `reject()` を skip しなければいけない。だから `Stmt::Expr` でも return frame が必要。

### 実装方針

`Stmt::Expr(expr)` の rest continuation を作る。

```rust
fn lower_handled_effectful_expr_stmt(
    &mut self,
    expr: &runtime::Expr,
    rest: &[runtime::Stmt],
    tail: Option<&runtime::Expr>,
    expected_effects: &[core_ir::Path],
    handler: CpsHandlerId,
    value_cont: Option<CpsContinuationId>,
) -> CpsLowerResult<core_ir::Path> {
    let post = self.fresh_continuation();
    let ignored = self.fresh_value();

    self.lower_effectful_expr_terminator(expr, post)?;
    self.finish_current();

    self.current = ContinuationBuilder::new(post, vec![ignored]);
    self.lower_handled_block(rest, tail, expected_effects, handler, value_cont)
}
```

結果を捨てるだけでも、callee が `ScopeReturn` を返したら post-cont へ戻らず、scope target へ jump する。
普通に値を返したら post-cont で rest へ進む。

---

# 4. `EffectfulForce` の対象を広げる

報告では、EffectfulForce の必要性が見えて、local test は通った。

今後の注意点はこれ。

```text
ForceThunk stmt を同期 stmt として出す場所が残っていると、
thunk body の perform が return_frames=[] になりやすい
```

だから handler scope 内、または maybe effectful thunk に対する force は terminator にする。

### 対象

```text
- force_if_non_thunk_demand が挿む ForceThunk
- catch body の thunk force
- direct call result が thunk になった後の forced value
- return site force
```

全部を terminator にする必要はないけど、**handler scope 内で effectful になりうる force** は terminator が安全。

---

# 5. return_frames の導入方針を少し修正する

報告では、

```text
sync: callee に Vec::new() を渡す
terminator: caller frames + new_frame を渡す
```

と整理されている。
これは正しい。

ただし、sync call の中で effect が起こる可能性があるなら、その call はそもそも sync にしてはいけない。
つまり、「sync call に empty frames」はよいけど、その前提として、

```text
sync call = definitely pure / no caller rest capture needed
```

である必要がある。

今は `fold_impl` の callback apply が sync 扱いのまま残っている可能性が高い。
そこを effectful terminator へ分類するのが大事。

---

# 6. `std::undet.once` の失敗箇所をさらに pin する方法

次セッションでは、いきなり全部直すより、どの call/apply/force で frames が切れているか可視化するといい。

## 6.1 CPS dump で terminator を確認

`debugs_std_undet_once_skip_eval_layers` に dump 検査を足す。

確認する対象:

```text
- std::list::fold_impl
- std::undet::undet::each__mono*
- callback closure `\() x -> ...`
- std::flow::sub::sub wrapper
- once loop
```

見るべき形:

```text
fold_impl leaf x:
    f z x
```

ここが、

```text
ApplyClosure stmt
```

ならダメ。

期待は、

```text
EffectfulApply terminator
```

または curried なら、

```text
EffectfulApply f z -> post1
post1(fn):
    EffectfulApply fn x -> post2
```

のような split。

## 6.2 eval trace を入れる

CPS eval に一時的な trace を入れると、かなり分かる。

```rust
trace_return_frames("enter", function.name, current, return_frames.len());
trace_terminator("EffectfulApply", function.name, resume, return_frames.len());
trace_perform(effect, return_frames.len(), active_handlers);
trace_resume(resumption.return_frames.len(), extras.len());
```

特に、`branch()` perform 時に `return_frames.len()` がいくつかを見る。

期待:

```text
branch in fold callback:
    return_frames should include:
      callback apply post frame
      fold_impl post frame
      each/sub post frame
      work post-call frame
```

少なくとも `work` の `guard` へ戻る frame が入っていないなら、そこが切れ目。

---

# 7. local minimal test をもう一段 std fold に近づける

今通った `debugs_local_choice_caller_rest_eval` は DirectCall ベースっぽい。
次は closure callback を入れた local minimal test が必要。

## Test A: closure callback 内 branch + caller rest

```yulang
pub act choice:
  pub branch: () -> bool
  pub reject: () -> never

my call_callback(f: int -> [choice] int): [choice] int = f 0

my once_dfs_int(x: [choice] int): int = catch x:
    choice::branch (), k -> catch k true:
        choice::reject (), _ -> k false
        v -> v
    choice::reject (), _ -> 0
    v -> v

my work(): [choice] int = {
    my n = call_callback: \_ -> case choice::branch ():
        true -> 1
        false -> 2
    if n == 1:
        choice::reject ()
    else:
        n
}

once_dfs_int { work() }
```

期待: `2`

これが落ちるなら `EffectfulApply` が足りない。

## Test B: fold-like recursion

```yulang
pub act choice:
  pub branch: () -> bool
  pub reject: () -> never

my fold2(z, f) = {
    my z1 = f z 1
    f z1 2
}

my once_dfs_int(x: [choice] int): int = catch x:
    choice::branch (), k -> catch k true:
        choice::reject (), _ -> k false
        v -> v
    choice::reject (), _ -> 0
    v -> v

my work(): [choice] int = {
    my n = fold2 0: \_ x -> case choice::branch ():
        true -> x
        false -> choice::reject ()
    if n == 1:
        choice::reject ()
    else:
        n
}

once_dfs_int { work() }
```

期待: `2`

これは std fold より小さく、closure apply chain を踏む。

---

# 8. `std::undet.each` の conceptual model

質問 3 への答えとして、期待される挙動をはっきり書くとこう。

`each [1,2,3]` は `fold` の callback 内で `branch()` し、`true` なら `sub::return x` で `fold` 全体を抜ける。`false` なら次の要素へ進む。`fold` が全部終わったら `reject()` する。

`once` は `branch` の resumption を queue に保存しながら、まず `k true` を試す。失敗したら queue から `k false` を取り出して再開する。

つまり `work` の例ではこうなるべき。

```text
once starts work
  each performs branch for x=1
    once handler stores k, resumes k true
      sub::return 1 exits each
      work receives n=1
      guard fails => reject
        once handles reject
        queue has k
        resume k false
          fold continues to x=2
          branch again
          once stores k2, resumes k2 true
            sub::return 2 exits each
            work receives n=2
            guard passes
            work returns 2
  once value arm returns just 2
case unwraps 2
```

ここで必要なのは、`k true` / `k false` の resumption が、

```text
fold callback continuation
+ fold_impl continuation
+ each/sub continuation
+ work post-call continuation
```

を全部含むこと。
この stack のどこかが sync ApplyClosure で切れていると `0` になる。

---

# 9. 具体的な作業順

## Step 1: `EffectfulApply` lowering を実装範囲拡大

優先度最高。

```text
- lower_handled_block Let value が ApplyClosure
- lower_handled_block Expr stmt が ApplyClosure
- lower_expr の ApplyClosure が effectful context 内
```

型判定は最初 conservative でいい。

```rust
fn apply_may_perform(callee: &runtime::Expr, arg: &runtime::Expr) -> bool {
    function_type_may_perform(&callee.ty)
        || expr_may_perform(arg)
        || type_unknown_or_polymorphic(&callee.ty)
}
```

判定できないなら true でよい。

## Step 2: `Stmt::Expr` effectful terminator split

`xs.fold ...` の結果を捨てる expression statement があるなら必須。

## Step 3: `EffectfulForce` の使用箇所確認

特に `force_if_non_thunk_demand` で ForceThunk を挿んだ箇所が handler scope 内なら、terminator にする。

## Step 4: local callback minimal test

`std::undet` なしで closure callback + caller rest を確認。

## Step 5: `std::undet.once` debug test

`debugs_std_undet_once_skip_eval_layers` の Layer 1。

## Step 6: CPS repr eval

CPS eval が通ったら同じ terminators を cps_repr eval に実装。

## Step 7: Cranelift

最後。

---

# 10. CPS repr / Cranelift への波及

今は `cps_repr.rs` / `cps_repr_cranelift.rs` の新 terminator が `todo!()` / `UnsupportedTerminator` と報告にある。
これ自体は今は問題ない。CPS eval を通すのが先。

でも設計上は、あとで必ず同じものが必要。

```text
CPS eval:
  EffectfulCall / Apply / Force
CPS repr eval:
  同じ
Cranelift:
  continuation function + return frame heap/runtime object
```

Cranelift はかなり大きくなるので、CPS eval で semantics が固まるまで触らないのが正解。

---

# 11. 彼に渡す具体指示

そのまま渡せる形で書くねぇ。

```text
write12 の return frame 方向は正しいです。
local choice caller-rest test が通ったので、resumption が caller post-call cont を持つという核は成立しています。

ただし std::undet.once がまだ 0 になるのは、return frame を作るべき effectful call site が DirectCall let-binding に限られているからだと思います。
std::undet.each は fold_impl 内の callback application `f z x` を多用するので、ApplyClosure も effectful terminator 化しないと caller rest が resumption に入らないです。

次にやること:
1. CPS dump で std::list::fold_impl / each__mono* / callback closure を見る。
   `f z x` が CpsStmt::ApplyClosure のままなら、それが最優先の修正対象。
2. EffectfulApply lowering を実装範囲拡大する。
   - let value の ApplyClosure
   - expr statement の ApplyClosure
   - handler/effectful context 内の ApplyClosure
3. ApplyClosure が effectful かの判定は最初は conservative でよい。
   function type に effect row がある / unknown / polymorphic / active handler context なら EffectfulApply。
   std fold callback を pure 扱いしない。
4. Stmt::Expr も effectful terminator split する。
   結果を捨てる xs.fold(...) でも、sub::return が起きたら後続 reject() を skip する必要がある。
5. EffectfulForce の対象も確認する。
   sync ForceThunk の中で perform すると return_frames が失われる。
6. local minimal test を追加する:
   std::undet を使わず、callback closure 内で branch し、caller work が callback call 後に reject するケース。
   期待値 2。
7. local callback test が通ったら debugs_std_undet_once_skip_eval_layers を再実行。
8. CPS eval が通るまで cps_repr / Cranelift は触らない。

注意:
- sync DirectCall/ApplyClosure に Vec::new() return_frames を渡す方針は正しいが、
  その call が effectful なら sync 扱いしてはいけない。
- active_handler.is_some() だけで判定しない。std fold_impl は定義時 active_handler がなくても実行時に handler stack の下で動く。
- inherited flag は消さない。return frame 復元時だけ保存された active_handlers を復元する。
```

---

# 12. りなの最終判断

かなり大変だけど、**方向は正しい** よ〜。

今までは、

```text
resumption に caller rest を入れる
```

ところまで進んだ。

次は、

```text
どの call/apply/force が caller rest を切る可能性があるか
```

を漏れなく拾う段階。

`std::undet.each` は高階関数 `fold` の callback 内で effect を投げるので、**ApplyClosure を effectful terminator にしない限り、たぶん最後まで安定しない**。
だから次の焦点は `EffectfulApply`。その次が `Stmt::Expr`。Cranelift はその後でいいと思うねぇ。
