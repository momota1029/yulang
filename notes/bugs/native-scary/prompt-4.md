結論から言うと、見るべき不変条件は **「condition 専用 post-continuation は condition 評価が終わった瞬間に消費済みでなければならない」** だと思うよ〜。

`BoolNot Int("2")` はかなり決定的で、then branch の `each` / `.once` が replay した値 `2` が、まだ生き残っていた **if condition の `cond_cont`** に流れ込んでる形に見える。つまり「junction condition の結果を branch continuation に戻すために作った frame」が、then branch の undet resumption に捕まってしまっている。

---

## まず分けるべき不変条件

### 正しい形

effectful condition はこうなるべき。

```text
outer handler prompt, e.g. once
  └─ condition post-frame, owner = current eval
       └─ condition expression eval
            └─ inner handler prompt, e.g. junction
```

condition 内の `junction` operation が resumption を作るとき、捕まえるのは **junction prompt の内側だけ**。condition post-frame は junction prompt の外側なので、junction の resumption には入らない。

condition が bool を返したら、condition post-frame は pop されて、`cond_cont` が走る。

```text
cond_cont(bool):
  if bool:
      then_cont
  else:
      else_cont
```

この時点で return frame stack から condition post-frame は消えていないとダメ。

その後 then branch の `each` が `undet::branch` を perform したとき、outer `once` prompt の内側として捕まるべき continuation は、

```text
rest of then branch
```

だけ。**condition post-frame は絶対に入ってはいけない**。

---

## 今の破れ方

`lower_handled_effect_condition_if` は `cond_cont` を作って、`lower_handled_body(cond, ..., Some(cond_cont))` に渡している。つまり condition result を branch continuation に戻す構造自体はある。

ただし `lower_handled_body` 内の perform は `begin_resume_after_perform_value` に落ちると、`Perform { resume: resume_cont }` を作り、その後 `resume_cont` に戻る形だけを作る。ここでは「caller の post continuation を ordinary return frame に積む」わけではない。

なので、`Handle { body: Thunk }` みたいな handler wrapper が condition の中にあると、handler result を `cond_cont` に戻したいのに、`cond_cont` が ordinary post-frame として delimiting されていない。ここを雑に “Handle body thunk は effectful” にすると、たしかに condition post-frame はできるけど、`sub::sub` wrapper みたいな広い経路まで EffectfulCall 化されて JIT missing function を踏む。これは分類が粗すぎる。

---

# 答え 1: `lower_handled_effect_condition_if` で condition 専用 boundary を作るべき

**作るべき。ただし handler threshold ではなく、ordinary return-frame boundary として作るのがよさそう。**

一番筋がよいのは、effectful condition をその場で direct に `lower_handled_body(cond, ..., Some(cond_cont))` へ渡すのではなく、condition 全体を thunk 化して、caller 側で `EffectfulForce { resume: cond_cont }` する形。

概念的にはこう。

```rust
fn lower_handled_effect_condition_if(...) -> CpsLowerResult<typed_ir::Path> {
    let saved_locals = self.locals.clone();
    let saved_local_exprs = self.local_exprs.clone();
    let saved_resumptions = self.resumptions.clone();

    let cond_cont = self.fresh_continuation();
    let then_cont = self.fresh_continuation();
    let else_cont = self.fresh_continuation();
    let cond_value = self.fresh_value();

    // ここがポイント:
    // cond を普通に lower_handled_body(... Some(cond_cont)) しない。
    // cond 全体を thunk として作り、EffectfulForce で cond_cont を
    // ordinary post-frame に載せる。
    let cond_thunk = self.lower_thunk(cond)?;
    self.terminate(CpsTerminator::EffectfulForce {
        thunk: cond_thunk,
        resume: cond_cont,
    });
    self.finish_current();

    self.current = ContinuationBuilder::new(cond_cont, vec![cond_value]);
    self.locals = saved_locals.clone();
    self.local_exprs = saved_local_exprs.clone();
    self.resumptions = saved_resumptions.clone();
    self.terminate(CpsTerminator::Branch {
        cond: cond_value,
        then_cont,
        else_cont,
    });
    self.finish_current();

    ...
}
```

`EffectfulForce` は eval 側で post-force continuation を return frame として push する。しかも `owner_initial_frame_count` は current eval の `initial_frame_count` を保存する形なので、prompt ownership 修正と同じ ownership 規則に乗る。

この形の利点は 3 つ。

1. **condition post-continuation が普通の return frame として消費される**
2. **condition 内 handler の prompt capture からは condition frame が外れる**
3. **`Handle { body: Thunk }` を全局的に may-perform 扱いしなくて済む**

つまり、`sub::sub` wrapper まで EffectfulCall 化しない。condition position だけで boundary を作る。

---

# 答え 2: ScopeReturn frame-walk 側で condition 特別扱いはしない方がいい

`ScopeReturn` frame-walk に “condition ならこう” という分岐を入れるのは避けた方がいいと思う。

frame-walk 側の不変条件はもっと汎用で十分。

```text
return frame の continuation に jump / resume するなら、
その return frame 自身は必ず消費済みである。
```

つまり、condition frame が then branch の `each` resumption に残っていたら、それは frame-walk が “condition を知らないから” ではなく、

```text
condition post-frame が ordinary return frame として消費される経路に乗っていない
```

または

```text
ScopeReturn / normal result shortcut が continue_return_frames を迂回している
```

という generic bug だねぇ。

`3e038e1` では captured continuation の handler stack threshold も return frame slice に合わせて rebase している。この方向は正しい。ただ、今回の `BoolNot Int("2")` は threshold のズレというより、**condition frame がそもそも branch 後に残っている**症状に見える。captured continuation 内で handler threshold を rebase する関数は既に handler frame 側も rebase している。

だから確認するなら trace でこれを見る。

```text
then branch の each/branch perform 時点で、
return_frames に cond_cont の frame が残っているか？
```

残っているなら lowerer / result routing の問題。
残っていないのに `BoolNot Int("2")` なら values/env の取り違え。

---

# 答え 3: may-perform 判定だけでは不十分

**不十分だと思う。**
必要なのは may-perform ではなく、もっと正確にはこれ。

```text
この expression position は、effectful evaluation result を
caller の post-continuation へ戻す必要があるか？
```

つまり **position-sensitive boundary**。

同じ `Handle { body: Thunk }` でも、

| 位置                              | 必要な扱い                                                              |
| ------------------------------- | ------------------------------------------------------------------ |
| tail position                   | post-frame 不要なことが多い                                                |
| condition position              | bool を branch continuation に返す post-frame が必要                      |
| match scrutinee                 | scrutinee value を pattern dispatch に返す post-frame が必要              |
| primitive / role method operand | operand value を残りの primitive/apply continuation に返す post-frame が必要 |
| handler arm 内の pure final value | post-frame にしない方がよい                                                |

「handler arm が resumption を使うか」は handler body の性質であって、expression の consumer position を表さない。だから junction simple caseは通っても、then branch の `each` / `.once` で condition frame が残りすぎる。

`lower_handler_body_expr` にはすでに `apply_chain_contains_resume_argument` のような handler arm 内 reentry 用の特別経路がある。これは handler body の中で resumption をどう使うかを見る判定だねぇ。
でも今回必要なのはそれとは別で、**condition consumer の post-continuation をどう delimit するか**。

---

# `BoolNot Int("2")` の直接診断

これはたぶんこういう流れ。

```text
if condition:
    each...
else:
    2
```

で、condition post-frame が残ったまま then branch の `each` が perform。

`each` の resumption が outer `once` prompt の内側を capture するとき、本来は then branch の残りだけを捕まえるべきなのに、残存 condition frameまで捕まえる。

後で `.once` が queue の resumption を replay すると、

```text
k false / k true の返り値
```

または else 側の `2` が、condition の `cond_cont` に渡る。

`cond_cont` は bool を期待して `Branch` するので、JIT/eval は `BoolNot Int("2")` で落ちる。

この症状は **condition frame leak** と見るのが自然。

---

# 実装の方向

## 1. `lower_handled_effect_condition_if` 専用 helper を足す

名前例:

```rust
fn lower_effectful_condition_boundary(
    &mut self,
    cond: &runtime::Expr,
    cond_cont: CpsContinuationId,
) -> CpsLowerResult<CpsValueId>
```

ただし返り値は `cond_value` というより、呼び出し側で fresh して continuation param にする方が今の構造に合う。

中身はざっくり:

```rust
let cond_thunk = self.lower_thunk(cond)?;
self.terminate(CpsTerminator::EffectfulForce {
    thunk: cond_thunk,
    resume: cond_cont,
});
self.finish_current();
```

その後:

```rust
self.current = ContinuationBuilder::new(cond_cont, vec![cond_value]);
self.terminate(CpsTerminator::Branch { ... });
```

この boundary は condition position 専用。`Handle { body: Thunk }` の general lowering は変えない。

---

## 2. match scrutinee も同じ問題を持つ可能性あり

`lower_handler_body_match` は effectful scrutinee に対して、今は `lower_handled_body(scrutinee, ..., Some(scrutinee_cont))` を使っている。

condition と同じ構造なので、将来的にはここも同じ boundary helper に寄せた方がいい。

ただし今すぐ junction を直すなら condition だけでよさそう。

---

## 3. trace invariant を入れる

debug trace で次を出すと即判定できる。

### condition boundary 作成時

```text
ConditionBoundaryPush:
  cond_cont = C
  pre_return_frames_len = N
```

### then/else branch 入り口

```text
ConditionBoundaryConsumed:
  cond_cont = C
  return_frames must not contain continuation C
```

eval 層で直接 continuation id を runtime frameに持っているので、`Perform` trace の return_frames summary に `owner_function + continuation` を出すとよさそう。

### then branch の `undet::branch` perform 時

```text
Perform effect=undet::branch
captured return_frames must not contain cond_cont
```

これで `BoolNot Int("2")` の原因が一発で見える。

---

# ScopeReturn / owner_initial 側で見るなら

condition 専用分岐は入れない。見るならこの generic invariant だけ。

```text
continue_return_frames / frame-walk / ScopeReturn dispatch のどの経路でも、
「ある return frame の continuation を実行する」なら、
その frame は rest frames から除去済み。
```

特に怪しいのは、`Perform` 後の normal-value shortcut。

`3e038e1` では inherited handler + RWH env の plain result を古い prompt へ再包装しない修正が入っている。`cps_eval.rs` 側でも、`frame.install_eval_id != current_eval_id` かつ handler arm が `ResumeWithHandler` を使うなら plain result を返す分岐がある。

この shortcut が condition post-frame の `continue_return_frames` を迂回しているなら、condition frame が残る。
ただしこれは shortcut 自体を消すというより、

```text
plain result を返す前に、現在 eval に pending return frame があるなら
continue_return_frames に通すべきか
```

を見る感じ。

でも優先順位としては、まず lowering 側で `EffectfulForce` boundary を作る方が安全だと思う。

---

# 最小 regression

## A. condition post-frame が必要な最小

```yulang
act done:
    pub ret: bool -> never

my run(x: [done] bool): bool = catch x:
    done::ret b, _ -> b

if run: done::ret true:
    18
else:
    2
```

期待:

```text
18
```

これは junction なしで condition handler result leak を刺す。

---

## B. condition frame が then branch resumption に残らないことを見る最小

```yulang
use std::undet::*;

act done:
    pub ret: bool -> never

my run(x: [done] bool): bool = catch x:
    done::ret b, _ -> b

({
    my y =
        if run: done::ret true:
            each [3]
        else:
            2
    y
}).once
```

期待:

```text
:just 3
```

これで `BoolNot Int("2")` が出るなら、condition frame が `each` resumption に混ざっている。

---

## C. condition false 側も見る

```yulang
use std::undet::*;

act done:
    pub ret: bool -> never

my run(x: [done] bool): bool = catch x:
    done::ret b, _ -> b

({
    my y =
        if run: done::ret false:
            each [3]
        else:
            2
    y
}).once
```

期待:

```text
:just 2
```

これで then 側の handlerだけでなく else側も確認できる。

---

# まとめ

* **見るべき不変条件**は `condition post-frame is consumed before entering then/else`。
* `lower_handled_effect_condition_if` には condition 専用 boundary が必要。ただし handler threshold ではなく ordinary `EffectfulForce` / return-frame ownership。
* `ScopeReturn` frame-walk に condition special-case は入れない。入れるなら「frame continuation を実行するなら、その frame は消費済み」という generic invariant だけ。
* handler arm の resumption use を may-perform 判定にするのは不十分。必要なのは **position-sensitive post-continuation boundary**。
* `BoolNot Int("2")` は、then branch `each` の resumption に condition frame が残っている証拠にかなり近い。

次に直すなら、`lower_handled_effect_condition_if` だけを `cond thunk + EffectfulForce(cond_cont)` に変える小 patch が一番よさそうだねぇ。
