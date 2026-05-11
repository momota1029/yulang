読んだうえでの結論はこれだねぇ。

**次に実装LLMへ渡すべき主作業は、`once` の ApplyClosure をさらに触ることではなく、`EffectfulCall` が返した `Thunk` を `Return` が早すぎるタイミングで post-call frame に渡してしまう問題を直すこと**だよ〜。

write16 で `std::undet::undet::once` 内の curried apply はすでに無条件 `EffectfulApply` 化され、`EffectfulApply(Resumption)` の frame order も直っている。それでも `debugs_std_undet_once_skip_eval_layers` は `cps:3 vs vm:2` のまま。trace で判明した本質は、`each` → `fold_impl` の `EffectfulCall` が push した `F_each_post_fold` が、`fold_impl` の `MakeThunk + Return` によって**thunk body 実行前に消費される**ことだねぇ。

---

# 1. ここまでの前提整理

## すでに壊してはいけない土台

write12 以降で return frame 機構が入り、`CpsTerminator` には `EffectfulCall` / `EffectfulApply` / `EffectfulForce` が追加されている。これは「call site の post-call continuation を return frame として積む」ための IR だねぇ。

write14 では `initial_frame_count` refactor が入り、sync call と effectful terminator の役割分担が固まった。

```text
sync DirectCall / ApplyClosure / ForceThunk:
  parent return_frames を callee に渡す
  initial_frame_count = parent return_frames.len()
  => Perform は parent frames を capture できる
  => 普通の Return では parent frames を consume しない

EffectfulCall / EffectfulApply / EffectfulForce:
  post-call continuation を CpsReturnFrame として push
  callee.initial_frame_count = push 前の return_frames.len()
  => callee の Return は push された post-call frame を consume できる
```

これは `debugs_local_choice_callback_rest_eval` を通した重要な土台だから、大きく書き換えないほうがいいよ〜。

write15 では `std::list::fold_impl` / `std::undet::each` / `std::undet::once` を higher-order helper として扱い、targeted に `EffectfulCall` / `EffectfulApply` 化した。さらに `ScopeReturn` 用に `return_frame_threshold` も入った。その結果、`std::undet.once` の失敗は `cps:0` から `cps:3` へ進み、「完全に探索できない」から「探索は進むが 2 で止まらず 3 へ行く」状態になった。

write16 では、`once` 内の全 closure apply を `EffectfulApply` 化し、`EffectfulApply(Resumption)` の frame order も修正した。commit diff でも、`force_effectful_apply` が `std::undet::undet::once` にだけ立ち、`lower_apply` の条件に追加されているのが確認できる。

---

# 2. いまのバグの正体

write16 report の trace がかなり決定的だねぇ。

```text
Perform: branch ... return_frames.len=1 initial=0
EffectfulApply: once cont 6 ...
Return: ... List([Resumption(...)]) ...
EffectfulApply: once cont 9 ...
Perform: sub::return ... return_frames.len=1
Return: each cont 2 value=Plain(Int("3"))
```

ポイントはこれ。

```text
branch Perform が 1 回しか出ていない
x=2 の branch Perform が起きていない
それなのに each は最終的に 3 を返している
```

つまり、once 側の `k true` / `k false` の `EffectfulApply` 化だけでは足りなかった。write16 の修正は必要だったけど、残りの原因は別の場所だよ〜。

本質はこの流れ。

```text
each:
  EffectfulCall fold_impl -> F_each_post_fold を push

fold_impl:
  実体のある探索をすぐ実行せず、
  MakeThunk + Return(thunk) する

Return(thunk):
  return_frames に F_each_post_fold があるので、
  auto Return-trigger が F_each_post_fold を consume

F_each_post_fold / each cont 12:
  ForceThunk(thunk) を sync stmt として実行

sync ForceThunk:
  この時点では return_frames = []
  thunk body も frames=[] で走る

thunk body 内の branch Perform:
  F_each_post_fold を capture できない
```

なので、`F_each_post_fold`、つまり「fold が返ったあと each が reject へ進むか、sub::return で抜けるかを決める post-fold rest」が thunk body から見えなくなる。これで resumption replay が正しく fold/each の rest を復元できず、結果が 2 で止まらず 3 に流れる、という読みだねぇ。

---

# 3. 次にやるべき修正方針

## 一言で言うと

**`Return(thunk)` が post-call frame を consume する前に、「次の frame がその thunk を即 `ForceThunk` する形か」を見て、そうなら thunk body を同じ return_frames / 同じ initial_frame_count で先に評価する。**

これが一番筋が良いと思うよ〜。

### なぜ `EffectfulForce` へ単純変換ではないか

write16 で「post-call `ForceThunk` を `EffectfulForce` に変える」試みは `cps:3 → cps:0` に悪化している。これは、frame ownership と handler threshold の不変条件を守らずに frame を追加した可能性が高い。

だから次の修正は、lowering 側で雑に `ForceThunk` を terminator 化するより、**eval 側の `Return(thunk)` 時点で、まだ F_post が stack に残っているうちに thunk body を評価する**ほうが安全だねぇ。

---

# 4. 実装LLMへの具体指示

以下をそのまま渡すとよさそうだよ〜。

---

## 目的

```text
debugs_std_undet_once_skip_eval_layers の CPS eval を VM と一致させる。

現状:
  CPS eval: 3
  VM:       2

目標:
  CPS eval: 2
  VM:       2
```

このタスクでは CPS eval semantics を直す。CPS repr eval / Cranelift backend 対応は範囲外。write15 で ignore 化した Cranelift 系 std::undet テストは、この段階では解除しない。

---

## 絶対に守る前提

```text
1. write14 の initial_frame_count 設計を大きく書き換えない。

2. sync DirectCall / ApplyClosure / ForceThunk は、
   parent return_frames を inherit するが、
   callee の普通の Return では consume しない。

3. EffectfulCall / EffectfulApply / EffectfulForce は、
   call site の post-call continuation を return frame として push する。

4. Resume / ResumeWithHandler / ApplyClosure(Resumption) は、
   captured continuation replay なので initial_frame_count = 0 のまま。

5. return_frame_threshold は証拠なしに外さない。

6. ApplyClosure 全体を global に EffectfulApply 化しない。
   write16 で once 内の ApplyClosure はすでに対応済み。

7. Stmt::Expr 全体を global に split しない。

8. Cranelift backend を同時に直そうとしない。
```

---

# 5. 実装の中心アイデア

## 問題のある現在の挙動

いまは `EffectfulCall fold_impl` のあと、こうなる。

```text
return_frames = [ ..., F_each_post_fold ]

fold_impl returns Thunk

Return(thunk):
  return_frames が initial_frame_count より長いので
  continue_return_frames(thunk, own_frames) を呼ぶ

continue_return_frames:
  F_each_post_fold を pop
  each cont 12 に thunk を渡す

each cont 12:
  ForceThunk(thunk) を sync stmt で実行

sync ForceThunk:
  return_frames はもう空
  thunk body の Perform が F_each_post_fold を capture できない
```

これをこう変える。

```text
Return(thunk):
  top return frame を見る

  top frame の continuation が
  「受け取った値を即 ForceThunk する post-call cont」
  なら、F_each_post_fold をまだ pop しない

  thunk body を、
    return_frames = 現在の return_frames
    initial_frame_count = 現在の initial_frame_count
  で評価する

thunk body の Perform:
  F_each_post_fold を capture できる

thunk body の普通の Return:
  F_each_post_fold を consume して each cont 12 へ進む
```

重要なのは、thunk body を評価するときにこれを守ること。

```text
initial_frame_count = return_frames.len()
```

ではない。

```text
initial_frame_count = 現在の initial_frame_count
```

または、EffectfulCall callee 側で使われている `pre_push_count` 相当の threshold を維持する。

`initial_frame_count = return_frames.len()` にすると、F_each_post_fold が inherited 扱いになり、また consume されなくなる。これは今回のバグを再生する方向だねぇ。

---

# 6. 実装手順

## Step 0: baseline を取る

```bash
cargo test -p yulang-native

cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

期待値。

```text
cargo test -p yulang-native
  => pass

debugs_local_choice_caller_rest_eval
  => pass

debugs_local_choice_callback_rest_eval
  => pass

debugs_std_undet_once_skip_eval_layers
  => fail
  => cps:3 vs vm:2
```

ここが違うなら、今回の作業に入る前に差分を見る。

---

## Step 1: trace を少し増やす

write16 で `Perform` / `Return` / `EffectfulApply` trace は入っている。次は、`EffectfulCall` / sync `ForceThunk` / `continue_return_frames` も見る。

追加したい trace。

```text
CpsTerminator::EffectfulCall:
  - current function
  - current continuation
  - target
  - resume
  - pre_push_count
  - new_frames.len()
  - initial_frame_count

CpsStmt::ForceThunk:
  - current function
  - current continuation
  - thunk owner_function / entry
  - return_frames.len()
  - initial_frame_count
  - inherited として渡す値

continue_return_frames:
  - pop する frame.owner_function
  - frame.continuation
  - rest.len()
  - frame.owner_initial_frame_count
  - 渡す initial_frame_count

Return:
  - value が Thunk かどうか
  - top return frame が即 ForceThunk cont かどうか
```

実行。

```bash
YULANG_CPS_TRACE_FRAMES=1 \
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

確認したいこと。

```text
Return(thunk) の直後に F_each_post_fold が pop されているか
pop 後の each cont 12 が ForceThunk(thunk) をしているか
その ForceThunk 実行時に return_frames.len = 0 になっているか
```

これが出れば、write16 report の読みと一致する。

---

## Step 2: top frame が「即 ForceThunk」か判定する helper を作る

`cps_eval.rs` に helper を追加する。

名前例。

```rust
fn return_frame_immediately_forces_param(
    module: &CpsModule,
    frame: &CpsReturnFrame,
) -> CpsEvalResult<Option<CpsValueId>>
```

この helper は、`frame` の continuation を見て、次の形なら `Some(param)` を返す。

```text
continuation.params.len() >= 1
let returned = continuation.params[0]

continuation.stmts の先頭が:
  CpsStmt::ForceThunk { dest: _, thunk }

かつ:
  thunk == returned
```

もっと安全にするなら、まずはこの条件をさらに狭くしていい。

```text
frame.owner_function.starts_with("std::undet::undet::each")
```

または

```text
frame.owner_function contains "each"
```

ただし名前ベースは一時策としてコメントを残す。

推奨はこの順。

```text
第1段階:
  top frame continuation が返り値 param を即 ForceThunk する場合だけ対象

第2段階:
  それでも広すぎて regression が出るなら、
  frame.owner_function が std::undet::undet::each 系のときだけ対象
```

---

## Step 3: `Return` branch に pre-force 経路を入れる

`CpsTerminator::Return(value)` の現在の流れは、おそらくこう。

```rust
let v = read_value(function, &values, *value)?;
if return_frames.len() <= initial_frame_count {
    return Ok(v);
}
let own_frames = return_frames.split_off(initial_frame_count);
return continue_return_frames(module, v, &own_frames, &[]);
```

この `continue_return_frames` の前に、targeted pre-force を挟む。

擬似コード。

```rust
let mut v = read_value(function, &values, *value)?;

if let CpsRuntimeValue::Thunk(thunk) = &v {
    if return_frames.len() > initial_frame_count {
        if let Some(top_frame) = return_frames.last() {
            if return_frame_immediately_forces_param(module, top_frame)?.is_some() {
                trace_cps(
                    "ReturnPreForceThunk",
                    format!(
                        "fn={} cont={:?} top_frame={}: {:?} frames.len={} initial={}",
                        function.name,
                        current,
                        top_frame.owner_function,
                        top_frame.continuation,
                        return_frames.len(),
                        initial_frame_count,
                    ),
                );

                return force_returned_thunk_before_frame_consumption(
                    module,
                    thunk.clone(),
                    top_frame,
                    return_frames.clone(),
                    initial_frame_count,
                );
            }
        }
    }
}
```

ここで大事なのは、**return frame を pop する前に thunk body を実行する**こと。

---

## Step 4: thunk body 評価 helper を作る

名前例。

```rust
fn force_returned_thunk_before_frame_consumption(
    module: &CpsModule,
    thunk: Rc<CpsThunk>,
    top_frame: &CpsReturnFrame,
    return_frames: Vec<CpsReturnFrame>,
    initial_frame_count: usize,
) -> CpsEvalResult<CpsRuntimeValue>
```

中身の考え方。

```text
1. thunk.owner_function を探す。

2. handlers / guards は top_frame のものを優先する。
   理由:
     本来なら F_each_post_fold が pop されたあと、
     each cont 12 の ForceThunk が frame.active_handlers / frame.guard_stack の文脈で動く。
     それを pop 前に先取りするので、top_frame の文脈を使うのが自然。

3. return_frames は pop せず、そのまま渡す。

4. initial_frame_count は現在の initial_frame_count を渡す。
   F_each_post_fold を own frame のままにするため。

5. thunk body がさらに Thunk を返すなら、同じ条件で peel する。
   ただし無限 loop を避けるため、まずは sync ForceThunk と同じ while 形にする。
```

擬似コード。

```rust
fn force_returned_thunk_before_frame_consumption(
    module: &CpsModule,
    mut thunk: Rc<CpsThunk>,
    top_frame: &CpsReturnFrame,
    return_frames: Vec<CpsReturnFrame>,
    initial_frame_count: usize,
) -> CpsEvalResult<CpsRuntimeValue> {
    loop {
        let owner = function_by_name(module, &thunk.owner_function)?;

        let result = eval_continuations(
            module,
            owner,
            thunk.entry,
            Vec::new(),
            thunk.values.as_ref().clone(),
            top_frame.active_handlers.clone(),
            top_frame.guard_stack.clone(),
            return_frames.clone(),
            initial_frame_count,
        )?;

        match result {
            CpsRuntimeValue::Thunk(next) => {
                thunk = next;
                continue;
            }
            other => return Ok(other),
        }
    }
}
```

ここは少し繊細だよ〜。

`eval_continuations` は handler を `into_inherited` する入口なので、`top_frame.active_handlers` を渡したときの inherited 化が既存 sync call と同じ扱いになる。write14 の sync force も cross-function/thunk entry では `eval_continuations` を使っているので、この形から始めるのが自然だねぇ。

もし trace 上で handler の inherited 状態が崩れるなら、`eval_continuations` ではなく `resume_continuation` を使うかを検討する。ただし最初からそこへ飛ばないほうがいい。既存 sync ForceThunk の作法に寄せる。

---

# 7. 期待される trace の変化

修正前。

```text
Return: fold_impl value=Thunk return_frames.len=1 initial=0
continue_return_frames: pop F_each_post_fold
ForceThunk: each cont 12 return_frames.len=0
Perform: branch ... only once
Return: each cont 2 value=3
```

修正後に見たい形。

```text
Return: fold_impl value=Thunk return_frames.len=1 initial=0
ReturnPreForceThunk: top_frame=each cont 12 frames.len=1 initial=0
Force returned thunk body with frames.len=1 initial=0
Perform: branch ... return_frames.len >= 1
...
x=1 guard reject
resume k false
Perform: branch ...  // x=2 側、または正しい fold continuation 側で新しく起きる
Perform: sub::return 2
Return: work/root value=2
```

最低限、**branch Perform が 1 回だけではなくなる**はずだよ〜。

---

# 8. 失敗したときの分岐

## A. まだ `cps:3`

見る場所。

```text
ReturnPreForceThunk が発火しているか
```

### 発火していない場合

top frame の continuation が想定と違う。

次を trace に出す。

```text
top_frame.owner_function
top_frame.continuation
continuation.params
continuation.stmts[0..3]
```

可能性。

```text
1. ForceThunk が first stmt ではない
2. return value param が params[0] ではない
3. ForceThunk の前に Literal / Tuple / Select などがある
4. each cont 12 ではなく別 cont が top frame
```

対応。

```text
ForceThunk が first stmt でないなら、
「少数の pure administrative stmt を飛ばして ForceThunk を探す」
程度に広げる。

ただし、branch / perform / call / apply を飛ばすのは禁止。
```

## B. `cps:0` に悪化

これは write16 の `EffectfulForce` 試行と同じ方向の壊れ方だねぇ。

まず確認。

```text
thunk body eval に initial_frame_count = return_frames.len() を渡していないか
```

これはダメ。

```text
initial_frame_count = return_frames.len()
```

正しくは、F_post を own frame として残すためにこれ。

```text
initial_frame_count = 現在の initial_frame_count
```

次に確認。

```text
top_frame.active_handlers ではなく、現在の callee active_handlers を使っていないか
```

`fold_impl` の `Return(thunk)` 時点の callee active handlers は、`each cont 12` の force 文脈とズレる可能性がある。まずは top frame の文脈を使う。

## C. local callback test が落ちる

対象範囲が広すぎる。

pre-force 条件を絞る。

```text
return value が Thunk
かつ return_frames.len() > initial_frame_count
かつ top frame が即 ForceThunk
かつ top_frame.owner_function が std::undet::undet::each 系
```

これで `debugs_local_choice_callback_rest_eval` などの一般ケースに影響しにくくなる。

## D. `ScopeReturn` が root へ escape する

`return_frame_threshold` か inherited handler の扱いが崩れている。

この場合も、まず threshold を外すのではなく trace する。

```text
ScopeReturn prompt
target
matched handler prompt
handler inherited
return_frame_threshold
truncate 前 frames.len
truncate 後 frames.len
```

write15 の threshold は「handler install 後に push された frames を non-local exit 時に捨てる」ために入っている。これを外すと、sub::return 後に fold の続きが残りやすくなる。

---

# 9. なぜ lowering 側ではなく eval 側がよさそうか

候補は大きく三つある。

## 候補 A: sync `ForceThunk` を `EffectfulForce` にする

write16 で試して `cps:0` に悪化済み。frame ownership と handler threshold を同時に正しく扱う必要があり、単純変換では危ない。

## 候補 B: `Return(thunk)` の auto frame consumption 前に thunk body を評価する

今回のおすすめ。

理由。

```text
- 問題が起きている瞬間に直接介入できる
- F_each_post_fold がまだ stack に残っている
- post-cont の ForceThunk を先取りするだけなので、意味が局所的
- top frame が即 ForceThunk する場合だけに絞れる
```

## 候補 C: `fold_impl` の `MakeThunk + Return` を生成しないよう lowering を変える

根本的に見えるけど、危ない。

理由。

```text
- Thunk wrapping は effect / demand / return type の設計に絡む
- higher_order_helper だけ特別扱いすると標準ライブラリ依存が増える
- 既存 golden や thunk-typed return の意味に波及しやすい
```

最初にやるなら B。C は B が破綻したときの第二候補でいいと思うよ〜。

---

# 10. 実装LLMに渡す短い作業文

```text
目的:
debugs_std_undet_once_skip_eval_layers を CPS eval:2 / VM:2 に一致させる。
write16 後の現状は cps:3 vs vm:2。

重要な現状:
- once 内の curried ApplyClosure は write16 で全て EffectfulApply 化済み。
- EffectfulApply(Resumption) の frame order も write16 で修正済み。
- それでも失敗する。
- trace では branch Perform が1回しか出ない。
- 原因は each の EffectfulCall fold_impl が push した F_each_post_fold を、
  fold_impl の Return(Thunk) が thunk body 実行前に consume してしまうこと。
- その後 each cont 12 の sync ForceThunk が frames=[] で thunk body を走らせるため、
  thunk body 内の branch Perform が F_each_post_fold を capture できない。

実装方針:
CpsTerminator::Return の処理で、Return 値が CpsRuntimeValue::Thunk かつ
return_frames の top frame が「返り値を即 ForceThunk する continuation」なら、
continue_return_frames で top frame を pop する前に、その thunk body を評価する。

thunk body 評価時の注意:
- return_frames は現在の return_frames をそのまま渡す。
- initial_frame_count は現在の initial_frame_count を渡す。
- initial_frame_count = return_frames.len() にしない。
  それをすると F_each_post_fold が inherited 扱いになってまた consume されない。
- handlers / guard_stack は top return frame の active_handlers / guard_stack を使う。
  本来 top frame を pop した後に ForceThunk が走る文脈を先取りするため。
- thunk がさらに Thunk を返すなら、sync ForceThunk と同じように loop で peel する。
- ScopeReturn が返ったら既存の dispatch / propagation ルールを壊さない。

対象範囲:
最初は top frame が即 ForceThunk する場合だけ。
regression が出るなら top_frame.owner_function が std::undet::undet::each 系の場合だけに絞る。

触らないこと:
- write14 の initial_frame_count 設計を大改造しない。
- return_frame_threshold を外さない。
- once の ApplyClosure をさらに global 化しない。
- Stmt::Expr 全体を effectful split しない。
- Cranelift backend を同時に直さない。

確認:
1. cargo test -p yulang-native
2. cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture
3. cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture
4. YULANG_CPS_TRACE_FRAMES=1 cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture

成功条件:
- 通常テスト pass
- local choice caller/callback tests pass
- debugs_std_undet_once_skip_eval_layers が CPS eval:2 / VM:2
- trace 上、branch Perform が1回だけで終わらない
- Return(Thunk) の直後に F_each_post_fold を pop せず、pre-force 経路が発火する
```

---

# 11. 私の判断

いま一番避けたいのは、`EffectfulForce` や global lowering を増やして「どの frame が own でどれが inherited か」をまた混ぜることだねぇ。

今回のバグはかなり局所的に見える。

```text
EffectfulCall が返す Thunk
+
top return frame がその Thunk を即 ForceThunk する
+
Return auto-consumption が早すぎる
```

だから、**`Return(thunk)` の auto-consume 直前に、top frame の即 ForceThunk を先取りする targeted 修正**が一番まっすぐだと思うよ〜。
