読んだよ〜。結論から言うと、**次に実装LLMへ渡すべき作業は「write15 の targeted lowering をさらに広げる」ではなく、`std::undet.once` の handler 内で起きている curried `ApplyClosure` / resumption apply の捕捉漏れを trace で確定し、`once` 内に限って `EffectfulApply` 化する作業**だねぇ。

write15 report では、`fold_impl` / `each` / `once` 向けの targeted lowering、`EffectfulCall/Apply` 化、demand-side forcing、`return_frame_threshold` による delimited-continuation extent 管理が入っている。その結果、write14 時点の `cps:0 vs vm:2` から `cps:3 vs vm:2` まで進んでいて、完全失敗ではなく「バックトラックが動き始めたが、2 で止まらず 3 まで進む」状態になっている。ここが一番重要な読みだよ〜。

---

## 実装LLMへの大前提

このタスクの目的はこれ。

```text
debugs_std_undet_once_skip_eval_layers を、
CPS eval: 2
VM:       2
に一致させる。
```

やらないことはこれ。

```text
- Cranelift backend 対応を先にやらない
- ApplyClosure 全体を global に EffectfulApply 化しない
- Stmt::Expr 全体を global に split しない
- write14 の initial_frame_count 設計を大きく書き換えない
- return_frame_threshold を勘で外さない
- fold-like local test を主 oracle にしない
```

write14 で入った `initial_frame_count` 設計は、「sync call は親 frames を inherit するが、通常 Return では consume しない」という中核修正だねぇ。これは `debugs_local_choice_callback_rest_eval` を通した土台なので、まず壊さない扱いにする。

---

# 実行手順

## Step 0: baseline を固定する

まず、作業前にこのコマンドを走らせる。

```bash
cargo test -p yulang-native

cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

期待する現状はこれ。

```text
cargo test -p yulang-native
  => 既存通常テスト pass

debugs_local_choice_caller_rest_eval
  => pass

debugs_local_choice_callback_rest_eval
  => pass

debugs_std_undet_once_skip_eval_layers
  => fail
  => cps:3 vs vm:2
```

ここで `cps:0 vs vm:2` なら、write15 の変更がまだ入っていない状態。
ここで local callback test が落ちるなら、write14 の `initial_frame_count` 周辺が壊れている状態。
どちらの場合も、`once` の追加修正へ進む前に現状差分を切り分ける。

---

## Step 1: まず trace を入れて、`3` になる道筋を確定する

write15 report の読みでは、現在の挙動はだいたいこう。

```text
1. x=1 で branch=true
2. sub::return 1
3. work 側で n=1
4. guard fail
5. reject
6. once reject arm が保存済み continuation k1 を false で resume
7. x=2 に進むべき
8. しかし CPS は最終的に x=3 を返す
```

ここで確認したい問いは一つ。

```text
k1 false の false は、x=1 の branch の else に戻っているか？
それとも、x=2 の branch 結果として誤って使われているか？
```

この違いが超重要だねぇ。

### trace を入れる場所

`crates/yulang-native/src/cps_eval.rs` に、env var guard 付きの trace を入れる。

```rust
fn trace_cps(event: &str, msg: impl std::fmt::Display) {
    if std::env::var_os("YULANG_CPS_TRACE_FRAMES").is_some() {
        eprintln!("[cps-trace] {event}: {msg}");
    }
}
```

最低限、以下の場所で出す。

```text
CpsTerminator::Perform
  - effect 名
  - current function
  - current continuation
  - return_frames.len()
  - initial_frame_count
  - active_handlers.len()

CpsStmt::ApplyClosure
  - callable が Closure か Resumption か
  - dest / closure / arg
  - return_frames.len()
  - initial_frame_count

CpsTerminator::EffectfulApply
  - callable が Closure か Resumption か
  - resume continuation
  - push 前 frames len
  - push 後 frames len
  - callee/resumption に渡す initial_frame_count

CpsTerminator::EffectfulCall
CpsTerminator::EffectfulForce
  - 同上

CpsTerminator::Return
  - value
  - return_frames.len()
  - initial_frame_count
  - own frames の範囲

continue_return_frames
  - pop する frame
  - resume 先 function / continuation
  - rest.len()
  - owner_initial_frame_count

handle_scope_return / dispatch_scope_return
  - prompt
  - target
  - return_frame_threshold
  - truncate 前後の return_frames.len()
```

実行はこう。

```bash
YULANG_CPS_TRACE_FRAMES=1 \
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

---

## Step 2: CPS dump で `once` の branch arm を見る

write15 report は、`once__mono4` の `cont 6`、特に branch arm の `ApplyClosure` を疑っている。ここを dump する。

見る対象 function 名はこのあたり。

```text
std::undet::undet::once
once__mono
std::undet::undet::each
std::list::fold_impl
root
work
```

dump で特に探す形はこれ。

```text
CpsStmt::ApplyClosure { ... }
```

`once` の branch arm では、source 的にはこういう構造があるはず。

```text
loop(k true, queue + [k])
```

これは curried apply なので、CPS では複数段の `ApplyClosure` になりやすい。

```text
tmp1 = ApplyClosure(k, true)
tmp2 = ApplyClosure(loop, tmp1)
tmp3 = ApplyClosure(tmp2, queue_plus_k)
```

または、局所関数 `loop` の表現次第で少し違う形になる。

ここで重要なのは、**`k true` が Resumption apply である可能性がある**こと。`cps_eval.rs` の `CpsStmt::ApplyClosure` は、runtime value が `Closure` の場合と `Resumption` の場合を分けて処理している。つまり静的にはただの `ApplyClosure` でも、実行時には captured continuation replay になりうる。

---

## Step 3: trace の判定表

trace を見て、次のどれかに分類する。

### A. `x=2` の branch が `Perform` を起こしていない

これは本命。

```text
k1 false のあと、
x=2 の branch() が新しい Perform として handler に届かず、
false がそのまま x=2 側の branch 結果みたいに使われている
```

この場合、`k false` の resumption replay と、その後の handler body continuation の接続がずれている。

修正対象は `once` 内の curried `ApplyClosure`、特に `k true` / `k false` / `loop(...)` 周辺の `EffectfulApply` 化。

### B. `x=2` の branch は `Perform` しているが、handler が false を選んでいる

この場合は queue / loop state 管理が怪しい。

```text
branch handler が本来 loop(k true, queue+[k]) すべきところで、
古い false / 古い queue / 古い continuation を使っている
```

修正対象は `once` の branch arm 内の `loop(k true, queue+[k])` の apply 順序と、return frame に入る handler body rest。

### C. `x=2` で `sub::return 2` しているのに fold が続いて `3` になる

この場合は `ScopeReturn` / `return_frame_threshold` が怪しい。

```text
sub::return 2 が each/sub scope を抜けるべきなのに、
handler scope 内の fold continuation が truncate されず残っている
```

この場合だけ `return_frame_threshold` を見る。
ただし、write15 で threshold と truncate はすでに入っているので、最初からここを疑いすぎない。

---

## Step 4: 最初に入れるべき修正

一番安全な第一パッチはこれ。

```text
std::undet::undet::once 内に限って、
closure apply を型判定に頼らず EffectfulApply 化する。
```

理由は、write15 の現状判定が `expr.ty` の `Thunk` や direct callee の return type に寄っていて、curried partial apply では型が `Thunk` ではなく `Fun` / `Unknown` / closure value になりやすいからだねぇ。report でもここが不安定点として挙がっている。

### 実装方針

`crates/yulang-native/src/cps_lower.rs` に helper を足す。

```rust
fn is_std_undet_once_helper_name(name: &str) -> bool {
    name.starts_with("std::undet::undet::once")
}
```

`FunctionLowerer` にすでに `higher_order_helper` があるなら、`once` 専用判定もそこから見られるようにする。

```rust
let once_helper = name.starts_with("std::undet::undet::once");
```

そして `lower_apply` 側で、既存の条件に加えて `once_helper` を見る。

```rust
let force_effectful_apply =
    self.once_helper
    || (self.higher_order_helper && result_type_is_thunk_wrapped);
```

ただし対象は **closure apply** に絞る。

```text
- primitive apply は対象外
- direct_apply_path で既知の DirectCall に解決できるものは既存経路を優先
- runtime::ExprKind::Apply として closure apply になるものだけ対象
```

`once` 内では curried apply の内側と外側の両方が `EffectfulApply` になるのを許す。
ここで片方だけ effectful にすると、`k true` の post-call rest か `loop(...)` の post-call rest のどちらかが漏れる可能性がある。

期待する lowering 形はこう。

```text
current:
  EffectfulApply k true -> post_k_true

post_k_true(tmp):
  EffectfulApply loop tmp -> post_loop_partial

post_loop_partial(loop_tmp):
  EffectfulApply loop_tmp queue_plus_k -> post_loop_done

post_loop_done(result):
  ...
```

実際の `loop` 表現が direct call なら、`EffectfulCall` 側も同じ考えで扱う。
ただし最初は `once` 内の `ApplyClosure` を主対象にする。`DirectCall` まで広げるのは trace で必要と分かった後でいい。

---

## Step 5: `EffectfulApply` が Resumption を扱えるか確認する

ここはかなり大事。

`CpsStmt::ApplyClosure` は `Closure` と `Resumption` の両方を扱っている。`k true` / `k false` は runtime value として `Resumption` になりうる。

なので、`EffectfulApply` 側が `Closure` しか扱っていないなら、`Resumption` 分岐を追加する必要がある。

### Resumption 版 `EffectfulApply` の意味

やりたい意味はこれ。

```text
handler body 側:
  my y = k true
  rest(y)

k true は captured continuation を再開する。
captured continuation が完了したあと、handler body の rest(y) に戻る。
```

つまり、`EffectfulApply` の `resume` continuation は、**resumption replay が終わった後に実行される post-call frame** だねぇ。

実装時の注意点。

```text
- post-call frame は current function/current continuation の続き
- frame.owner_initial_frame_count は現在の initial_frame_count
- resumption replay 自体は captured frames を consume してよいので initial_frame_count = 0
- ただし post-call frame は captured frames より後に実行される位置へ入れる
```

ここで雑に `adjusted_frames.push(post_frame)` すると危ない。
`continue_return_frames` が frame vector の末尾から pop する実装なら、末尾に入れた frame が先に実行されてしまう。実装LLMは `continue_return_frames` の消費順を先に読む必要がある。

明確な判定基準はこれ。

```text
EffectfulApply(Resumption k, true) の直後、
最初に実行される continuation は k が捕捉していた branch site の continuation。
handler body の post-call continuation は、その captured continuation が値を返した後。
```

trace でこの順序を検証する。

---

## Step 6: `return_frame_threshold` は後回し

write15 で `CpsHandlerFrame.return_frame_threshold` が追加され、`ScopeReturn` が handler scope を抜けるときに、handler install 後に push された return frames を truncate する設計になっている。さらに `continue_return_frames` 側には threshold truncate 後の不整合を避ける clamp も入っている。

だから、ここは最初に触らない。

触る条件はこれだけ。

```text
trace 上で x=2 の branch=true が起きる
sub::return 2 も起きる
ScopeReturn の target / prompt も一致する
それでも return_frames.truncate(threshold) 後に fold の x=3 continuation が残る
```

この証拠が出た場合だけ、`return_frame_threshold` の値が「handler install 時の return_frames.len()」になっているかを見る。

---

## Step 7: fold-like local test は主タスクにしない

write15 report では、write15 §7.2 の fold2-based Test B は VM レベルでも期待値が曖昧になりやすく、commit しなかったと書かれている。だから今回も、fold2 local test を主 oracle にしない方がいい。

主 oracle はこれ。

```text
debugs_std_undet_once_skip_eval_layers
```

補助 oracle はこれ。

```text
debugs_local_choice_caller_rest_eval
debugs_local_choice_callback_rest_eval
```

local tests が落ちたら、write14/write13 の土台を壊した扱い。

---

## Step 8: 成功条件

最終的にこうなれば成功。

```bash
cargo test -p yulang-native

cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture

cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

期待結果。

```text
cargo test -p yulang-native
  => pass

debugs_local_choice_caller_rest_eval
  => pass

debugs_local_choice_callback_rest_eval
  => pass

debugs_std_undet_once_skip_eval_layers
  => CPS eval と VM が 2 で一致
```

Cranelift の `EffectfulCall/Apply/Force` 未対応テストは、write15 report の通り別段階扱いでいい。3 件を `#[ignore]` にした状態は、CPS eval semantics を固めるための一時的な切り分けだねぇ。

---

# 実装LLMにそのまま渡す指示文

```text
目的:
debugs_std_undet_once_skip_eval_layers の CPS eval を VM と一致させる。
現在は write15 後で cps:3 vs vm:2。write14 時点の cps:0 より進んでいるので、outer frames はある程度捕捉できている。残りは std::undet.once の branch/reject handler 内の curried ApplyClosure / resumption apply / loop state 管理の問題として扱う。

重要な前提:
- write14 の initial_frame_count 設計は壊さない。
- sync call は parent return_frames を inherit するが、callee の通常 Return では consume しない。
- EffectfulCall/Apply/Force は call site の post-call continuation を frame として push する。
- Resume / ResumeWithHandler / ApplyClosure(Resumption) は captured continuation replay なので initial_frame_count = 0。
- Cranelift backend 対応はこのタスクの範囲外。
- ApplyClosure 全体や Stmt::Expr 全体を global に Effectful 化しない。

作業:
1. baseline test を取る。
   cargo test -p yulang-native
   cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored --nocapture
   cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture
   cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture

2. cps_eval.rs に env var guard 付き trace を入れる。
   見るイベントは Perform, ApplyClosure, EffectfulApply, Return, continue_return_frames, ScopeReturn dispatch。
   特に k false の false が x=1 の branch else に戻るか、x=2 の branch 結果として誤用されるかを見る。

3. CPS dump で std::undet::undet::once / once__mono / std::undet::undet::each / std::list::fold_impl を見る。
   once の branch arm、特に loop(k true, queue+[k]) 周辺の ApplyClosure を特定する。
   write15 report は once__mono4 cont 6 の branch arm を疑っている。

4. cps_lower.rs で std::undet::undet::once 内の closure Apply を targeted EffectfulApply 化する。
   既存の expr.ty Thunk 判定や info_returns_thunk 判定に頼らず、once 内の curried ApplyClosure は effectful にする。
   primitive apply と既知 pure direct call には広げない。
   global ApplyClosure 全体には広げない。

5. EffectfulApply evaluator が Resumption runtime value を扱えるか確認する。
   扱えないなら CpsStmt::ApplyClosure の Resumption 分岐と同等の処理を EffectfulApply に追加する。
   そのとき、post-call frame は captured continuation が完了した後に実行される位置へ入れる。
   frame の消費順は continue_return_frames を読んで確認する。
   trace で、EffectfulApply(Resumption k, true) の直後に handler post frame が先に走っていないことを確認する。

6. 再テストする。
   debugs_std_undet_once_skip_eval_layers が cps:2 vs vm:2 になれば成功。
   cps:3 のままなら trace を分類する:
     - x=2 branch Perform が無い: resumption apply / ApplyClosure lowering がまだ足りない
     - x=2 branch Perform があるが false を選ぶ: once loop queue state の接続が違う
     - x=2 sub::return 2 後に x=3 へ進む: return_frame_threshold / ScopeReturn truncate を疑う

7. return_frame_threshold は証拠が出るまで触らない。
   触る場合は、handler install 時の return_frames.len() が threshold になっているか、
   ScopeReturn dispatch 時に handler install 後の frames が確実に truncate されるかだけを見る。

8. 成功後、trace は env var guard のまま残すか、不要なら消す。
   テスト期待値は CPS eval と VM の 2 一致。
   Cranelift ignored はこの段階では解除しない。
```

---

## 私の読み

一番ありそうなのは、**`once` の branch arm 内の `k true` / `loop(...)` が sync `ApplyClosure` のままで、resumption replay と handler body の post-call continuation のつなぎ順が足りない**パターンだと思うよ〜。

write15 で `fold_impl` 側の local rest はかなり捕まるようになった。だから `0` ではなく `3` まで進んだ。残りは「探索が 2 で成功した瞬間に止まる」ための once 側の continuation extent、特に curried apply と resumption apply の扱いだねぇ。
