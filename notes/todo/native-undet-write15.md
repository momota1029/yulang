読んだよ〜。結論として、**write14 は `cps_eval.rs` の `initial_frame_count` refactor を終えた段階で区切れていて、次は `std::undet.once` が落ちる原因である「`fold_impl` 内の local rest が resumption に入らない」問題を潰す段階**だねぇ。
ここで雑に `ApplyClosure` 全体や `Stmt::Expr` 全体を effectful 化すると Cranelift 側の既存 regression を起こしやすいから、**trace で欠けている frame を確認してから、`fold_impl` 周辺に targeted lowering を入れる**のが一番安全だと思うよ〜。

---

# まず現状理解

## write14 で完了済みのこと

`native-undet-write14-report.md` によると、write14 では `cps_eval.rs` だけを変更して、sync call が親の `return_frames` を **inherit するが consume しない** ように直している。具体的には、`eval_function_with_context` / `eval_continuations` / `resume_continuation` に `initial_frame_count` を渡し、`Return` では `initial_frame_count` より後ろの own frames だけを consume する設計になった。

これで、次のような区別が入った。

```text
sync call:
  callee に parent return_frames を渡す
  callee.initial_frame_count = parent_return_frames.len()
  => Perform は親 frames を捕まえられる
  => 普通の Return では親 frames を消費しない

EffectfulCall / EffectfulApply / EffectfulForce:
  call site が自分の post-call continuation を frame として push する
  callee.initial_frame_count = push 前の return_frames.len()
  => callee の Return は push された own frame を consume できる
```

この変更により、`debugs_local_choice_callback_rest_eval` は通った。つまり、**callback 内の `branch()` が outer continuation を辿る核はもう成立している**。

## まだ落ちているもの

まだ落ちているのは `debugs_std_undet_once_skip_eval_layers` で、現状は `cps:0 vs vm:2`。write14 report は、これは `initial_frame_count` ではなく、**`fold_impl` 内の非 tail / local rest を resumption に入れる次段階の問題**だと切り分けている。

標準ライブラリを見ると、`std::undet.each` はこうなっている。

```yulang
pub each xs = sub::sub {
    xs.fold (): \() x -> if branch() { sub::return x } else ()
    reject()
}
```

つまり、`fold` の callback 内で `branch()` し、true なら `sub::return x` で `each` 全体を抜け、false なら次の要素へ進む形だねぇ。

そして `std::list::fold` の中核はこれ。

```yulang
my fold_impl xs z f = case std::list::view_raw xs:
    list_view::empty -> z
    list_view::leaf x -> f z x
    list_view::node(left, right) -> fold_impl(right, fold_impl left z f, f)
```

ここで危ないのは `f z x` と、`node` branch の `fold_impl left z f` の後に `fold_impl right ...` へ進む local rest だよ〜。

---

# 核心の見方

write14 後の sync call inheritance は、**すでに存在する outer frames** を callee に渡せる。
でも、sync call は **その call site 自身の post-call continuation を新しい frame として push しない**。

つまりこういうこと。

```text
caller side:
  my y = f x
  rest(y)

sync ApplyClosure のまま:
  callee receives parent frames
  でも「rest(y)」は return_frames に入らない

EffectfulApply terminator:
  「rest(y)」を CpsReturnFrame として push
  callee receives parent frames + this local frame
```

`std::undet.once` の失敗は、まさにここっぽい。
outer の `once` / `sub` / `work` 由来の frame は write14 で見えるようになった。でも `fold_impl` の「false を選んだあと次の要素へ進む」local rest が frame 化されていないから、`k false` で探索を続けるべきところが続かず、最終的に `reject()` 側へ落ちて `0` になる、という読みだねぇ。

---

# 最優先の作業方針

## 一言で言うと

**`cps_eval.rs` の中核 refactor は触らず、まず trace で frame stack を確認する。その後、`fold_impl` 周辺の callback apply / local rest を targeted に `EffectfulApply` / 必要なら `EffectfulCall` へ lower する。**

やらないほうがいいのはこれ。

```text
- ApplyClosure 全体を一律 EffectfulApply 化
- Stmt::Expr 全体を一律 effectful terminator split
- active_handler.is_some() だけに基づく判定
- Cranelift 未対応のまま既存 _through_cps_repr_cranelift テストを広範に壊す変更
```

`CpsTerminator` にはすでに `EffectfulCall` / `EffectfulApply` / `EffectfulForce` があるから、IR 定義そのものを増やす必要はたぶんない。

---

# 別 LLM に渡す実装手順

## Step 0: baseline を固定する

まず、作業前に現状を再確認する。

```bash
cargo test -p yulang-native
cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

期待する現状。

```text
- 通常テストは pass
- debugs_local_choice_callback_rest_eval は pass
- debugs_std_undet_once_skip_eval_layers は cps:0 vs vm:2 で fail
```

ここが違うなら、先に現状差分を確認する。
特に `debugs_local_choice_callback_rest_eval` が落ちるなら write14 の `initial_frame_count` refactor が壊れている可能性があるから、次へ進まない。

---

## Step 1: CPS dump で `fold_impl` の形を見る

`debugs_std_undet_once_skip_eval_layers` か `debugs_std_undet_once_cps_shape` に、対象 function を絞った dump を足す。

見る対象名はこのへん。

```text
- root
- once
- loop
- each
- sub
- fold
- fold_impl
- callback closure
```

dump で特に見るもの。

```text
std::list::fold_impl の leaf branch:
  f z x

std::list::fold_impl の node branch:
  fold_impl(right, fold_impl left z f, f)

std::undet.each:
  xs.fold (): callback
  reject()
```

危険な形はこれ。

```text
CpsStmt::ApplyClosure { ... }      // callback apply が stmt のまま
CpsStmt::DirectCall { ... }        // non-tail fold_impl left が stmt のまま
CpsStmt::ForceThunk { ... }        // effectful thunk force が stmt のまま
```

期待する targeted 修正後の形は、少なくとも問題箇所がこうなること。

```text
CpsTerminator::EffectfulApply { resume: post_cont, ... }

必要なら:

CpsTerminator::EffectfulCall { resume: post_cont, ... }
CpsTerminator::EffectfulForce { resume: post_cont, ... }
```

---

## Step 2: eval trace で「何が欠けているか」を確定する

`cps_eval.rs` に一時 trace を足す。恒久コードにしてもよいけど、その場合は env var guard を付けるとよさそう。

例。

```rust
fn trace_cps_frames(event: &str, function: &str, cont: CpsContinuationId, len: usize, initial: usize) {
    if std::env::var_os("YULANG_CPS_TRACE_FRAMES").is_some() {
        eprintln!(
            "[cps frames] {event} function={function} cont={cont:?} return_frames.len={len} initial={initial}"
        );
    }
}
```

入れる場所。

```text
- resume_continuation の loop entry
- CpsTerminator::Perform
- CpsTerminator::EffectfulCall
- CpsTerminator::EffectfulApply
- CpsTerminator::EffectfulForce
- CpsTerminator::Return
- continue_return_frames の pop 直前/直後
- CpsStmt::DirectCall / ApplyClosure / ForceThunk の sync call 境界
- Resume / ResumeWithHandler / ApplyClosure(Resumption)
```

trace で確認する問いはこれ。

```text
branch() が fold callback 内で Perform した瞬間、
return_frames に何が入っているか？
```

判断分岐。

```text
A. outer frames も入っていない
   => write14 の sync inheritance がまだ足りない。
      DirectCall / ApplyClosure / ForceThunk stmt が parent return_frames.clone()
      と initial_frame_count = parent_len を渡しているか確認する。

B. outer frames は入っているが、fold の「次の要素へ進む rest」がない
   => これが今回の本命。
      fold_impl 内の callback apply / non-tail fold call を targeted Effectful* 化する。

C. local rest も入っているのに結果が 0
   => Resume 後の ScopeReturn routing、handler inherited flag、
      guard stack snapshot、ResumeWithHandler の extra handler injection を疑う。
```

まず B を想定して進めるのが自然だねぇ。

---

## Step 3: lowering の修正対象を絞る

修正対象は `crates/yulang-native/src/cps_lower.rs`。
`cps_eval.rs` は trace 以外では触らない方針で進める。write14 の中核はもう成立しているから、ここをまた大きく動かすと原因が混ざる。

狙う call site はこの順。

### 3.1 `fold_impl` の callback apply

`list_view::leaf x -> f z x` は curried apply なので、lowering 後はだいたい次のような段階になるはず。

```text
tmp = ApplyClosure(f, z)
result = ApplyClosure(tmp, x)
Return(result)
```

このうち、少なくとも callback 本体へ入る apply は `EffectfulApply` にする。

安全寄りなら、`f z` と `(f z) x` の両方を targeted に effectful 化してよい。
`f z` 自体が effect を起こさなくても、余分な frame は普通の Return で即消費されるだけなので、CPS eval の意味は保ちやすい。

期待形。

```text
EffectfulApply f z -> post_1

post_1(tmp):
  EffectfulApply tmp x -> post_2

post_2(result):
  Return result
```

### 3.2 `fold_impl` の node branch の non-tail recursive call

`list_view::node(left, right) -> fold_impl(right, fold_impl left z f, f)` では、`fold_impl left z f` の戻り値を使って `fold_impl right ...` へ進む。

ここが sync `DirectCall` のままだと、left 側で `branch()` が起きたときに「left が終わったら right へ行く」という local rest が capture されない可能性がある。

dump / trace でこの local rest が欠けていたら、ここも targeted `EffectfulCall` にする。

期待形。

```text
EffectfulCall fold_impl(left, z, f) -> post_left

post_left(z1):
  DirectCall or EffectfulCall fold_impl(right, z1, f)
```

`post_left` が resumption に入ることが重要。
right 側の call を effectful にするかは trace で決める。tail call なら必須ではないが、callback が effectful である以上、targeted 範囲内では effectful にしても意味は壊れにくい。

### 3.3 `std::undet.each` の `xs.fold ...; reject()`

`std::undet.each` には `xs.fold ...` の後に `reject()` がある。
ここは「fold が普通に全部終わったら reject」「途中で `sub::return x` したら reject を skip」という意味になる。

もし lowering 後に `xs.fold ...` が `Stmt::Expr` の sync call で、`reject()` へ進む rest が capture されていないなら、ここも effectful terminator split が必要。

ただしここは **global `Stmt::Expr` split はしない**。
対象を `std::undet.each` / `std::list::fold` 経路に絞るか、型・effect 情報から「この expr statement は effectful thunk/call/apply」と判定できる場合だけにする。

---

## Step 4: 判定条件を `active_handler.is_some()` だけにしない

ここは大事。
`fold_impl` は標準ライブラリ関数として定義されているから、lowering 時点では handler scope の中にいないことが多い。
でも実行時には `once` / `sub` handler の下で動く。

だから、この条件は弱すぎる。

```rust
active_handler.is_some()
```

代わりに、最低限こう見る。

```text
- callee の型が effectful そうか
- callee の戻り値が Thunk / Unknown か
- callee が関数引数・callback・closure value か
- current function が effectful callback を引数に取る高階関数か
- std::list::fold_impl の known callback path か
```

write13 で `callee_type_may_perform` が入っているので、まずそれを再利用する。write13 report では `Fun { ret }` の ret が `Thunk` か `Unknown` なら effectful 扱いする helper が入った、と記録されている。

ただし、それだけで拾えない場合がある。
その場合は、次の fallback を足す。

```text
callee が current function の parameter 由来なら maybe effectful
callee が closure-valued local で型が Unknown / Thunk / opaque なら maybe effectful
std::list::fold_impl 内の f apply は maybe effectful
```

名前ベースの `std::list::fold_impl` 判定は最終手段。
入れるなら、コメントに「temporary targeted workaround」と書いて、後で effect row based 判定へ置き換える前提を明記するのがよさそうだねぇ。

---

## Step 5: 共通 helper を作る

`EffectfulApply` を出す処理を let / expr / tail / nested apply でコピペすると壊れやすい。
共通 helper に寄せる。

イメージ。

```rust
fn lower_effectful_apply_to_cont(
    &mut self,
    closure: CpsValueId,
    arg: CpsValueId,
    resume: CpsContinuationId,
) {
    self.set_terminator(CpsTerminator::EffectfulApply {
        closure,
        arg,
        resume,
    });
}
```

実際には `closure` と `arg` を CPS value に lower する処理も必要だから、もう少し高水準の helper にしてよい。

let binding 用。

```text
my y = f x
rest
```

lowering 目標。

```text
current:
  EffectfulApply f x -> post

post(result):
  bind result to pattern y
  lower rest
```

expr statement 用。

```text
f x
rest
```

lowering 目標。

```text
current:
  EffectfulApply f x -> post

post(_ignored):
  lower rest
```

tail expression 用。

```text
f x
```

lowering 目標。

```text
current:
  EffectfulApply f x -> post

post(result):
  Return result
```

tail でも frame を作るかは targeted 範囲内ならあり。
ただし、広範囲に tail apply まで effectful 化すると Cranelift 側へ波及しやすいから、まずは `fold_impl` callback path に限るのが無難。

---

## Step 6: `EffectfulApply` eval 側の既存挙動を確認する

`cps_ir.rs` には `EffectfulApply` が定義済み。意味は `EffectfulCall` と同じで、call site の post-call computation を return frame に捕まえるもの。

`cps_eval.rs` 側で確認する点。

```text
EffectfulApply の push 前に pre_push_count = return_frames.len() を取る
CpsReturnFrame.owner_initial_frame_count = current initial_frame_count
callee/resumed eval に initial_frame_count = pre_push_count を渡す
```

これは write14 report の強調点。
`owner_initial_frame_count` と `callee.initial_frame_count` を混同しない。

```text
frame.owner_initial_frame_count = 現在の eval の initial_frame_count
callee.initial_frame_count      = push 前の return_frames.len()
```

前者は「この frame の owner eval を再開したときに復元する threshold」。
後者は「callee にとって、どこからが own frame か」。

---

## Step 7: `EffectfulCall` も候補に入れる

trace の結果、欠けている local rest が `ApplyClosure` ではなく `DirectCall` 由来なら、`EffectfulApply` だけでは足りない。

特に疑う場所。

```yulang
fold_impl(right, fold_impl left z f, f)
```

ここで inner `fold_impl left z f` が sync `DirectCall` stmt なら、その後の `fold_impl right ...` が frame 化されていない可能性がある。

その場合は、同じ考え方で targeted `EffectfulCall` を使う。

```text
current:
  EffectfulCall fold_impl(left, z, f) -> post_left

post_left(z1):
  lower fold_impl(right, z1, f)
```

この修正は `std::undet.once` の探索で「false を選んだら次の leaf へ進む」ために必要になりうる。

---

## Step 8: `EffectfulForce` は最後に確認する

write14 report では `EffectfulForce` もすでに扱われている。
ただし今回の本命は `fold_impl` の local rest なので、先に `Apply` / `DirectCall` を見る。

`EffectfulForce` を疑う条件。

```text
- callback apply / fold call を effectful 化しても branch Perform 時の frames が足りない
- trace 上、Thunk body に入る直前に return_frames が消えている
- ForceThunk stmt が handler scope / maybe effectful thunk に対して sync 実行されている
```

この場合だけ、targeted `EffectfulForce` の lowering 範囲を広げる。
最初から force 全体を effectful 化しないほうがいい。

---

# 実装上の禁止事項

別 LLM にはここを強めに伝えるとよさそう。

```text
1. write14 の initial_frame_count refactor を大きく書き換えない。
   これはすでに local callback test を通している中核変更。

2. sync call の parent frame inheritance を戻さない。
   sync call は parent frames を渡すが、initial_frame_count = parent_len にして consume しない。

3. Resume / ResumeWithHandler / ApplyClosure(Resumption) を sync call と同じ扱いにしない。
   resumption replay は captured frames を consume してよいので initial_frame_count = 0。

4. active_handler.is_some() だけで effectful lowering を判断しない。
   std::list::fold_impl は定義時に handler scope がなくても、実行時には handler stack の下で動く。

5. Stmt::Expr 全体をいきなり effectful split しない。
   write13 report で Cranelift regression を起こすことが分かっている。

6. ApplyClosure 全体を一律 EffectfulApply 化しない。
   まず fold_impl / undet.each 経路に絞る。

7. Cranelift を同時に直そうとしない。
   まず CPS eval の semantics を VM と一致させる。
```

---

# 期待するテスト追加・変更

## 1. 既存の local callback test は維持

`debugs_local_choice_callback_rest_eval` は write14 の成功条件なので、落とさない。

```bash
cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture
```

期待値。

```text
cps: 2
vm: 2
```

## 2. fold に近い local minimal test を追加

`std::undet` だけだと標準ライブラリの層が厚いから、fold-like な小テストを足すと原因が見やすい。

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

期待値。

```text
2
```

この test が落ちるなら、`std::list::fold_impl` 固有ではなく、**callback apply + local rest** 一般の問題。

## 3. `std::undet.once` の Layer 1 を通す

最終的に見るのはこれ。

```bash
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

まずは Layer 1、つまり CPS eval と VM の一致だけを合格条件にする。

```text
CPS eval: 2
VM:       2
```

Layer 2 / Layer 3、つまり CPS repr eval / Cranelift が `UnsupportedTerminator` や未実装 runtime helper で落ちるなら、その時点で別タスクに分ける。write14 report でも「その時点で cps_repr / Cranelift の扱いも決める」となっているから、ここで無理に全部まとめない。

---

# 成功条件

今回の write15 相当での成功条件はこう。

```text
必須:
- cargo test -p yulang-native が regression なし
- debugs_local_choice_callback_rest_eval が継続 pass
- fold-like local minimal test が pass
- debugs_std_undet_once_skip_eval_layers の CPS eval が VM と一致して 2

望ましい:
- trace で branch Perform 時の return_frames に fold local rest が入っている
- global ApplyClosure / Stmt::Expr split なし
- 既存 _through_cps_repr_cranelift テストの regression なし

次タスク送りでよい:
- CPS repr eval の Effectful* 対応
- Cranelift の Effectful* 対応
- 名前ベース targeted 判定を effect row based 判定へ一般化
```

---

# そのまま別 LLM に渡す指示文

```text
目的:
notes/todo/native-undet-write14-report.md の続きとして、debugs_std_undet_once_skip_eval_layers が cps:0 vs vm:2 になる原因を直す。
write14 の initial_frame_count refactor は成功しているので、cps_eval.rs の中核設計は原則として触らない。
次に直すべきなのは std::list::fold_impl 内の callback apply / local rest が resumption に入らない問題。

現状:
- CpsTerminator には EffectfulCall / EffectfulApply / EffectfulForce が存在する。
- write14 で sync DirectCall / ApplyClosure / ForceThunk は parent return_frames を callee に渡し、initial_frame_count = parent_len にするようになった。
- これで outer frames は Perform に見えるようになった。
- ただし sync call は call site 自身の post-call continuation を push しない。
- std::undet.each は xs.fold の callback 内で branch() し、true なら sub::return x、false なら次要素へ進む。
- std::list::fold_impl は leaf で f z x、node で fold_impl(right, fold_impl left z f, f) を使う。
- したがって fold_impl 内の local rest を return frame として push する targeted lowering が必要。

作業順:
1. debugs_std_undet_once_skip_eval_layers に CPS dump と return_frames trace を足す。
   branch() が fold callback 内で Perform した瞬間の return_frames.len と中身を確認する。
2. outer frames が入っているが fold local rest がないことを確認する。
   outer frames もないなら write14 の sync inheritance を先に確認する。
3. cps_lower.rs で、std::list::fold_impl 周辺の callback apply を targeted EffectfulApply 化する。
   leaf の f z x は curried apply なので、f z と (f z) x のどちらが sync ApplyClosure のままか dump で見る。
   安全寄りなら targeted 範囲内で両方 EffectfulApply にしてよい。
4. node branch の fold_impl(right, fold_impl left z f, f) で、inner fold_impl left z f の後続 rest が欠けているなら targeted EffectfulCall 化する。
5. std::undet.each の xs.fold ...; reject() が Stmt::Expr sync call のままで reject skip rest が欠けているなら、その箇所だけ targeted expr statement split する。
   Stmt::Expr 全体を global split しない。
6. 判定条件は active_handler.is_some() だけにしない。
   fold_impl は lowering 時点で handler scope 外だが、実行時には once/sub handler の下で動く。
   callee_type_may_perform、Unknown/Thunk return、callee が function parameter/callback 由来、std::list::fold_impl known path を使って conservative に判定する。
7. cps_eval.rs の EffectfulApply / EffectfulCall / EffectfulForce では、pre_push_count と owner_initial_frame_count を混同しない。
   frame.owner_initial_frame_count = current initial_frame_count。
   callee.initial_frame_count = pre_push_count。
8. Resume / ResumeWithHandler / ApplyClosure(Resumption) は initial_frame_count = 0 のままにする。
   resumption replay は captured frames を consume してよい。
9. まず CPS eval を VM と一致させる。
   CPS repr eval / Cranelift は Layer 1 が通った後の別段階にする。
10. テスト:
   - cargo test -p yulang-native
   - cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored --nocapture
   - fold-like local minimal test
   - cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture

禁止:
- ApplyClosure 全体を一律 EffectfulApply 化しない。
- Stmt::Expr 全体を一律 split しない。
- write14 の sync call inheritance を戻さない。
- initial_frame_count を削除しない。
- Cranelift 対応を同時に広げすぎない。
```

---

私の判断では、今回の実装の本丸は **「inherit で見える outer frames」と「call site が新しく作る local rest frame」を混同しないこと**だねぇ。
write14 は前者を直した。次は後者、つまり `fold_impl` の callback/local continuation を frame 化する段階だよ〜。
