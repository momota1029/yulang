おお、write27-b はちゃんと一段進んでるねぇ。`UnsupportedTerminator` / `todo!` から **JIT が compile + run まで行って `I64Mismatch(vm:2, cps:0)`** になったのは大きい。Layer 3 が「未実装」から「意味論差分」へ進んだ、かなり良い状態だよ〜。

ただ、report を読んで一つ強く気になった点がある。

> `switch_eval_context_for_callee` が `initial = return_frame_len(push 後)` にしているなら、そこはまず直すべきだと思う。

Layer 1/2 の意味論では、EffectfulCall / EffectfulForce / EffectfulApply の callee に渡す `initial_frame_count` は **push 前の frame len** だよ〜。push 後 len を渡すと、F_post が callee の own frame ではなく inherited 扱いになって、`yulang_cps_return_i64` が frame を consume しない危険がある。

---

# まず最優先で見る点

## `switch_eval_context_for_callee` の initial

write27-b report では、Effectful* codegen の流れがこう書かれている。

```text
push_return_frame_for_resume で F_post push
switch_eval_context_for_callee で fresh eval id + initial = return_frame_len (push 直後)
```

でも Layer 1/2 で正しかった形はこれ。

```text
pre_push_count = return_frames.len()
push F_post
callee.initial_frame_count = pre_push_count
```

つまり Cranelift 側もこうするべき。

```rust
let pre_push_count =
    call_i64_helper(module_backend, builder, "yulang_cps_return_frame_len_i64", &[])?;

push_return_frame_for_resume(...)?;

let fresh_eval =
    call_i64_helper(module_backend, builder, "yulang_cps_fresh_eval_id_i64", &[])?;

call_i64_helper(
    module_backend,
    builder,
    "yulang_cps_set_eval_context_i64",
    &[fresh_eval, pre_push_count],
)?;
```

`switch_eval_context_for_callee` が内部で push 後の len を読む設計なら、引数に `pre_push_count` を渡す形へ変えるのが良い。

```rust
fn switch_eval_context_for_callee(
    module_backend: &mut M,
    builder: &mut FunctionBuilder<'_>,
    initial_frame_count: ir::Value, // pre_push_count
) -> Result<(), ...>
```

## なぜ大事か

`yulang_cps_return_i64` は report どおり:

```text
if frame_len <= initial { return value; }
else if thunk && immediate_force { pre-force }
else continue_return_frame
```

という意味だねぇ。

もし push 後 len を initial にすると:

```text
frame_len = pre + 1
initial   = pre + 1
```

なので `frame_len <= initial` になって、F_post を consume しない。
すると EffectfulCall が「post continuation を return frame にする」という肝を失う。

今の `cps:0` は Perform がまだ old abort だから、そこが主因に見える。でもこの initial bug が残ったまま Perform を ScopeReturn 化しても、次の frontier でまた詰まりそうだよ〜。

---

# write27-c の推奨順

私は write27-c をこう切るのがいいと思う。

```text
c0. Effectful* callee initial を pre_push_count に修正
c1. trace helper を入れて F_post consume を確認
c2. Handler frame full fields を入れる
c3. Perform を ScopeReturn 化
c4. route_scope_return_i64(fallback) を実装
c5. sync internal call の eval context save/restore + route
c6. EffectfulApply(Resumption) helper
```

`c0` は b の hotfix に近い。まずそこを直すのが安全。

---

# c1: JIT runtime trace を入れる

Layer 3 は Rust helper の中で状態が動くから、trace がないと見えづらい。`YULANG_CPS_JIT_TRACE=1` みたいな env guard で、次を出すと良いよ〜。

```text
[JIT-CPS] push_return_frame:
  len_before
  len_after
  cont
  env_len
  owner_eval
  owner_initial
  immediate_force

[JIT-CPS] set_eval_context:
  eval
  initial

[JIT-CPS] return_i64:
  value
  frame_len
  initial
  action=noop | pre_force | continue

[JIT-CPS] continue_return_frame:
  owner_eval
  owner_initial
  restored_handlers_len
  restored_guards_len

[JIT-CPS] scope_return_set:
  prompt
  target
  value

[JIT-CPS] route_scope_return:
  prompt
  target
  current_eval
  initial
  frame_len
  action=current_handler | frame_walk | propagate

[JIT-CPS] perform_select:
  effect
  prompt
  install_eval
  synthetic?
```

まず見るべき期待値:

```text
EffectfulCall each:
  push_return_frame len_before=N len_after=N+1
  set_eval_context fresh, initial=N

callee Return:
  return_i64 frame_len=N+1 initial=N action=continue/pre_force
```

ここが `action=noop` なら、まだ initial が間違ってる。

---

# c2: Handler frame full fields

write27-b ではまだ Perform が old abort、handler frame extension も未完了。write27-c では `NativeCpsI64HandlerFrame` に Layer 1/2 相当の情報が必要だねぇ。

```rust
#[derive(Clone)]
struct NativeCpsI64HandlerFrame {
    handler: CpsHandlerId,

    // dynamic prompt identity
    prompt: u64,
    install_eval_id: u64,
    inherited: bool,

    // handler arm env / guard
    handlers: ...
    guards: Vec<i64>,

    // ScopeReturn escape
    escape_continuation: usize,
    escape_env: Box<[i64]>,
    return_frame_threshold: usize,

    // optional/debug
    synthetic: bool,
}
```

`escape_continuation` は `extern "C" fn(*const i64, i64) -> i64` として transmute して呼ぶ前提。

## install helper は `_full` を新設

既存 `yulang_cps_install_handler_i64(handler)` は残して、新 helper を追加するのが安全。

```rust
extern "C" fn yulang_cps_install_handler_full_i64(
    handler: i64,
    escape_continuation: i64,
    escape_env_len: i64,
    return_frame_threshold: i64,
    install_eval_id: i64,
    inherited: i64,
    // env slots...
) -> i64
```

ただし env len は N=0..4 family にする方が既存 style と合う。

```text
yulang_cps_install_handler_full_i64_0(...)
...
yulang_cps_install_handler_full_i64_4(...)
```

`push_return_frame_i64_N` と同じ考えだねぇ。

## InstallHandler stmt codegen

InstallHandler stmt で:

```text
prompt = fresh_prompt helper
escape_cont = func_addr(escape continuation)
escape_env = escape continuation env slots
threshold = return_frame_len()
install_eval = current_eval_id()
inherited = false
install_handler_full(...)
```

ここまで入ると、Perform が selected handler の prompt/install_eval/escape を持てる。

---

# c3: Perform を ScopeReturn 化

現状は old abort helper が残っていて、それが `cps:0` の主因と report が見ている。ここは同意だよ〜。

Perform codegen は、handler arm natural return をこう扱う。

```text
handler arm result = value

if selected frame is synthetic:
    return value  // legacy passthrough
else:
    scope_return(prompt=selected.prompt, target=selected.escape, value)
    route_scope_return(value)
    return routed
```

ここで `target` は JIT では `CpsContinuationId` ではなく、escape continuation pointer 的に扱うのが自然。ただ、route は matched handler frame の escape を使えるから、slot の target は主に sentinel / debug 用でも良い。

おすすめは:

```text
target = selected.escape_continuation as i64
```

`EXIT_RWH_TARGET` は `-1` のまま。

## selected frame metadata helper

Perform codegen から selected frame の prompt/install_eval/synthetic/escape を取りたいので、helper を増やすのがよさそう。

```rust
yulang_cps_selected_handler_prompt_i64() -> i64
yulang_cps_selected_handler_install_eval_i64() -> i64
yulang_cps_selected_handler_synthetic_i64() -> i64
yulang_cps_selected_handler_escape_i64() -> i64
```

あるいはもっとまとめて:

```rust
yulang_cps_scope_return_from_selected_handler_i64(value) -> i64
```

これが一番楽かも。

```rust
extern "C" fn yulang_cps_scope_return_from_selected_handler_i64(value: i64) -> i64 {
    if selected handler is active real frame {
        yulang_cps_scope_return_i64(frame.prompt, frame.escape_continuation as i64, value)
    }
    value
}
```

Cranelift 側は handler arm call 後にこれを呼ぶだけ。

---

# c4: `route_scope_return_i64(fallback)` 設計

report の質問 1 への答え。

私は `fallback_value` を引数に取る形がいいと思う。

```rust
extern "C" fn yulang_cps_route_scope_return_i64(fallback_value: i64) -> i64
```

挙動:

```text
if no active scope_return:
    return fallback_value

if matched:
    clear scope_return
    call escape / continue frame
    return result

if no match:
    leave scope_return active
    return fallback_value
```

`no match` の時に slot を active のまま残すのが大事。そうすれば caller の internal-call 後 check がさらに route できる。

codegen 側は:

```text
if scope_return_active:
    routed = route_scope_return(result)
    return routed
```

で良い。

## current handler stack → frame walk の順

helper 内は Layer 1/2 と同じ。

```text
1. current handler stack reverse search
   prompt == sr.prompt
   install_eval_id == current_eval_id

2. no match なら return_frames[current_initial..] reverse walk
   handler.prompt == sr.prompt
   handler.install_eval_id == frame.owner_eval_id
```

match 時:

```text
- handler stack truncate
- return frame stack truncate at threshold
- restore context
- clear sr
- call escape_continuation(escape_env, sr.value)
```

## 注意: threshold の扱い

`return_frame_threshold` は install 時点の `return_frame_len()`。route 時に:

```rust
if frames.len() > threshold {
    frames.truncate(threshold);
}
```

で良いはず。JIT helper 側では stack が thread-local なので、truncate は自然にできる。

---

# c5: sync internal call の eval context save/restore

write27-b report では、Effectful* codegen は入ったけど、sync internal call の context save/restore は write27-c 残り。ここは必須だよ〜。

`DirectCall / ApplyClosure / ForceThunk / Resume / ResumeWithHandler` の後:

```text
saved_eval = current_eval_id()
saved_initial = current_initial()
callee_initial = return_frame_len()
callee_eval = fresh_eval_id()
set_eval_context(callee_eval, callee_initial)

result = call...

set_eval_context(saved_eval, saved_initial)

if scope_return_active():
    routed = route_scope_return(result)
    return routed

continue
```

重要なのは **route 前に caller context を復元する** こと。sync call は caller eval が alive だから、caller の eval_id / initial で dispatch する必要がある。

EffectfulCall は tail-call 的なので caller context restore は不要寄りだけど、sync call は必ず restore してねぇ。

---

# c6: EffectfulApply Resumption helper

これは write27-c の本命後半だねぇ。

Cranelift IR で anchor merge / combined frames を組むのは避ける。Rust helper が良い。

```rust
extern "C" fn yulang_cps_effectful_apply_resumption_i64_N(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    owner_initial: i64,
    owner_eval: i64,
    immediately_forces: i64,
    env_slots...
) -> i64
```

helper 内:

```text
1. F_post を作る
2. current return frames + F_post = new_frames
3. resumption.handled_anchor で anchor merge
4. adjusted_res_frames = merge_extras_into_frames(resumption.return_frames, current_handlers, anchor)
5. combined_frames = new_frames + adjusted_res_frames
6. resumed_handlers = merge_resumption_handlers(resumption.handlers, current_handlers, anchor)
7. set return frame stack = combined_frames
8. set handler stack = resumed_handlers
9. set guard stack = resumption.guards
10. set eval_context(fresh, 0)
11. call resumption.target(resumption.env, arg)
```

この helper が入れば、write24/25 で確立した anchor merge + frame walk の JIT 版が乗る。

---

# ひとつ気になる点: EffectfulCall result をそのまま return する設計

write27-b では EffectfulCall/Force/Apply が:

```text
target を呼ぶ
result を return
```

になっている。これは `target` 側の `yulang_cps_return_i64` が F_post を consume するなら正しい。

ただし、そのためには繰り返すけど:

```text
callee initial = pre_push_count
```

が必須。push 後 len だと consume されない。

だから write27-c の最初の test はこれを見てほしい。

```text
EffectfulCall each:
  push len_before=0 len_after=1
  set_eval_context initial=0
  callee Return:
    return_i64 frame_len=1 initial=0 action=continue/pre_force
```

もし initial=1 なら即修正。

---

# Aborted / abort helper の扱い

report の質問 3 への答え。

まだ消さない方がいい。
write27-c で Perform を ScopeReturn 化しても、legacy fallback / old tests / transition path で使われる可能性がある。

削除はこの後。

```text
1. Layer 3 OK
2. grep yulang_cps_abort
3. grep Aborted
4. 使われていないなら削除
```

今消すと、old abort 由来か new ScopeReturn 由来かの差分が見えなくなる。

---

# write27-c の成功 frontier

最終的に見たい trace はこれ。

```text
EffectfulCall each:
  push F_work_post
  callee initial=pre_push

Return fold_impl Thunk:
  return_i64 action=pre_force
  retained F_each_post

Perform branch:
  resumption frames include F_each_post + F_work_post

EffectfulApply Resumption:
  anchor merge gives [outer, inner, H_sub]

Perform sub::return:
  scope_return_set prompt=H_sub
  route_scope_return:
    frame walk match F_each_post
    handlers_before=[outer, inner, H_sub]
    handlers_after=[outer, inner]
    call each escape cont2

continue_return_frame:
  pop F_work_post
  restored handlers=[outer, inner]

Perform reject:
  selected handler prompt=inner once

final:
  cps_cranelift=2
```

今は `cps_cranelift=0` だけど、ここまで来れば `2` に届くはず。

---

# 別LLMへ渡す短い指示文

```text
write27-c の最初に、Effectful* callee context の initial_frame_count を確認する。
push 後 frame_len ではなく、push 前 pre_push_count を callee initial にする。
これが違うと F_post が consume されない。

次に Handler frame full fields を入れる:
  prompt
  install_eval_id
  inherited
  escape_continuation
  escape_env
  return_frame_threshold
  guard snapshot
  handler env

既存 install_handler_i64 は残し、新 helper install_handler_full_i64_N を作る。
InstallHandler stmt codegen は full helper を使う。

Perform codegen は old abort ではなく ScopeReturn を使う。
selected real handler の natural return を:
  scope_return(prompt, escape_cont, value)
に変換し、route_scope_return(fallback_value) を呼ぶ。
synthetic handler は raw value を返す。

route_scope_return_i64(fallback) を Rust helper で実装する。
match したら clear slot + call escape。
match しなければ slot active のまま fallback を返す。

sync DirectCall / ApplyClosure / ForceThunk / Resume / RWH は
callee call 前に eval context を fresh にし、
call 後に caller context を restore してから route_scope_return を呼ぶ。

EffectfulApply Resumption は専用 Rust helper に寄せる。
anchor merge + combined_frames は Cranelift IR ではなく Rust 側で計算する。
```

---

# 質問への答えまとめ

## 1. route_scope_return の戻り値設計

`route_scope_return_i64(fallback_value)` が良い。
match すれば escape result、match しなければ fallback を返しつつ slot active のまま。caller 側がさらに route できる。

## 2. install_handler helper

既存 `yulang_cps_install_handler_i64` は残して、新 `install_handler_full_i64_N` を作るのが安全。write27-c の新 codegen だけ full helper に切り替える。

## 3. abort helper 削除

まだ削除しない。Layer 3 が通ってから grep して消す。

---

# 最後に

write27-b の到達はかなり良いよ〜。`UnsupportedTerminator` から `I64Mismatch` は、実装が走る場所まで来た証拠。次の最大リスクは、Perform ScopeReturn 化より前に **Effectful* の initial が push 後 len になっていること**。ここだけは最初に潰しておくと、write27-c の残りがずっと読みやすくなると思う。
