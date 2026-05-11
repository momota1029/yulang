やったねぇ、Layer 2 到達かなり大きい。write25 が「CPS eval の意味論が通った」だったなら、write26 は「CPS repr interpreter も同じ意味論に乗った」だねぇ。`ScopeReturn / eval_id / walk routing / pre-force / Return inherited preservation` を repr interpreter 側へ移植して、Layer 1 + Layer 2 が OK、残りは Layer 3 の `cps_repr_cranelift` という整理で合っていると思うよ〜。

次の write27 は、**単に `EffectfulCall/Apply/Force` の todo を消すだけでは足りない**。Cranelift 側にも、write25/26 で確立した return-frame semantics を載せる必要がある。既存の Cranelift file には resumption / env / handler stack / abort / thunk / list / guard 系の helper symbol が既に大量に登録されているから、その上に拡張するのが現実的だねぇ。

---

## 結論

write27 の本線はこれ。

```text
cps_repr_cranelift の old abort-slot semantics を、
ScopeReturn + eval_id + return-frame stack semantics へ拡張する。

その上で EffectfulCall / EffectfulApply / EffectfulForce を codegen する。
```

やってはいけないのはこれ。

```text
EffectfulCall target args resume
  → call target
  → call resume(result)
```

この sync shim は、write25 の成功条件を壊すよ〜。`F_work_post` や `F_each_post` が resumption の captured chain に入らない。Layer 1/2 で何週間も追っていた同じバグに戻る。

---

# write27 の推奨実装順

## Step 0: Cranelift の TODO を消す前に trace frontier を固定

まず現状の本命 test を走らせる。

```bash
RUST_BACKTRACE=1 \
YULANG_CPS_TRACE_FRAMES=1 \
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture
```

期待:

```text
Layer 1 (CPS eval): OK
Layer 2 (CPS repr eval): OK
Layer 3: Effectful{Call,Apply,Force} todo panic
```

ここを baseline にしてから触る。

---

## Step 1: native scalar runtime に ScopeReturn slot を追加

今の Cranelift runtime には `yulang_cps_abort_i64` / `yulang_cps_abort_active_i64` / `yulang_cps_abort_value_i64` / `yulang_cps_clear_abort_i64` がある。これは古い `Aborted(value)` 相当だと思う。write26 で repr interpreter は `ScopeReturn { prompt, target, value }` へ移ったので、Cranelift 側も value だけでは足りない。

追加する runtime state:

```rust
struct NativeScopeReturnI64 {
    active: bool,
    prompt: u64,
    target: usize,
    value: i64,
}
```

helper 案:

```rust
extern "C" fn yulang_cps_scope_return_i64(prompt: i64, target: i64, value: i64)
extern "C" fn yulang_cps_scope_return_active_i64() -> i64
extern "C" fn yulang_cps_scope_return_prompt_i64() -> i64
extern "C" fn yulang_cps_scope_return_target_i64() -> i64
extern "C" fn yulang_cps_scope_return_value_i64() -> i64
extern "C" fn yulang_cps_clear_scope_return_i64()
```

既存 abort helper はすぐ消さなくていい。まずは bridge する。

```text
old abort helper:
  value-only abort

new scope-return helper:
  prompt + target + value
```

`Aborted` variant も同じ。write26 で legacy として残したのは正しい判断。Layer 3 が通るまで消さない方がいいよ〜。

---

## Step 2: native return-frame stack を追加する

Layer 1/2 の鍵は return frame。Cranelift 側にも必要。

JIT continuation signature は既に概念上こういう形だと思う。

```text
continuation(env, arg...) -> i64
```

だから return frame には「後で呼ぶ continuation pointer」と「env pointer」を保存できる。

runtime struct 案:

```rust
#[derive(Clone)]
struct NativeReturnFrameI64 {
    continuation: extern "C" fn(i64, i64) -> i64,
    env: i64,

    handler_stack_snapshot: NativeHandlerStackSnapshot,
    guard_stack_snapshot: NativeGuardStackSnapshot,

    owner_initial_frame_count: usize,
    owner_eval_id: u64,
}
```

multi-arg continuation があるなら、今回の scalar subset では `resume` continuation の param はだいたい 1 つのはず。既存の continuation function signature が params 数に応じて違うなら、arity ごとの helper が必要。

helper 案:

```rust
extern "C" fn yulang_cps_return_frame_len_i64() -> i64
extern "C" fn yulang_cps_push_return_frame_i64(
    continuation_ptr: i64,
    env: i64,
    owner_initial_frame_count: i64,
    owner_eval_id: i64,
) -> i64

extern "C" fn yulang_cps_continue_return_frames_i64(value: i64) -> i64
```

ただし、`continue_return_frames` は handler stack / guard stack / eval context を復元して continuation を呼ぶ必要がある。ここは Rust helper 側でやるのが一番楽だよ〜。

---

## Step 3: eval context を thread-local に置く

Layer 1/2 では `current_eval_id` と `initial_frame_count` を関数引数で thread していた。Cranelift の continuation function signature にこれ以上 hidden params を増やすより、scalar runtime の thread-local context に置く方が実装しやすいと思う。

runtime state:

```rust
struct NativeEvalContextI64 {
    current_eval_id: u64,
    initial_frame_count: usize,
}
```

helper:

```rust
extern "C" fn yulang_cps_fresh_eval_id_i64() -> i64
extern "C" fn yulang_cps_current_eval_id_i64() -> i64
extern "C" fn yulang_cps_current_initial_frame_count_i64() -> i64
extern "C" fn yulang_cps_set_eval_context_i64(eval_id: i64, initial: i64)
```

`continue_return_frames_i64` が frame を pop するとき:

```text
set current_eval_id = frame.owner_eval_id
set initial_frame_count = frame.owner_initial_frame_count
restore handler stack snapshot
restore guard stack snapshot
call frame.continuation(frame.env, value)
```

これで interpreter の `resume_continuation(... current_eval_id=frame.owner_eval_id)` と対応する。

---

## Step 4: handler frame に prompt / install_eval_id / escape を載せる

Cranelift handler stack が既にあるなら、そこに fields を足す。

必要:

```rust
struct NativeHandlerFrameI64 {
    prompt: u64,
    handler_id: usize,

    // handler arm entry に必要なもの
    arm_entry: extern "C" fn(...)->i64,
    env: i64,

    // ScopeReturn dispatch 用
    escape: extern "C" fn(i64, i64)->i64,
    escape_env: i64,
    return_frame_threshold: usize,
    install_eval_id: u64,

    inherited: bool,

    // guard snapshot
    guard_stack_snapshot: ...
}
```

Layer 1/2 の `escape_owner_function` は Cranelift では function string ではなく、「escape continuation pointer + env」で持つ方が自然。owner check 相当は、`install_eval_id` と「この escape pointer がこの frame の owner continuation」として runtime が保証する。

ただし安全策として、最初は Cranelift runtime で owner check を省くより、**handler frame に owner code id を持たせる**のもあり。

```rust
owner_function_id: u64
```

でも JIT prototype なら code pointer で十分かもしれない。

---

## Step 5: `Perform` codegen を ScopeReturn ベースに変える

今の Cranelift Perform はおそらく:

```text
select handler
make resumption
call handler arm
if handler arm returns abort -> return_if_abort_active
```

みたいな構造だと思う。

write27 では:

1. `select_handler` で frame を選ぶ
2. selected frame の prompt/install_eval_id を anchor として resumption に保存
3. resume continuation + env + return frame stack snapshot から resumption を作る
4. handler arm を呼ぶ
5. handler arm の natural return を `ScopeReturn(prompt, escape, value)` として runtime slot に入れる
6. `route_scope_return` を呼ぶ

ただし synthetic fallback frame の場合は write26 と同じく raw value を返す。write26 report でも synthetic は `install_eval_id != REPR_SYNTHETIC_EVAL_ID` のチェックを入れている。

---

## Step 6: `return_if_scope_return_active` を作る

今の `return_if_abort_active` 相当を ScopeReturn 版へ更新する。

helper / codegen どちらでもよいけど、まずは helper 推奨。

```rust
extern "C" fn yulang_cps_route_scope_return_i64() -> i64
```

この helper がやること:

```text
if no active ScopeReturn:
  return sentinel? or current value unchanged

let sr = current scope_return

1. current handler stack で prompt/install_eval_id == current_eval_id を探す
2. 見つからなければ return frame stack[initial_frame_count..] を reverse walk
3. match したら:
   - handler より内側の handlers を捨てる
   - rest_frames を threshold で truncate
   - clear scope_return
   - set eval context to matched frame owner_eval_id
   - restore handler/guard snapshots after truncate
   - call escape continuation with sr.value
4. 見つからなければ:
   - caller に scope_return active のまま返す
```

Cranelift 側では internal call の後:

```text
call target/helper
if scope_return_active:
  result = route_scope_return()
  return result
```

これを `DirectCall / ApplyClosure / ForceThunk / Resume / Effectful*` の後に挟む。

---

## Step 7: `EffectfulCall` codegen

擬似 codegen:

```text
pre_push_count = return_frame_len()

resume_env = make_env_for_continuation(resume)
resume_fn  = continuation_func_ref(function, resume)

push_return_frame(
  resume_fn,
  resume_env,
  owner_initial_frame_count = current_initial_frame_count(),
  owner_eval_id = current_eval_id()
)

set callee initial_frame_count = pre_push_count
set callee eval_id = fresh_eval_id()

result = call target(args)

if scope_return_active:
  routed = route_scope_return()
  return routed

// 通常 return は target 側の Return が frame consume する設計なら、
// ここに来ないのが理想。
// ただし実装初期は保険で:
return continue_return_frames(result)
```

ここは設計上の分岐がある。

### 推奨

`Return` codegen 側で:

```text
if return_frame_len() > current_initial_frame_count():
  return continue_return_frames(value)
else:
  return value
```

を実装する。

そうすると `EffectfulCall` の callee が plain return した時、callee 側の Return が自動で `F_post` を pop して resume cont へ進む。Layer 1/2 と同じ。

だから `EffectfulCall` terminator 自体は target を呼んで、その result を返せばよい。target の内部 Return が frame を consume するからねぇ。

---

## Step 8: `EffectfulForce` codegen

`EffectfulForce` も同じ。

```text
pre_push_count = return_frame_len()
push return frame for resume
set thunk-body initial = pre_push_count
call yulang_cps_force_thunk_i64(thunk)
if scope_return_active: route
return result
```

ただし write26 で発見された通り、ForceThunk は nested Thunk loop が必要だった。

Cranelift helper `yulang_cps_force_thunk_i64` が既に trampoline 的に nested thunk を force できるなら OK。そうでないなら helper 側を loop 化する。

---

## Step 9: `EffectfulApply` codegen

### Closure

```text
pre_push_count = return_frame_len()
push return frame for resume
call yulang_cps_apply_closure_i64(closure, arg)
if scope_return_active: route
return result
```

### Resumption

ここが一番難しい。Layer 1/2 と同じ:

```text
new_frames = current return_frames + [F_post]
adjusted_res_frames = merge_extras_into_frames(resumption.return_frames, current_handler_stack, resumption.handled_anchor)
combined_frames = new_frames + adjusted_res_frames
resumed_handlers = merge_resumption_handlers(resumption.handlers, current_handler_stack, anchor)
resume with initial=0
```

これを全部 Cranelift IR でやるのはきつい。Rust helper に寄せるのがいい。

helper 案:

```rust
extern "C" fn yulang_cps_effectful_apply_resumption_i64(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    post_env: i64,
    owner_initial: i64,
    owner_eval: i64,
) -> i64
```

helper 側で:

```text
- F_post を作る
- anchor merge
- combined_frames を作る
- eval context initial=0
- call resumption target
```

既存 `yulang_cps_resume_i64` と `yulang_cps_resume_with_handler_i64` があるから、そこを拡張して post frame を受け取れる variant を作るのが自然。

---

# write27 を小さく切る案

Layer 3 は大きい。なので、こう切ると安全。

## write27-a: runtime state と Return frame consume だけ

実装:

```text
- ScopeReturn slot
- eval context
- return frame stack
- Return terminator が return frame を consume
- DirectCall / ForceThunk 後の scope-return route
```

まだ Effectful* TODO は残してもいい。まず既存 tests regression なしを見る。

## write27-b: EffectfulCall + EffectfulForce

`std::undet.each` の Step 4 narrow でまず必要なのは EffectfulCall と ForceThunk 周辺。EffectfulApply は once branch でも必要になるかもしれないが、順番として:

```text
EffectfulCall
EffectfulForce
EffectfulApply Closure
EffectfulApply Resumption
```

がよさそう。

## write27-c: EffectfulApply Resumption + anchor merge

ここで本命 test の Layer 3 を狙う。

---

# Aborted variant の扱い

今は消さない方がいい。

理由:

```text
- cps_repr interpreter では legacy bridge として残した
- cps_repr_cranelift には abort helper がまだある
- Layer 3 migration 中に消すと、古い effect tests の failure reason が見えにくくなる
```

write27 の最後で Layer 3 が通ってから:

```text
Aborted 使用箇所を grep
abort helper 使用箇所を grep
完全に ScopeReturn へ寄せられたら削除
```

この順が安全。

---

# ForceThunk nested loop について

これは regression test を足した方がいい。write26 で「決定的な fix」と書かれているし、cps_eval にはあったが cps_repr に欠けていた差分だねぇ。

小さい test 方針:

```text
function returns Thunk(Thunk(value))
ForceThunk once from caller context
期待: inner value まで force
```

source で作れるなら source test、難しければ CPS IR / repr eval unit でもいい。

将来の抽象化はありだけど、今は shared trait 化しない方がいい。`cps_eval`, `cps_repr`, `cranelift` は runtime value と実行方式が違いすぎる。まず regression で差分を固定するのが現実的だよ〜。

---

# `りなに渡す質問` への答え

## Q1. Layer 3 codegen 方針

素直な「push frame は値保存命令列、tail-call は jump」だけだと足りない可能性が高い。

Cranelift continuation は関数化されているので、複雑な return-frame / handler-stack / eval-id 操作は Rust helper に寄せるのがいい。

おすすめ:

```text
Cranelift IR:
  - env を作る
  - continuation function pointer を渡す
  - runtime helper を呼ぶ

Rust helper:
  - return frame stack
  - handler stack snapshot
  - guard stack snapshot
  - eval context
  - ScopeReturn routing
  - resumption frame merge
```

つまり codegen は「状態機械を組む」より「必要な runtime helper を呼ぶ」寄り。

## Q2. Aborted 削除

Layer 3 完了まで削除しない。
完了後、abort helper と Aborted variant の使用がゼロになったら削除でよさそう。

## Q3. eval trait 的な共有化

今はやらない方がいい。

ただし、共有化したいロジックはある。

```text
- handler merge order
- ScopeReturn walk routing の仕様
- nested ForceThunk loop の条件
- Return inherited preservation
```

コード共有より先に、**仕様コメント + regression tests** で同期する方が安全だねぇ。

---

# 別LLMへ渡す短い指示文

```text
write27 の目的:
  debugs_std_undet_once_skip_eval_layers の Layer 3
  cps_repr_cranelift JIT backend を通す。

やらないこと:
  EffectfulCall/Apply/Force を sync call + resume の shim にしない。
  write25/26 の return-frame semantics を崩さない。
  Aborted / abort helper をいきなり削除しない。

実装方針:
  Cranelift backend に ScopeReturn + eval_id + return-frame stack を載せる。
  複雑な状態操作は Rust runtime helper に寄せる。

必要な runtime state:
  - current_eval_id
  - current_initial_frame_count
  - scope_return { active, prompt, target, value }
  - return_frame_stack
  - handler frames with prompt/install_eval_id/escape/threshold
  - guard stack snapshots

EffectfulCall:
  - resume continuation の env を作る
  - return frame を push
  - callee initial_frame_count = pre_push_count
  - callee eval_id = fresh
  - target を call
  - Return terminator 側が frame consume する

EffectfulForce:
  - return frame push
  - thunk body を force
  - nested Thunk loop も helper 側で保証

EffectfulApply:
  - Closure は EffectfulForce と同型
  - Resumption は helper で anchor merge + combined_frames を作る

Return terminator:
  - if return_frame_len > current_initial_frame_count:
      if value is thunk and top_frame immediately ForceThunk:
          pre-force v2
      else:
          continue_return_frames(value)
    else:
      return value

After every internal call:
  - if scope_return_active:
      route_scope_return()
      return routed

最初の到達目標:
  1. TODO panic を消す
  2. Layer 3 mismatch / crash を trace
  3. Perform branch -> sub::return -> FrameWalkMatch -> reject inner once の
     frontier を Cranelift trace でも確認
```

---

# 最後に

write26 は「探索」じゃなくて「意味論同期」の成功だねぇ。次の Layer 3 は、コード量としては重いけど、何を実装すべきかはかなり明確になった。

私の一番強い助言はこれ。

```text
Cranelift で Effectful* を軽く sync 化しない。
必ず return frame stack と ScopeReturn routing を runtime helper として載せる。
```

これを守れば、Layer 1/2 で勝った意味論を Layer 3 へ運べると思うよ〜。
