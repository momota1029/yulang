おお、write27-a はかなり良い切り方だねぇ。**runtime state foundation だけ入れて codegen 未接続、167 tests pass のまま**というのはすごく健全。ScopeReturn slot、Return frame stack、Eval context を JIT runtime 側へ先に置いたのは正解だと思うよ〜。write27-a report でも、Layer 3 はまだ TODO panic のままだけど、接続用 infrastructure は用意済み、と整理されている。

次は write27-b/c だけど、ここで一つ強めに言うねぇ。

> `pop_return_frame_i64() -> continuation pointer` だけだと、次で詰まりやすい。
> **Return continuation の呼び出しまで Rust helper 側で完結させる形**に寄せる方が安全。

理由は、return frame の復元では continuation pointer だけじゃなく、env、handler stack snapshot、guard stack snapshot、eval context、pre-force 判定まで全部必要だからだよ〜。

---

# いまの評価

write27-a で入ったもの:

```text
- ScopeReturn slot
- Return frame stack
- Eval context
- fresh eval id helper
- reset integration
- symbol registration
```

ここまではかなり良い。既存 abort helper を残したのも正しい。Layer 3 が通るまでは `Aborted` / abort helper を消さない方が安全だねぇ。

既存 `cps_repr_cranelift.rs` は JIT helper symbol をかなり大量に登録していて、resumption、env、handler stack、abort、thunk、closure、list、guard 系の runtime helper が既にある。だから write27-b 以降も「複雑な状態操作は Rust helper、Cranelift は helper 呼び出し」という方向で行くのが自然だよ〜。

---

# 最優先の修正案

## `pop_return_frame_i64` より `continue_return_frames_i64(value)` が欲しい

write27-a の helper は今こう。

```text
yulang_cps_pop_return_frame_i64() -> i64
  continuation pointer or -1
```

でも、これだと codegen 側で次を全部扱う必要が出る。

```text
- popped frame の env
- restored handler stack
- restored guard stack
- restored eval context
- continuation pointer の arity
- continuation call
```

env が返ってこないなら、codegen 側では continuation を正しく call できない。env 用 getter を増やす手もあるけど、分割しすぎると事故る。

私ならこうする。

```rust
extern "C" fn yulang_cps_continue_return_frame_i64(value: i64) -> i64
```

この helper が内部で:

```text
1. return frame を pop
2. handler stack snapshot を復元
3. guard stack snapshot を復元
4. eval context を frame.owner_eval_id / frame.owner_initial_frame_count に復元
5. continuation pointer + env + value で JIT continuation を呼ぶ
6. result を返す
```

continuation function の型は scalar subset なら基本:

```rust
extern "C" fn(env: i64, arg: i64) -> i64
```

で足りるはず。return frame は「1つの返り値を resume continuation に渡す」用途だからねぇ。

---

# Return terminator codegen は helper へ寄せる

write27-b の Return codegen は、Cranelift 側で loop を作るより helper 一発が安全。

追加 helper 案:

```rust
extern "C" fn yulang_cps_return_i64(value: i64) -> i64
```

この helper が Layer 1/2 の Return terminator 意味論を担当する。

```text
if return_frame_len <= current_initial_frame_count:
    return value

if value is thunk
   && top_frame.immediately_forces_param
   && top_index >= current_initial_frame_count:
    // pre-force v2
    // top frame retained
    set eval_context(top_frame.owner_eval_id, return_frame_len)
    call top_frame.continuation(top_frame.env, value)
    return result

else:
    return continue_return_frame_i64(value)
```

これなら Cranelift Return terminator codegen は単純。

```text
call yulang_cps_return_i64(value)
return result
```

## 重要: return frame に `immediately_forces_param` を保存する

pre-force v2 には `return_frame_immediately_forces_param` 判定が必要。でも Cranelift runtime は `CpsContinuationId` や function body を知らない。

だから push 時に codegen 側で判定して、frame に bool を保存する。

```rust
struct NativeCpsI64ReturnFrame {
    continuation: usize,
    env: i64,
    handlers: Vec<NativeCpsI64HandlerFrame>,
    guards: Vec<i64>,
    owner_initial_frame_count: usize,
    owner_eval_id: u64,

    immediately_forces_param: bool, // 追加
}
```

`push_return_frame` の signature も拡張。

```rust
yulang_cps_push_return_frame_i64(
    continuation,
    env,
    owner_initial,
    owner_eval,
    immediately_forces_param,
) -> i64
```

`immediately_forces_param` は codegen 時に、resume continuation の ABI continuation を見て計算する。

```rust
return_frame_immediately_forces_param_abi(function, resume_cont_id)
```

Layer 1/2 の helper と同じ判定を ABI/Cranelift 側へ移す感じだねぇ。

---

# eval context の扱いで注意

write27-a で eval context helper が入った。次はこれを **Effectful* だけでなく sync internal call にも使う**必要がある。

## sync `DirectCall` / `ApplyClosure` / `ForceThunk`

Layer 1/2 では sync call はこう。

```text
callee に fresh eval id を与える
callee.initial_frame_count = current return_frame_len
callee は inherited frames を見るが、通常 Return では consume しない
caller eval は alive なので、callee return 後に caller eval context を復元する
```

Cranelift でも同じ。

codegen pattern:

```text
saved_eval = current_eval_id()
saved_initial = current_initial_frame_count()
callee_initial = return_frame_len()
callee_eval = fresh_eval_id()

set_eval_context(callee_eval, callee_initial)
result = call target / force thunk / apply closure
set_eval_context(saved_eval, saved_initial)

if scope_return_active():
    routed = route_scope_return()
    return routed

write result to dest and continue
```

これを忘れると、ScopeReturn routing が wrong eval id で動く可能性がある。

## EffectfulCall / EffectfulForce / EffectfulApply

Effectful terminator は tail-call 的に現在 eval が終わるので、caller context restore は不要寄り。

```text
pre_push = return_frame_len()
push F_post(owner_eval=current_eval, owner_initial=current_initial)
set_eval_context(fresh_eval_id(), pre_push)
call callee
if scope_return_active(): route
return result
```

---

# continuation pointer の取り方

report の質問 2 への答え。

既存コードには `continuation_func_ref` / `continuation_func_ref_by_name` があり、continuation function を Cranelift function ref として解決する流れがある。effectful function は continuation を JIT function として declare/define しているので、これを使うのが基本だねぇ。

`push_return_frame` に渡す pointer は、Cranelift 側で function address を取る。

概念:

```rust
let func_ref = continuation_func_ref(module_backend, builder, function, resume, functions)?;
let cont_ptr = builder.ins().func_addr(types::I64, func_ref);
```

ただし Cranelift の version/API によって `func_addr` の型引数まわりが少し違うかもしれない。既存の `MakeThunk` / `MakeClosure` codegen が continuation pointer を helper に渡しているはずだから、そこを真似るのが一番安全だよ〜。

---

# handler frame extension は helper push が良い

report の質問 3 への答え。

`NativeCpsI64HandlerFrame` に prompt / install_eval_id / escape / threshold / inherited を足すのは正しい。ただ、Cranelift IR 側で frame struct 相当を全部組むのは避けた方がいい。

おすすめは helper に寄せる。

```rust
extern "C" fn yulang_cps_install_handler_full_i64(
    handler_id: i64,
    escape_cont: i64,
    escape_env: i64,
    return_frame_threshold: i64,
    install_eval_id: i64,
    inherited: i64,
) -> i64
```

または既存 `yulang_cps_install_handler_i64` を拡張してもいいけど、既存 tests との互換を見るなら新 helper の方が安全。

`escape_cont` も function pointer で持つ。
`escape_env` は escape continuation の environment pointer。

ScopeReturn route helper が match したら:

```text
clear scope_return
restore handler/guard/eval/frame stack
call escape_cont(escape_env, value)
```

ここも Rust helper 側で完結させると codegen が軽くなる。

---

# write27-b の最小スコープ

write27-b では、いきなり EffectfulApply Resumption まで行かなくていいと思う。

まずこれ。

## b1. Return helper を実装

```text
yulang_cps_return_i64(value)
yulang_cps_continue_return_frame_i64(value)
```

Return terminator codegen を差し替える。

期待:

```text
既存 167 tests pass
Layer 3 todo panic はまだ残ってもよい
```

## b2. sync internal call の eval context save/restore

`DirectCall` / `ApplyClosure` / `ForceThunk` stmt 後に:

```text
save caller eval context
set callee eval context
call
restore caller eval context
if scope_return_active: route
```

まだ `route_scope_return` が未実装なら、active check だけ入れて old abort route と併用でもいい。

## b3. EffectfulCall + EffectfulForce

`std::undet.each` narrow lowering で最初に必要なのはここ。

```text
EffectfulCall each
ForceThunk chain
Return pre-force
```

EffectfulApply Resumption は後で必要になるけど、まず TODO panic がどこまで進むかを見る価値がある。

---

# write27-c の本命

## `route_scope_return_i64(value)` を Rust helper に寄せる

helper でやること:

```text
if no scope_return active:
    return value

let sr = scope_return

1. current handler stack で:
   handler.prompt == sr.prompt
   handler.install_eval_id == current_eval_id
   を reverse search

2. 見つかれば:
   handler stack truncate
   return frame threshold truncate
   clear sr
   call handler.escape(value)
   return result

3. 見つからなければ:
   return_frames[current_initial_frame_count..] を reverse walk

4. frame.active_handlers で:
   handler.prompt == sr.prompt
   handler.install_eval_id == frame.owner_eval_id
   を探す

5. 見つかれば:
   frame.active_handlers truncate
   return_frames truncate
   restore frame context
   clear sr
   call handler.escape(value)
   return result

6. 見つからなければ:
   return value with sr still active
```

Cranelift 側では internal call 後に:

```text
if scope_return_active:
    result = yulang_cps_route_scope_return_i64(result)
    return result
```

`result` 引数は fallback 用。実際の sr value は slot から読む。

---

# EffectfulApply Resumption は専用 helper がよい

ここを Cranelift IR でやると地獄っぽい。

専用 helper:

```rust
extern "C" fn yulang_cps_effectful_apply_resumption_i64(
    resumption: i64,
    arg: i64,
    post_cont: i64,
    post_env: i64,
    owner_initial: i64,
    owner_eval: i64,
    immediately_forces_param: i64,
) -> i64
```

helper 内で:

```text
1. F_post を作る
2. resumption.handled_anchor を見る
3. merge_resumption_handlers
4. merge_extras_into_frames
5. combined_frames = new_frames + adjusted_res_frames
6. eval_context = fresh, initial=0
7. call resumption target
```

これは Layer 1/2 の `EffectfulApply(Resumption)` と同じ。

---

# warning について

8 個の dead_code warning は今は問題ない。write27-a は helper を symbol 登録しただけだから自然だよ〜。write27-b/c で codegen から呼び始めると消えるはず。

ただし、write27-b が終わっても残る helper があるなら、そこは本当に不要か、まだ write27-c 用かを見直すとよい。

---

# Aborted / abort helper の削除時期

まだ消さない。

write26 でも `Aborted` は legacy bridge として残した。write27-a でも abort helper は codegen からまだ呼ばれている。Layer 3 完全通過前に消すと、failure が混ざって読みづらい。

削除タイミング:

```text
1. Layer 3 が OK
2. yulang_cps_abort_* を grep
3. Aborted を grep
4. 使われていなければ削除
```

---

# 別LLMへ渡す短い指示文

```text
write27-b では、Cranelift codegen 側で continuation call loop を作り込まず、
return-frame continuation call まで Rust helper に寄せる。

追加・変更する helper:
  yulang_cps_continue_return_frame_i64(value) -> i64
  yulang_cps_return_i64(value) -> i64
  yulang_cps_route_scope_return_i64(fallback_value) -> i64
  yulang_cps_is_thunk_i64(value) -> i64  // pre-force 用、既存 registry があればそれを使う

Return frame に immediately_forces_param: bool を追加する。
push_return_frame の引数にも immediately_forces_param を足す。
この bool は codegen 時に resume continuation を見て計算する。

Return terminator codegen:
  result = call yulang_cps_return_i64(value)
  return result

sync DirectCall / ApplyClosure / ForceThunk:
  saved_eval = current_eval_id
  saved_initial = current_initial
  callee_initial = return_frame_len
  callee_eval = fresh_eval_id
  set_eval_context(callee_eval, callee_initial)
  call
  restore saved_eval/saved_initial
  if scope_return_active:
      result = route_scope_return(result)
      return result
  else continue

EffectfulCall / EffectfulForce:
  pre_push = return_frame_len
  push return frame(resume_cont_ptr, resume_env, current_initial, current_eval, immediate_force)
  set_eval_context(fresh_eval_id, pre_push)
  call target/thunk
  if scope_return_active:
      result = route_scope_return(result)
  return result

EffectfulApply Resumption は write27-c で専用 helper:
  yulang_cps_effectful_apply_resumption_i64(...)
に寄せる。
anchor merge / combined_frames は Rust 側で計算する。
```

---

# 質問への答えまとめ

## 1. Return terminator codegen は Rust helper 完結が安全？

うん、かなり強くそう思う。codegen 側で loop を作るより、`yulang_cps_return_i64(value)` に寄せる方が安全。pre-force v2、frame pop、eval context restore、continuation call が全部一箇所にまとまる。

## 2. continuation function pointer の取得は？

既存の continuation function ref 解決を使い、Cranelift の `func_addr` 系で i64 pointer 化する。`MakeThunk` / `MakeClosure` が既に continuation pointer を helper に渡しているなら、その実装を真似るのが一番よい。

## 3. handler frame push は helper？

helper が良い。prompt/install_eval/escape/threshold/guard snapshot/env snapshot を codegen 側で組むと複雑すぎる。`install_handler_full` 的な helper を作って、Cranelift は必要な pointer と env だけ渡す形がよさそうだよ〜。

---

# 最後に

write27-a は「正しい足場だけ作って regression なし」で、かなり理想的な a-step だねぇ。次の b-step で一番大事なのは、**Return continuation の呼び出しを codegen 側にばらさず、runtime helper にまとめること**。

これをやると、Layer 1/2 の意味論を Layer 3 に載せる時の事故がかなり減ると思うよ〜。
