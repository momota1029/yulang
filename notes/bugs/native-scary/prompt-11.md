読んだよ〜。
結論から言うと、ノートの見立てはかなり当たっていると思う。**handler selection ではなく、`RoutedJump` を native の `i64` 戻り値モデルへ押し込んだところで、非局所 jump が普通値に落ちている**のが主犯候補だねぇ。

## いまの症状整理

`prompt-7.md` の「2026-05-17 再調査」では、`last` の `perform_select` は成功し、`last::break` 側も選ばれていて、さらに `route_scope_return` の frame-walk も outer `last::sub` prompt を見つけている、という整理になっている。つまり「handler が見つからない」ではなく、「見つかった後の `RoutedJump` が jump として生き残らない」問題だねぇ。

`notes/bugs/index.md` の `native_open_range_for_last_returns_payload.yu` 節も同じ結論で、有限 range に `say` を入れると `0 1 2 3 4 6 7 5` のように `last` 後も iteration が続く、という観測がある。これは「最終結果だけ `5` に見える小さいテスト」は false positive で、実際には loop-control が壊れている、というかなり危ない状態だねぇ。

## 実装上の対応箇所

repr 側はだいぶ筋が通っている。`dispatch_scope_return_repr!` はまず `resolve_routed_jump_repr` を通して、まだ解決できない `RoutedJump` はそのまま上へ返す。つまり `RoutedJump` を普通値として `dest` に入れたり、post-call continuation に食わせたりしない構造になっている。

さらに repr の `try_route_scope_return_through_return_frames_repr` は、target が inherited caller activation 側にあるとき `CpsReprRuntimeValue::RoutedJump` を返す。`resolve_routed_jump_repr` は frame count が threshold まで下がった時点で、保存された `owner_function` / `target` / `values` / `return_frames` / `eval_id` で `resume_continuation(...)` を呼ぶ。ここが「値を返す」じゃなくて「eval loop の位置を移す」意味を持っている。

native 側の `yulang_cps_route_scope_return_i64` も frame-walk で match したら `routed_jump_abort(...)` を作っている。なので route 自体は native でも概ね届いている。

## 一番怪しい地点

ここが本丸っぽい。

`abort_result_or_return` は `yulang_cps_abort_mode_i64()` が `2` のとき、`yulang_cps_consume_abort_i64()` を呼んで、その結果を `no_abort` block に合流させている。つまり **consume した結果を普通のローカル値として扱う**。

そして `consume_native_i64_abort` の `RoutedJump` branch は、保存された handler / guard / eval context を復元しつつ、`return_frames` は直接入れずに `NATIVE_CPS_I64_PENDING_ROUTED_RETURN_FRAMES` へ退避し、escape continuation を Rust helper 内で呼んで、その result を返している。

この組み合わせがかなり危ないねぇ。

```text
RoutedJump consume
  -> escape continuation を呼ぶ
  -> result が i64 として戻る
  -> abort_result_or_return の no_abort に合流
  -> 呼び出し元 continuation の普通の後続処理が続く
  -> fold / range iteration が続く
```

`prompt-7.md` の「escape continuation result が普通の関数戻り値として fold / range continuation へ流れる」という観測と、実装がぴったり噛み合っている。

## 直近で切るべき実験パッチ

私なら、まず **`RoutedJump` consume を通常の mode 2 consume から分離**するねぇ。`Scoped` abort と `RoutedJump` を同じ `consume -> no_abort 合流` に乗せない。

### 1. native abort に predicate helper を足す

今 `native_i64_abort_is_routed_jump()` は Rust 内では使われているけど、JIT lowering 側から分岐する helper としては見えていないように見える。なので exported helper を足すのが安全そう。

```rust
#[unsafe(no_mangle)]
extern "C" fn yulang_cps_abort_is_routed_jump_i64() -> i64 {
    NATIVE_CPS_I64_ABORT.with(|slot| {
        i64::from(slot.borrow().is_routed_jump())
    })
}
```

それを `runtime_symbols.rs` にも登録する。

### 2. `abort_result_or_return` の mode 2 を split する

今は mode 2 が全部 no_abort に合流する。ここを分ける。

ざっくり形はこれ。

```rust
let consume = builder.ins().icmp_imm(ir::condcodes::IntCC::Equal, mode, 2);
let consume_block = builder.create_block();
let return_block = builder.create_block();

...

builder.switch_to_block(consume_block);
let is_routed = call_i64_helper(
    module_backend,
    builder,
    "yulang_cps_abort_is_routed_jump_i64",
    &[],
)?;

let routed_block = builder.create_block();
let scoped_block = builder.create_block();
builder.ins().brif(is_routed, routed_block, &[], scoped_block, &[]);

builder.switch_to_block(routed_block);
let routed = call_i64_helper(module_backend, builder, "yulang_cps_consume_abort_i64", &[])?;
builder.ins().return_(&[routed]);

builder.switch_to_block(scoped_block);
let abort_value = call_i64_helper(module_backend, builder, "yulang_cps_consume_abort_i64", &[])?;
builder.ins().jump(no_abort, &[ir::BlockArg::Value(abort_value)]);
```

ポイントは、**`RoutedJump` consume の結果を `dest` に入れない**こと。ここで普通値として合流した瞬間に、`fold` の次 iteration が生き返る。

### 3. `consume_native_i64_abort` の `RoutedJump` branch も疑う

ここもかなり怪しい。

今は routed `return_frames` を実 frame stack に入れず、pending に入れている。

```rust
NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| frames.borrow_mut().clear());
NATIVE_CPS_I64_PENDING_ROUTED_RETURN_FRAMES.with(|pending| {
    *pending.borrow_mut() = Some(NativeCpsI64PendingRoutedReturnFrames {
        skip_initial_frame_count: eval_context.initial_frame_count,
        frames: return_frames.clone(),
    });
});
...
let result = cont(env.as_ptr(), value);
result
```

repr の `resolve_routed_jump_repr` は、escape continuation を **保存された `return_frames` つきで** `resume_continuation` している。だから native もまずは pending ではなく、直接 stack に戻す実験を切る価値が高い。

```rust
NATIVE_CPS_I64_RETURN_FRAMES.with(|frames| {
    *frames.borrow_mut() = return_frames.clone();
});
NATIVE_CPS_I64_PENDING_ROUTED_RETURN_FRAMES.with(|pending| {
    *pending.borrow_mut() = None;
});
NATIVE_CPS_I64_EVAL_CONTEXT.with(|ctx| *ctx.borrow_mut() = eval_context);

let cont: NativeCpsI64Continuation = unsafe { std::mem::transmute(continuation) };
cont(env.as_ptr(), value)
```

ただし、これは単体だとまだ普通 return に落ちる可能性がある。だから **2 の `abort_result_or_return` split とセット**で見るのがよさそうだねぇ。

## regression はこの順がよさそう

まず false positive を潰すため、戻り値だけじゃなく副作用順を見る test を最優先で置くといい。

```yulang
use std::flow::*
use std::out::*

{
    for x in 0..<8:
        if x == 5:
            last
        else:
            out.write(x.show ++ " ")
    5
}
```

期待は `0 1 2 3 4 ` だけで、`6 7` が出たら失敗。

その後に:

```yulang
use std::flow::*
{
    for x in 0..:
        if x == 5: last
        else: ()
    5
}
```

これは native で timeout しないことを見る。

さらに `0..<10000` + `last` を入れて、有限 range で「最後まで回って偶然 5」になっていないことも確認するのがよさそう。

## いま止めるべきもの

修正が入るまで、`yulang run --native` で `std::flow::last` / open range / `for` loop-control を通すのはかなり危ないと思う。少なくとも user-facing native では、この系だけ interpreter fallback か unsupported に落とす逃げ道を入れた方がいい。結果が間違うだけじゃなく、open range だと無限化・メモリ枯渇に直結するからねぇ。

私の見立てでは、次に触る一点はこれ：

> **`abort_result_or_return` の mode 2 consume を、`RoutedJump` だけ no_abort 合流から外す。さらに `consume_native_i64_abort::RoutedJump` の pending return-frame 復元を、repr の `resume_continuation(... return_frames ...)` に近づける。**

ここを直さず handler search 側を触ると、また false positive に引っかかりそうだよ〜。
