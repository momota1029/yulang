---
title: native-undet-write27-e 実装レポート — handler stack 膨張の根治 + Resume anchor merge
date: 2026-05-12
---

# native-undet-write27-e 実装レポート

## 結論（先に）

write27-d で「**SR routing 後に inner once が消える**」と見えていた現象、
trace を厚くしたら原因が **handler stack の指数的膨張** だと判明した。

- `apply_closure_i64` が `current + closure.handlers` を thread_local
  stack に append していて、毎回 caller stack を closure handlers
  で重ね塗りしていた。Layer 2 (`cps_repr.rs:2247`) は
  `eval_continuations(..., active_handlers, ...)` で **caller stack
  をそのまま**渡すだけ — `closure.handlers` は call 時には未使用。
- `force_thunk_i64` も `current + thunk.handlers + pending` の append
  → 膨張をさらに加速。Layer 2 (`cps_repr.rs:1648`) は
  `if !active_handlers.is_empty() { active_handlers } else { thunk.handlers }`
  で「caller が空なら thunk の handlers を採用、そうでなければ caller
  をそのまま」。
- `Resume` stmt → `yulang_cps_resume_i64` は **anchor merge を全く
  していなかった**。Layer 2 (`cps_repr.rs:1879`) は
  `merge_resumption_handlers_repr` + `merge_extras_into_frames_repr`
  + `eval_continuations(..., adjusted_frames, 0)` で anchor merge
  と combined frames を使う。

この 3 つを Layer 2 と整合させたら、Layer 3 trace は劇的に綺麗に
なり、**frame_walk match + effectful_apply_resumption + 2 段ネスト
した once の inner Perform** まで全部走るように。

Layer 3 `debugs_std_undet_once_skip_eval_layers` は依然 fail だけど、
失敗形は `I64Mismatch { index: 0, vm: 2, cps_cranelift: <heap_ptr> }`
で、**意味論ロジックは通っていて、最後の値の表現だけが違う**。
once が `std::opt::opt::just v` の heap variant を返し、外側の
`case` が `just v -> v` で v を取り出すところまでは届いていない
感じ。これは SR / anchor merge と別系統のバグだよ〜。

既存 167 tests **pass**、local choice 系 **pass**。

---

## 進捗まとめ

```text
write27-d 後:
  Layer 3: cps_cranelift=0 (SR resolved 後 inner once 喪失)
  原因仮説:
    A. handler stack 順序が逆? (B が正解?)
    B. current_eval_id が H_sub install eval と一致?

write27-e で trace 厚くして分かったこと:
  → どちらでもなく **handler stack が指数的に膨張**していた
  → apply_closure_i64 / force_thunk_i64 が append していた
  → さらに Resume が anchor merge していなかった

write27-e 後:
  Layer 3: cps_cranelift=<heap_ptr>  (意味論パス突破、値表現の差)
  trace:
    - perform_select 全部 origin=RealInstall
    - route_scope_return action=frame_walk fi=2 hi=2 ← 期待通り
    - effectful_apply_resumption.in/out が呼ばれて anchor merge 動作
    - 2 段ネストの once (prompt=4 install_eval=61 等) も install
    - sub::return value=1, value=2 が SR で走り frame_walk match
    - 最終的に heap pointer (opt::just _) を返している
```

---

## e1〜e4 — trace 厚化と debug flag

### `format_handler_stack` / `format_return_frames`

各 frame を `h<id>(p=<prompt>,ev=<eval_or_SYN>,<origin>,inh=<bool>)` の
形で出すヘルパを追加。`route_scope_return.scan` と
`scope_return_set (perform_finish)` と
`effectful_apply_resumption.in/out` でこれを使って、stack と frames を
inline dump するように。

最初の trace で気づいた事実:

```text
stack=[h1(p=1,ev=3), h1(p=0,ev=SYN,PendingEnv), h1(p=1,ev=3),
       h1(p=0,ev=SYN,PendingEnv), h0(p=2,ev=6),
       ...同じパターンが何十回繰り返し...]
```

handler stack が **20〜200 個の frame** で構成され、ほとんどが
重複。これは write27-d 時点では何が起きているか分からない情報
だった。

### `YULANG_CPS_JIT_FORCE_FRAME_WALK_SR=1`

env-guard で `route_scope_return_i64` の current-handler scan を
skip して frame-walk path 強制する debug flag。今回の根治では
直接使わなかったけど、route order が問題の場合に検証する手段
として残してある。

### `resumption_anchor` trace

`yulang_cps_set_resumption_anchor_from_selected_i64` が set した
`(prompt, install_eval_id)` を表示。

---

## e5 — handler stack 膨張の根治

### Bug 1: `apply_closure_i64`

旧:
```rust
extern "C" fn yulang_cps_apply_closure_i64(value: usize, arg: i64) -> i64 {
    let closure = ...;
    with_native_i64_cps_state(
        native_i64_handler_stack_with_captured(&closure.handlers),  // ← BUG
        closure.guard_stack.to_vec(),
        || (closure.code)(closure.env.as_ptr(), arg),
    )
}
```

`native_i64_handler_stack_with_captured` は
`current.clone() + closure.handlers` を返す。closure を 1 段呼ぶ
たびに stack に closure.handlers が追加される。closure 内で別の
closure を呼べば、そこの apply_closure でまた append → 指数的
膨張。

新 (Layer 2 と整合):
```rust
extern "C" fn yulang_cps_apply_closure_i64(value: usize, arg: i64) -> i64 {
    let closure = ...;
    (closure.code)(closure.env.as_ptr(), arg)  // caller stack のまま
}
```

Layer 2 の `EffectfulApply::Closure` 分岐は
`eval_continuations(..., active_handlers, ...)` で active_handlers
を使うのみ。`closure.handlers` は make_closure 時点での装飾用で、
call 時には未使用 — JIT もそれに揃える。

### Bug 2: `force_thunk_i64`

旧は同様に `current + thunk.handlers + pending` を append。

新 (Layer 2 の `if !active_handlers.is_empty() { ... } else { thunk.handlers }`):
```rust
let handlers = if current_handlers_empty {
    thunk.handlers.to_vec()
} else {
    NATIVE_CPS_I64_HANDLER_STACK.with(|s| s.borrow().clone())  // そのまま
};
```

`pending` は持ち越さない (JIT 特有の補助構造で、Layer 2 にない概念
なので持ち越し対象から外す)。

### Bug 3: `yulang_cps_resume_i64`

これは決定打だった。旧:
```rust
extern "C" fn yulang_cps_resume_i64(...) -> i64 {
    with_native_i64_cps_state(
        resumption.handlers.to_vec(),     // 単純置き換え
        resumption.guard_stack.to_vec(),
        || (resumption.code)(...),
    )
}
```

Layer 2 `cps_repr.rs:1879` の Resume:
```text
resumed_handlers  = merge_resumption_handlers(captured, current, anchor)
adjusted_frames   = merge_extras_into_frames(captured_frames, current, anchor)
eval_continuations(..., resumed_handlers, ..., adjusted_frames, initial=0)
```

JIT 側も同じく anchor merge + combined frames を実行。Resume helper
内で thread_local return_frames を `adjusted_frames` で一時的に
swap し、eval context も fresh+initial=0 にして resumption.code を
呼び、終わったら caller の state を完全に復元するように直した。

これで Resume が write27-d で新設した `effectful_apply_resumption`
と同じ anchor merge セマンティクスを持つようになった。

---

## 結果の trace

trace を見ると、以下の通り正しい frontier に進んでいる:

```text
install h1(p=1) outer once
install h0(p=2) outer sub::return
perform_select handler=1 prompt=1 install_eval=3 idx=0 RealInstall  ← outer once
install h1(p=3) inner once
resume: anchor=(1,3)
  captured=[h1(p=1,ev=3), h0(p=2,ev=6)]
  current=[h1(p=3,ev=29)]
  resumed=[h1(p=1,ev=3), h1(p=3,ev=29), h0(p=2,ev=6)]   ← anchor merge 効いた
  adjusted_frames=5

perform_select handler=0 prompt=2 idx=2 RealInstall   ← outer sub::return
scope_return_set prompt=2 value=1
route_scope_return action=frame_walk fi=2 hi=2 value=1   ← 期待通りの frame_walk

perform_select handler=1 prompt=3 install_eval=29 idx=1   ← inner once
install h1(p=4) inner inner once
effectful_apply_resumption.in/out  ← c6 helper 発火
  anchor=(1,3)
  resumed_handlers=[h1(p=1,ev=3), h1(p=4,ev=61), h0(p=2,ev=6)]

perform_select handler=1 prompt=4 install_eval=61 idx=1
install h1(p=5) deeper inner once
resume: anchor=(4,61)
  resumed=[h1(p=1,ev=3), h1(p=4,ev=61), h1(p=5,ev=88), h0(p=2,ev=6)]

perform_select handler=0 prompt=2 idx=3
scope_return_set prompt=2 value=2   ← sub::return value=2
route_scope_return action=frame_walk fi=5 hi=3 value=2

(...略...) heap pointer をエスケープ
```

意味論的には Layer 2 と同じ動きをしている。最後だけ値の表現が
ちがう (`scope_return_set value=137771815914464` のような heap ptr)。

---

## テスト結果

```text
cargo test -p yulang-native              => 167 pass / 17 ignored
debugs_local_choice_caller_rest_eval     => pass
debugs_local_choice_callback_rest_eval   => pass
debugs_std_undet_once_skip_eval_layers
  => Layer 1 OK / Layer 2 OK
     Layer 3 FAIL: I64Mismatch(vm:2, cps_cranelift:<heap_ptr>)
```

write27-d との差: `cps_cranelift=0` (値が出ない) → `<heap_ptr>`
(意味論は通って値が出るが表現が違う)。

---

## 残る Layer 3 のバグ

test source:
```yu
my work(): int = {
    my n = each [1, 2, 3]
    guard: n > 1
    n
}
case work().once:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
```

期待結果: `2` (each 1,2,3 を once で最初の guard 通過 = 2)。

trace から見ると JIT は `2` まで内部で計算しているが、最終
return が `opt::just 2` の heap variant pointer になっており、
外側 `case` で `just v -> v` で v を取り出すところで詰まって
いる感じ。

trace の最後の方:
```text
scope_return_set value=137771815914464 (= heap pointer of opt::just _)
route_scope_return action=propagate (上位 eval まで escape できず)
```

仮説:
- once 側が `opt::just 2` を heap value で組み立てるところまでは
  OK。
- 外側 `case` の Variant 解体 codegen と、SR / return-frame の
  interaction で v が取れていない。
- もしくは `opt::just` の内部 payload が heap pointer (別の heap
  object) になっていて、再 unwrap が必要。

これは SR routing / anchor merge とは独立した layer 3 codegen の
バグなので、別の write27-f で追うのが筋。

---

## 触ったファイル

- `crates/yulang-native/src/cps_repr_cranelift.rs`
  - `format_handler_stack` / `format_return_frames` 形式化ヘルパ (e1)
  - `jit_force_frame_walk_sr` env flag (e4)
  - `route_scope_return.scan` trace + force-frame-walk 経路 (e2, e4)
  - `scope_return_set (perform_finish)` trace に stack + frames (e3)
  - `effectful_apply_resumption.in/out` trace に captured/current/
    resumed_handlers/new_frames (e1)
  - `yulang_cps_apply_closure_i64` を caller stack 維持に (e5)
  - `yulang_cps_force_thunk_i64` を Layer 2 整合の if-else 分岐に (e5)
  - `yulang_cps_resume_i64` を anchor merge + state swap に (e5)

---

## 次の作業（write27-f 候補）

1. **case + opt::just の Layer 3 codegen 検査**:
   - `CpsStmt::VariantTagEq` / `VariantPayload` / `Variant` の
     codegen を Layer 2 と比較。
   - heap pointer のまま return される経路がどこか追う。
2. もしくは: once handler の natural arm return が `just v` を
   構築するところで、`v` が heap-wrapped されている可能性を見る。
3. `Aborted` / `yulang_cps_abort_*` legacy の grep → Layer 3 通過
   後に削除判定。

---

## ひとこと

write27-e は **値だけ見れば `0 → heap_ptr` でやっぱり 2 では
ない**けど、内容的には決定的な前進だよ〜。

- 一番厄介に見えていた「inner once 喪失」は、実は handler stack
  の指数膨張 + Resume の anchor merge 抜けが原因の symptom だった。
- trace を厚くしたおかげで一気に根本原因が見えた。
- 残る差は variant unwrap 系の別バグで、write27-d/e の SR/anchor
  /resumption 系統とは独立した layer 3 codegen の問題。

frontier はもう「effect handler の意味論」ではなく「value 表現の
codegen」に移ってる。ここまで来ると射程内だね。
