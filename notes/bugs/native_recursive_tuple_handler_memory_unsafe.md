# native: recursive tuple-returning handler is memory-unsafe

2026-05-17 発見。docs/examples 経由で `yulang run --native` を流していて気付いた。

**memory-unsafety 部分は 2026-05-17 commit `3bad594` で解消**:
`make_closure` は closure.code を entry continuation 直接にしていて、
`apply_closure` 経由だと `lower_effectful_function_wrapper` の
`force_function_result_if_thunk` を skip していた。handler arm が thunk を
返す場合（scope_return 経由で perform_finish した結果など）、その thunk が
force されずに caller に戻り、heap value handle として deref されて
pointer 形整数が漏れていた。`yulang_cps_apply_closure_i64` の最後で
`yulang_cps_force_thunk_i64` を call するようにして消えた。
force_thunk は非 thunk に対して idempotent なので安全。

残った別バグ:
- `unit` 表示が `0` になる（u3/t1/t5 の第一要素 `0` が `()` のあるべき表示と異なる）。
  これは display 側の Show role dispatch の問題で、memory unsafety とは別系統。
- 兄弟ファイル `native_recursive_handler_for_last_tail_skips_value_arm.yu`
  および最小化版 `native_recursive_handler_block_tail_escapes.yu` の
  「block tail が listen の戻り値を貫通する」問題は **2026-05-18 に解消**。
  root cause は memory unsafety とは別で、effectful direct call statement の後続
  continuation が return-frame protocol に乗っていなかったこと。

2026-05-18 追記:
`crates/yulang-native/src/cps_repr_cranelift.rs` の JIT runtime helper 群を
`cps_repr_cranelift/runtime_i64.rs` へ切り出した後に再調査。
`route_scope_return` は prompt 1 の frame-walk で外側 `listen` handler を見つけ、
handler value arm の tuple `(0, "0\n")` までは作れている。
ただし、`RoutedJump` を普通値に落とす箇所だけを止めると最終結果は
`(0, "0\n")` になり、期待値 `(5, "0\n")` には届かない。
つまり `5` が tuple を貫通するだけでなく、そもそも `k()` の resumption が
block tail `5` までを返せていない。

root cause は、effectful な `DirectCall` statement の後続 continuation が
return-frame protocol に乗っていないこと。`for_in` の戻りを
受けて block tail `5` へ進む continuation が、native の通常 call stack 側に残り、
resumption capture / `RoutedJump` の対象から外れている。局所的に
`abort_result_or_return` の routed jump consume を変えるだけでは不十分。

同日修正:
`cps_effectful_calls::reify_effectful_direct_calls` を追加し、CPS lowering の
capture 推論前に、effectful callee への `DirectCall` statement を
`EffectfulCall` terminator + 明示的な resume continuation へ正規化するようにした。
これで call site の後続 continuation が return-frame protocol に乗る。
`native_recursive_handler_block_tail_escapes.yu` は native でも `(5, "0\n")`、
`native_recursive_handler_for_last_tail_skips_value_arm.yu` は
`(5, "0\n1\n2\n3\n4\n")` になる。
`native_recursive_tuple_handler_memory_unsafe.yu` は native で `(0, "x")` のままなので、
残りは既知の unit 表示 `0` 問題だけ。

2026-05-18 追加修正:
unit literal を native i64 scalar `0` ではなく `NativeCpsI64HeapValue::Unit` として
lower するようにした。continuation / resumption を経由して `(_, str)` の `_` で
型ヒントが落ちても、tuple/list 等の runtime value 表示では `()` として復元できる。
また native executable harness 側で、CPS lane が `Unknown` でも runtime root type が
bool なら bool 表示を保つようにした。
unit を heap value にすると、prompt-exit marker と古い `return_frame_threshold` が
ずれる既存ケースが debug assert に当たったため、ScopeReturn の truncate 点は
既に使っている prompt-exit marker を正とし、古い threshold 一致 assert は外した。
これで `native_recursive_tuple_handler_memory_unsafe.yu` は native でも `((), "x")`。

既存の `native_recursive_handler_for_last_tail_skips_value_arm.yu` と同根だが、
`for` / `last` が無くても、**handler arm から再帰呼び出しして tuple を返す形**
だけで踏める。返値が pointer 形状の整数として漏れる（毎回値が変わる）ため、
single bug というより memory-safety まわりが疑わしい（当時の判断）。

## 切り分け表

`yulang run --interpreter --print-roots` を基準、`yulang run --native --print-roots`
を観測値とする。すべて 2026-05-17 のスナップショットで再現。

| ケース | handler 形 | 戻り値型 | interpreter | native (修正前) | native (修正後 = 3bad594) |
| --- | --- | --- | --- | --- | --- |
| u1 | `op,k -> rec(k(), n+1)`, `v -> n` | `int` | `3` | `3` ✓ | `3` ✓ |
| u3 | `op,k -> rec(k(), n+1)`, `v -> (v, n)` | `(int, int)` | `(99, 2)` | `810610592` 等（毎回変わる） | `(99, 2)` ✓ |
| t1 | `op,k -> rec(k(), log + o)`, `v -> (v, log)` | `(int, str)` | `(99, "a\nb\n")` | `280001392` 等 | `(99, "ab")` ✓（注: log 連結 `+ "\n"` を入れた版なら `(99, "a\nb\n")`） |
| t3 | t1 + `for` body 内 `if x == 5: last` | `(int, str)` | `(5, "0\n1\n2\n3\n4\n")` | `5`（tuple が崩れて第一要素のみ） | `5`（未解決、companion bug） |
| t5 | t1 を 1 回だけ recurse | `(_, str)` | `((), "x")` | `474247824` 等 | `(0, "x")`（unit→0 表示だけ残る） |

境界（修正前の判断、参考まで）:

- **u1 が動く** → 再帰 + state passing そのものは OK
- **u3 で壊れる** → tuple 戻り値が trigger（state の型が str か int かは関係ない）
- **t5 で壊れる** → 再帰が 1 回でも踏む（unbounded recursion は無関係）

## 既存の `.yu` 文書との関係

`notes/bugs/native_recursive_handler_for_last_tail_skips_value_arm.yu` は t3 と同形。
そちらの文書では「`last` の routed jump 後に value arm が当たらない」と読まれているが、
実際には `last` 無しでも壊れるので、**diagnose を broaden** すべき。

具体的には:

- 「last の handler search が壊れている」ではない（u1 が動く）
- 「recursive handler の arm が壊れている」でもない（u1 が動く）
- 「tuple 戻り値を持つ recursive handler の **closing** が壊れている」が正しい

t5 が最小ケース。1 回の `say` だけで garbage が出るので、`last` も `for` も外して
ここから掘るのが速いと思う。

## 最小 repro（`.yu`）

`notes/bugs/native_recursive_tuple_handler_memory_unsafe.yu` を参照。
ここに inline で書いておくと:

```yulang
pub act out:
    pub say: str -> ()

our listen(x: [_] _, log: str): (_, str) = catch x:
    out::say o, k -> listen(k (), log + o)
    v -> (v, log)

listen(out::say "x", "")
-- interpreter: ((), "x")
-- native: 474247824 等の pointer 形整数（毎回変わる）
```

## 同時に拾った別系統の小バグ

`--print-roots` の bool 表示が native で `1` / `0` になる。

```yulang
true       -- interpreter: true / native: 1
[true, false]   -- interpreter: [true, false] / native: [1, 0]
(true, false)   -- 両方 (true, false) ✓
```

bare top-level bool と list 要素は `int` 経由の Show を踏むが、tuple は型を見て
分岐できているっぽい。Show role の dispatch path が `--print-roots` 側で
i64 デフォルトに落ちている疑い。memory unsafe ではないので優先度は低い。

## 確認方法

```bash
yulang run --interpreter --print-roots <file>
yulang run --native      --print-roots <file>
```

毎回 garbage が変わることを見るには、native を 5 回くらい繰り返して走らせる。
