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
  「block tail が listen の戻り値を貫通する」問題は **未解決**（root cause は別）。

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
