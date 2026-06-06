# ⑫ handler の継続型の effect 行に Any(top) が漏れる

## テスト
`tests::handler_continuation_in_queue_principal_avoids_top_in_effect_row` — `crates/yulang-infer/src/tests.rs:482`

## 入力
```yu
type list 'a
pub cons(x: 'a, xs: list 'a): list 'a = xs

my act eff:
    our op: () -> bool
    our handle(x: [eff] 'a, queue: list (bool -> [eff] 'a)) = catch x:
        op(), k -> cons(k, queue)
        value -> queue

eff::handle
```

## バグ表
| | |
|---|---|
| 期待値（正）| principal evidence の nested function effect 行に `Any`/top を含まない |
| 実際値（誤）| `Fun { param: Var(t9), param_effect: Any, ret_effect: Never, ret: Fun{...} }` — 継続 `k` の **param_effect が Any** |

## なぜ期待値が正しいか
継続 `k` の型は `bool -> [eff] 'a`。queue は `list (bool -> [eff] 'a)` で、`cons(k, queue)` が
通る以上 k の型は queue 要素型と一致するはず。effect 行は `[eff]` であって `Any`(top) ではない。
nested fun の param_effect に top が乗るのは健全な principal 形ではない（top は「何でも起きうる」で、
ここは閉じた `[eff]` のはず）。

## 診断（要 Codex 深掘り）
`apply_principal_callees_in_module` が拾う evidence の中で、継続 `k`（`bool -> [eff] 'a`）の
**param_effect スロットに `Any` が入っている**。catch 腕 `op(), k -> cons(k, queue)` で
継続 `k` の型を作る所か、その effect 行の確定で top が混入している。ユーザ「何か踏んでる」。

候補の発生源:
- catch/handler の継続 `k` 型構築（lower 段の catch 腕処理）
- effect 行の確定（`solve/effect_row.rs`）で未拘束 effect var が top に潰れる
- export/principal evidence 構築（`apply_principal_callees_in_module` 経路）

## 見るべき場所
- `crates/yulang-infer/src/tests.rs:430-505`（`type_contains_any` と
  `apply_principal_callees_in_module` の定義もこの近辺）
- catch 腕の継続型 lowering
- `crates/yulang-infer/src/solve/effect_row.rs`

## 修正方針
継続の param_effect がどこで `Any` になるか dump で追い、`[eff]`(閉じた行)になるべき所が
top に潰れている地点を特定して塞ぐ。`type_contains_any` を満たす最小の混入点を二分探索的に。

## ⚠️ 改竄防止
このテストは「top を含まない」という**健全性の検査**。`type_contains_any` の判定や
assert を緩めて通すのは厳禁。実際の混入を止めること。
