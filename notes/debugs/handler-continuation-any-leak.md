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
| 期待値（正）| 継続 `k` は**開いた effect 行**（tail 変数つき）で、**入力型 `bool`・出力型 `'a` がちゃんと出る**形。`Any`/top ではない（テストは「nested fun effect 行に Any/top 無し」を検査）|
| 実際値（誤）| `Fun { param: Var(t9), param_effect: Any, ret_effect: Never, ret: Fun{...} }` — 継続 `k` の **param_effect が Any**（＝開いた行が top に潰れている）|

## なぜ期待値が正しいか（※ユーザ訂正 2026-06-06）
**「閉じた `[eff]` になるべき」ではない**。継続 `k` は effect-polymorphic なので、その effect 行は
**開いた行**（tail 変数つき＝後から effect を足せる）であるのが正しい。そのうえで
**入力型 `bool`・出力型 `'a` がちゃんと出てくる**べき。

**おかしいのは `Any`(top) だけ**。top は「何でも起きうる＝情報を全部失った」退化形で、これがここに
乗るのがバグ。期待は「開いた effect 行（入力/出力が正しく出る）」で、それが top に潰れているのを直す
——**行を閉じて直すのではない**。

cf. ④⑤ と同じテーマ。effect 行はこういう位置では**開いているのが自然**で、退化形に潰れるのが病
（④⑤＝裸 Con 区間、⑫＝top）。

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
継続の param_effect がどこで `Any` になるか dump で追い、**開いた effect 行**になるべき所が
top に潰れている地点を特定して直す（**行を閉じるのではない**——開いた行のまま、top を正しい
residual/tail 変数に戻す。入力 `bool`・出力 `'a` が出ること）。`type_contains_any` を満たす
最小の混入点を二分探索的に。

## ⚠️ 改竄防止 / 誤修正防止
- このテストは「top を含まない」という**健全性の検査**。`type_contains_any` の判定や
  assert を緩めて通すのは厳禁。実際の top 混入を止めること。
- **行を閉じて top を消す**のも誤り。開いた effect 行のまま、入力/出力型が出る形で直す。
