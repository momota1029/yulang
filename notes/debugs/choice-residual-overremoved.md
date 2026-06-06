# ⑧ choice の残差 effect 行が消えすぎる（保留・①の後）

## テスト
`tests::choice_effect_residual_coalesces_across_open_rows` — `crates/yulang-infer/src/tests.rs`
（失敗 assert は `open_row_residual` helper 内 `tests.rs:2950`、"p return effect should have one row"）

## 入力（抜粋）
```yu
pub choice(p: () -> [parse ...] 'a, q: () -> [parse ...] 'a): [parse ...] 'a =
    my snap = parse::snapshot()
    catch p():
        parse::fail e, _ if parse::is_cut() -> parse::fail e
        parse::fail e1, _ ->
            parse::restore snap
            catch q(): parse::fail e2, _ -> parse::fail: e1.merge e2
```

## バグ表
| | |
|---|---|
| 期待値（正）| p の return effect は **1 行**（残差 row を 1 本持つ）。p_residual == q_residual == result_residual |
| 実際値（誤）| p の return effect の row 数が **0**（tests.rs:2950 で left=0 right=1）|

## なぜ期待値が正しいか
`choice` は p/q を catch して `parse::fail` を 1 つだけ handle、残りの parse effect は素通し。
よって p/q/result の return effect は共通の残差 row を 1 本ずつ持つはず（3 つが同じ residual var）。
0 行は「素通しの parse effect が消えた」＝過剰除去。

## 診断（仮説なし・要調査）
memory `infer-test-pass-2026-06-06` ⑧: 残差 row が消えすぎ。ユーザも手がかり無しで保留扱い。
①（cooccur 過剰マージ）と同根（残差 effect の極性／共起の扱い）の可能性はあるが未確認。

## 進め方（①の後回し）
**①を直してから再測定**する。①の修正で連動して直るかもしれない。
①後にこのテストを単独再測定し、まだ 0 行なら残差抽出を dump で追う。
仮説が立つまでコードを触らない（闇雲な変更は禁止）。

## 見るべき場所
- effect row の compact 化・残差抽出（`crates/yulang-infer/src/simplify/compact.rs`,
  `crates/yulang-infer/src/solve/effect_row.rs`）
- `open_row_residual` が見る `ty.rows`（tests.rs:2946-2956）がどこで空になるか

## ⚠️ 改竄防止
"should have one row" の 1 は choice のセマンティクスから確定。**期待を 0 に下げて通すのは厳禁**。
