# ⑧ choice の残差 effect 行が消えすぎる（保留・①の後）

## テスト
`tests::choice_preserves_parse_residual_on_callback_and_result_effects` — `crates/yulang-infer/src/tests.rs`

最初の失敗 assert は rendered type の callback effect 数を見る。2026-06-07 時点の actual:

```text
(unit -> α) -> (unit -> α) -> [parse<β, γ, δ, ε>] α
```

`p` / `q` callback が `unit -> α` に潰れており、表示上も parse effect が消えている。
ここを直した後、同じテスト内の compact 構造チェックで
`p_residual == q_residual == result_residual` を確認する。

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
| 期待値（正）| rendered type の p/q callback は parse effect を持つ。compact では p_residual == q_residual == result_residual |
| 実際値（誤）| rendered type が `(unit -> α) -> (unit -> α) -> [parse<β, γ, δ, ε>] α` になり、p/q callback effect が消える |

## なぜ期待値が正しいか
`choice` は p/q を catch して `parse::fail` を 1 つだけ handle、残りの parse effect は素通し。
よって p/q/result の return effect は共通の残差 row を 1 本ずつ持つはず（3 つが同じ residual var）。
`unit -> α` は「素通しの parse effect が消えた」＝過剰除去。

## 診断（仮説なし・要調査）
memory `infer-test-pass-2026-06-06` ⑧: 残差 row が消えすぎ。ユーザも手がかり無しで保留扱い。
①（cooccur 過剰マージ）と同根（残差 effect の極性／共起の扱い）の可能性はあるが未確認。

## 進め方（①の後回し）
**①を直してから再測定**する。①の修正で連動して直るかもしれない。
①後にこのテストを単独再測定し、まだ callback effect が消えるなら残差抽出を dump で追う。
仮説が立つまでコードを触らない（闇雲な変更は禁止）。

## 見るべき場所
- effect row の compact 化・残差抽出（`crates/yulang-infer/src/simplify/compact.rs`,
  `crates/yulang-infer/src/solve/effect_row.rs`）
- `callback_parse_residual` が見る `ty.rows` がどこで空になるか

## ⚠️ 改竄防止
`p` / `q` callback が parse effect を持つことは choice のセマンティクスから確定。
**期待を `(unit -> α) -> (unit -> α) -> ...` に下げて通すのは厳禁**。
