# 例の検査

このガイドの例は、パーサ(`crates/yu-syntax`)に通して確かめる。構文は `syntax-v0` として凍結されているので、
ガイドと実装のズレを、機械で検出できる。

## 検査の道具

```text
cargo run --offline -p yu-syntax --example syntax_guide_check -- syntax-guide/ja/src/
```

- `--quiet`: 要約の表だけを出す。
- `--tree`: 各ブロックの CST(構文木)も出す。
- 構文エラー(recovery の `Error` / `Invalid`)が出ずに読めれば `ok`。`...` を含む断片は `placeholder` で、失敗に数えない。
- 終了コードは、指示と結果が食い違ったときだけ 1。

各 `yulang` コードブロックの直前に、検査の指示をコメントで書ける。

````text
<!-- check: parse-ok -->
<!-- check: parse-error -->
````

`parse-error` は、よくある間違いの例が、本当に構文エラーになることを確かめる指示。

## 確認できること、できないこと

2026-11-07 時点の結果: 33 ブロック中、31 が `ok`、1 が `placeholder`、1 が `recovery`。lambda の record 引数と、record の式の spread は `ok`。`recovery` の 1 件は、パーサがまだ読めない形(対象なしの `case:`)で、`spec/parser-gaps.md` に台帳がある。ガイドの該当箇所にも注記してある。

| 確認できる | 確認できない |
| --- | --- |
| 構文エラーなしで読めること | infix 演算子の**優先順位**の括弧の補い方(`xs \| map f == ys` が `xs \| (map f == ys)` になること)。CST では演算子の鎖が平らなまま |
| 呼び出しの形の**結合**(`f(x)` / `f (x)` / `f: x`、`f xs.map` / `f xs .map`、`xs[0]` / `xs [0]`、`f g(x)` / `f g (x)`)。CST のノードの種類で見分けられる | record か block か(CST の上では、どちらも波括弧のブロックで、区切りの `,` で見分けるしかない) |
| | `shape:` 指示の自動比較(指示は表示するだけ) |

演算子を使う例は、検査の道具が持つ**仮の演算子表**(std の prelude がまだ無いため)で読ませている。結合力の一部は推測なので、
優先順位の確認は、prelude ができてから、演算子を解決する段階で行う。
