# 例の検査

このガイドの例は、パーサ(`crates/yu-syntax`)に通して確かめる。構文は `syntax-v0` として凍結されているので、
ガイドと実装のズレを、機械で検出できる。

## 検査の形(予定)

各 `yulang` コードブロックの直前に、検査の指示をコメントで書く。

````text
<!-- check: parse-ok -->
```yulang
f(x)
```

<!-- check: parse-ok; shape: App(f, x) -->
```yulang
f (x)
```
````

- `parse-ok`: 構文エラー(recovery の `Error` / `Invalid`)が出ずに読める。
- `parse-error`: 構文エラーになる(よくある間違いの例)。
- `shape`: 構文木の結合の形が、書いたとおりになる(括弧を補った形と比べる)。

## 状態

検査の道具は、まだ無い。作る仕事は、`yu-syntax` の `ParsedFile` を使う小さな Rust の道具(1 ファイルの構文を読み、
recovery の有無と、結合の形を出す)。完成するまでは、各例に「未検査」と書く。
