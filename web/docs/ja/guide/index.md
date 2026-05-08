# はじめに

Yulang は、role ベースの多相と代数的エフェクトを持つ、実験段階の静的型付き言語です。
この文書は最終仕様ではなく、現在のコンパイラと標準ライブラリの挙動を説明します。

::: tip Playground
このページの例は <a href="/" target="_self">Playground</a> でそのまま試せる。
:::

## Yulang の軸

Yulang には通常の関数とユーザー定義演算子があります。そのうえで、いくつかの基本機能も
ユーザー定義に近い形で表されます。

- `+`、`return`、`last`、`or` などは parser 専用の builtin ではなく、標準 prelude から export されます。
- interface は `role` で宣言し、`impl` で型ごとに実装します。
- effect は `act` で宣言し、operation として呼び、`catch` で処理します。

```yulang
act console:
    our read: () -> int

our ask() = console::read()

our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console(k 42)

run_console:
    ask()
```

`ask` は `console` エフェクトを要求します。`run_console` はそのエフェクトを捕まえ、
型から取り除きます。

## まず覚える概念

- program は statement の列です。トップレベル式は CLI/playground で評価・表示されます。
- binding の左辺は pattern です。`my f x = ...` は名前と引数 pattern を持つ binding、`my (a, b) = pair` は分解です。
- `my $x = ...` で可変 binding を作り、`$x` で読み、`&x = v` で書きます。
- `role` は interface です。`impl` で型ごとに実装します。
- `x: [console] int` のような型は、`int` を返す effectful computation を表します。`catch` は effect operation を処理します。
- `struct` / `enum` / `act` / `error` / `role` は、method、variant、operation などを置く companion module を作ります。
- `//` は通常コメントです。`--` と `---` は doc comment です。

## 次に読むもの

- [ツアー](./tour) — Yulang の主要機能を一通り見る
- [リファレンス](/ja/reference/) — 構文と意味の詳細
- <a href="/" target="_self">Playground</a> — 実際に動かす
