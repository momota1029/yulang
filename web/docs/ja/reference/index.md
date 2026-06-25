# 言語リファレンス

Yulang の構文と意味を機能ごとにまとめたページです。言語を学ぶときはガイドへ、
何かを調べるときはこちらへ来てください。

## プログラムの形

Yulang の program は、top-level statement の列です。statement は宣言と式に
分かれ、宣言には `my`、`our`、`pub`、`struct`、`enum`、`act`、`role`、`impl`、
`error`、`cast`、`type`、`use`、`mod` があります。トップレベルに裸の式を書く
と、その式は実行され、CLI / playground の Result pane に表示されます。

## Visibility

| Keyword | 意味 |
|---------|------|
| `my`    | private binding。local でも top-level でも置けます |
| `our`   | public。囲んでいる module の companion から見えます |
| `pub`   | 外部 module へ export。playground の Types pane にも現れます |

## コメント

```yulang
// 通常の line comment。

/* 通常の block comment。 */

-- 単一行 doc comment（line comment ではありません）。

---
複数行 doc block。
markdown と ```yulang fence を含められます。
---
```

`//` と `/* ... */` は通常のコメント、`--` と `---` は doc comment です。
doc comment は構文木や tooling に現れる可能性があり、`//` と入れ替え可能
ではありません。

## トピック別

**表面の構文**

- [構文スタイル](./syntax-style) — 括弧を省くタイミングと書き方
- [適用と演算子](./application) — `f x` / `f(x)` / `f: x` / `f.method` の違い
- [演算子宣言](./operators) — `infix`、`prefix`、`suffix`、優先順位

**値と型**

- [値と型](./types) — 型の世界
- [文字列](./strings) — 文字列の構造、エスケープ、補間
- [パターンマッチ](./patterns) — pattern の全形
- [構造体とロール](./structs) — `struct`、`with:`、`role`、`impl`
- [キャスト](./casts) — `cast(x: A): B`、compiler が挿入する場所

**計算**

- [関数](./functions) — 宣言、curry、named 引数
- [制御構文](./control-flow) — `for`、`sub:`、`case`、参照
- [エフェクト](./effects) — `act`、`catch`、handler の形
- [エラー](./errors) — `error`、`fail`、`from`、`up`、`wrap`

**スタイル**

- [イディオム](./idioms) — Yulang らしい書き方

**理論**

- [型推論の理論](./type-theory) — 推論器が裏で何をしているか

**標準ライブラリ**

- [中核](./std/core), [list](./std/list), [str](./std/str)
- [opt](./std/opt), [result](./std/result)
- [io::file](./std/fs), [control::nondet](./std/undet)
