# 言語リファレンス

Yulang の top-level 構文、可視性、コメント、詳細な参照先をまとめる。
言語要素を調べるときはこのページから探し、学習順に読むときはガイドを使う。

## プログラムの形

Yulang のプログラムは top-level statement の列である。
statement は宣言と裸の式に分かれ、宣言には `my`、`our`、`pub`、`struct`、`enum`、`act`、`role`、`impl`、`error`、`cast`、`type`、`use`、`mod` がある。
Playground は裸の式を評価して最後の root 値を表示し、CLI では `yulang run --print-roots` が root 式の値を表示する。

## 公開範囲

| Keyword | 意味 |
|---------|------|
| `my`    | private binding。local と top-level のどちらにも置ける |
| `our`   | 囲んでいる companion module へ binding を export する |
| `pub`   | module の外へ binding を export し、Playground の Types pane にも表示する |

## コメント

```yulang
// 通常の line comment。

/* 通常の block comment。 */

-- 単一行 doc comment（line comment ではない）。

---
複数行 doc block。
markdown と ```yulang fence を含められる。
---
```

`//` と `/* ... */` は通常のコメント、`--` と `---` は doc コメントである。
doc コメントは構文木や tooling に残るため、`//` と入れ替えることはできない。

## トピック別

表面の構文

- [構文スタイル](./syntax-style)：括弧を省くタイミングと書き方
- [application と演算子](./application)：`f x` / `f(x)` / `f: x` / `f.method` の違い
- [演算子宣言](./operators)：`infix`、`prefix`、`suffix`、優先順位

値と型

- [値と型](./types)：型の世界
- [文字列](./strings)：文字列の構造、エスケープ、補間
- [パターンマッチ](./patterns)：pattern の全形
- [struct と role](./structs)：`struct`、`with:`、`role`、`impl`
- [cast](./casts)：`cast(x: A): B`、compiler が挿入する場所

計算

- [関数](./functions)：宣言、curry、named 引数
- [制御構文](./control-flow)：`for`、`sub:`、`case`、参照
- [effect](./effects)：`act`、`catch`、handler の形
- [エラー](./errors)：`error`、`fail`、`from`、`up`、`wrap`

スタイル

- [イディオム](./idioms)：Yulang らしい書き方

理論

- [型推論の理論](./type-theory)：推論器が裏で何をしているか

標準ライブラリ

- [中核](./std/core), [list](./std/list), [str](./std/str)
- [opt](./std/opt), [result](./std/result)
- [io::file](./std/fs), [control::nondet](./std/nondet)
