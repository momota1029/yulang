# 言語リファレンス

Yulang の構文と意味を、機能ごとにまとめる。

## プログラムの形

Yulang の program は、top-level statement の列である。statement には宣言と式がある。

宣言の例:

- `my`
- `our`
- `pub`
- `struct`
- `enum`
- `act`
- `error`
- `role`
- `impl`
- `cast`
- `type`
- `use`
- `mod`

トップレベルに裸の式を書くと、その式は実行され、playground の Result pane に表示される。

## Visibility

| Keyword | 意味 |
|---------|------|
| `my` | private binding。local または top-level に置ける |
| `our` | companion module に公開する |
| `pub` | 外部へ export する。playground の Types pane にも表示される |

## コメント

```yulang
// これは通常の line comment。

/* これは通常の block comment。 */

-- これは単一行 doc comment。

---
これは複数行 doc block。
markdown と ```yulang fence を含められる。
---
```

`//` は通常の line comment、`/* ... */` は通常の block comment である。
`--` と `---` は doc comment なので、構文木や tooling に現れる可能性がある。

## 関連ページ

- [値と型](./types)
- [関数](./functions)
- [制御構文](./control-flow)
- [文字列](./strings)
- [適用と演算子](./application)
- [構文スタイル](./syntax-style)
- [演算子宣言](./operators)
- [構造体とロール](./structs)
- [キャスト](./casts)
- [エフェクト](./effects)
- [エラー](./errors)
- [パターンマッチ](./patterns)
- [モジュール](./modules)
- [イディオム](./idioms)
- 標準ライブラリ：[中核](./std/core), [list](./std/list), [str](./std/str), [opt](./std/opt), [result](./std/result), [undet](./std/undet)
