# 章8 エラー・標準ライブラリの境界

状態の凡例は [README](README.md)。この章は、`error` の使い方（宣言は章5.7）と、**言語と標準ライブラリの境界**を扱う。
標準ライブラリの個々の API（`list`、`str`、`file` など）の仕様は、この `spec/` の対象外。ここでは「何が言語で、何が std か」だけを決める。

## 8.1 エラーは名指しで捕まえる　〔要確認〕

```yulang
my read_text_or_label path = catch read_text path:
    io_err::not_found _, _ -> "(missing)"
    io_err::denied _, _ -> "(denied)"
    value -> value
```

- エラーは **effect として流れ**、`catch` の arm で operation 名を書いて**名指しで**捕まえる。
- 型を消去した catch-all（`catch _ -> ...`）や、任意の `Display` を実行時に dispatch する仕組みは**ない**。anyhow 風の境界は意図的に提供しない。
- 各エラーは effect 行の中で具体的な型を保つので、発火元と handler を型から特定できる。

## 8.2 `fail`　〔要確認〕

```yulang
my missing path = fail (io_err::not_found path)
```

- `fail` は prelude の prefix 演算子で、`\e -> e.throw` と同じ。特別な構文ではない（`e.throw` と書いても動く）。
- エラー値を effect として送り出すときに使う。読みやすさのために選ぶ。

## 8.3 `wrap`: エラー effect を値に閉じる　〔要確認〕

```yulang
my wrapped = io_err::wrap: read_text path
case wrapped:
    result::ok text -> text
    result::err err -> err.show
```

- `E::wrap` は、引数の thunk が起こす `E` の effect を捕まえて、`result _ E` を返す。

## 8.4 `from` と `up`: エラーを集約する　〔要確認〕

```yulang
pub error app_err:
    file from io_err
    parse from parse_err

my read_and_parse path =
    app_err::up:
        my text = read_text path        // [io_err]
        parse_json text                 // [parse_err]
    // block 全体の effect は [app_err]
```

- `from` 付きの variant は、narrower なエラーを包む variant と、そこへの変換規則（章6.5 の cast）を作る。
- `E::wrap` は、リンクされた narrower なエラーも同時に捕まえる。
- `E::up` は、narrower なエラーを `E` の effect に変換する handler。

出典: `main:web/docs/ja/reference/errors.md`

## 8.5 言語と標準ライブラリの境界　〔線引きは確定〕

| 言語（`spec/` の対象） | 標準ライブラリ（対象外） |
| --- | --- |
| 構文、`mod` / `use`、可視性、型、`act` / `catch`、`role` / `impl`、`cast`、`error` 宣言の展開 | `list`、`str`、`opt`、`result`、`file` などのデータ型と API |
| 演算子の**宣言の仕組み**（章1.5） | **標準の演算子表**（`+`、`==`、`and` など）。prelude が定義する |
| effect と handler の意味 | `sub` / `return`、`last` / `next` / `redo`（`std::control::flow`）、`nondet`、`junction`、`throw` |
| `Fold` を使う `for` の構文 | `Fold` role と range |

- 通常の entry file は、prelude を暗黙に import する（`use std::prelude::*`）。prelude を無効にする設定もある。
- `sub`・`return`・`last` などは**予約語ではなく**、prelude が再公開する名前（章3c）。
- 標準ライブラリの安定性は段階が分かれる（stable / provisional / experimental）。
- 言語の構文が前提にする std の最小限（`Fold`、`Index` など）は、`spec/` に書く（確定, 2026-11-04）。
- 標準 API の仕様（file、server、instant など）は、この `spec/` に**取り込む**（確定, 2026-11-04）。素材は `main:spec/2026-07-01-*`、`2026-07-02-*`。章は標準ライブラリの章として後で立てる。

出典: `main:web/docs/ja/reference/std/index.md`、`main:web/docs/ja/reference/errors.md`

## 確認してほしい点

なし（K1・K2 は反映済み）。
