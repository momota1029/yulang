# エラー

`error` は、effect として流れる型付きエラーをまとめて宣言する短縮構文である。

## 宣言

```yulang
pub error io_err:
    not_found path
    denied path
    invalid_path path
```

この一行で次のものがまとめて生成される。

- `pub enum io_err` — variant は `not_found path` / `denied path` /
  `invalid_path path`。
- `pub act io_err` — variant と同名の operation を持ち、戻り値は `never`。
- `impl Throw io_err` — `type throws = '[io_err]` と `our e.throw` を持ち、
  対応する operation を発火する。
- `impl Display io_err` — 既定の文字列化（手書きの impl で上書き可能）。
- `io_err::wrap` — companion module 内のヘルパー。error effect を `result`
  値に閉じる。
- `io_err::up` — companion module 内の handler。他の error 型が
  `from io_err` を宣言している場合、narrower error を `io_err` の effect に
  持ち上げる。

## constructor と operation は同名

variant 名は **データ構築子と effect operation の両方** として使える。
文脈で必要な側が選ばれる。

```yulang
my err: io_err = io_err::not_found path    // 値として構築
io_err::not_found path                       // effect として発火
```

## `fail` で投げる

`fail` は prelude の prefix 演算子で、`e.throw` を透過的に呼ぶ。

```yulang
pub prefix(fail) = \e -> e.throw
```

構築したエラー値を effect として送り出すときに使う。

```yulang
my read_text_from_host path = read_text path
```

推論型は概ね `path -> [file, io_err] str` の形になり、エラーが effect row に
明示される。

## 名指しで捕まえる

`catch` の effect arm は、operation 名を直接書いてエラーを捕まえる。

```yulang
catch read_text path:
    io_err::not_found _, _ -> "(missing)"
    io_err::denied _, _ -> "(denied)"
    value -> value
```

Yulang のエラー設計は **常に名指しで捕まえる** ことを前提にしている。
`Display` を実行時に dispatch して任意のエラーを文字列化するような型消去の
ラッパー（いわゆる anyhow 的なもの）は意図的に採用していない。各エラーは
effect row の中で常に具体的な名前で見え、発火地点と捕捉地点が型から分かる。

## `wrap`：値に閉じる

```yulang
my read_text_safe path = case io_err::wrap: read_text path:
    result::ok text -> text
    result::err err -> err.show
```

`E::wrap` は、引数 thunk が起こす対応 error effect を捕まえて `result _ E`
を返す。`E` に `from` エントリがある場合、`wrap` はリンクされた narrower
error も同時に捕まえ、生成された `Cast` impl 経由で wrap する。

## `from` による集約

```yulang
pub error app_err:
    file from io_err
    parse from parse_err
```

これにより次のものが生成される。

- variant `app_err::file io_err` と `app_err::parse parse_err`
- `Cast io_err -> app_err` と `Cast parse_err -> app_err` の impl
- `io_err` と `parse_err` も同時に捕まえる拡張版 `app_err::wrap`
- narrower error を `app_err` effect に変換する handler `app_err::up`

```yulang
my read_and_parse path =
    app_err::up:
        my text = read_text path                // [io_err]
        parse_json text                         // [parse_err]
    // block 全体の effect は [app_err]
```

基礎的な変換機構については [Casts](./casts) を、`catch` と effect row の
全般的な話は [Effects](./effects) を参照。
