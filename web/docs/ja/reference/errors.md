# エラー

`error` は、effect として流れる型付きエラーをまとめて宣言する短縮構文である。

## 宣言

```yulang
pub error io_err:
    not_found path
    denied path
    invalid_path path
    failed (path, str)
```

この一行で次のものがまとめて生成される。

- `pub enum io_err` — variant は `not_found path`、`denied path`、
  `invalid_path path`、`failed (path, str)`。
- `pub act io_err` — variant と同名の operation を持ち、戻り値は `never`。
- `impl Throw io_err` — `type throws = '[io_err]` と `our e.throw` を持ち、
  対応する operation を発火する。
- `impl Display io_err` — 既定の文字列化（手書きの impl で上書き可能）。
- `io_err::wrap` — companion module 内のヘルパー。error effect を `result`
  値に閉じる。
- `from` entry がある場合だけ生成される `up` helper。リンクした narrower error を、宣言した error 型に持ち上げる。

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
my missing path = fail (io_err::not_found path)
```

`missing` を呼ぶと `io_err::not_found` が発火し、`fail` によってその error が effect row に現れる。

## 名指しで捕まえる

`catch` の effect arm は、operation 名を直接書いてエラーを捕まえる。

```yulang
my read_text_or_label path = catch read_text path:
    io_err::not_found _, _ -> "(missing)"
    io_err::denied _, _ -> "(denied)"
    value -> value
```

Yulang のエラー設計は **名指しで捕まえる** ことを前提にしている。型を消去した catch-all や、任意の `Display` 実装を runtime dispatch する仕組みはなく、anyhow 型の境界を意図的に提供していない。各 error は effect row の中で具体的な型を保つため、発火元と handler を型から特定できる。

## `wrap`：値に閉じる

```yulang
my read_text_safe path =
    my wrapped = io_err::wrap: read_text path
    case wrapped:
        result::ok text -> text
        result::err err -> err.show
```

`E::wrap` は、引数 thunk が起こす対応 error effect を捕まえて `result _ E`
を返す。`E` に `from` エントリがある場合、`wrap` はリンクされた narrower
error も同時に捕まえ、生成された変換を通じて wrap する。

## `from` による集約

次の抜粋では、parser module が `parse_err` と `parse_json` を定義済みであるとする。

```yulang
pub error app_err:
    file from io_err
    parse from parse_err
```

これにより次のものが生成される。

- variant `app_err::file io_err` と `app_err::parse parse_err`
- `io_err` と `parse_err` から `app_err` への生成済み変換
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
