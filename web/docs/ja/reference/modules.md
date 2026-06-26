# モジュール

`use` による import、`my` / `our` / `pub` の visibility、companion module、ドット選択の解決、標準ライブラリの一覧を扱う。

## `use`

```yulang
use std::control::nondet::*
use std::data::list::map
use std::core::ops::{(+), (-)}
use my_module::old_name as new_name
use noisy::* without debug
```

`use` は module 内の名前を scope へ入れる。`*` は見えているものをまとめて import する。`{...}` による group、`as` による rename、`without` による除外も使える。operator 名は `(+)` のように括弧付きで import できる。

## Realm と band の path

realm は version 付きの解決空間であり、band は realm 内の import / build の島である。
module path は 1 つの band の中にある。

local file では、`realm.toml` のある directory が explicit editable realm になる。
`realm.toml` が見つからない場合は、entry file の親 directory が implicit editable
realm になる。entry file は root module だが、realm root からの相対 file path 由来の
band path も持つ。

```text
main.yu          band main
tools/parser.yu  band tools/parser
```

bare path は current band の中だけを探す。

```yulang
use helper::answer
```

`helper::answer` の same-band lookup が失敗しても、compiler は sibling band として
探し直さない。current realm の別 band を import する場合は `realm/` を使う。

```yulang
use realm/helper::answer
use realm/tools/parser::json::value
```

band 境界の手前は `/`、band root 以後は `::` で区切る。予約 qualifier `band::` は
current band root から始まる。

```yulang
use band::inner::value
```

entry file が `main.yu` の場合、`realm/main::value` は entry root module への alias
になる。`main.yu` を二重に load せず、cross-band cycle としても扱わない。

`std::...` は standard library への prebound alias であり、bare first segment を
same-realm band として fallback 解決する一般規則ではない。

## Companion module

`struct`、`type ... with:`、`enum`、`act`、`error`、`role` は同名の companion module を作る。body 内の `our` / `pub` はそこへ入る。

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point::norm2 (point { x: 3, y: 4 })
point { x: 3, y: 4 } .norm2
```

`enum` と `error` の variant も companion に入る。

```yulang
opt::just 1
io_err::not_found "path"
```

prelude が `just`、`nil`、`ok`、`err` のような標準 variant を reexport するため、通常は修飾名なしで書ける。

`act` の operation も同じ。

```yulang
out::write "hi"
```

## `act copy`

`act copy = source` は、別の `act` から新しい effect family を作る。これは
alias ではない。copy 先 family から出る operation は、copy 元 family の
operation とは別物として扱われる。

copy 元から継承されるのは `pub` / `our` の surface だけである。copy 元 body
の `my` operation や helper member は copy 元 act の private に留まり、copy
先 companion や `with:` body からは見えない。

```yulang
act source:
    my hidden = 1
    our visible = 2

act copy = source with:
    my local = 3
    our own = local
```

`copy` には `visible`、`local`、`own` が入るが、`hidden` は入らない。copy
元の exported member が source-private helper に依存している場合、その copy
は ill-formed になりうる。private helper を copy 経由で持ち出さないことが
visibility の規則である。

## Dot selection

`expr.method` は、まず receiver の型に結び付いた field や method を探し、その後 role method や effect-row method も解決対象にする。

- struct field と `with:` method
- `type ... with:` で定義された method
- `.add`、`.index`、`.show` のような role method
- `.list`、`.logic`、`.once` のような effect-row method

anonymous record の場合、`.field` は record field を取り出す。act operation 自体は、通常 `out::write "hi"` のように path で呼ぶ。

## Standard library modules

| Module | 内容 |
|--------|------|
| `std::prelude` | entry file が通常 import する基本定義、role、operator、std reexport |
| `std::core::ops` | `+`, `-`, `*`, `/`, comparison, `and`, `or`, `not` |
| `std::data::list` | list operations と `Index` impl |
| `std::data::range` | range constructors と `Fold` impl |
| `std::data::opt` | `opt 'a` と、prelude reexport された `nil` / `just` |
| `std::data::result` | `result 'ok 'err` と、prelude reexport された `ok` / `err` |
| `std::text::str` | `str` と indexing |
| `std::control::var` | `ref 'e 'a`、local mutable binding、update helper |
| `std::control::flow` | `sub`, loop control, label loop primitives |
| `std::data::fold` | `Fold` role と default method `.find` / `.contains` |
| `std::control::nondet` | `each`, `guard`, `.list`, `.once`, `.logic` |
| `std::control::junction` | `all`, `any` |
| `std::io::console` | `say`, `println`, `print`, `note`, `eprint`, `warn`, `die` と、背後の `out` / `err` / `warn` / `die` effect |
| `std::io::file` | `read_text`, `read_at`, `open`, `write_text`, `exists`, `is_file`, `is_dir` と `io_err` |
| `std::control::throw` | `Throw` role と `fail` |
| `std::data::index` | `Index` role |
