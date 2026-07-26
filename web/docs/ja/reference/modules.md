# module

このページでは、`use`、realm と band の path、companion module、dot selection、標準ライブラリの module map を扱う。

## `use`

次の抜粋は import 構文を示す。
`my_module` と `noisy` は、プログラム側が用意する module を表す。

```yulang
use std::control::nondet::*
use std::data::list::map
use std::core::ops::{(+), (-)}
use my_module::old_name as new_name
use noisy::* without debug
```

`use` は module 内の名前を scope へ入れる。
`*` は見えているものをまとめて import する。
`{...}` による group、`as` による rename、`without` による除外も使える。
演算子名は `(+)` のように括弧付きで import できる。

## Realm と band の path

realm は version 付きの解決空間であり、band は realm 内の import / build の島である。
module path は 1 つの band の中にある。

local ファイルでは、`realm.toml` のある directory が explicit editable realm になる。
`realm.toml` が見つからない場合は、entry ファイルの親 directory が implicit editable realm になる。
entry ファイルは root module だが、realm root からの相対ファイル path 由来の band path も持つ。

```text
main.yu          band main
tools/parser.yu  band tools/parser
```

bare path は current band の中だけを探す。

```yulang
use helper::answer
```

`helper::answer` の same-band lookup が失敗しても、compiler は sibling band として探し直さない。
current realm の別 band を import する場合は `realm/` を使う。

```yulang
use realm/helper::answer
use realm/tools/parser::json::value
```

install 済み local realm を import する場合は `local/` provider prefix を使う。

```yulang
use local/theme/colors::palette v1.0.0
```

editable realm は次のように install できる。

```toml
[realm]
name = "theme"
version = "1.0.0"
```

```sh
yulang realm install .
```

band 境界の手前は `/`、band root 以後は `::` で区切る。
予約 qualifier `band::` は current band root から始まる。

```yulang
use band::inner::value
```

entry ファイルが `main.yu` の場合、`realm/main::value` は entry root module への alias になる。
`main.yu` を二重に load せず、cross-band cycle としても扱わない。

`std::...` は標準ライブラリへの prebound alias であり、bare first segment を same-realm band として fallback 解決する一般規則ではない。

## Companion module

`struct`、`type ... with:`、`enum`、`act`、`error`、`role` は同名の companion module を作る。
body 内の `our` / `pub` はそこへ入る。

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point::norm2 (point { x: 3, y: 4 })
// または、同じ意味の dot selection
point { x: 3, y: 4 } .norm2
```

`enum` と `error` の variant も companion に入る。

```yulang
opt::just 1
io_err::not_found "path"
```

prelude が `just`、`nil`、`ok`、`err` のような標準 variant を reexport するため、通常は修飾名なしで書ける。

`act` の operation も companion member である。
`std::io::console` では、`out::write "hi"` のように呼び出す。

```yulang
out::write "hi"
```

## `act copy`

`act copy = source` は、別の `act` から新しい effect family を作る。
これは alias ではない。
copy 先 family から出る operation は、copy 元 family の operation とは別物として扱われる。

copy 元から継承されるのは `pub` / `our` の surface だけである。
copy 元 body の `my` operation や helper member は copy 元 act の private に留まり、copy 先 companion や `with:` body からは見えない。

```yulang
act source:
    my hidden = 1
    our visible = 2

act copy = source with:
    my local = 3
    our own = local
```

`copy` には `visible`、`local`、`own` が入るが、`hidden` は入らない。
copy 元の exported member が source-private helper に依存している場合、その copy は ill-formed になりうる。
private helper を copy 経由で持ち出さないことが可視性の規則である。

## Dot selection

`expr.method` は、まず receiver の型に結び付いた field や method を探し、その後 role method や effect-row method も解決対象にする。

- struct field と `with:` method
- `type ... with:` で定義された method
- `.add`、`.index`、`.show` のような role method
- `.list`、`.logic`、`.once` のような effect-row method

anonymous record の場合、`.field` は record field を取り出す。
act operation 自体は、通常 `out::write "hi"` のように path で呼ぶ。

## 標準ライブラリ module

| Module | 内容 |
|--------|------|
| `std::prelude` | entry ファイルが通常 import する `Add`、`Eq`、`Ord`、`Display`、`len`、`id`、`compose`、`last` / `next` / `redo`、`return`、`fail`、range 演算子、core std reexport |
| `std::core::ops` | `+`, `-`, `*`, `/`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `and`, `or`, `not` |
| `std::data::list` | `map`、`filter`、`fold`、`sort`、`cons`、`uncons`、`rev`、`append` などの list operation |
| `std::data::range` | range constructors と `Fold` impl |
| `std::data::opt` | `opt 'a` と、prelude reexport された `nil` / `just` |
| `std::data::result` | `result 'ok 'err`、prelude reexport された `ok` / `err`、`map`、`and_then`、`unwrap_or` |
| `std::text::str` | `str` 型と `Index` impl |
| `std::control::var` | `ref 'e 'a`、local mutable binding support、update helper |
| `std::control::flow` | `sub`、`loop`、label-loop primitive |
| `std::data::fold` | `.fold` と default method `.find` / `.contains` を持つ `Fold` role |
| `std::control::nondet` | `each`、`guard`、`list`、`once`、`logic` |
| `std::control::junction` | effectful comparison の `all`、`any` |
| `std::io::console` | `say`, `println`, `print`, `note`, `eprint`, `warn`, `die` と、背後の `out` / `err` / `warn` / `die` effect |
| `std::io::file` | `read_text`、`write_text`、`text`、`text_with`、`exists`、`is_file`、`is_dir` と `io_err` エラー |
| `std::control::throw` | `Throw` role と `fail` support |
| `std::data::index` | `Index` role |
