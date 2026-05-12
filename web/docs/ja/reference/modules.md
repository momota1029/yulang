# モジュール

`use` による import、`my` / `our` / `pub` の visibility、companion module、ドット選択の解決、標準ライブラリの一覧を扱う。

## `use`

```yulang
use std::undet::*
use std::list::map
use std::ops::{(+), (-)}
use my_module::old_name as new_name
use noisy::* without debug
```

`use` は module 内の名前を scope へ入れる。`*` は見えているものをまとめて import する。`{...}` による group、`as` による rename、`without` による除外も使える。operator 名は `(+)` のように括弧付きで import できる。

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
fs_err::not_found "path"
```

prelude が `just`、`nil`、`ok`、`err` のような標準 variant を reexport するため、通常は修飾名なしで書ける。

`act` の operation も同じ。

```yulang
console::println "hi"
```

## Dot selection

`expr.method` は、まず receiver の型に結び付いた field や method を探し、その後 role method や effect-row method も解決対象にする。

- struct field と `with:` method
- `type ... with:` で定義された method
- `.add`、`.index`、`.show` のような role method
- `.list`、`.logic`、`.once` のような effect-row method

anonymous record の場合、`.field` は record field を取り出す。act operation 自体は、通常 `console::println "hi"` のように path で呼ぶ。

## Standard library modules

| Module | 内容 |
|--------|------|
| `std::prelude` | entry file が通常 import する基本定義、role、operator、std reexport |
| `std::ops` | `+`, `-`, `*`, `/`, comparison, `and`, `or`, `not` |
| `std::list` | list operations と `Index` impl |
| `std::range` | range constructors と `Fold` impl |
| `std::opt` | `opt 'a` と、prelude reexport された `nil` / `just` |
| `std::result` | `result 'ok 'err` と、prelude reexport された `ok` / `err` |
| `std::str` | `str` と indexing |
| `std::var` | `ref 'e 'a` と update helper |
| `std::flow` | `sub`, loop control, label loop primitives |
| `std::fold` | `Fold` role と default method `.find` / `.contains` |
| `std::undet` | `each`, `guard`, `.list`, `.once`, `.logic` |
| `std::junction` | `all`, `any` |
| `std::console` | `print`, `println` |
| `std::fs` | 暫定 filesystem API |
| `std::error` | `Throw` role |
| `std::index` | `Index` role |
