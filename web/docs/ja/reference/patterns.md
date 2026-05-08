# パターンマッチ

## `case`

```yulang
case value:
    0 -> "zero"
    n -> "other"
```

arm は上から順に試され、最初に match した arm の body が評価される。

## Pattern

| Pattern | 意味 |
|---------|------|
| `_` | wildcard |
| `x` | 名前へ bind |
| `42`, `"hi"`, `true`, `false` | literal |
| `(a, b)` | tuple |
| `{ x, y }` | record |
| `[]`, `[1, 2]`, `[x, ..rest]` | list |
| `just x`, `nil` | prelude から reexport された enum variant |
| `opt::just x`, `opt::nil` | qualified path で書く enum variant |
| `tag x` | unambiguous な短い enum variant |

`[x, ..rest]` は head と tail を分解します。list pattern の spread は middle や
head にも置けます。record pattern に書いた field は、default がない限り必須です。
record pattern でも残り field の spread を扱えます。

## Guard

```yulang
case n:
    0 -> "zero"
    x if x < 0 -> "negative"
    _ -> "positive"
```

guard が false の arm は skip される。

## Record pattern default

関数引数の record pattern は default を持てる。

```yulang
my f {x = 0, y = 0} = x + y
```

これは optional argument として動く。default は左から右へ評価され、前の field を参照できる。

## Enum pattern

```yulang
enum color = red | green | blue

case c:
    color::red -> 0
    color::green -> 1
    color::blue -> 2
```

variant は enum の companion module に入る。`use color::*` した場合は短い名前でも使える。
