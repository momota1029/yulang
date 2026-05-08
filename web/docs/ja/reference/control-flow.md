# 制御構文

制御構文は、特に断らない限り式として使えます。

## `if`

```yulang
if x > 0: "positive" else: "non-positive"

if cond:
    a
else:
    b

if cond { a } else { b }
```

`if` の条件は `bool` です。`else` がない場合、false branch は `()` になります。

## `case`

```yulang
case value:
    0 -> "zero"
    n if n < 0 -> "negative"
    _ -> "other"
```

`case` arm は上から順に試されます。guard は pattern の後ろに `if` を書きます。

## `catch`

```yulang
catch action:
    console::read(), k -> k "42"
    value -> value
```

operation arm は operation の payload と continuation `k` を受け取ります。
`k value` を呼ぶと計算を再開します。value arm は通常終了を処理します。

## `for`

```yulang
for x in 0..10:
    println x.show
```

`for x in xs:` は `Fold` を実装する値を走査します。body は関数へ lower され、
plain な `for` expression は `()` を返します。

loop control は prelude から入ります。

```yulang
for x in 0..:
    if x == 10: last
    else: ()
```

`last`、`next`、`redo` は、現在の loop から抜ける、次の反復へ進む、反復をやり直す
ための操作です。

## ラベル

```yulang
for 'outer x in 0..:
    for y in 0..:
        if y == 3: last 'outer
        else: ()
```

labelled loop は label 値を body に渡します。`last 'outer`、`next 'outer`、
`redo 'outer` は、その label の loop を対象にします。

## `sub` と `return`

```yulang
sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0
```

`sub:` は早期 return scope を作ります。`return value` は直近の `sub:` から
抜けます。nullfix の `return` は `()` を返します。

labelled `sub` もあります。

```yulang
sub 'done:
    'done.return 42
    0
```

`sub`、`return`、`last`、`next`、`redo` は標準ライブラリ / prelude の surface
であり、parser 専用 keyword ではありません。

## Block と Lambda

```yulang
{
    my x = 1
    x + 1
}

\x -> x + 1
\x y -> x + y
```

block は statement を順に評価し、最後の式を返します。lambda は `\` で始まり、
複数引数は curried function として扱われます。
