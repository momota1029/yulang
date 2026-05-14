# 制御構文

制御構文は、特に断らない限り式として使える。

## `if`

```yulang
if x > 0: "positive" else: "non-positive"

if cond:
    a
else:
    b

if cond { a } else { b }
```

`if` の条件は `bool` である。`else` がない場合、false branch は `()` になる。

## `case`

```yulang
case value:
    0 -> "zero"
    n if n < 0 -> "negative"
    _ -> "other"
```

`case` arm は上から順に試される。guard は pattern の後ろに `if` を書く。

## `catch`

```yulang
catch action:
    console::read(), k -> k "42"
    value -> value
```

operation arm は operation の payload と continuation `k` を受け取る。`k value` を呼ぶと計算を再開する。value arm は通常終了を処理する。

## `for`

```yulang
for x in 0..10:        // 11 回反復: 0..10 は閉区間 (半開は 0..<10)
    println x.show
```

`for x in xs:` は `Fold` を実装する値を走査する。body は関数へ lower され、plain な `for` expression は `()` を返す。

loop control は prelude から入る。

```yulang
for x in 0..:
    if x == 10: last
    else: ()
```

`last`、`next`、`redo` は、現在の loop から抜ける、次の反復へ進む、反復をやり直すための操作である。

## ラベル

```yulang
for 'outer x in 0..:
    for y in 0..:
        if y == 3: last 'outer
        else: ()
```

labelled loop は label 値を body に渡す。`last 'outer`、`next 'outer`、`redo 'outer` は、その label の loop を対象にする。

## `sub` と `return`

```yulang
sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0
```

`sub:` は早期 return scope を作る。`return value` は直近の `sub:` から抜ける。nullfix の `return` は `()` を返す。

labelled `sub` もある。

```yulang
sub 'done:
    'done.return 42
    0
```

`sub`、`return`、`last`、`next`、`redo` は標準ライブラリ / prelude の surface であり、parser 専用 keyword ではない。

## Block と Lambda

```yulang
{
    my x = 1
    x + 1
}

\x -> x + 1
\x y -> x + y
```

block は statement を順に評価し、最後の式を返す。lambda は `\` で始まり、複数引数は curried function として扱われる。
