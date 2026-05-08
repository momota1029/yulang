# 関数

## 宣言

```yulang
my add x y = x + y
```

`my` は private binding を宣言します。`our` と `pub` は現在の module から binding を公開します。
生成された companion module の中では、method や operation を公開するために `our` がよく使われます。

binding の左辺は pattern です。pattern が直接の名前である場合、その後ろに続く pattern が関数引数になります。

```yulang
my x = 1
my add x y = x + y
my (a, b) = (1, 2)
```

複数引数は左から右へ curried function として扱われます。

## 呼び出し

```yulang
add 1 2
add(1, 2)
```

空白による application と、空白なしの C-style call syntax の両方があります。
`add 1 2` と `add(1, 2)` はどちらも curried application へ lower されます。
`f(x)` は call、`f (x)` は grouped expression `(x)` を引数にした whitespace application です。

## Lambda

```yulang
\x -> x + 1
\x y -> x + y
```

lambda は `\` から始まる。複数引数 lambda も curried。

## Record pattern と省略可能引数

```yulang
my area {width = 1, height = 2} = width * height

area { width: 3 }
area {}
area { width: 3, height: 4 }
```

default を持つ record pattern は optional named argument として働く。default は左から右に評価される。

## 型注釈

```yulang
my double(x: int): int = x + x
```

注釈は省略できることが多いが、公開 API や曖昧な場所では書いた方が読みやすい。

effectful な引数や戻り値の型は [エフェクト](./effects) と [値と型](./types) で扱います。
