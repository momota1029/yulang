# ツアー

Yulang の主要機能を短く巡るページです。すべての例は <a href="/" target="_self">Playground</a> で実行できます。

## 基本

```yulang
1 + 2
```

トップレベルに式を書くと、その値が実行結果に表示されます。binding は `my` で定義します。

```yulang
my double x = x + x
double 21
```

`my` は private、`our` は companion module に公開、`pub` は外部へ export します。

## 構造体

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
```

`struct` は nominal な record type です。`with:` block には companion module へ入る method を書けます。
`our p.norm2` の `p` は receiver 名で、`point` の値に対する `.norm2` として呼べます。

## 省略可能引数

record pattern の default は、named optional argument として使えます。

```yulang
my area {width = 1, height = 2} = width * height

area { width: 3 }
area {}
area { width: 3, height: 4 }
```

default は左から右へ評価され、前の field を参照できます。

```yulang
my f {a = 1, b = a + 1, c = b + 1} = (a, b, c)
f {}             // (1, 2, 3)
f { a: 10 }      // (10, 11, 12)
```

## 可変 binding と参照

`my $x = ...` は可変 binding を作ります。`$x` は読み取り、`&x = v` は書き込みです。

```yulang
my $x = 10
&x = $x + 1
$x
```

同じ `&` 形式は field や index にも使えます。

```yulang
my $xs = [2, 3, 4]
&xs[1] = 6
$xs
```

## 非決定性

`std::undet` の `each` は選択を作ります。`.list` はすべての結果を集めます。

```yulang
(each [1, 2, 3] + each [4, 5, 6]).list
```

`.once` は最初に見つかった結果を `opt` で返します。無限の選択では、前の選択を使って後の範囲を絞ると、探索が早く結果に到達します。

```yulang
{
    my a = each 1..
    my b = each a<..
    my c = each b<..

    guard: a * a + b * b == c * c

    (a, b, c)
} .once
```

## Junction

`all` と `any` は collection 全体に比較を持ち上げます。

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    1
else:
    0
```

## エフェクト

`act` は effect interface を宣言します。operation は普通の関数のように呼び、`catch` で処理します。

```yulang
act console:
    our read: () -> int

our ask() = console::read()

our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console(k 42)

run_console:
    ask()
```

handler arm の `k` は continuation です。`k value` を呼ぶと、operation の呼び出し位置へ値を返して計算を再開します。

## ループと早期 return

`for x in xs:` は `Fold` を実装する値を走査します。list や range は標準で対応しています。
`sub:` は早期 return scope を作り、`return value` が直近の `sub:` から抜けます。

```yulang
sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0
```

`last` / `next` / `redo` は loop control です。prelude から operator として入ります。

## エラー

`error` は enum と effect operation 群を同時に作る糖衣です。

```yulang
error fs_err:
    not_found str
    denied str
    invalid_path str
```

`fs_err::not_found "path"` は、文脈によって data constructor としても、throwing operation としても読めます。
別の error へまとめる場合は `from` を使います。

```yulang
error io_err:
    fs from fs_err
```

## コメント

```yulang
// 通常の line comment

-- doc comment

---
複数行の doc comment
---
```

`--` は普通のコメントではなく doc comment なので、通常のメモには `//` を使います。
