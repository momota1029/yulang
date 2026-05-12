# エフェクト

Yulang の副作用は algebraic effect として扱います。effect は宣言され、
呼び出され、handler で処理され、型に追跡されます。

## 宣言

```yulang
act console:
    our read: () -> str
    our println: str -> ()
```

`act` は effect interface を作ります。operation は `our` または `pub` の
signature として並べます。同名の companion module が作られ、
`console::read` のように参照できます。

## 呼び出し

```yulang
println "hello"
my line = console::read()
```

effect operation は普通の関数のように呼べます。呼び出した関数の型には、
その effect が残ります。

## Handler

```yulang
our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console(k "42")
    console::println _, k -> run_console(k ())
```

`catch expr:` は handler です。operation arm は operation の引数と
continuation `k` を受け取ります。`k value` を呼ぶと、operation の場所へ値を
返して計算を続けます。

handler は effect row から処理済み effect を取り除きます。たとえば
`action` が `[console; e] 'a` のような computation type を持つなら、
`run_console action` は残りの effect だけを持ち、`'a` を返します。

## Effect row

```yulang
[console; e] str
() -> [console; e] str
```

`[...]` の中に effect を並べます。`; e` は残りの effect を表す row variable
です。`[_]` は annotation 内で推論に任せるための placeholder として使えますが、
effect row type そのものの標準形ではありません。

effect は型引数を持つこともできます。

```yulang
act ref_update 'a:
    our update: 'a -> never
```

そのため row には `ref_update int` のような entry も入ります。型表示では Greek
variable が出ることがありますが、source annotation では row tail に `e` のような
名前を使うのが普通です。

effect-row method は nominal value companion ではなく、receiver の effect row から
選ばれます。

```yulang
use std::undet::*

(each [1, 2, 3]).list
```

同じ row 内の複数の effect が同名 method を持つ場合、row が絞られるまで selection
は ambiguous になります。

## Propagation

effectful な関数を呼ぶと、その effect は外側へ伝播します。handler を置いた
場所でだけ取り除かれます。

```yulang
our ask() = console::read()

our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console(k "42")
```

## `error` 宣言

`error` は、`enum`、throwing operation を持つ `act`、`impl Throw`、
`impl Display`、`wrap` / `up` companion helper をまとめて生成する短縮構文です。

```yulang
error fs_err:
    not_found str
    denied str
    invalid_path str
```

各 variant は data constructor と effect operation の両方として使われます。
値として必要な文脈では `fs_err` の値になり、effect として必要な文脈では
`fs_err` effect を発火する operation になります。

`fail`、名指し catch、`wrap`、`from` 集約、`up` の使い方を含む全体像は
[エラー](./errors) を参照。

通常の `enum` variant でも `from` は使えます — [キャスト](./casts) を参照。
