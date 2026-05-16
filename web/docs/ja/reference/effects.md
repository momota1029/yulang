# エフェクト

Yulang の副作用は algebraic effect として扱う。effect は宣言され、呼び出され、handler で処理され、型に追跡される。

## 宣言

```yulang
act console:
    our read: () -> str
    our println: str -> ()
```

`act` は effect interface を作る。operation は `our` または `pub` の signature として並べる。同名の companion module が作られ、`console::read` のように参照できる。

## 呼び出し

```yulang
say "hello"
my line = console::read()
```

effect operation は普通の関数のように呼べる。呼び出した関数の型には、その effect が残る。

## Handler

```yulang
our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console(k "42")
    console::println _, k -> run_console(k ())
```

`catch expr:` は handler である。operation arm は operation の引数と continuation `k` を受け取る。`k value` を呼ぶと、operation の場所へ値を返して計算を続ける。

handler は effect row から処理済み effect を取り除く。たとえば `action` が `[console; e] 'a` のような computation type を持つなら、`run_console action` は残りの effect だけを持ち、`'a` を返す。

### handler は shallow

Yulang の handler は **shallow** である。arm は一度だけ operation を受け取り、
`k` で再開された計算は同じ handler に自動では包まれない。再開後に同じ
effect を起こしても、handler は二度目に発火せず、effect はそのまま外側へ
伝播する。

operation を連続で受けたいときは、arm 側で continuation を再度 handler で
包む書き方をする。

```yulang
our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console (k "42")    -- ← run_console で巻き直す
    console::println _, k -> run_console (k ())
    v -> v
```

このリファレンスの handler 例の多くがこの自己再帰形なのはそのため。
operation が 1 度しか起きない前提なら再帰を省ける。effect を繰り返し起こす
任意の計算を扱うときは再帰が必須。

## Effect row

```yulang
[console; e] str
() -> [console; e] str
```

`[...]` の中に effect を並べる。`; e` は残りの effect を表す row variable である。`[_]` は annotation 内で推論に任せるための placeholder として使えるが、effect row type そのものの標準形ではない。

effect は型引数を持つこともできる。

```yulang
act ref_update 'a:
    our update: 'a -> never
```

そのため row には `ref_update int` のような entry も入る。型表示では Greek variable が出ることがあるが、source annotation では row tail に `e` のような名前を使うのが普通。

effect-row method は nominal value companion ではなく、receiver の effect row から選ばれる。

```yulang
use std::undet::*

(each [1, 2, 3]).list
```

同じ row 内の複数の effect が同名 method を持つ場合、row が絞られるまで selection は ambiguous になる。

## Propagation

effectful な関数を呼ぶと、その effect は外側へ伝播する。handler を置いた場所でだけ取り除かれる。

```yulang
our ask() = console::read()

our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console(k "42")
```

## `error` 宣言

`error` は、`enum`、throwing operation を持つ `act`、`impl Throw`、`wrap` / `up` companion helper をまとめて生成する短縮構文である。

```yulang
error fs_err:
    not_found str
    denied str
    invalid_path str
```

各 variant は data constructor と effect operation の両方として使われる。値として必要な文脈では `fs_err` の値になり、effect として必要な文脈では `fs_err` effect を発火する operation になる。

`fail`、名指し catch、`wrap`、`from` 集約、`up` の使い方を含む全体像は [エラー](./errors) を参照。

通常の `enum` variant でも `from` は使える。[キャスト](./casts) を参照。

## 関連

- [値と型](./types) — function type と effect row の表示。
- [型推論の理論](./type-theory) — handler が effect を消す規則と hidden evidence。
