# 章3c 制御構文・参照

状態の凡例は [README](README.md)。この章は `for` / `last` / `next` / `redo`、`sub` / `return`、label、`$x` / `&x`、`do` を扱う。
これらは標準ライブラリ（prelude）の面と、少数の構文でできている。parser 専用の予約語ではないものが多い。
effect と handler の意味は章5 に回す。

## 3c.1 `for`　〔閉区間は確定、他は要確認〕

```yulang
for x in 0..10:
    say x
```

- `for x in xs:` は `Fold` を実装する値を走査する。body は関数に落ち、`for` 式そのものは `()` を返す。
- **`0..10` は閉区間**（11 回反復する）。半開区間は `0..<10`。意図した仕様（確定, 2026-11-04）。

```yulang
for x in 0..<10:     // 10 回
    say x
```

出典: `main:web/docs/ja/reference/control-flow.md` §for
注意: 閉区間が既定なのは Rust や Python と逆なので、罠に当たる（T5）。

## 3c.2 `last` / `next` / `redo`　〔確定〕

```yulang
for x in 0..:
    if x == 10: last      // ループを抜ける
```

- `last` は現在のループから抜ける。`next` は次の反復へ進む。`redo` は同じ反復をやり直す。
- これらは prelude で定義された演算子で、`loop` effect の操作を呼ぶ。予約語ではない。
- **使える場所の制限はない。** `last` などは普通の effect の操作で、**handler を作れば捕まえられる**。
  `for` は自分用の handler を持っているので `for` の中で効くだけ。`sub:` は `return` だけを捕まえ、`last` / `next` / `redo` は**捕まえない**。
  （確定, 2026-11-04）

```yulang
for x in 0..:
    sub:
        if x == 3: last     // sub は last を捕まえないので、外側の for に届く
        say x
```

## 3c.3 label　〔`sub` の形は確定、他は要確認〕

```yulang
for 'outer x in 0..:
    for y in 0..:
        if y == 3: last 'outer
```

- label は `'outer` のように `'` で始める。`last 'outer` / `next 'outer` / `redo 'outer` は、その label のループを対象にする。
- `sub` の label の形は **`'done.return 42` に一本化する**（確定, 2026-11-04）。
  label は値で、`.return` はその label に対する操作。`return 'done 42` という別の綴りは仕様に採らない。
- `last` / `next` / `redo` の label の形（`last 'outer` のままか、`'outer.last` にそろえるか）は未決定（確認 M1）。
- 現在のパーサ（yu-syntax）は、`for` の見出しの label しか読めない。式の中の `'x` は未実装（[パーサの未実装](parser-gaps.md)）。

## 3c.4 `sub` と `return`　〔要確認〕

```yulang
sub:
    for x in 0..:
        if x == 5: return x
    0
```

- `sub:` は早期 return の範囲を作る。`return value` は直近の `sub:` から抜ける。値なしの `return` は `()` を返す。
- label 付きの `sub` もある。`'done.return 42` の形に一本化する（3c.3）。

```yulang
sub 'done:
    'done.return 42
    0
```

- 深い入れ子の代わりに、`sub:` と `return` で成功経路を平らに保つのが推奨の書き方。

出典: `main:web/docs/ja/reference/control-flow.md`、`main:web/docs/ja/reference/idioms.md`

## 3c.5 `case` と `catch` の label（再帰）　〔要確認〕

`case 'label value:` と `catch 'label action:` は、arm の集合全体に再帰の名前を付ける。body から `'label next` を呼ぶと、同じ arm 集合が `next` に再適用される。

```yulang
my result = case 'count 3:
    0 -> "done"
    n -> 'count (n - 1)
```

- label は個々の arm ではなく、arm 集合に属する。

出典: `main:web/docs/ja/reference/control-flow.md` §case と catch のラベル

## 3c.6 局所の参照 `$x` と `&x`　〔要確認〕

```yulang
my incremented =
    my $count = 0
    &count = $count + 1
    $count
```

- `my $count = 0` は局所の可変な参照を作る。`$count` は読み出し、`&count = value` は更新。
- これらは handled な `var` effect に展開される。したがって、更新は**型システムから見える**（effect 行に `var` が乗る）。
  参照は宣言された scope の中で使い、外部の可変変数として扱わない。
- State は純粋な継続スレッディングで実現される（メモリ上の穴ではない）。

出典: `main:web/docs/ja/guide/pitfalls.md`「参照は effect、メモリ穴ではない」、`main:web/docs/ja/reference/idioms.md`

## 3c.7 `do`　〔確定〕

`do` は、**後ろに続く文を継続（lambda）として切り出し、`do` の位置に渡す**印（確定, 2026-11-04）。
`my 名前 = 式` の右辺に `do` を書くと、`名前` が lambda の引数になり、残りの文が本体になる。

```yulang
my a = f(g do)
b
// 同じ意味:
f(g \a -> b)
```

```yulang
my x = effectful do
rest
// 同じ意味:
effectful \x -> rest
```

- 継続は `do` を含む最も内側の呼び出し（上の例では `g`）の引数になる。`f(...)` の括弧の中に収まる。
- effectful な API を、見た目上は direct style で書くための構文。

## 3c.8 effectful な条件　〔章5 へ〕

`if` の条件が非決定的な場合（`all` / `any`）は、`std::control::junction` が提供する effectful な真偽値として扱われる。
通常の `bool` の条件は通常の経路を通る。意味は章5 で書く。

## 確認してほしい点

- **M1** `last` / `next` / `redo` の label は、`'outer.last` のように `'done.return` とそろえるか。`case` / `catch` の label（3c.5）の呼び出し形 `'count (n - 1)` も、同じ流儀（`'count.…`）にそろえるか。
