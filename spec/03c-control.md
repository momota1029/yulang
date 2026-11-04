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

## 3c.3 label　〔形は確定、`case` / `catch` の再帰の形は未決定〕

```yulang
for 'outer x in 0..:
    for y in 0..:
        if y == 3: last 'outer
        if y == 4: 'outer.last      // 同じ意味
```

- label は `'outer` のように `'` で始める。label は値で、操作を `.` で付けて呼べる。
- **操作は 2 つの形で書ける**（確定, 2026-11-04）。意味は同じ。
  - label を値として使う形: `'done.return 42`、`'outer.last`、`'outer.next`、`'outer.redo`
  - 演算子の形: `return 'done 42`、`last 'outer`、`next 'outer`、`redo 'outer`
- `sub 'done:` は、label `'done` を body に渡す。
- `case` / `catch` の arm 集合の再帰（3c.5）は、label の操作として `'count.again (n - 1)` と書く（確定, 2026-11-04）。
- パーサ（yu-syntax）は、式の中の `'x` を読める（2026-11-04）。見出し（`for` / `case` / `catch`）の label は従来どおり。

## 3c.4 `sub` と `return`　〔要確認〕

```yulang
sub:
    for x in 0..:
        if x == 5: return x
    0
```

- `sub:` は早期 return の範囲を作る。`return value` は直近の `sub:` から抜ける。値なしの `return` は `()` を返す。
- `return` は effect の操作で、関数や lambda に暗黙の `sub` はない（確定, 2026-11-04）。`return` は、実行時にそれを呼んだ地点を囲んでいる直近の `sub:` が受け取る。
  呼ばれた関数の中で `return` しても、呼び出し元の `sub:` の中ならそこへ抜ける。囲む `sub:` が全くなければ、`return` の effect が受け手なしで残り、型に現れる（章5）。

```yulang
my find_negative xs =
    sub:
        for x in xs:
            if x < 0: return x
        0
```

- 呼ばれた関数の中の `return` が、呼び出し元の `sub:` に届くのは意図した動き（確定, 2026-11-04）。effect の通常の動作で、直近の handler が受け取る。
  これを驚きにしないのが衛生性（hygiene）の役割で、どの `sub:` に届くかは名前や label の束縛で決まる。ライブラリの作者は label 付き（`sub 'done:` と `'done.return`）で閉じられる。

```yulang
my check x = if x < 0: return x      // check の中の return

sub:
    check -1                          // この sub を抜ける
    "unreachable"
```

- label 付きの `sub` もある。`'done.return 42` と `return 'done 42` のどちらでも書ける（3c.3）。

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
    n -> 'count.again (n - 1)      // 再帰。`again 'count (n - 1)` とも書ける
```

- 再帰は `last` / `return` と同じ流儀で、label の操作として呼ぶ（確定, 2026-11-04。操作の名前は `again`）。素材の `'count (n - 1)` の形は採らない。
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

- **M2** `case 'count 3:` や `catch 'again 3:` の body から、arm 集合を再適用するときの書き方（現行は `'count (n - 1)`）は、`'count.…` のような流儀にそろえるか、このままか。
