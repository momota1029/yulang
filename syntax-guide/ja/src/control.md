# 制御構文と参照

この章は、繰り返し(`for`)、そこからの脱出(`last` / `next` / `redo`、`sub` / `return`)、label、局所の参照(`$x` / `&x`)、`do` を見る。
これらの多くは、**予約語ではなく、標準ライブラリ(prelude)が定義する名前**でできている。effect と handler の意味は spec の章5 に任せる。

## `for`

```yulang
for x in 0..10:
    say x
```

`for x in xs:` は、`Fold` を実装した値を走査する。list・range・`str`・map・`opt` など、`Fold` を実装した型なら何でも回せる。ユーザー定義型も、`impl Fold` を書けば回せる。
body は関数に落ちる。**`for` 式の値は、常に `()`**。値を返したいときは、`sub:` と `return` で包む(下で説明する)。

### 範囲は閉区間

```yulang
for x in 0..10:      // 11 回(0 から 10 まで)
    say x

for x in 0..<10:     // 10 回(0 から 9 まで)
    say x
```

`0..10` は**閉区間**。半開区間は `0..<10`。Rust や Python の既定と逆なので、気を付ける。
`0..` のように上限のない range も回せる。抜けるのは書き手の責任(`last` を使う)。

状態: 閉区間は確定。他は仮採用。パース検査済み。出典: `spec/03c-control.md` 3c.1。

## `last` / `next` / `redo`

```yulang
for x in 0..:
    if x == 10: last      // ループを抜ける
```

| 名前 | 意味 |
| --- | --- |
| `last` | 現在のループから抜ける |
| `next` | 次の反復へ進む |
| `redo` | **同じ要素**で、本体を最初からやり直す(それまでの副作用は戻らない) |

これらは prelude で定義された名前で、`loop` effect の操作を呼ぶ。`for x in xs: body` は、標準ライブラリの `loop::for_in xs (\x -> body)` に展開される。
`for_in` が `last` / `next` / `redo` の handler を持つので、`for` の中でだけ効く。使える場所に構文上の制限は無く、handler を作れば自分で捕まえられる。

```yulang
for x in 0..:
    sub:
        if x == 3: last     // sub は last を捕まえないので、外側の for に届く
        say x
```

`sub:` は `return` だけを捕まえ、`last` / `next` / `redo` は捕まえない。
状態: 確定・パース検査済み。出典: `spec/03c-control.md` 3c.2。

## label

```yulang
for 'outer x in 0..:
    for y in 0..:
        if y == 3: last 'outer
        if y == 4: 'outer.last      // 同じ意味
```

- label は `'outer` のように `'` で始める。label は値で、操作を `.` で付けて呼べる。
- 操作は 2 つの形で書ける。意味は同じ。
  - label を値として使う形: `'done.return 42`、`'outer.last`、`'outer.next`、`'outer.redo`
  - 演算子の形: `return 'done 42`、`last 'outer`、`next 'outer`、`redo 'outer`

状態: 形は確定・パース検査済み。出典: `spec/03c-control.md` 3c.3。

## `sub` と `return`

```yulang
sub:
    for x in 0..:
        if x == 5: return x
    0
```

`sub:` は、早期 return の範囲を作る。`return value` は、直近の `sub:` から抜ける。値なしの `return` は `()` を返す。

```yulang
my find_negative xs =
    sub:
        for x in xs:
            if x < 0: return x
        0
```

- 関数や lambda に**暗黙の `sub` は無い**。`return` は、それを呼んだ地点を囲んでいる直近の `sub:` が受け取る。
- 呼ばれた関数の中で `return` しても、呼び出し元の `sub:` の中なら、そこへ抜ける(effect の通常の動作)。囲む `sub:` が全く無ければ、`return` の effect が受け手なしで残り、型に現れる。

```yulang
my check x = if x < 0: return x      // check の中の return

sub:
    check -1                          // この sub を抜ける
    "unreachable"
```

### label 付きの `sub`

どの `sub:` に届くかを、名前で決めたいときは、label を付ける。

```yulang
sub 'done:
    'done.return 42
    0
```

ライブラリの作者は、label 付き(`sub 'done:` と `'done.return`)で、自分の範囲を閉じられる。深い入れ子の代わりに、`sub:` と `return` で成功の経路を平らに保つのが、推奨の書き方。
状態: 仮採用・パース検査済み。出典: `spec/03c-control.md` 3c.4。

## `case` と `catch` の label(再帰)

`case 'label value:` と `catch 'label action:` は、arm の集合全体に再帰の名前を付ける。body から `'label.again x` を呼ぶと、同じ arm の集合が `x` に再適用される。

```yulang
my result = case 'count 3:
    0 -> "done"
    n -> 'count.again (n - 1)      // 再帰。`again 'count (n - 1)` とも書ける
```

label は、個々の arm ではなく、arm の集合に属する。
状態: 仮採用・パース検査済み。出典: `spec/03c-control.md` 3c.5。

## 局所の参照: `$x` と `&x`

```yulang
my incremented =
    my $count = 0
    &count = $count + 1
    $count
```

- `my $count = 0` は、局所の可変な参照を作る。`$count` は読み出し、`&count = value` は更新。
- 参照を作る書き方は 2 つだけ。`my $count = 0`(初期値から新しい参照を作る)と、`my &count = &other`(既にある参照を別名で束縛する)。普通の `my n = 0` は不変の値で、`$n` / `&n` は書けない。
- 参照は第一級の値で、関数に渡すことも、返すことも自由にできる。

```yulang
my incr &r = &r = $r + 1       // 参照を引数に取る
my pick c &a &b = if c: &a else: &b     // 選んだ参照を返す
```

### 参照は effect で、メモリの穴ではない

`my $a = a; b` は、`&a::run a (\&a -> b)` の形に直される。`&a::run` が handler で、`b` が `&a` を受け取る lambda の本体になる。
そのため、`&a` を scope の外へ持ち出すと、対応する handler が無いので、変数操作の effect が回収されずに残り、型エラーになる。`&a::run` は利用者が直接呼んでよい。

```yulang
&a::run 0 (\&a ->
    &a = $a + 1
    $a)
```

更新は、型システムから見える(effect 行に `var` が乗る)。State は純粋な継続のやり取りで実現される。
状態: 仮採用・パース検査済み。出典: `spec/03c-control.md` 3c.6。

## `do`

`do` は、**後ろに続く文を継続(lambda)として切り出し、`do` の位置に渡す**印。
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

継続は、`do` を含む**最も内側の呼び出し**(上の例では `g`)の引数になる。`f(...)` の括弧の中に収まる。
effect を使う API を、見た目では上から下へ書く形(direct style)で書くための構文。
状態: 確定・パース検査済み。出典: `spec/03c-control.md` 3c.7。

## この章で扱っていないもの

- `if` の条件が非決定的な場合(`all` / `any`、junction)→ spec の章5.9。
- `catch` の handler の意味と、effect の「引ける」条件 → spec の章5。
