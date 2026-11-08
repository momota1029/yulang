# 章3c 制御構文・参照

状態の凡例は [README](README.md)。この章は `for` / `last` / `next` / `redo`、`sub` / `return`、label、`$x` / `&x`、`do` を扱う。
これらは標準ライブラリ（prelude）の面と、少数の構文でできている。parser 専用の予約語ではないものが多い。
effect と handler の意味は章5 に回す。

## 3c.1 `for`　〔閉区間は確定、他は仮採用〕

```yulang
for x in 0..10:
    say x
```

- `for x in xs:` は `Fold` を実装する値を走査する。`Fold` を実装した型なら何でも走査できる（list・range・`str`・map・`opt` など。ユーザー定義型も `impl Fold` を書けば回せる。確定, 2026-11-04）。`0..` のような上限のない range も `Fold` なので回せ、`last` で抜けるのは書き手の責任。body は関数に落ち、`for` 式そのものは `()` を返す。
- `for` 式の値は常に `()`（確定, 2026-11-04）。`last` は値を取らない。値を返したいときは `sub:` と `return` で包む。
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
- `for x in xs: body` は、標準ライブラリの `loop::for_in xs (\x -> body)` に展開される（確定, 2026-11-06。実装は `main:lib/std/control/flow.yu`）。`for_in` が `last` / `next` / `redo` の handler を持ち、`xs.fold` で各要素を走査する。
  - `last`: 走査全体を抜ける。
  - `next`: 今回の反復を終えて、次の要素へ進む。
  - `redo`: **同じ要素 `x` で、本体を最初から**やり直す。それまでの副作用は巻き戻さない。
- label 付きの `for 'outer x in xs: body` は `label_loop::for_in` に展開され、label は `last` / `next` / `redo` を持つ値として本体に渡される。
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

## 3c.3b label を受け取る値 `labeled`　〔考え方は確定、記法は仮採用〕

label を「渡す形」と「渡さない形」を、特別な型や複製された関数（`f#labeled` など）を作らずに、一つの関数で扱うための規則。

- **`sub 'done:` は、label を束縛するラムダを受け取る関数の呼び出しである**（確定, 2026-11-08, ユーザーの説明）。`sub 'done: body` は `sub \'done -> body` と同じ。同じく `for 'label x in xs: body` は `xs.for \'label x -> body` と同じ。label は、ラムダ引数として字句的に束縛される名前で、衛生性（章5.4）は、この束縛で説明される。
- **label を受け取る値の型は、普通の enum `labeled('l, 'a)` である**（確定, 2026-11-08, ユーザーの説明）。二つのバリアントを持つ。`labeled` は label を受け取る関数 `'l -> 'a` を包み、`raw` は label を受け取らない普通の値 `'a` を包む。特別な矢印の型は作らない。バリアントと型の名前は仮。
- **`'a` から `labeled('l, 'a)` へ cast できる**（`raw` に包む）（確定, 2026-11-08）。cast は 6.5 の cast と同じ規則で、**その型が求められたときにだけ**入る。`'a <: labeled(...)` が求められるのは上界の位置だけで、それ以外の位置に `labeled` が現れることはない。したがって、`labeled` の二重 cast は起きない。型が求められなければ、何も変換されない（漸進的型付けで、境界の型に合わせて変換が入る形と似ている）。
- **label が指定されているかは、この enum のパターンマッチで観察できる**（確定, 2026-11-08）。観察は、関数が引数の型を `labeled('l, 'a)` と宣言したときだけ起きる（`Option` を受け取る関数と同じで、opt-in）。`sub` や `for` は、`raw` の値を受け取った場合は label を作らずに済ませてよい（実行の最適化。意味は変わらない）。
- **`raw` への cast の実行時の費用は、消去・無視である**（確定, 2026-11-08）。型が静的に分かるなら、enum の印も消せる。
- **label は同時に一つだけ受け取る**（確定, 2026-11-08）。label は制御構造のものなので、`labeled` を入れ子にして複数の label を受け取る形は想定しない。
- **label の型は自由で、持ち出してよい**（確定, 2026-11-08）。持ち出した label は、それを受ける handler が無いので使えない。使おうとすると、その label の操作（`return`、`last`、`next`、`redo`、`again`）の effect が、**処理されない effect として静的に報告される**（行に出る）。実行時に落ちる形にはしない。受ける handler は label の identity で決まる。同じ型の別の `sub` の内側で、前の `sub` の label を使っても、そちらには受けられない。
- **仮採用・未決**: enum の宣言の記法、バリアント名、`\'l ->` という束縛子の記法、label への application の形（`v 'label`）、パターンの形、`labeled` の variance、`return` のように label を省略する形が最も近い `sub` を指す規則との関係。構想の経緯は `notes/ideas/2026-11-08-label-receiving-values.md`。
- 核の計算体系（Lean）での扱い: この機能は M1 の後に、核の型付けと衛生性の定理に足す（`notes/plan/m1-plan.md` の T11）。

## 3c.4 `sub` と `return`　〔仮採用〕

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

## 3c.5 `case` と `catch` の label（再帰）　〔仮採用〕

`case 'label value:` と `catch 'label action:` は、arm の集合全体に再帰の名前を付ける。body から `'label next` を呼ぶと、同じ arm 集合が `next` に再適用される。

```yulang
my result = case 'count 3:
    0 -> "done"
    n -> 'count.again (n - 1)      // 再帰。`again 'count (n - 1)` とも書ける
```

- 再帰は `last` / `return` と同じ流儀で、label の操作として呼ぶ（確定, 2026-11-04。操作の名前は `again`）。素材の `'count (n - 1)` の形は採らない。
- label は個々の arm ではなく、arm 集合に属する。

出典: `main:web/docs/ja/reference/control-flow.md` §case と catch のラベル

## 3c.6 局所の参照 `$x` と `&x`　〔仮採用〕

```yulang
my incremented =
    my $count = 0
    &count = $count + 1
    $count
```

- 参照を作るのは `my $count = 0`（初期値から新しい参照を作る）と `my &count = &other`（既にある参照 `other` を別名で束縛する）の 2 つの形だけ（確定, 2026-11-04）。普通の `my n = 0` は不変の値で、`$n` / `&n` は書けない。

- `my $count = 0` は局所の可変な参照を作る。`$count` は読み出し、`&count = value` は更新。
- 参照は第一級の値で、関数に渡すことも、関数から返すことも自由にできる（確定, 2026-11-04）。scope の中で複数の変数から 1 つを選んで返す、といった処理を書けるようにするため。

```yulang
my incr &r = &r = $r + 1       // 参照を引数に取る
my pick c &a &b = if c: &a else: &b     // 選んだ参照を返す
```

- 参照の束縛は、`my $a = a; b` が `&a::run a (\&a -> b)` の形に直される（確定, 2026-11-04）。`&a::run` が handler で、`b` が `&a` を受け取る lambda の本体になる。
  したがって、`&a` を scope の外へ持ち出しても、対応する handler がないので、変数操作の effect が global に出てきて回収されず、型エラーになる。参照専用の「脱出検査」があるわけではなく、ふつうの未処理の effect として現れる。
  `&a` を `&a::run` とペアにして外へ出せば、クロージャに近い操作ができる。
- `&a::run` は利用者が直接呼んでよい（確定, 2026-11-04）。`my $a = ...` は糖衣で、同じことを手で書ける。

```yulang
&a::run 0 (\&a ->
    &a = $a + 1
    $a)
```

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
通常の `bool` の条件は通常の経路を通る。意味は章5.9 に書いた。

## 確認してほしい点

なし（M2 は G1・G2 で解決: `'count.again (n - 1)`）。
