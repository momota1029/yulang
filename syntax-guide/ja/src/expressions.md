# 式の基本

Yulang は式指向で、ここに出る構文はほとんどが値を持つ。この章は、値の書き方、名前の引き方、lambda、`if`、`case` を順に見る。
呼び出しの形(`f(x)` / `f (x)` / `f: x`)と波括弧の読み分けは [空白で意味が変わる形](whitespace.md) に書いた。

## 値の書き方

```yulang
1            // 整数
1.5          // 小数
"hello"      // 文字列
true         // 真偽値
()           // unit
(1, "x")     // tuple
[1, 2, 3]    // list
{x: 1, y: 2} // record
```

状態: 確定(数値の型)・仮採用(他)・パース検査済み。出典: `spec/03-expressions.md` 3.1。

整数は任意精度。小数 literal は 64 ビットの浮動小数点数(IEEE 754 binary64)になる。

### 数値の書き方

```yulang
1_000_000    // 桁区切りの _
0xff         // 16 進
0b1010       // 2 進
0o755        // 8 進
1e3          // 指数
1.5e-2
```

`1.` や `.5` のような省略形は書けない。`1.foo` が method 呼び出しと紛れるため。
小数 literal が無限大に溢れる場合(`1.0e309` など)は、静的にエラーになる。

状態: 確定・パース検査済み。

### list と record の spread

```yulang
[1, ..xs, 3]          // xs の要素をここに展開する
{x: 1, ..rest}        // rest の field をここに展開する
[0, ..(1..10), 11]    // range など、走査できる値も展開できる
```

list の spread は、list だけでなく、走査できる値(`Fold` を実装した値)なら何でも受ける。
状態: 確定。list の spread はパース検査済み。**record の式の spread(`{x: 1, ..rest}`)は、現在のパーサがまだ読めない**(`spec/parser-gaps.md`)。出典: `spec/03-expressions.md` 3.1。

### 文字列

```yulang
"line1\nline2"        // escape
"smile \u{1F600}"     // Unicode escape
"hello %{name}"       // 式の埋め込み
"hex = %x{255}"       // 16 進で埋め込む
"%8.3{text}"          // 幅 8、最大 3 文字
"%*>8{side}"          // fill `*`、右寄せ、幅 8
"%+#08x{255}"         // "+0x000ff"
```

`%{式}` は、式の値を `Display` で文字列にして埋め込む。`%` と `{` の間に、Rust 風の書式指定を置ける。
書式の並びは `%[[fill]align][sign][#][0][width][.precision][kind]{式}`(`kind` は `?` `x` `X`)。

状態: 確定・パース検査済み。

### 複数行の文字列

`"""` で囲むと、複数行の文字列になる。字下げの取り方は、閉じの `"""` がどこにあるかで決まる。

```yulang
my a =
    """
    line1
      line2
    """                  // "line1\n  line2"

my b = """
    line1
      line2"""          // "line1\n  line2"
```

- 閉じの `"""` が**行頭(字下げのみ)に来る**ときは、その字下げを各行から取り除く。
- 閉じの `"""` が最後の行の末尾に付くときは、最初と最後の改行を除き、行の中で一番浅い字下げを取り除く。
- 閉じの `"""` が行頭にあるとき、内容の行にその字下げより浅いものがあれば、エラーになる。

状態: 確定(例の解釈は見直し中)・パース検査済み。

## 名前を引く

```yulang
x                        // 名前
std::data::list::map     // module の path
p.x                      // field、または method
xs[0]                    // index
```

状態: 仮採用・パース検査済み。出典: `spec/03-expressions.md` 3.2。

- 単純な名前は、字句的な局所の名前、module の中の名前、`use` で入れた名前の順に探す。
- `a::b` は module の path。
- `p.x` は field、または method。まず値の型に結びついた field と method を探し、次に role の method と effect の method を探す。
- 存在しない field を読む(`{x: 1}.y`)のは、実行時ではなく、コンパイル時の型エラーになる。

### `xs[0]` と `xs [0]`

`xs[0]` は index で、`xs.index 0` と同じ。`xs [0]` と空白を空けると、`xs` に list literal `[0]` を渡す裸の application になる。
list の index が有効なのは `0 ≤ i < 長さ` のときだけで、**負の index は末尾相対にならない**。無効な index は、名前のある error として起こる。

### `x.foo::bar`

```yulang
x.foo::bar     // foo::bar x(path の先を method として x に適用する)
(x.foo)::bar   // field を取ってから path を進む
```

状態: 確定・パース検査済み。

## lambda

```yulang
\x -> x + 1
\x y -> x + y     // \x -> \y -> x + y と同じ
```

`\pat -> body`。引数には名前だけでなく pattern を書ける。複数並べると、カリー化された lambda になる。
引数に書けるのは、必ず成功する pattern(tuple・record・`_`・名前)だけ。`\(just x) -> x` のように失敗しうるものは、エラーになる(`case` を使う)。

```yulang
\(a, b) -> a + b
\{x, y} -> x + y     // 現在のパーサは、この行を読めない(下の注を見る)
\_ -> 0
```

状態: 仮採用。`\(a, b)` と `\_` はパース検査済み。**`\{x, y} -> ...`(record の分解)は、現在のパーサがまだ読めない**(`spec/parser-gaps.md`)。出典: `spec/03-expressions.md` 3.4。

## ブロックと `with`

```yulang
{
    my x = 1
    x + 1
}
```

ブロックは文を順に評価し、最後の式が値になる。**式は、書いた順(左から右、上から下)に評価される**。tuple の成分も、関数の引数も、record の field も同じ。

### 式の `with:`

```yulang
my area r = pi * r * r with:
    our pi = 3.14159         // our なので、本体から見える
    my unused = 1            // my なので、本体からは見えない
```

`target with:` の下に書いた binding は、`target` から見える局所の名前になる。Haskell の `where` に近い。
`our` と `pub` はどちらも本体から見える。`my` は `with:` の中だけ。

状態: 確定・パース検査済み。出典: `spec/03-expressions.md` 3.5。

## `if`

```yulang
if n < 0: "negative"
elsif n == 0: "zero"
else: "positive"

if cond { a } else { b }
```

`if` は式で、条件は真偽値。条件は上から順に試す。`else` が無いとき、式全体は `opt` になる。

```yulang
if cond: do_something()          // 結果は opt unit。文として使える
my r = if x > 0: x               // opt int(通れば just x、通らなければ nil)
```

状態: 仮採用・パース検査済み。出典: `spec/03-expressions.md` 3.6。

## `case`

```yulang
case n:
    0 -> "zero"
    x if x < 0 -> "negative"
    _ -> "positive"
```

arm は上から順に試す。最初に pattern が合って、guard が真になった arm が選ばれる。guard は pattern の後ろに `if` で書き、pattern が束縛した名前を使える。
arm の本体が複数の文のときは、`->` の後ろで改行して字下げする。波括弧でも書ける。

```yulang
case n:
    0 -> "zero"
    x ->
        my y = x * 2
        y + 1
```

どの arm にも合わない場合がありうるなら、エラーになる(網羅性の検査)。

### `case:`(対象なし)

`case:` と書くと、一引数の関数ができる。`\x -> case x:` の略。

```yulang
my handle = case:
    ok res -> res
    err e  -> fail_page e
```

パイプライン(次の節)の右辺や、関数を渡す場所に置ける。

状態: `case:` は確定、パース検査済み。他の `case` はパース検査済み(仮採用)。出典: `spec/03-expressions.md` 3.7。

## パイプライン `|`

```yulang
"data" | parse | render     // render (parse "data")
xs | map f                  // map f xs
```

`x | f` は、左辺の値を右辺の**最後の引数**にする。`|` の結合力は全演算子の中で一番弱いので、左辺は `and` / `or` を含む式全体になる。
詳しくは [演算子は宣言で決まる](operators.md) を見る。

## この章で扱っていないもの

- 名前の分解や `my` の分割代入 → pattern の章(予定)。
- `for` / `last` / `next`、`sub` / `return`、`$x` と `&x` → 制御構文の章(予定)。
- `catch` と effect、parser DSL → それぞれの章(予定)。`catch` は spec にも要確認が残っている。
