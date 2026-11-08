# 章3 式

状態の凡例は [README](README.md)。この章は式の骨格を扱う。**pattern は [章3b](03b-patterns.md)**、effect と handler の意味は章5 に回す。
`do` / `sub` / `return` / `for` / `last` / `next` / `redo` / `$x` / `&x` は、制御構文として別にまとめる（章3c）。
Yulang は式指向で、ここに出る構文はほとんどが式として値を持つ。

## 3.1 literal　〔数値型は確定、他は仮採用〕

```yulang
1            // integer
1.5          // float
"hello"      // string
true         // bool
()           // unit
(1, "x")     // tuple
[1, 2, 3]    // list
{x: 1, y: 2} // record
```

- 波括弧の読み分け（確定, 2026-11-04）: 先頭が名前で、`,` が付いたら record、それ以外は block。
  理由は、`;` は式の意味を変える（文の区切り）が `,` は変えないため。
  field が 1 つの record は末尾に `,` を付けて `{x: 1,}` と書く。`{x: 1}` は block（値は `x: 1`、つまり `x 1` の application）。
  値を省略した field（`{x, y}` は `{x: x, y: y}`）を認める。1 つだけなら `{x,}`。`{x}` は block で、値は `x`。
  spread だけが入った波括弧（`{..rest}`）は record（確定, 2026-11-07。spread は文としては意味を持たない）。

```yulang
{x: 1, y: 2}     // record
{x: 1,}          // field が 1 つの record
{x, y}           // {x: x, y: y}
{x,}             // {x: x}
{x: 1}           // block（x: 1 は application）
{x}              // block（値は x）
{}               // 空の record
{;}              // 空の block（値は unit）。`()` と書いてもよい
```

- list は spread を持つ: `[1, ..xs, 3]`。record も spread を持つ: `{x: 1, ..rest}`。
- **list の spread の対象は、list に限らず、任意の `Fold` を実装した値**（確定, 2026-11-06）。`[0, ..(1..10), 11]` のように、range や、ユーザー定義の `Fold` の値を直接 spread できる。spread は、その値を走査順に辿って、要素を新しい list へ入れる。`for`（章3c.1）と同じ `Fold` の role 解決・辞書・effect を使うので、走査が起こす effect は、その式の effect 行に載る。無限の `Fold` を spread すると、構築は終わらない（`for` と同じ）。式は書いた順に評価される（上記）。

- 文字列は `"..."` で、`\n` などの escape と `\u{1F600}` の Unicode escape を使える。`"""` で囲んだ複数行の文字列もある。
- 複数行文字列の字下げ（確定, 2026-11-04。例の解釈は要見直し）:
  - 閉じの `"""` が**行頭（字下げのみ）に来る**ときは、その字下げを基準にして各行から取り除く。
  - 閉じの `"""` が行頭に来ない（最後の行の末尾に付く）ときは、最初と最後の改行を除き、行の中で一番小さい字下げを各行から取り除く（ブロックとして読む）。

```yulang
my a =
    """
    line1
      line2
    """                  // "line1\n  line2"（閉じの字下げ 4 を取る）

my b = """
    line1
      line2"""          // "line1\n  line2"（最小の字下げ 4 を取る）
```

  - 閉じ `"""` が行頭にあるとき、内容の行にその字下げより浅いものがあればエラー（確定, 2026-11-04）。

- 式の埋め込みは `%{式}` で、値を `Display` role で文字列にする（確定, 2026-11-04）。`%` と `{` の間に Rust 風の書式指定を置ける。

```yulang
"hello %{name}"
"hex = %x{255}"          // 16 進
"%8.3{text}"             // 幅 8、最大 3 文字
"%*>8{side}"             // fill `*`、右寄せ、幅 8
"%+#08x{255}"            // "+0x000ff"
```

  書式の並びは `%[[fill]align][sign][#][0][width][.precision][kind]{式}`（`kind` は `?` `x` `X`）。詳細は main の `web/docs/ja/reference/strings.md` が素材で、`str` の API は標準ライブラリの章で扱う。

- 数値 literal は桁区切りの `_`（`1_000_000`）、`0x` `0b` `0o` の進数、指数（`1e3`、`1.5e-2`）、小数を書ける。`1.` や `.5` のような省略形は書けない（`1.foo` が method 呼び出しと紛れるため）（確定, 2026-11-04）。

- `int` は**任意精度**、`1.5` のような小数 literal は `float`（確定, 2026-11-04）。
- **`float` は IEEE 754 binary64**（確定, 2026-11-06）。小数 literal は、有限の範囲内なら最近接・偶数丸めで `float` の値になる。丸めた結果が有限なら受理され（`1.7976931348623158e308` は最大有限値に丸まる）、**無限大へ溢れる literal（`1.0e309` など）は静的にエラー**になる（確定, 2026-11-06）。無限大が欲しいときは、名前のついた定数を使う。厳密な値が欲しいときは、標準ライブラリの有理数の型を使う（`int` から `float` への変換は、有理数を経由する cast として std が登録する。`frac`）。

出典: `main:notes/design/yulang-language-report.md` §6.1
`float` の精度と string の書式は、型と標準ライブラリの章で扱う。

## 3.2 名前・path・field　〔`x.foo::bar` は確定、他は仮採用〕

```yulang
x
std::data::list::map
p.x
xs[0]
```

- 単純な名前は、字句的な local、module scope、`use` で入れた名前の順に探す。
- `a::b` は module path。
- 存在しない field を読む（`{x: 1}.y`）のはコンパイル時の型エラーで、実行時エラーにはしない（確定, 2026-11-04）。
- `p.x` は field selection、または method。まず receiver の型に結びついた field と method を探し、次に role の method と effect 行の method を探す。
- `xs[0]` は index で、`xs.index 0` のように field selection と application に落ちる。`[ ]` は `Index` role の `index` への糖衣で、`Index` を実装した型なら何でも使える（list・map・`str` など）。
  list の index が有効なのは `0 ≤ i < length` のときだけで、**負の index は無効**である（末尾相対にはしない。確定, 2026-11-06）。`[10, 20][-1]` は有効な位置を指さない。無効な index（範囲外、空の list、負）は、**名前つきの error effect** として起こる（確定, 2026-11-06）。`xs[i]` の型の effect 行にその error が載り、`catch` で捕まえられ、`wrap` で `result` に戻せる（章5.7）。型は重くなるが、利用者が書かなければならない型は少ない。error が増えたときにまとめて扱う仕組み（`errors` のようなもの）は、将来の拡張として検討する。
  effect の名前と payload は確定（確定, 2026-11-06）: `error index_err: out_of_range int`。payload は無効だった index で、負の index・空の list・上限超過のどれも、同じ operation で扱う。
  `xs [0]` と空白を空けると、`xs` に list literal `[0]` を適用する裸 application になり、index にはならない（`f(x)` と `f (x)` の区別と同じ。確定, 2026-11-04）。
- `x.foo::bar` は「`foo::bar` を `x` に適用する」method の糖衣（`foo::bar x`）で、field を取ってから path を進む意味ではない（確定, 2026-11-04）。
  field を取ってから path を進みたいときは `(x.foo)::bar` と括弧で包む。同名の method が複数あるときに、path で指定して呼ぶ用途が想定される（用途は推測）。

出典: `main:notes/design/yulang-language-report.md` §6.2、`main:web/docs/ja/reference/modules.md` §Dot selection

## 3.3 application　〔仮採用〕

呼び出しの形は 4 つあり、**どれも同じカリー化された application に落ちる**。違うのは表記と結合の仕方だけ。

```yulang
f x y            // ((f x) y)    ML 風: 空白で並べる
f(x, y)          // ((f x) y)    C 風: callee と ( の間に空白がない
x.method y       // ((x.method) y)
f: body          // body 全体を 1 つの引数にする
```

- `f()` は空の引数リストではなく、unit `()` を 1 つ適用する（確定, 2026-11-04）。引数なしの関数という概念はなく、副作用や遅延が欲しいときは unit を受ける関数で書く。`hello` と `hello()` は別物。

```yulang
my hello () = "hi"
hello()          // 呼ぶ
hello            // 関数そのもの（呼ばれない）
```
- 空白は意味を持つ（`f(x)` と `f (x)` と `f: x` は別。章1.4）。
- `.` / `::` / `(...)` / `[...]` の後置と ML の並置は、prelude のどの infix 演算子よりも強く結合する。

```yulang
1 + f x          // 1 + (f x)
not x.field      // not (x.field)
```

- 前置演算子（`-` や `not`）は application より弱い（確定, 2026-11-04）。`-f x` は `-(f x)`、`not f x` は `not (f x)`、`-x.abs` は `-(x.abs)`。

- 並置の右辺では、空白の直前で止まる。そのため `f g(x)` は `f (g(x))`、`f g (x)` は `(f g) x`。

出典: `main:web/docs/ja/reference/application.md`

## 3.4 lambda　〔仮採用〕

```yulang
\x -> x + 1
\x y -> x + y     // \x -> \y -> x + y
```

- `\pat -> body`。引数は名前に限らず pattern を書ける。複数並べるとカリー化された lambda になる。
- 引数に書ける pattern は irrefutable（必ず成功するもの）だけ（確定, 2026-11-04）。tuple・record・`_`・名前は書けて、`\(just x) -> x` のように失敗しうるものはエラー（`case` を使う）。`my` の分解と同じ規則。

```yulang
\(a, b) -> a + b
\{x, y} -> x + y
\_ -> 0
```

出典: `main:notes/design/yulang-language-report.md` §6.4

## 3.5 block と `with`　〔仮採用〕

```yulang
{
    my x = 1
    x + 1
}

target with:
    our helper = ...
```

- block は文を順に評価し、最後の式が値になる。
- **式は、書いた順（左から右、上から下）に評価される**（確定, 2026-11-06）。tuple の成分、関数の引数、record の field（と spread）、`let` の右辺→本体のどれも同じである。値を使わない式も、評価はされる。
- 式の `with:` は Haskell の `where` に近い（確定, 2026-11-04）。`target with:` の下に書いた binding 群は、`target`（tail）から見える局所の名前になる。式の `with` は companion を足すものではない。

```yulang
my area r = pi * r * r with:
    our pi = 3.14159         // our なので、本体 pi * r * r から見える
    my unused = 1            // my なので、本体からは見えない（with: の中だけ）
```

- `with:` の中で `our` / `pub` を付けた binding は tail から見え、`my` を付けたものは見えない（確定, 2026-11-04）。
  `with:` の中では `our` と `pub` に違いはない（どちらも tail から見えるだけ）。
- `with:` の中の `our` 同士は順番を問わず参照できる（確定, 2026-11-04）。値制限を受けるもの（関数適用を含む式）だけは、値制限を受けるもの同士の上下を入れ替えるとエラーになる。lambda・literal・constructor など値制限を受けないものは、どこに置いてもエラーにならない。

```yulang
my area r = c * r with:
    our c = base * 2          // 関数適用（演算）を含む → 値制限を受ける
    our base = 3              // literal → 値制限を受けない。下にあってもよい
    our d = f 1               // 値制限を受ける
    our f = \x -> x          // lambda → 受けない。下にあってもよい
```

  （上の `c` と `d` を入れ替えるとエラー、`base` と `f` の位置は自由、というのが現時点の読み。D2・D3 との関係は E15 で確かめる。）

出典: `main:notes/design/yulang-language-report.md` §6.5

## 3.6 `if`　〔仮採用〕

```yulang
if n < 0: "negative"
elsif n == 0: "zero"
else: "positive"

if cond { a } else { b }
```

- `if` は式で、条件は `bool`。`elsif` と `else` を持てる。条件は上から順に試す。
- `else` がないとき、式全体は `opt` になる（確定, 2026-11-04。以前の「`()` を返して値は捨てる」を改訂）。then 側の値 `v` は `just v`、通らなかったときは `nil`。結果は使っても使わなくてもよい。
- **後置 `if`**（確定, 2026-11-08, ユーザーの決定。パーサは 2026-11-08 に対応済み。設計は `notes/design/2026-11-08-postfix-if-addendum.md`）。式の後ろに `if 条件` を置く形 `式 if 条件` を許す。`else` は付けられない（`else` が要るときはブロック形を使う）。結果は上の規則どおり `opt`（条件が真なら `just v`、偽なら `nil`）。糖衣であり、`if 条件: 式` の前置の形への書き換えで意味が決まる。
  - **結合力は最も弱い**: `|`（3.9）よりも、インラインの `:` の本体よりも弱く、後置 `if` はその左側の式全体にかかる。たとえば `say: 1 + 2 + 3 if 6 < 7` は `(say: 1 + 2 + 3) if 6 < 7` と読む。もし `:` の本体の中に入ると、`say` の引数が `opt` になり、意味が変わってしまうため。同じ理由で、`for x in xs: last if done` は、ループ全体が `done` で守られる読みになる。各回の中で守りたいときは、ブロック形か括弧を使う。
  - 前置の `if` との区別は、`if` に続く条件を読んだ後に、`:` か `{` が来るか、文の終わりが来るかで決まる。
  - 括弧の中（`(x if c)`）にも、式として置ける。
  - 読む人の驚きの観点（章0の方針）から、条件が行の最後に来る形は、`return x if c`・`last 'outer if done` のような早期脱出のガードで最も自然に読める。`opt` が型に出るので、`a = 1 if false` のような「評価されない束縛」の驚きは、型で追える。

```yulang
if cond: do_something()          // 結果の opt unit を捨てて文として使える
my r = if x > 0: x               // opt int
```

- 文の位置で値を捨てても警告は出さない（確定, 2026-11-04）。

- 条件が effectful な場合の扱い（junction。`all` / `any`）は章5 で書く。

出典: `main:web/docs/ja/reference/control-flow.md`

## 3.7 `case`　〔仮採用〕

```yulang
case n:
    0 -> "zero"
    x if x < 0 -> "negative"
    _ -> "positive"
```

- arm は上から順に試し、最初に pattern が合って guard が真になった arm が選ばれる。
- **case 全体の静的な effect 行は、全 arm の guard と body の行を合流する**（確定, 2026-11-08, ユーザーの決定。保守的な規則）。先行する arm が必ず合うせいで、後ろの arm に実行時には決して到達しなくても、その arm の effect を行に含める。たとえば、先頭が default も guard もない wildcard `_ -> 1` で、第二 arm の guard が `Tick` を起こす関数を呼ぶとき、case 全体の型は `Tick` を起こしうる行を持つ。理由: `if` の両枝の行を合流する規則と揃い、行の計算が網羅性の解析の強さに依存しないため。実際には呼ばれないことは、実行の順序（最初に合う arm だけが選ばれる）から別に言える。
- guard は pattern の後ろに `if` で書く（確定, 2026-11-04。`where` は宣言の型制約に使うので guard には使わない）。guard からは pattern が束縛した名前が見える。
- arm の本体が複数文のときは、`->` の後ろを改行して字下げすれば block になる（章1.3 の規則）。波括弧 `-> { ... }` でも書ける（確定, 2026-11-04）。

```yulang
case n:
    0 -> "zero"
    x ->
        my y = x * 2
        y + 1
```

- **`case:`（対象の式なし）は、一引数の関数を作る**（確定, 2026-11-06）。`case:` は `\x -> case x:` の略で、パイプライン（章3.9）の右辺や、関数として渡す場所に置ける。arm の意味は `case x:` と同じ。

```yulang
my handle = case:
    ok res -> res
    err e  -> fail_page e

route req | http_err::wrap | case:      // パイプラインの最後に置く
    ok res -> res
    err e  -> fail_page e
```

  **`catch:`（対象なし）も、一引数の関数を作る**（確定, 2026-11-07）。`catch:` は `\a -> catch a:` の略で、arm の意味は `catch a:` と同じ。
  **`x | catch:` では、左辺 `x` の effect は handler に届く**（確定, 2026-11-08, ユーザーの決定。E7）。`x | catch: ...` は `catch x: ...` と同じ意味で、左辺は評価されずに**計算のまま** `catch` に渡り、`catch` の中で実行される。パイプラインが左辺を「先に評価する」というのは、計算を引数に渡す順序の話であり、`x` を実行してから渡す意味ではない。これは `|` の一般の規則（3.9）の一例で、`catch` の特別扱いではない（2026-11-08, ユーザーの訂正）。
  arm が複数の引数を取る形があるかは、引き続き要確認。

- **網羅性を検査する**。どの arm にも合わない場合があるなら、エラーになる（確定, 2026-11-04）。
- 網羅性の細部（guard 付きの arm の扱いなど）は [章3b](03b-patterns.md) に書く。

出典: `main:web/docs/ja/reference/control-flow.md` §case、`main:notes/design/yulang-language-report.md` §6.7

## 3.8 `catch`（骨格のみ）　〔意味は章5〕

```yulang
catch expr:
    value -> value
    effect_pat, k -> body
```

- arm の pattern が 1 個なら value arm、2 個なら effect arm。effect arm の 2 個目の pattern は継続 `k` を受け取る。
- handler の意味、effect の「引ける」条件（章末 T2）は章5 で書く。

出典: `main:notes/design/yulang-language-report.md` §6.8

## 3.9 パイプライン `|`　〔存在は確定、細部は仮採用〕

```yulang
"data" | parse | render
xs | map f
```

- `x | f` は左辺を右辺に渡す。**あらゆる計算が `|` を通して流せる**（確定, 2026-11-08, ユーザーの訂正）。左辺は値としてでなく**計算**として右辺へ渡る。`catch` だけの特別な規則ではなく、`x | catch: ...` が `catch x: ...` と同じ意味になるのは、この一般の規則の一例である。conduit のように、計算どうしを `|` でつなげられる必要があるため。`|` に専用の評価規則はなく、`x | f` は `f x` と同じ意味である（確定, 2026-11-09, ユーザー。引数の行の cast と起動時放出も同じ。5.5c）。計算どうしをつなぐこと（conduit）に専用の意味は無く、普通の effect と handler で書く（確定, 2026-11-09, ユーザー: handler が effect を受けて effect を出せば十分）。残る細部（結合力との整合、評価順と hygiene、計算を受ける引数の型の表し方）は `notes/ideas/2026-11-08-pipe-computations.md`。`lhs | rhs` は `rhs lhs`（確定, 2026-11-04）。左辺は右辺の**最後の引数**になる。`xs | map f` は `map f xs`、`xs | map f | filter g` は `filter g (map f xs)`。
- `|` の結合力は全演算子の中で一番弱い（確定, 2026-11-04）。左辺は `and` / `or` を含む式全体になる。

```yulang
xs | map f == ys           // xs | (map f == ys)
1 + 2 | f                  // f (1 + 2)
a and b | f                // f (a and b)
```

出典: `main:web/docs/ja/reference/idioms.md`、`main:notes/design/yulang-language-report.md` §6.3

## 3.10 parser DSL（`rule { ... }` と `~"..."`）　〔仕様に入れると確定〕

`~"GET :resource"` や `rule { ... }` は parser 値を作る。`case` の arm では**入力文字列全体**にマッチし、名前付き capture を binding にする。

```yulang
my request(source: str): str = case source:
    ~"GET :resource" -> resource
    _ -> "no match"
```

- 意味が大きいので、専用の章（parser DSL）を後で立てる。ここでは、`case` の arm に parser pattern が書けることだけを述べる。

出典: `main:web/docs/ja/reference/parser-dsl.md`

## 確認してほしい点

- **E6** `|` の結合力が実装で一番弱くなっているか確かめる（仕様は確定）。
- **E7**（解決, 2026-11-08）: `x | catch:` で、左辺 `x` の effect は handler に届く。左辺は計算のまま渡る（上の `catch:` の項）。
