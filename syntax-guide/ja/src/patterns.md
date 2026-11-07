# pattern

pattern は、値に名前を束縛するあらゆる場所に現れる。`case` の arm、`catch` の arm、関数の引数、`my` の分割代入、lambda の引数は、**同じ pattern の文法**を共有する。
この章は、pattern の種類と書き方、読まれ方を見る。網羅性の検査や型の規則は `spec/03b-patterns.md` に任せる。

## pattern の種類

| pattern | 例 | 合う値 |
| --- | --- | --- |
| wildcard | `_` | 何でも |
| 名前 | `x` | 何でも。`x` に束縛 |
| literal | `42`, `"hi"`, `true`, `()` | 等しい値 |
| 範囲 | `0..10`, `..0`, `1..` | 閉区間に入る値 |
| tuple | `(a, b)` | tuple |
| record | `{ x, y }`, `{ x: name }`, `{ x = 0 }` | 指定した field を持つ record |
| list | `[]`, `[x, ..rest]`, `[..init, last]` | list |
| polyvariant | `:ready`, `:some value` | 同じ tag と payload |
| enum variant | `opt::just x`, `nil` | その variant |
| or | `"yes" \| "y"` | どちらかの選択肢 |
| as | `pat as name` | `pat` に合い、値全体も `name` に束縛 |

```yulang
case point:
    (0, 0) -> "origin"
    (x, 0) -> "on x axis"
    (x, y) -> "other"
```

状態: 仮採用・パース検査済み。出典: `spec/03b-patterns.md` 3b.1。

## 範囲

```yulang
case n:
    0..10 -> "small"
    11.. -> "large"
    ..-1 -> "negative"
    -1..5 -> "around zero"
```

`a..b` は閉区間 `[a, b]`。片側だけの `a..`(a 以上)と `..b`(b 以下)も書ける。負の整数も bound にできる(`-1..5`、`..-1`)。`-` は整数に隣接させる。`..` だけは書けない。
状態: 確定。ただし、**2 番目以降の arm が `-1` のように、`-` と整数で始まる形は、現在のパーサがまだ読めない**(`notes/design/2026-11-07-parser-gap-closure-addendum-2.md` の WP-15)。1 番目の arm なら読める。

## 名前か、variant か

pattern の位置で、`red` のような**修飾なしの名前は、variant ではなく新しい束縛**になる。

```yulang
enum color = red | green | blue

case c:
    red -> "r"      // red は何にでも合う新しい変数。下の arm には到達しない
    green -> "g"
    blue -> "b"
```

variant に合わせたいときは、`color::red` と修飾するか、先に `use color::*` を書く。

```yulang
case c:
    color::red -> "r"
    color::green -> "g"
    color::blue -> "b"
```

- prelude が再公開する `just` / `nil` / `ok` / `err` などは、修飾なしで variant として使える。
- 式の位置の未解決の `red` は name error だが、pattern の位置では束縛になる。この非対称は暗黙の意味変化なので、気を付ける。
- 通るが、その後ろで到達しなくなった arm には警告が出る。

状態: 確定(警告の方針)・パース検査済み。出典: `spec/03b-patterns.md` 3b.2。

## record

```yulang
case config:
    { host: h = "localhost", port = 80 } -> h + ":" + port.show
```

- 明示した field は、default がなければ必須。
- `field: name` で別名に束縛する。`field = value` で default を与える。両方は `field: name = value`。
- default は、その field が型の上で省略可能なときだけ書ける。pattern に default を書くと、推論が自動的にその field を省略可能にする。
- default は、field が欠けているときに評価される。**default の式からは、同じ pattern でそれまでに照合して束縛した名前が見える**。照合は field の記述順(左から右)に進む。

```yulang
my outer = 10
case { x: 3 }:
    { x: outer, y: result = outer } -> result    // y が無いので default の outer は、x の束縛 3
```

- record の spread `..name` は、**残りではなく入力 record 全体**を束縛する。他の field があってもよいことだけを示すなら、`.._` を使う。

```yulang
case p:
    { x, .._ } -> x
    { x, ..whole } -> whole
```

状態: 仮採用(default の可視性などは確定)・パース検査済み。出典: `spec/03b-patterns.md` 3b.3。

## list

```yulang
case xs:
    [] -> 0
    [x] -> x
    [first, ..rest] -> first
```

- spread は 1 つだけ置ける。先頭にも末尾にも置ける(`[..init, last]`)。
- `..name` は**残りの要素の list** に束縛される。`[1, 2, 3]` を `[first, ..rest]` に合わせると、`rest = [2, 3]`。
- record の spread とは意味が違う(record は入力全体、list は残りの要素)。

状態: 確定・パース検査済み。

## polyvariant と enum variant

```yulang
case x:
    :ready -> 1             // :ready () の略記
    :some value -> value    // tag と payload
    opt::just y -> y        // enum の variant
    nil -> 0
```

`:ready` は payload が unit の略記で、`:ready ()` と同じ。
symbol / polyvariant の pattern だけを使った `case` は、`_` を書かなくても網羅できる(走査対象の型が、pattern に書いた tag だけの閉じた型になる)。

状態: 確定・パース検査済み。

## or と as

```yulang
case v:
    "yes" | "y" -> true
    (a, 0) | (0, a) -> a
    x | y as z -> z
```

- or は、左の選択肢から照合して、最初に合った枝で確定する。
- or の選択肢は、同じ名前の集合を束縛しなければならない。`(a, 0) | (0, a)` は、どちらも `a` を束縛するので良い。違う名前を束縛する選択肢はエラー。
- `as` は or より弱い。`x | y as z` は `(x | y) as z` で、選択肢の全体に名前を付ける。

同じ照合の道筋で、同じ名前を二度束縛する pattern(`(x, x)` など)は、静的にエラーになる。別々の or の枝に同じ名前を書くのは良い。
状態: 確定・パース検査済み。出典: `spec/03b-patterns.md` 3b.6。

## pattern の型注釈

```yulang
case v:
    text: str -> text
    _ -> "fallback"
```

pattern の型注釈は、値の型を制約する。上の例で `v` が `int` なら、型エラーになる。
状態: 確定・パース検査済み。

## 反駁可能な pattern と、書ける場所

`my` の分割代入や lambda の引数に書ける pattern は、必ず成功するもの(反駁不能)だけ。

```yulang
my (a, b) = (1, 2)              // OK
my { x, y } = some_point        // OK
my [first, ..rest] = some_list  // 空の list だと失敗しうるので、構造としては反駁可能
```

- tuple・record・`_`・名前は、反駁不能として書ける。
- `my just x = some_opt` のように失敗しうるものは、エラーになる(`case` を使う)。
- 網羅性: `case` は網羅性を検査する。guard 付きの arm は網羅に数えない。

状態: 確定・パース検査済み。出典: `spec/03b-patterns.md` 3b.4、3b.5。
