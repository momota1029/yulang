# 章3b pattern

状態の凡例は [README](README.md)。pattern は、値に名前を束縛するあらゆる場所に現れる。
`case` の arm、`catch` の arm、関数の引数、`my` の分割代入、lambda の引数は、**同じ pattern の文法**を共有する。

## 3b.1 pattern の種類　〔仮採用〕

| pattern | 例 | 合う値 |
| --- | --- | --- |
| wildcard | `_` | 何でも |
| 名前 | `x` | 何でも。`x` に束縛 |
| literal | `42`, `"hi"`, `true`, `()` | 等しい値 |
| 範囲 | `0..10`, `..0`, `1..` | 閉区間 `[0, 10]` に入る値。片側だけの `a..`（a 以上）・`..b`（b 以下）も書ける。負の整数も bound にできる(`-1..5`, `..-1`。`-` は整数に隣接させる。確定, 2026-11-04)。`..` だけは書けない（確定, 2026-11-04。網羅性は Rust の範囲 pattern と同じ規則） |
| tuple | `(a, b)` | tuple |
| record | `{ x, y }`, `{ x: name }`, `{ x = 0 }` | 指定した field を持つ record |
| list | `[]`, `[x, ..rest]`, `[..init, last]` | list |
| polyvariant | `:ready`, `:some value` | 同じ tag と payload。`:ready` は payload が unit の略記で、`:ready ()` と同じ（確定, 2026-11-04） |
| enum variant | `opt::just x`, `nil` | その variant |
| or | `"yes" \| "y"` | どちらかの選択肢 |
| as | `pat as name` | `pat` に合い、値全体も `name` に束縛 |

```yulang
case point:
    (0, 0) -> "origin"
    (x, 0) -> "on x axis"
    (x, y) -> "other"
```

出典: `main:web/docs/ja/reference/patterns.md`

- **同じ照合の道筋で、同じ名前を二度束縛する pattern は、静的にエラーになる**（確定, 2026-11-06。Rust と同じ）。`(x, x)` や `(x, _) as x` は拒否される。別々の or の枝に同じ名前を書く `(x, 0) | (0, x)` は許される（3b.6）。重複を許して束縛を選ぶ規則も、二回目以降を等値の制約にする規則も、今は採らない。

## 3b.2 名前か、variant か　〔罠: T4、対処は確定〕

pattern の位置で、`red` のような**修飾なしの名前は、variant ではなく新しい束縛**になる。variant に合わせたいときは
`color::red` と修飾するか、先に `use color::*` を書く。

```yulang
enum color = red | green | blue

case c:
    red -> "r"      // red は何にでも合う新しい変数。下の arm は到達しない
    green -> "g"
    blue -> "b"
```

- prelude が re-export する `just` / `nil` / `ok` / `err` などは、修飾なしで variant として使える。
- 式の位置の未解決の `red` は name error だが、pattern の位置では束縛になる。この非対称は暗黙の意味変化なので危険。

出典: `main:web/docs/ja/reference/patterns.md` §enum pattern
この罠への対処は **案 B**（確定, 2026-11-04）。通すが、その後ろで到達しなくなった arm に警告を出す。

| 案 | 上の例の扱い |
| --- | --- |
| A 今のまま | 黙って通る。`name blue` も `"r"` を返す |
| **B 到達不能の警告（採用）** | 通る。ただし `green` / `blue` の arm に「到達しない」警告が出る |
| C Rust 流（E0170 相当） | 走査対象の型が `color` と分かっていて、`red` がその variant 名と同じなら**エラー**（採らない） |

## 3b.3 record・list の細部　〔仮採用〕

```yulang
case config:
    { host: h = "localhost", port = 80 } -> h + ":" + port.show
```

- 明示した field は、default がなければ必須。`field: name` で別名に束縛し、`field = value` で default を与える。
- default（`port = 80`）は、その field が型の上で省略可能（`port?: int`）なときだけ書ける。必須の field に default を書いたらエラー（欠けることがないため）。
  pattern に default を書くと、推論が自動的にその field を省略可能（`port?: int`）にする（確定, 2026-11-04）。省略可能な field の型表記は章4.3・章7.5 で扱う。
- default は field が欠けているときに評価される。そのため pattern の照合そのものが effect を持ちうる。
- **default の式からは、同じ pattern でそれまでに照合して束縛した名前が見える**（確定, 2026-11-06）。照合は field の記述順（左から右）に進み、先に束縛された名前は、後ろの default の式で使える。同名なら、pattern の束縛が外側の名前を隠す。field の記述順が名前解決にも影響するが、未使用の束縛の警告や型エラーで気づける。or pattern の各枝は、それぞれ自分の枝の束縛だけを見る。 **pattern は記述順に照合され、先行する部分が合わなければ、その arm の残りは打ち切られる**（確定, 2026-11-06）。後ろの default の式は評価されず、その effect も起きない。

```yulang
my outer = 10
case { x: 3 }:
    { x: outer, y: result = outer } -> result    // y が無いので、default の outer は x の束縛 3。結果は 3
```

- record の spread `..name` は、**残りではなく入力 record 全体**を束縛する（record の差は型システム上、十分に扱えないため）。
  他の field があってもよいことだけを示すなら `.._` を使う。
- list の spread は 1 つだけ置ける。先頭にも末尾にも置ける。`..name` は**残りの要素の list** に束縛される（`[1, 2, 3]` を `[first, ..rest]` に合わせると `rest = [2, 3]`。確定, 2026-11-04）。record の spread とは違う。

出典: `main:web/docs/ja/reference/patterns.md`

## 3b.4 網羅性　〔確定〕

- `case` は網羅性を検査し、網羅していなければエラーになる（章3.7）。
- **Rust と同じ**にする（確定, 2026-11-04）。特に **guard 付きの arm は網羅に数えない**。

```yulang
case n:
    x if x < 0 -> "negative"
    x if x >= 0 -> "non-negative"    // guard は網羅に数えないので、これだけではエラー
```

- 「何を網羅とみなすか」の細部は Rust の規則に従う。
- symbol / polyvariant の pattern を使った `case` は、`_` を書かなくても網羅できる。走査対象の型が、pattern に書いた tag だけの**閉じた型**になるため（確定, 2026-11-04）。

```yulang
my f x = case x:
    :ready -> 1
    :waiting -> 2
// x : :ready | :waiting（閉じた型）。_ は要らない
```

## 3b.5 `my` の分割代入　〔確定〕

```yulang
my (a, b) = (1, 2)
my { x, y } = some_point
my [first, ..rest] = some_list
```

- **反駁可能な pattern はエラーにする**（Rust の `let` と同じ, 確定, 2026-11-04）。素材は「検査されない」と書いていたが、それは実装の穴として扱う。

```yulang
my (a, b) = (1, 2)       // 反駁不能: OK
my just x = some_opt     // 反駁可能: エラー
```

出典: `main:web/docs/ja/reference/patterns.md` §my の pattern

## 3b.6 or pattern と束縛　〔確定〕

- **or pattern は左の選択肢から照合し、最初に合った枝で確定する**（確定, 2026-11-06）。その枝の束縛で guard を一度だけ評価し、guard が偽なら、右の選択肢を試し直さずに**次の arm** へ進む。guard は複数回評価されない。

```yulang
case (1, 2):
    (x, _) | (_, x) if x == 2 -> x    // 左の枝が合い x = 1。guard は偽 → 次の arm へ。結果は 0
    _ -> 0
```
- **or pattern の選択肢は、同じ名前の集合を束縛しなければならない**（Rust と同じ, 確定, 2026-11-04）。
  素材の実装は、違う名前を受け入れて実行時エラーになるが、それは実装の穴として扱う。

```yulang
x | y -> ...          // エラー: 選択肢で束縛する名前が違う
(a, 0) | (0, a) -> a  // OK: どちらも a を束縛する
```

## 3b.6' `as` と or の結合力　〔確定〕

- `as` は or（`|`）より弱い（確定, 2026-11-04）。`x | y as z` は `(x | y) as z` で、選択肢の全体に名前を付ける。

## 3b.7 pattern の型注釈　〔確定〕

- **pattern の型注釈は、値の型を制約する**（確定, 2026-11-04）。素材の実装は注釈を無視するが、それは実装の穴として扱う。

```yulang
case 41:
    text: str -> "..."     // 型エラー: 41 は int
    _ -> "fallback"
```

出典: `main:web/docs/ja/reference/patterns.md` §型 pattern は利用できない

## 確認してほしい点

なし（P1〜P5 は反映済み）。
