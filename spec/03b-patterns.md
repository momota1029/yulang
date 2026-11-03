# 章3b pattern

状態の凡例は [README](README.md)。pattern は、値に名前を束縛するあらゆる場所に現れる。
`case` の arm、`catch` の arm、関数の引数、`my` の分割代入、lambda の引数は、**同じ pattern の文法**を共有する。

## 3b.1 pattern の種類　〔要確認〕

| pattern | 例 | 合う値 |
| --- | --- | --- |
| wildcard | `_` | 何でも |
| 名前 | `x` | 何でも。`x` に束縛 |
| literal | `42`, `"hi"`, `true`, `()` | 等しい値 |
| tuple | `(a, b)` | tuple |
| record | `{ x, y }`, `{ x: name }`, `{ x = 0 }` | 指定した field を持つ record |
| list | `[]`, `[x, ..rest]`, `[..init, last]` | list |
| symbol | `:ready` | 同じ名前の symbol（payload なし） |
| polyvariant | `:some value` | 同じ tag と payload |
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

## 3b.2 名前か、variant か　〔罠: T4〕

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
要確認: pattern の位置の `red` を束縛として読む規則を、警告や error にするか（確認 P1）。

## 3b.3 record・list の細部　〔要確認〕

```yulang
case config:
    { host: h = "localhost", port = 80 } -> h + ":" + port.show
```

- 明示した field は、default がなければ必須。`field: name` で別名に束縛し、`field = value` で default を与える。
- default は field が欠けているときに評価される。そのため pattern の照合そのものが effect を持ちうる。
- record の spread `..name` は、**残りではなく入力 record 全体**を束縛する（record の差は型システム上、十分に扱えないため）。
  他の field があってもよいことだけを示すなら `.._` を使う。
- list の spread は 1 つだけ置ける。先頭にも末尾にも置ける。

出典: `main:web/docs/ja/reference/patterns.md`

## 3b.4 網羅性　〔確定〕

- `case` は網羅性を検査し、網羅していなければエラーになる（章3.7）。
- **Rust と同じ**にする（確定, 2026-11-04）。特に **guard 付きの arm は網羅に数えない**。

```yulang
case n:
    x if x < 0 -> "negative"
    x if x >= 0 -> "non-negative"    // guard は網羅に数えないので、これだけではエラー
```

- 「何を網羅とみなすか」の細部は Rust の規則に従う。Yulang 独自の pattern（symbol、polyvariant）の網羅性は未確認（確認 P2）。

## 3b.5 `my` の分割代入　〔要確認〕

```yulang
my (a, b) = (1, 2)
my { x, y } = some_point
my [first, ..rest] = some_list
```

- 素材では、`my` の分割代入は「pattern が必ず合う前提」で処理され、網羅性が検査されないとある。
  これは `case` の方針（検査する）と食い違う。Rust の `let` なら反駁可能な pattern はエラー（確認 P3）。

出典: `main:web/docs/ja/reference/patterns.md` §my の pattern

## 3b.6 or pattern と束縛　〔要確認〕

- 素材では、or pattern の選択肢が違う名前を束縛しても受け入れられ、選ばれなかった側の束縛を body で使うと実行時エラーになる。
  これは仕様というより実装の穴に見える（確認 P4）。

## 3b.7 pattern の型注釈　〔要確認〕

- パーサは `pattern: type` を受け付けるが、現状の実装は `case` の pattern の注釈を**検査せず無視する**。
  `text: str` は int の値にも合ってしまう。「値の型を制約するために使ってはならない」状態（確認 P5）。

出典: `main:web/docs/ja/reference/patterns.md` §型 pattern は利用できない

## 確認してほしい点

- **P1** pattern の位置の修飾なしの名前（`red`）が、同名の variant があっても束縛になる件。警告にするか、error にするか、今のままか。
- **P2** symbol / polyvariant の網羅性をどう扱うか。開いた型なので、網羅には `_` が必要という扱いでよいか。
- **P3** `my` の分割代入は、反駁可能な pattern ならエラーにするか（Rust の `let` と同じ）。
- **P4** or pattern の選択肢は、同じ名前の集合を束縛しなければならない、でよいか（Rust と同じ）。
- **P5** pattern の型注釈は、`case` の中でも**型を制約する**仕様にするか。現状の「無視する」は実装の穴か。
