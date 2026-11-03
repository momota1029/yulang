# 章9 parser DSL

状態の凡例は [README](README.md)。`~"..."` と `rule { ... }` は、**parser 値**を作る。`case` の arm に書くと、入力文字列を照合して capture を束縛する。
この章は DSL の見える意味だけを書く。背後の combinator（`token`、`word`、`rest`、`choice`、`many`、`some`、`optional`）と低水準の `parse` effect は `std::text::parse` の側の話。

## 9.1 `case` での照合　〔要確認〕

```yulang
use std::text::parse::*

my request(source: str): str = case source:
    ~"GET :resource" -> resource
    _ -> "no match"
```

- parser pattern は文字列だけを入力に取る。parse に成功し、**入力が残らず**、guard があれば真のときに、その arm が選ばれる。失敗すれば次の arm へ進む。
- `(request "GET users")` は `users`、`(request "GET users now")` は ` now` が残るので `no match`。

## 9.2 短い形 `~"..."`　〔要確認〕

| 形式 | 意味 |
| --- | --- |
| `text` | `text` に完全一致する。何も束縛しない |
| `:name` | `word` を実行し、その `str` を `name` に束縛する |
| `{parser}` | `parser` を実行し、値は捨てる |
| `{name = parser}` | `parser` を実行し、戻り値を `name` に束縛する |
| `{name = ..}` | 残りの入力をすべて `str` で `name` に束縛する |

- `:name` は英数字か `_` を 1 文字以上消費し、それ以外の文字の直前で止まる。隣り合う `:name` の間にはリテラルの区切りが要る。
- `..` は空白や句読点を含む残りをすべて返す。空文字列のこともあり、**分岐の最後の項目にだけ**置ける。

```yulang
~":method /:resource/{tail = ..}"
// "GET /users/42/edit" → method=GET, resource=users, tail=42/edit
```

## 9.3 長い形 `rule { ... }`　〔要確認〕

```yulang
case source:
    rule { left = word ":" right = word } -> left + "/" + right
    _ -> "no match"
```

- 同じ分岐の項目は 1 つの sequence になる。文字列リテラルは完全一致する token、`word` のような識別子は parser 値の参照。
- `name = parser` で 1 つの項目の戻り値を束縛する。複数の capture は 1 つの record になり、その field が arm の中の束縛になる。

| 反復 | 回数 | capture する値 |
| --- | --- | --- |
| `parser*` | 0 回以上 | `list` |
| `parser+` | 1 回以上 | 空でない `list` |
| `parser?` | 0 回か 1 回 | `opt`（0 回は `nil`） |

- **反復は greedy**。後続の項目が失敗しても、完了したマッチをやり直さない。`rule { "a"* "a" }` は `"aaa"` にマッチしない。
- **選択 `left | right`** は左から順に試す。左が途中まで入力を消費して失敗しても、分岐前の位置に戻って右を試す（backtrack）。
  1 つの分岐が成功したら、後ろの分岐は試さない。入力全体の検査は選択の後なので、`rule { "a" | "ab" }` は `"ab"` にマッチしない。

## 9.4 parser 値と prefix 実行　〔要確認〕

どちらの形も、関数に渡せる parser 値を作る。`case` の parser pattern と違って、`read_prefix` は**入力が残ってもよい**。

```yulang
my assignment = rule { key = word "=" value = word }

case read_prefix "name=alice;rest" assignment:
    result::ok found -> (found.value.key + "/" + found.value.value + "/" + found.rest).say
    result::err _ -> "no match".say
```

## 9.5 現在の制限（実装の穴か、仕様の制限か）

次は、パーサは受理するが lowering が拒否する形。

- 最短一致の反復 `*?` / `+?`。
- 最後以外の位置の `..`。
- `rule` の sequence に、capture していない値を返す parser を 2 つ以上置く（`rule { word word }`）。
- rule リテラルの `{...}` の中に parser 項目を 2 つ以上置く（`~"{word word}"`）。

## 確認してほしい点

- **L1** 9.5 の 4 つは、将来実装する前提の穴か、仕様として許さない制限か。
- **L2** 反復の greedy と、選択の backtrack（分岐前に戻る。ただし反復の中は戻さない）は、仕様として約束してよいか（PEG に近い意味）。
- **L3** `~"..."` の短い形の記法（`:name`、`{...}`、`..`）は、仕様に載せる範囲でよいか。
