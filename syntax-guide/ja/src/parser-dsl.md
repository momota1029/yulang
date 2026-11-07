# parser DSL

文字列を切り出して、名前に束縛する書き方。`~"..."` と `rule { ... }` の 2 つの形がある。
Perl の正規表現が受け持つ仕事(文字列から必要な部分を取り出す)を、`case` の arm と同じ構文で書ける。意味と背後の部品は spec の章9 に任せて、この章は書き方と読まれ方を見る。

## `case` の arm に書く

```yulang
use std::text::parse::*

my request(source: str): str = case source:
    ~"GET :resource" -> resource
    _ -> "no match"
```

`~"GET :resource"` は parser pattern。入力の文字列**全体**に照合して、`:resource` の部分を `resource` に束縛する。合えば、その arm が選ばれる。合わなければ次の arm へ進む。

- parse に成功し、**入力が残らず**、guard があれば真のときに、その arm が選ばれる。
- `request "GET users"` は `users`。`request "GET users now"` は ` now` が残るので、`"no match"`。

状態: 仮採用・パース検査済み。出典: `spec/09-parser-dsl.md` 9.1。

### 入れ子の位置にも書ける

parser pattern は pattern の一種なので、pattern を書ける場所ならどこにでも書ける。record の field、tuple の成分、variant の payload の中にも入れ子にできる。

```yulang
case req:
    { method: "GET", path: ~"/users/:id" } -> user_page id    // record の field の中
```

parser pattern は失敗しうる(反駁可能な)pattern なので、lambda の引数や、`my` の分割代入には書けない。

## 短い形 `~"..."`

| 形式 | 意味 |
| --- | --- |
| `text` | `text` に完全一致する。何も束縛しない |
| `:name` | `word` を実行し、その `str` を `name` に束縛する |
| `{parser}` | `parser` を実行し、値は捨てる |
| `{name = parser}` | `parser` を実行し、戻り値を `name` に束縛する |
| `{name = ..}` | 残りの入力をすべて `str` で `name` に束縛する |

```yulang
~":method /:resource/{tail = ..}"
// "GET /users/42/edit" → method=GET, resource=users, tail=42/edit
```

- `:name` は、英数字か `_` を 1 文字以上消費し、それ以外の文字の直前で止まる。隣り合う `:name` の間には、リテラルの区切りが要る。
- `..` は、空白や句読点を含む残りをすべて返す。空文字列のこともあり、**分岐の最後の項目にだけ**置ける。

状態: 記法を仕様に載せると確定・パース検査済み。出典: `spec/09-parser-dsl.md` 9.2。

## 長い形 `rule { ... }`

```yulang
case source:
    rule { left = word ":" right = word } -> left + "/" + right
    _ -> "no match"
```

- 同じ分岐の項目は、1 つの sequence になる。文字列リテラルは完全一致する token、`word` のような識別子は parser 値の参照。
- `name = parser` で、1 つの項目の戻り値を束縛する。複数の capture は 1 つの record になり、その field が arm の中の束縛になる。

### 反復と選択

| 反復 | 回数 | capture する値 |
| --- | --- | --- |
| `parser*` | 0 回以上 | `list` |
| `parser+` | 1 回以上 | 空でない `list` |
| `parser?` | 0 回か 1 回 | `opt`(0 回は `nil`) |

- **反復は greedy**。後続の項目が失敗しても、完了したマッチをやり直さない。`rule { "a"* "a" }` は `"aaa"` にマッチしない。
- **選択 `left | right`** は、左から順に試す。左が途中まで入力を消費して失敗しても、分岐前の位置に戻って右を試す(backtrack)。1 つの分岐が成功したら、後ろの分岐は試さない。入力全体の検査は選択の後なので、`rule { "a" | "ab" }` は `"ab"` にマッチしない。

```yulang
case line:
    rule { key = word "=" value = word } -> key + " is " + value
    _ -> "other"
```

状態: 仮採用・パース検査済み。出典: `spec/09-parser-dsl.md` 9.3。

## parser 値として使う

どちらの形も、関数に渡せる **parser 値**を作る。`case` の parser pattern と違って、`read_prefix` は**入力が残ってもよい**。

```yulang
my assignment = rule { key = word "=" value = word }

case read_prefix "name=alice;rest" assignment:
    result::ok found -> (found.value.key + "/" + found.value.value + "/" + found.rest).say
    result::err _ -> "no match".say
```

状態: 仮採用・パース検査済み。出典: `spec/09-parser-dsl.md` 9.4。

## 現在の制限

次の形は、パーサは受理するが、意味への変換が拒否する。**実装の穴として扱われ、将来実装される前提**になっている。

- 最短一致の反復 `*?` / `+?`。
- 最後以外の位置の `..`。
- `rule` の sequence に、capture していない値を返す parser を 2 つ以上置く(`rule { word word }`)。
- rule リテラルの `{...}` の中に、parser 項目を 2 つ以上置く(`~"{word word}"`)。

## Perl の正規表現との違い

- 正規表現のような暗号ではなく、`case` の arm と同じ構文で書く。取り出した名前は、そのまま arm の中の束縛になる。
- 照合は入力全体に対して行われ、残りがあれば失敗する。部分一致を探すのではない。
- 反復は greedy で、完了したマッチをやり直さない(backtrack するのは選択 `|` だけ)。この点は、正規表現の多くの実装と違う。
