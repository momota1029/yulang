# Parser DSL

Yulang の **parser DSL** は、`~"..."` と `rule { ... }` から parser 値を作る。
`case` arm の **parser pattern** は入力文字列全体にマッチし、名前付き capture を binding にできる。
このページでは、DSL の surface と、DSL が直接使う `std::text::parse` の combinator を扱う。
低水準の `parse` effect、独自エラー型、検索 helper、編集 helper は対象外とする。

## `case` でのマッチ

parser pattern は文字列だけを入力として受け取る。
parse が成功し、入力が残らず、`guard` がある場合はその条件も真であるときに arm を選ぶ。
いずれかの条件が失敗すると、`case` は次の arm へ進む。

```yulang
use std::text::parse::*

my request(source: str): str = case source:
    ~"GET :resource" -> resource
    _ -> "no match"

(request "GET users").say
(request "GET users now").say
```

2 回の呼び出しは `users` と `no match` を表示する。
最初の `:resource` は `users` を消費するが、2 番目では ` now` が残るため、parser pattern が文字列全体にマッチしない。

## 短い `~"..."` 形式

rule リテラルには、完全一致する text、word capture、埋め込んだ parser を並べられる。

| 形式 | 結果 |
| --- | --- |
| `text` | `text` に完全一致し、値を bind しない。 |
| `:name` | `word` を実行し、その `str` の結果を `name` として bind する。 |
| `{parser}` | `parser` を実行し、その値を捨てる。 |
| `{name = parser}` | `parser` を実行し、戻り値を `name` として bind する。 |
| `{name = ..}` | 残りの入力をすべて `str` として bind する。 |

### Word capture

compiler の surface では `:name` を lazy capture と呼ぶが、正規表現の最短一致ではない。
内部では `word` を実行し、英数字または underscore を 1 文字以上消費する。
英数字と underscore 以外の文字の直前で停止し、後続 item が失敗しても文字を戻さない。
そのため、隣り合う word capture の間にはリテラルの区切りが必要になる。

### Parser の埋め込みと rest capture

`{name = parser}` は、parser が消費した text ではなく、parser の戻り値を capture する。
特別な parser である `..` は、空白と句読点を含む残りの部分文字列をすべて返す。
空文字列を返すこともあり、分岐の最後の item にだけ置ける。

```yulang
use std::text::parse::*

my route(source: str): str = case source:
    ~":method /:resource/{tail = ..}" ->
        method + "|" + resource + "|" + tail
    _ -> "no match"

(route "GET /users/42/edit").say
(route "GET /users/").say
```

2 回の呼び出しは `GET|users|42/edit` と `GET|users|` を表示する。
リテラル `"/"` が `resource` の word capture を終わらせ、`tail` は最後の `"/"` より後ろをすべて受け取る。

## 長い `rule { ... }` 形式

`rule { ... }` では、sequence、parser 値、capture、grouping、反復、選択を明示できる。
同じ分岐にある item は 1 つの sequence になる。
文字列リテラルは完全一致する token になり、`word` のような識別子は parser 値を参照し、DSL が実行する。

### Sequence と capture

`name = parser` と書くと、1 つの parser item が返した値を bind できる。
複数の capture は 1 つの record になり、その `field` は parser pattern の arm で binding になる。

```yulang
use std::text::parse::*

my pair(source: str): str = case source:
    rule { left = word ":" right = word } -> left + "/" + right
    _ -> "no match"

(pair "alpha:beta").say
```

この例は `alpha/beta` を表示する。
2 つの `word` parser は文字列を返し、リテラル `":"` は区切りを検査して消費するだけである。

### 反復と capture の値

反復記号は、1 つの item または括弧で囲んだ group の直後に付ける。
capture の型は combinator の結果に従う。

| 形式 | マッチする回数 | capture する値 |
| --- | --- | --- |
| `parser*` | 0 回以上 | `list` |
| `parser+` | 1 回以上 | 空でない `list` |
| `parser?` | 0 回または 1 回 | `opt`。0 回なら `nil` |

```yulang
use std::text::parse::*

my repeats(source: str): str = case source:
    rule { pieces = "ha"* } -> pieces.len.show
    _ -> "no match"

my optional_piece(source: str): str = case source:
    rule { piece = "ha"? } -> case piece:
        nil -> "nil"
        just _ -> "just"
    _ -> "no match"

(repeats "").say
(repeats "hahaha").say
(optional_piece "").say
(optional_piece "ha").say
```

4 回の呼び出しは `0`、`3`、`nil`、`just` を表示する。
反復する token が `unit` を返す場合も、反復全体を capture すると combinator が作った `list unit` または `opt unit` を保つ。

反復は greedy であり、後続 item が失敗しても完了したマッチをやり直さない。
次の `"a"*` は `"aaa"` の 3 文字をすべて消費するため、最後の `"a"` はマッチできない。

```yulang
use std::text::parse::*

my needs_final_a(source: str): str = case source:
    rule { "a"* "a" } -> "matched"
    _ -> "no match"

(needs_final_a "aaa").say
```

この例は `no match` を表示する。

### 選択と backtrack

`left | right` は左から順に試す選択である。
まず左の分岐を試す。
失敗した場合は、左の分岐が途中まで入力を消費していても、分岐前の入力位置に戻って右の分岐を試す。

```yulang
use std::text::parse::*

my alternative(source: str): str = case source:
    rule { "ab" "x" | "ab" "y" } -> "matched"
    _ -> "no match"

(alternative "aby").say
```

この例は `matched` を表示する。
左の分岐は `"ab"` を消費してから `"x"` で失敗し、右の分岐は先頭から再開して `"aby"` を消費する。

1 つの分岐が成功すると、後ろの分岐は試さない。
入力全体の検査は選択の後に行うため、`rule { "a" | "ab" }` は `"ab"` にマッチしない。
最初の分岐が `"a"` で成功した後、残った `"b"` によって parser pattern の arm 全体が失敗する。

## Parser 値と prefix 実行

どちらの DSL 形式も、`read_prefix` のような関数へ渡せる parser 値を作る。
次の例では、capture を持つ `rule { ... }` の値を binding に保存する。
`case` の parser pattern と異なり、`read_prefix` は入力が残ることを許し、`prefix_result.rest` に返す。

```yulang
use std::text::parse::*

my assignment = rule { key = word "=" value = word }

case read_prefix "name=alice;rest" assignment:
    result::ok found ->
        (found.value.key + "/" + found.value.value + "/" + found.rest).say
    result::err _ -> "no match".say
```

この例は `name/alice/;rest` を表示する。
`assignment` は capture record を返し、`read_prefix` は parser が消費しなかった suffix を保つ。

DSL の背後にある主な combinator は、`token`、`word`、`rest`、`choice`、`many`、`some`、`optional` である。
`std::text::parse` の低水準 effect、エラー、検索、書き換えの API は、このページですべてを列挙しない。

## 現在の制限

最短一致の反復 `*?` と `+?` は token 化されるが、lowering は `yulang.unsupported-rule-lazy-quantifier` として拒否する。
greedy な `*` または `+` を使い、後続 parser を明示的に組み立てる。

rest parser の `..` も最後以外の位置で parser に受理されるが、lowering は `yulang.rule-rest-position` として拒否する。
`..` は分岐の最後へ移す。

`rule` の sequence には、capture していない値を返す parser を 1 つだけ置ける。
`rule { word word }` は parse されるが、2 つの戻り値を扱えないため、lowering が未対応の rule 式として拒否する。
sequence に複数の値を残す場合は、それぞれを `name = parser` で capture する。

rule リテラルの `{...}` interpolation を lowering するときは、parser item を 1 つだけ受け取る。
たとえば `~"{word word}"` は parse されるが、未対応の rule リテラル interpolation として拒否される。
別々の interpolation に分けるか、`rule { ... }` に sequence を書き、値を返す item を capture する。

## 関連ページ

- [パターンマッチ](./patterns)では、`case`、guard、parser pattern 以外の pattern を扱う。
- [ツアー → Parser pattern](../guide/tour#parser-pattern)には、短い機能例がある。
- [標準ライブラリ一覧 → `std::text::parse`](./std/)では、ほかの text API と並ぶ module の位置を確認できる。
