# `std::text::yumark` <Badge type="warning" text="暫定" />

`std::text::yumark` は、Yumark の `yumark_algebra`、Yumark 式が使う構築関数、HTML node と Markdown の描画処理を定義する。

> **暫定：** 静的な Yumark ドキュメントは動作するが、command、inline 式、injection、一部の tooling は未完成である。
> これらの追加に伴い、構築と描画の API は変わる可能性がある。

## ドキュメント値

Yumark のドキュメント値は、再利用可能な**ドキュメント構築関数**である。
format と `yumark_algebra 'repr` を受け取り、その algebra の表現を生成する。
検査やパターンマッチの対象になる具体的なドキュメント tree ではない。

`my` で名前を付けた構築関数は、表現について多相のままになる。
同じ値を `render_html_doc` と `render_markdown_doc` へ渡すと、各呼び出しが異なる algebra で関数を実行する。

## リテラルによる構築

`'[...]` は inline Yumark の構築関数を作り、`'{...}` は block Yumark の構築関数を作る。
これらは Yulang の式構文である。
compiler は静的な内容を `std::text::yumark` の構築関数へ lower する。
この `module` が独立した parser や macro 構文を宣言するわけではない。

```yulang
use std::text::yumark::{html_tag, render_html_doc, render_markdown_doc}

my inline = '[hello *Yumark*]
my block = '{# Title

A **strong** paragraph.
}

(
    html_tag (render_html_doc inline),
    render_markdown_doc inline,
    html_tag (render_html_doc block),
    render_markdown_doc block,
)
```

inline ドキュメントの結果には `"<span>hello </span><em><span>Yumark</span></em>"` と `"hello *Yumark*"` が含まれる。
block ドキュメントは、HTML では `h1` と段落、Markdown では元の見出しと段落として描画される。

静的な語彙では、text、段落、見出し、section close、順序付きと順序なしの list、code fence、block quote、emphasis、strong text を使える。
source の空行は段落を分けるが、表示用の `blank_line` 構築関数は呼び出さない。

## 関数による構築

プログラムは algebra を書かずに、ドキュメントを関数で直接構築できる。
手組みのドキュメントは format と algebra の引数を受け取り、外側の構築関数へ渡す関数になる。

```yulang
use std::text::yumark::{
    cons, html_tag, nil, paragraph, render_html_doc, render_markdown_doc,
    strong, text,
}

my document(format, algebra) =
    paragraph(
        cons(
            text("Hello "),
            cons(strong(cons(text("Yumark"), nil)), nil),
        ),
        format,
        algebra,
    )

(
    html_tag (render_html_doc document),
    render_markdown_doc document,
)
```

HTML の結果は `"<p><span>Hello </span><strong><span>Yumark</span></strong></p>"` になる。
Markdown の結果は `"Hello **Yumark**\n\n"` になる。
内側の呼び出しは部分適用された構築関数である。
外側の `paragraph` だけが `format` と `algebra` を明示的に受け取り、同じ組をドキュメント全体へ渡す。

## 描画

組み込みの描画先は次の 2 個である。

| 描画先 | format 型 | 表現 | 入口 |
| --- | --- | --- | --- |
| HTML | `html_format` | `html_node { tag: str, body: str }` | `render_html_doc(document)` |
| Markdown | `markdown_format` | `str` | `render_markdown_doc(document)` |

`render_html_doc` は `html_node` を返す。
`html_tag` は、その node を HTML 文字列に変換する。
`html_node` は公開された単純な `struct` であり、ブラウザの DOM node ではない。
組み込みの HTML algebra は、text を `body` へ入れる前に HTML の特殊文字へ変換しない。
`html_tag` は node を文字列化するだけで、入力内容の安全性を検査しない。
`render_markdown_doc` は Markdown を直接返す。

`run_yumark(format, document)` は汎用の入口である。
format の `YumarkFormat` impl を 1 回解決し、その algebra を取得して、ドキュメント全体を実行する。
`html_algebra()` と `markdown_algebra()` は、組み込みの 2 個の algebra 値を直接使うために公開する。

## 独自の描画先

compiler を変更せずに描画先を追加できる。
`yumark_algebra 'repr` のすべての slot を定義し、新しい format 型に `YumarkFormat` を実装して、`run_yumark` を呼び出す。
algebra は閉じているため、描画先は追加できるが、ドキュメント操作を増やすとすべての描画先に slot の追加が必要になる。

次の完全な描画先は、構造的な markup を除いて plain text を返す。

```yulang
use std::text::yumark::{YumarkFormat, run_yumark, yumark_algebra}

struct plain_format { marker: str }

my plain_nil() = ""
my plain_cons(left: str, right: str) = std::text::str::concat left right
my plain_text(value: str) = value
my plain_paragraph(children: str) = children
my plain_heading(marker: str, level: int, children: str) = children
my plain_blank_line(marker: str) = marker
my plain_section_close(marker: str, children: str) = children
my plain_list_block(ordered: bool, items: str) = items
my plain_list_item(marker: str, children: str) = children
my plain_list_item_body(children: str) = children
my plain_code_fence(info: str, body: str) = body
my plain_quote_block(children: str) = children
my plain_emphasis(children: str) = children
my plain_strong(children: str) = children

my plain_algebra(): yumark_algebra str = yumark_algebra {
    nil: plain_nil,
    cons: plain_cons,
    text: plain_text,
    paragraph: plain_paragraph,
    heading: plain_heading,
    blank_line: plain_blank_line,
    section_close: plain_section_close,
    list_block: plain_list_block,
    list_item: plain_list_item,
    list_item_body: plain_list_item_body,
    code_fence: plain_code_fence,
    quote_block: plain_quote_block,
    emphasis: plain_emphasis,
    strong: plain_strong,
}

impl plain_format: YumarkFormat:
    type repr = str
    our format.yumark_algebra _ = plain_algebra()

my render_plain(document): str =
    run_yumark(plain_format { marker: "plain" }, document)

render_plain '{# Title
A **plain** paragraph.
}
```

結果は `"TitleA plain paragraph."` になる。

## 構文の境界

parser は、ドキュメントの lowering が扱える範囲より広い Yumark grammar を認識する。
block Yumark 内の `\note[body]` のような command は parse されるが、現在は lowering で失敗する。
`[label](target)` のような inline 式も同じ段階で失敗する。
これらは利用可能なドキュメント操作ではない。

`'[...]` と `'{...}` の式自体は、inline と block の各文脈に合う静的な語彙とともに利用できる。
parser が受理するという理由だけで、command と inline 式を `module` API として扱ってはならない。

## 早見表

| 操作 | 役割 |
| --- | --- |
| `nil` | 空のドキュメント sequence を構築する |
| `cons(head, tail)` | 2 個の構築関数を順番に結ぶ |
| `text(value)` | plain text を構築する |
| `paragraph(children)` | child を段落として包む |
| `heading(marker, level, children)` | 見出しを構築する |
| `blank_line(marker)` | 明示的な表示用 spacer を構築する。source の空行は使わない |
| `section_close(marker, children)` | section close marker と child を構築する |
| `list_block(ordered, items)` | 順序付きまたは順序なしの list を構築する |
| `list_item(marker, children)` | list item を構築する |
| `list_item_body(children)` | list item body を構築する |
| `code_fence(info, body)` | fenced code block を構築する |
| `quote_block(children)` | block quote を構築する |
| `emphasis(children)` | emphasis 付き inline content を構築する |
| `strong(children)` | strong inline content を構築する |
| `render_html_doc(document)` | 構築関数を `html_node` として描画する |
| `html_tag(node)` | `html_node` を HTML 文字列に変換する |
| `render_markdown_doc(document)` | 構築関数を Markdown の `str` として描画する |
| `run_yumark(format, document)` | `YumarkFormat` impl を使って描画する |
| `html_format_value()` | 組み込みの `html_format` marker を返す |
| `markdown_format_value()` | 組み込みの `markdown_format` marker を返す |
| `html_algebra()` | 組み込みの `yumark_algebra html_node` を返す |
| `markdown_algebra()` | 組み込みの `yumark_algebra str` を返す |

## 関連ページ

- [文字列](../strings)：文字列構文と interpolation
- [`std::text::str`](./str)：描画後の文字列に対する操作
- [struct と role](../structs)：独自の format と role impl の定義
- [標準ライブラリ一覧](./)：すべての `module` の一覧
