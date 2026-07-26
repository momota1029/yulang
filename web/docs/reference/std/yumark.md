# `std::text::yumark` <Badge type="warning" text="Provisional" />

`std::text::yumark` defines the Yumark document algebra, the builders used by
Yumark expressions, and renderers for HTML nodes and Markdown.

> **Provisional:** Static Yumark documents work, but commands, inline
> expressions, injection, and some tooling remain incomplete. The construction
> and rendering API may change as those parts are added.

## Document values

A Yumark document value is a reusable **document builder**. Given a format and
a `yumark_algebra 'repr`, the builder produces that algebra's representation.
It is not a concrete document tree to inspect or pattern-match.

A let-bound builder remains polymorphic in its representation. The same value
can therefore be passed to `render_html_doc` and `render_markdown_doc`; each
call runs it with a different algebra.

## Literal construction

`'[...]` creates an inline Yumark builder, and `'{...}` creates a block Yumark
builder. These forms are Yulang expression syntax. The compiler lowers their
static content to the builders in `std::text::yumark`; the module does not
declare a separate parser or macro syntax.

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

The result contains `"<span>hello </span><em><span>Yumark</span></em>"` and
`"hello *Yumark*"` for the inline document. The block document renders as an
`h1` followed by a paragraph in HTML, or as the original heading and paragraph
in Markdown.

The supported static vocabulary includes text, paragraphs, headings, section
closes, ordered and unordered lists, code fences, block quotes, emphasis, and
strong text. Source blank lines separate paragraphs; they do not call the
visible `blank_line` builder.

## Builder construction

Programs can build a document directly without writing an algebra. A manual
document is a function that accepts the format and algebra parameters, then
passes them to the outer builder.

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

The result is
`("<p><span>Hello </span><strong><span>Yumark</span></strong></p>", "Hello **Yumark**\n\n")`.
The inner calls are partially applied builders. Only the outer `paragraph`
receives `format` and `algebra` explicitly; it passes the same pair through
the document.

## Rendering

The built-in rendering targets are:

| Target | Format type | Representation | Entry point |
| --- | --- | --- | --- |
| HTML | `html_format` | `html_node { tag: str, body: str }` | `render_html_doc(document)` |
| Markdown | `markdown_format` | `str` | `render_markdown_doc(document)` |

`render_html_doc` returns an `html_node`. `html_tag` turns that node into an
HTML string. An `html_node` is a plain public struct, not a browser DOM node.
The built-in HTML algebra does not escape text before placing it in `body`, so
`html_tag` is serialization rather than sanitization. `render_markdown_doc`
returns Markdown directly.

`run_yumark(format, document)` is the generic entry point. It resolves the
format's `YumarkFormat` implementation once, obtains its algebra, and runs the
whole document with that algebra. `html_algebra()` and `markdown_algebra()`
expose the two built-in algebra values for direct use.

## Custom rendering targets

A program can add a target without changing the compiler. Define every slot of
`yumark_algebra 'repr`, implement `YumarkFormat` for a new format type, and
call `run_yumark`. The algebra is closed: adding a target is extensible, but
adding a new document operation requires every target algebra to gain a slot.

This complete target strips structural markup and returns plain text:

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

The result is `"TitleA plain paragraph."`.

## Syntax boundary

The parser recognizes more Yumark grammar than the document lowerer supports.
In particular, grouped block commands such as `\note[body]` and inline
expressions such as `[label](target)` parse inside block Yumark, but currently
fail during lowering. They are not available document operations.

The `'[...]` and `'{...}` expression forms themselves are usable with the
static vocabulary appropriate to their inline and block contexts. Commands
and inline expressions must not be treated as module APIs merely because the
parser accepts them.

## Quick reference

| Operation | Purpose |
| --- | --- |
| `nil` | Build an empty document sequence |
| `cons(head, tail)` | Join two builders in order |
| `text(value)` | Build plain text |
| `paragraph(children)` | Wrap children as a paragraph |
| `heading(marker, level, children)` | Build a heading |
| `blank_line(marker)` | Build an explicit visible spacer; source blank lines do not use it |
| `section_close(marker, children)` | Build a section-close marker and its children |
| `list_block(ordered, items)` | Build an ordered or unordered list |
| `list_item(marker, children)` | Build a list item |
| `list_item_body(children)` | Build a list-item body |
| `code_fence(info, body)` | Build a fenced code block |
| `quote_block(children)` | Build a block quote |
| `emphasis(children)` | Build emphasized inline content |
| `strong(children)` | Build strong inline content |
| `render_html_doc(document)` | Render a builder as `html_node` |
| `html_tag(node)` | Turn an `html_node` into an HTML string |
| `render_markdown_doc(document)` | Render a builder as Markdown `str` |
| `run_yumark(format, document)` | Render through a `YumarkFormat` implementation |
| `html_format_value()` | Return the built-in `html_format` marker |
| `markdown_format_value()` | Return the built-in `markdown_format` marker |
| `html_algebra()` | Return the built-in `yumark_algebra html_node` |
| `markdown_algebra()` | Return the built-in `yumark_algebra str` |

## See also

- [Strings](../strings) — string syntax and interpolation
- [`std::text::str`](./str) — operations on rendered strings
- [Structs and roles](../structs) — defining a custom format and role implementation
- [Standard Library Catalogue](./) — the full module inventory
