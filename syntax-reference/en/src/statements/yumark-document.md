# Yumark document grammar

## 1. Authority and scope

This page specifies the `syntax-v0` Yumark grammar inside a doc-comment
declaration. The Authoritative
`notes/design/2026-09-01-doc-comment-yumark-addendum.md`,
`notes/design/oracles/2026-09-01-yumark-draft.md`, and later explicit
amendments govern it. [Doc-comment declaration](doc-comment-declaration.md)
specifies the envelope and Statement dispatch. Rendering, macro expansion,
and document-attachment semantics are outside scope.

## 2. Block grammar

```text
YumarkDocument := YumarkBlock*
YumarkBlock := BlankLine | Section | List | Quote | CodeFence
             | Paragraph | Command | My | Use | IfChain
```

A section heading begins with a line-start run of `#`. An implicit section
owns blocks until the next section boundary at the same or higher level. An
explicit section has a terminal `:`, requires a strictly deeper body, and may
have its corresponding section close.

A list item owns its marker and one `YmListItemBody`; a sibling marker, dedent,
or parent boundary ends that body. Quotes have prefix and explicit fenced
forms; depth and opener column determine an explicit close. Blank lines remain
`YmBlankLine` nodes. Consecutive ordinary text lines form a `YmParagraph`.

## 3. Inline grammar

```text
YumarkInline := Text | Group | Link | Image | Apply | Reference
              | Emphasis | Strong
```

`[...]` is an inline group, `[label](destination)` is a link, and
`![label](destination)` is an image. `*...*` and `**...**` are emphasis and
strong, selected longest-first. Inline apply and reference forms may own
document or Yulang arguments. Line-doc mode disables block starters and ends
at the first physical newline.

## 4. Raw fences

A triple-backtick opener produces `YmCodeFence` with marker, info, opening
newline, raw text, and a recovered close. Neither Yumark inline grammar nor
Yulang grammar runs in a raw body. Only an exact triple backtick at the opener
column closes the fence.

A fence whose first info atom is exact `yulang` is the special form selected
by the later parsed-Yulang amendment. Convergence of that body into the
canonical Yulang adapter is deferred to gate O6; Gate 6 does not fabricate
body facts.

## 5. Commands, `do`, `\if`, `\my`, and `\use`

A general command begins with backslash and a name, then may own Yulang and
document arguments in source order. An immediate document argument, `do`, a
local body, or a document/body after Yulang arguments determines its promotion
form. A local body is a braced or strictly indented document. A `do` capture is
an `YmDoCapture` child of its initiating command and owns later sibling blocks
in source order.

`\if` produces an `YmIfChain` containing `YmIf`, zero or more `YmElsif`, and
an optional `YmElse`. A condition is canonical Yulang inside
`YmIfCondition` or `YmElsifCondition`. Each branch body is a local Yumark
document; an inner body does not consume the branch boundary.

`\my` has a bare or parenthesized head. Its head is a canonical `Pattern`
inside `YmMyBindingHead`. Its one body is an inline expression, indented
expression, braced document, or indented document. `\use` has a parenthesized
form or a semicolon-terminated bare form and owns a canonical `UseTree`.

## 6. Embedded Yulang ownership

Yumark places canonical Yulang only in these closed adapter homes.

| Yumark owner | canonical Yulang child |
| --- | --- |
| `YmYulangArgs` | command/reference call arguments |
| `YmInlineApplyArgs` | inline-apply arguments |
| `YmMyBindingHead` | `Pattern` |
| `YmMyExpressionBody` | `OperatorChain` |
| `YmUse` | `UseTree` |
| `YmIfCondition`, `YmElsifCondition` | condition `OperatorChain` |

Embedded Yulang never opens a new public `Root`, `Statement`, or declaration
dispatch. It is not active in a raw fence, `YmDocArg`, or plain text. The
Yumark wrapper owns each delimiter exactly once, and a canonical child does
not duplicate a missing close owned by its wrapper.

## 7. Source-order Rowan schema

`YmDoc` contains recovered blocks in source order. Principal direct-child
orders are:

| form | direct-child order |
| --- | --- |
| section | heading, implicit/explicit `YmDoc` body, optional section close |
| list item | marker, `YmListItemBody` |
| quote | opener/prefix, document, recovered close for explicit form only |
| raw fence | open marker, info, opening newline, raw text, recovered close |
| general command | head/arguments, optional `YmCommandBody`, optional `YmDoCapture` |
| `\my` | `YmMyBindingHead`, exactly one body form |
| `\use` | backslash/name, route, terminating semicolon for bare form |
| if chain | `YmIf`, `YmElsif`*, `YmElse`? |

The direct CST streams one iterative grammar. Section, list, quote, group,
body, and argument nesting use an explicit frame stack rather than Rust
recursion, so a Rust call-depth limit is not a language limit.

## 8. Recovery vocabulary

Recovery nodes remain generic `Missing` or `Error`. Typed identity is the pair
of `YumarkOwner` and `YumarkSlot`.

```text
YumarkOwner := DocComment | Section | List | ListItem | Quote | CodeFence
             | InlineGroup | InlineLink | InlineImage | InlineApply
             | InlineReference | Emphasis | Strong | Command | My | Use
             | DocArgument | DoCapture | IfChain | IfBranch | ElsifBranch
             | ElseBranch

YumarkSlot := Starter | Name | Head | Arguments | Condition | BodyIntroducer
            | Body | Destination | BranchPredecessor | ClosingDelimiter
            | SectionClose | QuoteForm | ExpressionBody | Route | Terminator
```

A missing delimiter is a zero-width `Missing`. A malformed raw run is a
non-empty `Error` up to the active frame's safe stop. Safe stops include a
newline, active close, block-doc close, quote boundary, list sibling or
dedent, fence close, command-body boundary, and EOF. One committed recovery
record produces one generic recovery node at the same range.

## 9. Example and composition

````yulang
---
# Section
- first
- second with **strong** and [link](target)
> quote
\note[document argument]
\if(condition){shown}\else{fallback}
```text
raw *not emphasis*
```
---
````

A Yumark document is reachable only through the line or block envelope of a
[doc-comment declaration](doc-comment-declaration.md). See also the
[syntax content model](../conventions/syntax-content-model.md) and
[recovery topology](../conventions/recovery-error-invalid-topology.md).
