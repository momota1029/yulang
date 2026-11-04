# Doc-comment declaration

## 1. Authority and scope

This page specifies the `syntax-v0` `DocCommentDeclaration` envelope,
Statement dispatch, direct Rowan CST, and recovery. The Authoritative
`notes/design/2026-09-01-doc-comment-yumark-addendum.md` and its explicit
amendments govern it. The G12 attachment extension follows `spec/01-lexical.md`
§1.2 and §7 of `notes/design/2026-11-04-parser-gap-closure-addendum.md`.
[Yumark document grammar](yumark-document.md) specifies the document interior.
The parser preserves each document and its syntactic owner; concatenation,
lowering, name resolution, and presentation are outside scope.

## 2. Accepted syntax

```text
DocCommentDeclaration := LineDocComment | BlockDocComment
LineDocComment := "--" InlineDocument(LineDocMode)
BlockDocComment := "---" H* PhysicalNewline
                   BlockDocument(BlockDocMode)
                   RecoveredBlockDocClose
RecoveredBlockDocClose := DocBlockClose | Missing(DocComment, ClosingDelimiter)
DocBlockClose := LineStart "---" H* (PhysicalNewline | EOF)
```

`H` is a space or tab. Horizontal trivia and the physical newline participate
in marker admission, but the marker token commits only the `--` or `---`
bytes. A line form does not own its first physical newline. A block close does
not own its horizontal suffix or newline; those return to the outer statement
sequence.

## 3. Admission, dispatch, and boundaries

A leading `DocCommentDeclaration` is a standalone declaration, never trivia.
At root it is a direct `Root` child. In a nested canonical statement sequence
it is a child of the existing `Statement` wrapper. Root, braced, indented, and
inline colon bodies use the same canonical dispatch. An orphan document is valid.
A leading document on its own line directly before a declaration documents
that declaration; consecutive leading documents remain in source order.

The marker judge tests `---` before `--` at canonical Statement start.
An accepted marker at the statement base column ends the preceding expression
chain and wins over declared operators at that position. A same-line semicolon
does not start a standalone doc statement.

When `--` is absent from the effective operator table, a binding also accepts
a line document after its complete expression on the line where the binding
started, or directly after its `=` on that line before a body on following
lines. If several bindings start on a line, the last one owns the document.
A declared `--` retains its operator meaning in both positions. Continuation
lines, required operands after operators, and the interior of parentheses or
call arguments keep their existing parsing behavior.

Struct fields, enum variants, role methods, and act operations accept leading
line documents on their own lines and trailing line documents on the member's
start line. A member with `=` also accepts the after-`=` form. A comma between
a completed field or variant and its trailing document is kept with that member.
A document immediately after a member-body opener on the same line is not a
leading member document. Record type fields retain their existing behavior.

A root-leading doc declaration stops header discovery with `FirstNonHeader`;
later `use` and operator declarations are not header facts.

A block opener or close requires physical line start, the opening base column,
exact `---`, and only a horizontal suffix. `---x`, `----`, mid-line `---`,
close-like text on the opening line, and a differently indented marker are not
envelope markers. `//` and `/* ... */` remain ordinary Yulang comments.

## 4. Source-order Rowan schema

```text
LineDocComment := DocCommentDeclaration(
  DocLinePrefix,
  YmDoc
)

BlockDocComment := DocCommentDeclaration(
  DocBlockOpen,
  Whitespace?,
  Newline,
  YmDoc,
  DocBlockClose | Missing
)
```

The direct CST streams the neutral Yumark grammar into the current builder; it
does not build or replay an AST event list. Source text remains lossless,
including trivia and recovery. Root form gains no synthetic `Statement`; only
nested form has the existing wrapper.

Attached line documents reuse `DocCommentDeclaration(DocLinePrefix, YmDoc)`.
They are direct children of the owning `BindingStatement`, `StructField`, or
`EnumVariant`. Role methods and act operations use `BindingStatement` too.
A binding's after-`=` document sits between `BindingHeader` and `BindingBody`;
its trailing document follows `BindingBody` (or `BindingHeader` for a method
header without a body). A field's after-`=` document follows its `Equals` token.
A trailing member document follows its type, payload, or default expression
and any comma immediately preceding the document.

Leading documents keep the sibling layout described above. In field and variant
sequences they precede the member node directly; in role and act bodies their
`Statement` wrapper precedes the member's `Statement`, with any block separator
between them. A later phase can therefore find the owner from the tree alone.
Leading and attached documents are both retained in source order; the parser
does not concatenate them. No new `SyntaxKind` is introduced.

## 5. Recovery CST

An unterminated block document places exactly one zero-width `Missing` at EOF.
Its typed identity is `YumarkOwner::DocComment` with
`YumarkSlot::ClosingDelimiter`. Close-like text that fails the strict close
predicate remains document text and does not cause an immediate missing node.

```xml
<DocCommentDeclaration>
  <DocBlockOpen text="---" /><Newline text="\n" />
  <YmDoc><YmParagraph><YmText text="body" /></YmParagraph></YmDoc>
  <Missing />
</DocCommentDeclaration>
```

Recovery inside Yumark remains with the exact section, list, quote, fence,
inline, or command owner. The envelope does not duplicate an inner recovery
for the same cause.

## 6. Source and CST example

```yulang
-- line *document*
my value = 1
---
# Heading
- item
> quote
---
```

The first newline is outside the line declaration. In block form, the opening
newline is inside the declaration and the newline after the closing `---`
belongs to the outer statement sequence.

### Binding and member line documents

```yulang
-- leading
my g x = x -- trailing
my h x = -- after equals
    x
struct point {
    x: int, -- x
    -- y
    y: int,
}
```

Both documents for `g` remain in order. The after-`=` document belongs to `h`;
the field documents belong to `x` and `y`, respectively. Block documents retain
their existing leading-only envelope and dispatch.

## 7. Composition and non-goals

The body composes with [Yumark document grammar](yumark-document.md). See also
the [syntax content model](../conventions/syntax-content-model.md),
[Rowan CST notation](../conventions/rowan-cst.md), and
[recovery topology](../conventions/recovery-error-invalid-topology.md).
A document adds no semantic member and does not change declaration evaluation.
Leading documents remain siblings; attached line documents use the owner-child
positions in §4.
