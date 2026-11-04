# Doc-comment declaration

## 1. Authority and scope

This page specifies the `syntax-v0` `DocCommentDeclaration` envelope,
Statement dispatch, direct Rowan CST, and recovery. The Authoritative
`notes/design/2026-09-01-doc-comment-yumark-addendum.md` and its explicit
amendments govern it. [Yumark document grammar](yumark-document.md) specifies
the document interior. Attachment semantics between a document and a later
declaration, lowering, name resolution, and presentation are outside scope.

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

`DocCommentDeclaration` is a standalone declaration, never trivia. At root it
is a direct `Root` child. In a nested canonical statement sequence it is a
child of the existing `Statement` wrapper. Root, braced, indented, and inline
colon bodies use the same canonical dispatch. An orphan document is valid.

The marker judge runs after caller-owned leading trivia and before a dynamic
operator only at canonical Statement start. It tests `---` before `--`.
An accepted marker at the statement base column ends the preceding expression
chain and wins over declared operators at that position.
Expression NUD, LED, and every other non-statement position retain the normal
user-declared operator path. A same-line semicolon does not start a doc
statement.

A root-leading doc declaration stops header discovery with `FirstNonHeader`;
later `use` and operator declarations are not header facts. Struct, enum,
record, role, and act field or owner-specific sequences do not admit a doc
declaration.

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

## 7. Composition and non-goals

The body composes with [Yumark document grammar](yumark-document.md). See also
the [syntax content model](../conventions/syntax-content-model.md),
[Rowan CST notation](../conventions/rowan-cst.md), and
[recovery topology](../conventions/recovery-error-invalid-topology.md).
A doc declaration adds no field member, declaration attachment, or synthetic
child of a following declaration.
