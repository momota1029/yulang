# Layout-aware separator authority

## Scope

This rule defines the comma-or-newline boundary for `ParenthesizedExpression`,
`ParenthesizedPattern`, `ListPattern`, `RecordPattern`, and inline colon
arguments that have no outer sequence owner. It decides whether trivia after a
complete item separates the next item or continues the current item.

The rule does not add semicolons as shared separators. It does not change item
grammar, literal trailing-comma meaning, matching-close ownership, or
statement and arm boundaries.

## Boundary rule

Each delimited sequence captures its layout base at its opener, before its
first item. If the opener's following trivia contains a physical newline and
the indentation following its last physical newline is deeper than the incoming
baseline, that indentation is the base. Otherwise the incoming baseline is the
base.

```text
DelimitedSeparator := ExplicitCommaBoundary
                    | ImplicitNewlineBoundary(base)

ImplicitNewlineBoundary(base) :=
    maximal trivia containing a physical newline
    whose following-line indentation <= base
```

After a complete item, an explicit comma takes priority. Without a comma, a
qualifying newline is a boundary. A deeper newline remains continuation trivia
for the current item. If neither separator occurs and another item starts on
the same line, recovery supplies the missing separator at that position.

For an inline colon application, a visible outer sequence owner retains both
comma and qualifying-newline authority. The colon RHS then has exactly one
argument. Without such an owner, the colon application owns its comma and
qualifying-newline boundaries after its first argument has started.

## Source order in the Rowan CST

An explicit comma is a source-bearing comma token in the sequence owner. An
implicit newline adds no separator token, `Missing(Comma)`, or separator node.
Its newline, spaces, and comments remain ordinary trivia in the container in
source order between the completed item and the next item or close.

This rule therefore adds no CST node. Literal trailing-comma meaning remains
literal: a trailing implicit newline is a valid terminator, but it is not a
trailing comma.

## Recovery and handoff

A qualifying newline between items, or immediately before the local close, is
valid and produces no recovery structure. A deeper newline is returned to the
current item; the sequence must not promote the following text to a new item.
A same-line next item without a comma receives one zero-width missing
separator and retries at the same source position.

If an outer owner already claims the gap, this rule does not consume it. In
particular, [ambient statement-owner boundary](ambient-statement-owner-boundary.md)
can retain a strict statement dedent or an `else`/`elsif` companion for the
enclosing statement context.

## Examples

| Source | Result |
| --- | --- |
| `()` | An empty parenthesized sequence. |
| `(a,)` | One item with a literal trailing comma. |
| `(\n  a\n  b\n)` | Base indentation `2`; two items; the final newline is a valid terminator. |
| `(a\nb)` at base `0` | Two items separated by a qualifying newline. |
| `(a\n  b)` at base `0` | The deeper newline continues the first item; `b` is not a second item. |
| `(f: a, b)` | The parenthesized sequence owns the comma, so the colon RHS has one argument. |

## Composition and limits

Construct pages define their own opener, item grammar, close, and any
construct-specific recovery. This page supplies only the shared newline
classification. It does not decide malformed TypeExpression newline recovery;
see [TMN](tmn-malformed-newline-owner-policy.md). It does not define the
ambient statement-owner cases that can take an otherwise local gap.

The governing source is the Authoritative *layout-aware comma-or-newline
delimited sequence authority* in
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`,
lines 9314–9693.
