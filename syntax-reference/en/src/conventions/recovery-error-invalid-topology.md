# Recovery `Error` and `Invalid` topology

This page defines the `syntax-v0` recovery topology for the lossless Rowan CST.
It specifies retained source structure, not accepted malformed syntax, grammar
slots, expected alternatives, or public diagnostic wording.

## Authority and scope

The Authoritative *Syntax freeze and vertical-implementation completion-policy
amendment* (2026-09-17) preserves `Missing`, raw `Error`, and structured
`Invalid` as recovery facts. The Authoritative *Error-token and Invalid-node
topology ordering addendum* defines their topology. These conventions retain
the accepted-input and recovery-ownership contracts.

## Raw malformed source

Raw recovery emits every physical source fragment that it owns as an `Error`
token leaf. It does not create a structural `Error` node.

```xml
<Error text="@" />
<Error text="/*bad*/" />
```

Adjacent `Error` leaves can form one opaque malformed run in source order. The
run has no invented internal grammar, and its leaf count is not a diagnostic
count.

Raw recovery emits its remaining physical fragments as `Error`, including
interior trivia, Yumark quote-prefix fragments, same-line EOF leading, and the
two consumed retry-leading prefixes. Trivia already emitted by an owning
production remains outside the run. Leading trivia left for a retry or
boundary owner also remains outside the run. Accepted tokens and ordinary
trivia outside raw recovery retain their native token kinds.

## Structured recovery

`Invalid` is a structural Rowan node for recovery that retains nested grammar,
a `Missing` child, or an `Error` child. It must not wrap an ordinary raw
`Error` token.

Only these structured owners may emit `Invalid`:

- Polymorphic-variant tag-name recovery.
- Record-pattern wrong-kind item or separator recovery.

This topology schematic is not a construct schema:

```xml
<Invalid>
  <Error text="@" />
  <Missing />
</Invalid>
```

`Invalid` retains nested source order and nested recovery elements. No other
owner may add an `Invalid` node by analogy.

## Structural diagnostic interpretation

The implemented shadow CST interpreter reads structural recovery from the CST
in source order. A `Missing` occurrence has its zero-width range. A maximal
adjacent group of raw `Error` tokens in one slot and immediate parent is one
malformed-input occurrence. Ordinary trivia, `Missing`, a nested node, or a
slot boundary ends the group. An `Invalid` occurrence is visited before its
children and keeps its outer range even when it contains valid nested syntax.

Cataloged occurrences can use precise schema-derived interpretation. Other
occurrences use a deterministic generic interpretation from CST facts only:
recovery kind, range, occurrence path or immediate structural parent, and
source/preorder ordinal. The interpreter does not read parser recovery records,
replay parsing, relex an opaque `Error`, infer a hidden recovery episode, or
create recovery nodes.

Environment-only facts, including operator conflicts, do not add `Invalid` or
otherwise mutate the CST.

## Publication status

The shadow interpreter is implemented. Public syntax diagnostics still use the
temporary parser ledger while Gate 4, the atomic diagnostic migration, remains
pending. Gate 4 requires total deterministic CST-derived interpretation; it
does not require exhaustive per-slot precision before ledger retirement.

The [source root, headers, and diagnostic ownership](source-root-and-diagnostics.md)
page defines the root and publication boundary. The [Rowan CST notation](rowan-cst.md)
page defines reversible `text` spelling and UTF-8 byte ranges.
