# Recovery `Error` and `Invalid` topology

This page specifies the implemented recovery topology for the lossless Rowan
CST. It specifies source shape only. It does not assign grammar slots, derive
expected syntax, or define the public diagnostic result.

## Raw malformed source

Raw recovery emits every physical source fragment that it owns as an `Error`
token leaf. It does not create a structural `Error` node.

```xml
<Error text="@" />
<Error text="/*bad*/" />
```

Adjacent `Error` leaves can form one opaque malformed run in source order.
The leaves do not expose an invented grammar within that run. Their count is
not a diagnostic count.

The raw mode emits its remaining physical fragments as `Error`, including
interior trivia, Yumark quote-prefix fragments, same-line EOF leading, and
the two consumed retry-leading prefixes. Trivia that an owning production
already emitted remains outside the run. Leading trivia left for a retry or
boundary owner also remains outside the run. Accepted tokens and ordinary
trivia outside raw recovery retain their native token kinds.

## Structured recovery

`Invalid` is a paired Rowan node. It is reserved for structured recovery that
retains nested grammar, a `Missing` child, or an `Error` child. It must not
wrap an ordinary raw `Error` token.

The following are the only structured owners that may emit `Invalid` in this
topology gate:

- Polymorphic-variant tag-name recovery.
- Record-pattern wrong-kind item or separator recovery.

The following is a topology schematic, not a construct schema:

```xml
<Invalid>
  <Error text="@" />
  <Missing />
</Invalid>
```

`Invalid` retains its nested source order and nested recovery elements. No
other owner may add an `Invalid` node by analogy.

## Missing and diagnostic publication

`Missing` remains a zero-width structural node in its containing grammar slot.
The Error-token and Invalid-node migration changes neither recovery ownership
nor the existing parser diagnostic machinery. Parser recovery records,
structured reservations, frozen-header reconciliation, diagnostic IDs,
and public diagnostic construction remain temporary compatibility machinery.

The complete per-slot schema is still required before diagnostics are derived
from a CST walk and before that compatibility machinery is removed. The
[source root, headers, and diagnostic ownership](source-root-and-diagnostics.md)
page defines that later boundary.

## Notation and ranges

The tags on this page use the XML-like Rowan notation, not runtime XML. Each
`Error` leaf owns the source spelling in its `text` attribute. The
[Rowan CST notation](rowan-cst.md) page defines reversible attribute escaping
and UTF-8 byte ranges.
