# Rowan CST notation

This page defines the notation and source-ownership conventions for Yulang's
lossless Rowan CST. It applies to the accepted `syntax-v0` grammar and direct
Rowan topology. It is a reference convention, not an implementation history.

## Authority and scope

The Authoritative *Syntax freeze and vertical-implementation completion-policy
amendment* (2026-09-17) preserves the accepted grammar, recovery ownership,
and direct Rowan topology as `syntax-v0`. The Authoritative *Rowan CST-only
successor amendment* and *Error-token and Invalid-node topology ordering
addendum* define the one-CST and recovery-topology conventions used here.

Construct pages define their accepted spellings and ordered child grammars.
This page defines neither a construct production nor diagnostic wording.

## Documentation notation

The notation is XML-like documentation. It is neither runtime XML nor an
interchange format. Paired tags denote Rowan nodes. A self-closing tag with a
`text` attribute denotes a source-bearing token leaf.

```xml
<OperatorChain>
  <PrefixOperator text="!" />
  <Missing />
</OperatorChain>
```

Structural nodes never contain bare character data. A source-bearing leaf
states its spelling in `text`; indentation and text outside a leaf therefore
do not represent source bytes.

The `text` attribute denotes reversible source spelling. This notation does
not use XML entities. It uses these canonical backslash escapes:

| Source character | `text` spelling |
| --- | --- |
| reverse solidus | `\\` |
| quotation mark | `\"` |
| carriage return | `\r` |
| line feed | `\n` |
| horizontal tab | `\t` |
| another U+0000--U+001F control character | `\u{XXXX}` with four uppercase hexadecimal digits |

Every other Unicode scalar value is literal. Decoding is exact: the decoded
spelling, rather than its visual notation, determines the leaf's UTF-8 byte
range. CRLF therefore remains distinct from LF, and a literal `\r` remains
distinct from a carriage return.

## Source order and losslessness

Nodes and token leaves appear in source order. Source-bearing leaves preserve
the complete source spelling; structural nodes add no unrepresented source
text. Reading the source-bearing leaves from left to right reconstructs the
source exactly.

Ordinary trivia outside a malformed run remains a source-bearing leaf owned by
its production. Trivia absorbed by a raw malformed run is represented by
`Error` leaves. A construct schema assigns each token and trivia leaf to one
grammar slot; this page does not assign construct-local slots.

## Recovery elements

`Missing` is a zero-width structural node in a documented grammar slot. It has
no `text` attribute and contributes no source bytes.

```xml
<OperatorChain>
  <PrefixOperator text="!" />
  <Missing />
</OperatorChain>
```

`Error` is always a token leaf, never a node. Each `Error` leaf represents an
already emitted physical source fragment in its owning slot. Adjacent leaves
can form one raw malformed run without exposing an invented grammar within the
run.

```xml
<Error text="@" />
<Error text="/*bad*/" />
```

Raw recovery maps every remaining physical fragment of its item to `Error`,
including interior trivia and Yumark quote-prefix fragments. It does not
absorb leading trivia already emitted by the owning production, or leading
trivia left for a retry or boundary owner.

`Invalid` is a structural node for schema-defined recovery that retains nested
grammar, a `Missing` child, or an `Error` child. It must not wrap an ordinary
raw `Error` token.

```xml
<Invalid>
  <Error text="@" />
  <ParenthesizedTypeGroup>
    <Missing />
  </ParenthesizedTypeGroup>
</Invalid>
```

The [recovery `Error` and `Invalid` topology](recovery-error-invalid-topology.md)
page defines the restricted structured owners.

## Source coordinates

Tree and diagnostic ranges are zero-based, half-open UTF-8 byte ranges. A
`Missing` range is zero-width. Source-bearing leaves determine their ranges
from their preserved spelling; structural nodes add no source text.

## Migration status

Direct Rowan construction and the `Error`-token/`Invalid`-node topology are
implemented. The CST-derived structural diagnostic interpreter is also
implemented as a shadow interpretation. Parser-ledger retirement remains
pending Gate 4, the atomic diagnostic migration. The final diagnostic direction
is CST and selected-syntax-environment derived; the temporary ledger is not a
second CST or a final source of truth.
