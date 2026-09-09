# Rowan CST notation

This page defines the notation for Yulang's lossless Rowan CST. It is an
Authoritative target specification. Direct construction with
`rowan::GreenNodeBuilder` and the `Error`-token and `Invalid`-node topology
are implemented. The later CST-derived diagnostic migration remains pending.

## Documentation notation

The notation is XML-like documentation, not runtime XML and not an interchange
format. Paired tags denote Rowan nodes. A self-closing tag with a `text`
attribute denotes a source-bearing token leaf.

```xml
<OperatorChain>
  <PrefixOperator text="!" />
  <Missing />
</OperatorChain>
```

Structural nodes never contain bare character data. A source-bearing leaf
states its spelling in `text`, so indentation and ordinary text outside a leaf
cannot carry source bytes.

The `text` attribute denotes reversible source spelling. This documentation
notation is not XML: it does not use XML entities. It uses these canonical
backslash escapes:

| Source character | `text` spelling |
| --- | --- |
| reverse solidus | `\\` |
| quotation mark | `\"` |
| carriage return | `\r` |
| line feed | `\n` |
| horizontal tab | `\t` |
| another U+0000--U+001F control character | `\u{XXXX}` with four uppercase hexadecimal digits |

Every other Unicode scalar value is literal. Decoding the attribute is exact:
the decoded spelling, rather than its visual notation, determines the leaf's
UTF-8 byte range. Thus CRLF remains distinct from LF, and a literal `\r`
remains distinct from a carriage return.

## Nodes, tokens, and trivia

A node is a structural CST element and uses paired tags. A token leaf is a
source-bearing CST element and uses a self-closing tag with `text`. Children
appear in source order.

Ordinary trivia outside a malformed run remains its own source-bearing leaf in
the owning production. Trivia absorbed by a raw malformed run is represented
by `Error` leaves instead. A schema must assign each token and trivia leaf to
one grammar slot; this page does not assign individual construct slots.

## Recovery elements

`Missing` is a zero-width structural node in a documented grammar slot. It has
no `text` attribute and contributes no source bytes.

```xml
<OperatorChain>
  <PrefixOperator text="!" />
  <Missing />
</OperatorChain>
```

`Error` is the implemented token topology. It is always a token leaf, not a node.
Each leaf represents an already-emitted physical source fragment in its owning
slot. Adjacent leaves can form one raw malformed run; the run exposes no
invented internal grammar.

```xml
<Error text="@" />
<Error text="/*bad*/" />
```

Raw recovery maps every remaining physical fragment of its item to `Error`,
including interior trivia and a Yumark quote prefix. It does not absorb leading
trivia that the owning production has already emitted, or leading trivia that
remains with a retry or boundary owner.

`Invalid` is the implemented node topology. It is used only for a schema-defined
structured recovery that retains nested grammar, `Missing`, or nested `Error`
children. An ordinary raw `Error` token must not receive an `Invalid` wrapper.

```xml
<Invalid>
  <Error text="@" />
  <ParenthesizedTypeGroup>
    <Missing />
  </ParenthesizedTypeGroup>
</Invalid>
```

## Source coordinates

Tree ranges and diagnostic ranges use zero-based, half-open UTF-8 byte ranges.
The range of a `Missing` node is zero-width. Source-bearing leaves preserve the
source spelling that determines their ranges; a structural node does not add
unrepresented source text.

## Implemented and pending topology

The direct Rowan builder emits `Error` token leaves and the restricted
`Invalid` node. The parser still publishes recovery diagnostics through its
temporary compatibility machinery. A later migration derives structural
diagnostics from the CST. The
[source-root and diagnostic ownership](source-root-and-diagnostics.md) page
specifies that later publication boundary.
