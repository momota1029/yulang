# Rowan CST notation text-attribute escaping addendum

Status: Authoritative

Approved-by: user

Approved-at: 2026-09-09

Drafted-by: primary from the user's XML-like CST notation decision

Date: 2026-09-09

Scope: the reversible spelling of a source-bearing `text` attribute in the
XML-like Rowan CST documentation notation. This is documentation notation
only. It does not create runtime XML, a serializer, a parser input format, or
an additional CST representation.

## Rule

The attribute value is decoded with the following canonical escapes, before
its spelling contributes to the leaf's UTF-8 byte range:

| source character | notation spelling |
| --- | --- |
| reverse solidus | `\\` |
| quotation mark | `\"` |
| carriage return | `\r` |
| line feed | `\n` |
| horizontal tab | `\t` |
| any other U+0000--U+001F control character | `\u{XXXX}` with four uppercase hexadecimal digits |

Every other Unicode scalar value is written literally. In particular, `&`,
`<`, `>`, and apostrophe have no XML-entity substitution. The notation is not
parsed as XML. A literal reverse solidus is always escaped, so a source spelling
which itself contains `\r`, `\n`, or `\u{000D}` remains distinct from a
carriage return, line feed, or other control character.

Decoding is exact and reversible. The resulting Rust/Yulang source spelling,
not the visual width of its notation, determines the token leaf and all source
ranges. This preserves LF and CRLF distinctly.

## Narrow supersession

This addendum supersedes only the unresolved exact-escaping sentence in
`2026-09-09-successor-rowan-cst-only-amendment-draft.md` **Rowan node
notation**, and the corresponding pending-escaping statements in the initial
`syntax-reference` Rowan-notation pages. All node/token, lossless-source and
diagnostic decisions remain unchanged.
