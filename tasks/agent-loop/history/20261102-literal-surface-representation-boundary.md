# Literal surface representation boundary

Date: 2026-11-02
Disposition: source-surface evidence only; parent premise delta 0.

## Observed source routes

The current `LocalSourceForm` producer has direct routes for unshadowed
`true`/`false` identifiers to `Boolean`, integer tokens to `Integer`, and
non-interpolated string tokens to `String`. Empty parenthesized expressions
are represented as `Unit`. These observations correct the earlier shorthand
that mentioned only Integer and String: Boolean and Unit routes are present.

The bounded native audit in
`notes/theory/2026-11-02-original-literal-carrier-r231.md` records these same
four producer families and notes that `DecodedString` is interpolation text,
not another L1 literal constructor. That audit found no FloatBits, Bytes, Path,
or Character variants in the inspected `LocalSourceForm` and literal producer.
This is a report about the inspected native representation, not a proof that
the entire repository has no such route or a reason to narrow the source
domain.

## Fixed mathematical source domain

The approved source rule in
`notes/design/2026-11-02-literal-l1-adoption.md` retains all eight raw
constructors: unit, bool, int, floatBits, string, bytes, path, and character.
The native observations above neither change that decision nor define the
Simple-sub generator or arbitrary-solution readout. Payload decoding from
integer spelling to `Int` and string spelling to the adopted raw `String`
payload also remains unproved in the cited audit.

## Research disposition

No source-domain restriction, semantic adoption, Rust change, Lean theorem,
test, or parent-theorem progress follows from this record. Parent premise delta
remains 0. A future source bridge still needs to account for all eight adopted
forms, preserve payload and source occurrence, and connect actual generated
constraints to every satisfying assignment in the original carriers.

Evidence locations:

- `crates/yu-hir/src/module/local_source.rs:2125-2134` (booleans)
- `crates/yu-hir/src/module/local_source.rs:2164-2176` (integer and string)
- `crates/yu-hir/src/module/local_source.rs:2190-2217` (empty parentheses to Unit)
- `notes/theory/2026-11-02-original-literal-carrier-r231.md` (bounded native audit)
- `notes/design/2026-11-02-literal-l1-adoption.md` (approved eight-form domain)
