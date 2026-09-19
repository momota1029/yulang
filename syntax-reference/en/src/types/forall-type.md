# `forall` types

## 1. Authority and scope

This page defines `ForallType` in `syntax-v0`. The Authoritative `forall`
sections of the 2026-08-20 syntax architecture and the `forall` current-Item
recovery authority govern this page.

It covers the contextual type-primary spelling `for 'a 'b: T`, its binders,
body, bounded layout, and recovery. It does not define statement `for`,
non-apostrophe binders, type meaning, lowering, or diagnostic wording.

## 2. Accepted syntax

```text
ForallType := "for" ForallTypeBinder { ForallTypeBinder } ForallColonTrivia ":" ForallBodyTrivia TypeExpression
ForallTypeBinder := ForallBinderBoundary ApostropheTypeBinderName
ForallBinderBoundary := nonempty same-line trivia | deeper continuation trivia
ApostropheTypeBinderName := "'" UnicodeIdentifierBody
```

The layout base is taken immediately after the accepted `for`. Binder boundaries
are nonempty. Colon and body gaps may be empty. An equal-or-shallower newline
does not become `forall`-owned trivia.

## 3. Admission and boundaries

At canonical type NUD position, exact maximal `for` admits `ForallType` before
an identifier. `forx`, `forall`, and `for_` remain identifiers. At a TypeApply
LED position, `for` is an ordinary identifier seed rather than another forall.

Before a binder, only an apostrophe binder or `:` makes progress. After a
binder, another apostrophe starts the next binder; a non-binder primary retries
as the body after a missing colon. The body owns paths, calls, applies, and
arrows. A raw forall is terminal, so an outer tail requires grouping.

## 4. Direct Rowan CST

`ForallType` contains `ForKw`, direct `ForallTypeBinder` children, colon-side
trivia, `Colon`, body trivia, and its direct body `TypeExpression` in source
order. Each binder contains its boundary trivia and apostrophe name. No
delimiter, list, or synthetic separator node is added.

## 5. Recovery CST

The first missing binder produces one binder-slot `Missing` and does not
cascade to colon or body. An adjacent binder produces a missing binder boundary
and retries the binder at the same position. After an accepted binder, EOF or a
protected boundary produces only a missing colon; a non-binder primary produces
a missing colon and retries the body.

A malformed binder, colon-side continuation, or body is a raw `Error` group in
the selected slot. A missing or malformed body after an accepted colon stays in
the body slot. Commas and semicolons are not binder separators, and protected
stops, closes, caller boundaries, and qualifying newlines remain unconsumed.

## 6. Source/CST examples

`for 'a: A -> A` has one direct `ForallTypeBinder`; its body contains the arrow
tail.

```text
for
  'a
  'b:
    Pair('a, 'b)
```

Each binder owns its leading continuation boundary. The deeper colon-to-body
trivia belongs to `ForallType`.

`(for 'a: 'a)::Result` groups the forall before the path tail.

## 7. Composition

[Standalone `TypeExpression` core](type-expression-core.md) defines the
recursive body grammar. The [syntax content model](../conventions/syntax-content-model.md),
[Rowan CST notation](../conventions/rowan-cst.md), and [recovery `Error` and
`Invalid` topology](../conventions/recovery-error-invalid-topology.md) define
the shared `syntax-v0` conventions.
