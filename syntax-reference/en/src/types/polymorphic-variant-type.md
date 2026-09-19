# Polymorphic-variant types

## 1. Authority and scope

This page defines `PolymorphicVariantType` in `syntax-v0`. The Authoritative
polymorphic-variant sections of the 2026-08-20 syntax architecture, the
polymorphic-variant current-Item recovery authority, and the structured
`Invalid` topology authority govern this page. The 2026-09-10
polymorphic-variant foreign-close slot authority governs its foreign-close
wrapper.

It covers the type-only form `:{A Int, B}`, tag and payload boundaries, and
recovery. It does not define expression or pattern variants, type semantics,
lowering, inference, or diagnostic wording.

## 2. Accepted syntax

```text
PolymorphicVariantType := ":" adjacent "{" G* [ PolymorphicVariantTag { PolyVariantTagBoundary PolymorphicVariantTag } [ PolyVariantTagBoundary ] ] "}"
PolymorphicVariantTag := Identifier { PolymorphicVariantPayload }
PolymorphicVariantPayload := nonempty same-line trivia TypeExpressionInTypeMlScope
PolyVariantTagBoundary := comma | qualifying newline
```

The `{` begins exactly at the colon end. A physical newline ends a tag's inner
payload sequence. Only the outer tag list can classify a qualifying newline as
a tag boundary.

## 3. Admission and boundaries

The canonical primary judge returns active stops and caller-owned closes before
it probes `for`, adjacent `"'["`, and adjacent `":{"`. Bare `:` does not
commit: `:{A}` is a variant primary, while `: {A}`, `:/*c*/{A}`, and `:\n{A}`
are not.

After admission, the outer brace/list owner controls tags and close recovery.
Within a tag, same-line payload candidates are siblings in Type-ML scope, not
TypeApply tails of one another. A completed variant returns to the ordinary
tail judge, so `F :{A}` is an apply argument.

## 4. Direct Rowan CST

`PolymorphicVariantType` contains colon, brace, direct
`PolymorphicVariantTag` children, commas, trivia, and close in source order.
Each tag contains its name and direct `PolymorphicVariantPayload` children.
Each payload contains its boundary trivia and direct `TypeExpression`.

`PolymorphicVariantForeignClose` wraps exactly one locally consumed foreign
close and its raw `Error` group. It is not a wrapper for an item error, a tag
separator error, accepted punctuation, trivia, `Missing`, retry source, or
`Invalid`. A tag-separator error stays a direct raw group in its separator
slot; it does not use the foreign-close wrapper.

Wrong-kind Type-shaped tag names use the restricted structured `Invalid`
topology defined for this owner. A malformed non-NUD tag remains a raw `Error`
group. No synthetic inner payload-list wrapper is added.

## 5. Recovery CST

A non-adjacent or incomplete `:{` introducer has no variant authority. A
leading or repeated comma produces a tag-slot `Missing`; a real trailing comma
before `}` is retained without an empty tag. A non-caller-owned semicolon is a
tag-separator raw `Error` and returns to the outer tag judge.

A wrong-kind Type-shaped tag name uses the variant's structured `Invalid`
recovery and retries the same tag slot. A malformed non-NUD tag is a raw
`Error` group in that slot. Missing payload boundaries and malformed payloads
recover in their own payload slots. A locally consumed foreign close has one
`PolymorphicVariantForeignClose` wrapper per close; missing or mismatched
braces otherwise recover in the close slot while caller-owned boundaries remain
unconsumed.

## 6. Source/CST examples

`:{A Int, B}` has tags `A` and `B`; `A` has one direct payload.

`:{A Int Bool}` has two sibling payloads under `A`. `Bool` is not a TypeApply
tail of `Int`.

```text
:{A Int
B}
```

The newline belongs to the outer tag-list boundary, not the inner payload
sequence.

## 7. Composition

[Standalone `TypeExpression` core](type-expression-core.md) defines payload
types and the ordinary tails after this primary. The [syntax content
model](../conventions/syntax-content-model.md), [Rowan CST
notation](../conventions/rowan-cst.md), and [recovery `Error` and `Invalid`
topology](../conventions/recovery-error-invalid-topology.md) define the shared
`syntax-v0` conventions.
