# Polymorphic-variant types

## 1. Status, authority, and last verification

The Authoritative polymorphic-variant primary addendum is lines 14527–15233 of `notes/design/2026-08-20-yu-syntax-chasa-architecture.md`. Its current caller-boundary behaviour is also covered by `ASOB-G` at 18358–19161.

The implementation series is `fd2f3ad8`, `52f45c52`, `e451063f`, `3a048bde`, `d37a77cf`, `54f1b927`, and `f4332308`; the final listed implementation gate is `f4332308`. In particular, `d37a77cf` moved AST and direct-CST realization onto one streaming driver rather than maintaining separate two-level judges.

## 2. Scope and non-scope

This TypePrimary is the type-only form `:{A Int, B}`: each plain identifier tag has zero or more payload types. The outer tag list owns comma and qualifying-newline boundaries; a tag's inner payload sequence owns non-empty same-line payload boundaries.

It does not add expression-side variant literals, pattern polymorphic variants, struct/enum/error payload semantics, declaration/use-site wiring, HIR/lowering, inference, resolver work, diagnostics wording, or formatting.

## 3. BNF-equivalent grammar

```text
TypePrimary := ... | PolymorphicVariantType
PolymorphicVariantType := Colon AdjacentLBrace PolyVariantOpeningTrivia [ PolymorphicVariantTag { PolyVariantTagBoundary PolymorphicVariantTag } [ PolyVariantTagBoundary ] ] RBrace
PolymorphicVariantTag := Identifier { PolymorphicVariantPayload }
PolymorphicVariantPayload := PolyVariantPayloadBoundary TypeExpressionInTypeMlScope
PolyVariantPayloadBoundary := NonEmptyTriviaWithoutPhysicalNewline
PolyVariantTagBoundary := ExplicitPolyVariantCommaBoundary | ImplicitNewlineBoundary(poly_variant_base)
ExplicitPolyVariantCommaBoundary := CommaBoundary
```

`AdjacentLBrace` means that `{` begins exactly at `Colon.end`. Any physical newline ends the inner payload sequence; only the outer list may classify a qualifying newline as a tag boundary.

## 4. Judge, priority, and owner boundary

The canonical primary judge first returns active stops/caller-owned closes, then probes `for`, adjacent `"'["`, and adjacent `":{"` before ordinary names, numbers, `(`, and `{`. Bare `:` never cuts: `:{A}` is the primary, while `: {A}`, `:/*c*/{A}`, and `:\n{A}` are not candidates (design lines 14612–14635).

After the pair is accepted, the outer brace/list frame owns tags and close recovery. A tag then runs its inner payload judge in Type-ML mode, so same-line payload candidates become siblings rather than TypeApply tails. The completed primary returns to the ordinary fixed tail judge: `F :{A}` is a TypeApply argument and later path/call/apply/arrow tails remain ordinary.

## 5. Byte-exact CST worked examples

The addendum gives complete source-order CST trees but no byte-range-annotated tree for this construct; no byte ranges are invented here.

```text
:{A Int, B}
```

Design lines 14980–14998 show `PolymorphicVariantType` owning `:`, `{`, tag `A`, its whitespace-bearing `PolymorphicVariantPayload`, comma, tag `B`, and `}`.

```text
:{A Int Bool}
```

Design lines 15000–15018 show two sibling payload nodes below tag `A`; `Bool` is not a TypeApply tail of `Int`.

```text
:{A Int
B}
```

Design lines 15020–15038 show the physical newline as outer-list trivia between the payload-bearing tag `A` and tag `B`, with no synthetic separator.

```text
:{
  A Pair(
    Int,
    Bool
  )
  B
}
```

Design lines 15042–15083 distinguish the newlines owned by nested `TypeCallTail` from the tag-level newline after `)`.

## 6. Parser-side AST shape

`TypePrimary::PolymorphicVariant(PolymorphicVariantType)` is a real primary. `PolymorphicVariantType` has exactly `colon`, `open`, recovered ordered `tags`, optional `trailing_comma`, recovered `close`, and `range`.

Each `PolymorphicVariantTag` has recovered `name`, recovered ordered `payloads`, and `range`. Each `PolymorphicVariantPayload` has recovered `boundary`, recovered boxed `type_expr`, and `range`. These are all source-slot fields; there is no synthetic inner-sequence wrapper.

The direct CST uses `SyntaxKind::PolymorphicVariantType`, `SyntaxKind::PolymorphicVariantTag`, and `SyntaxKind::PolymorphicVariantPayload`, retaining punctuation and trivia in source order.

## 7. Typed recovery table

| condition | recovery and continuation |
| --- | --- |
| non-adjacent or incomplete `:{` introducer | no variant authority; the ordinary primary owner continues |
| empty list or real `}` after a complete tag | valid list/close; a real trailing comma is retained without an empty tag |
| leading/repeated comma | one zero-width `PolymorphicVariantTag` Missing for each required tag slot |
| non-caller-owned semicolon | one `PolymorphicVariantTagSeparator` Error, then re-enter the outer tag judge |
| wrong-kind or malformed tag name | typed tag/name Error; retry the same tag slot without creating a second tag |
| empty payload gap followed by a primary | Missing `PolymorphicVariantPayloadBoundary`, then same-position type retry |
| malformed accepted payload boundary | one payload Error and same-slot retry; at an outer safe point the type slot is Incomplete without a cascade |
| missing/mismatched brace | one typed close Missing/Error; caller-owned boundaries remain unconsumed |

AST advances through the same accepted/recovery ranges as direct CST. Direct CST creates one committed Missing/Error record for each source-bearing or zero-width recovery node.

## 8. Boundary and state-restoration contract

Acceptance establishes a brace delimiter, `TypeDelimitedOwner::PolymorphicVariant`, local stops, layout frame, and Type-ML state. Normal, recovery, and rollback exits restore delimiter, stop, layout, type-owner, and Type-ML state exactly. The shared driver supplies the same tag/payload boundary and safe-point decisions to AST and direct CST.

## 9. Yulang2 divergences

Yulang3 intentionally narrows Yulang2's trivia-tolerant colon/brace spelling to adjacent `":{"`, requires a non-empty same-line payload boundary, emits source-bearing payload nodes rather than Yulang2-style direct payload children, and replaces generic invalid-token recovery with typed phases. It preserves plain-Identifier tag heads, zero-or-more payloads, comma-only explicit outer separation, qualifying outer newlines, and ordinary TypeApply/tail composition.

## 10. Known residual / deferred surface

`ASOB-G` documents the general caller-boundary-hidden-behind-missing-delimiter residual; this primary does not create an extra exemption beyond that characterization. Bracket rows and TypeExpression use-site wiring were deferred by the original addendum and are now specified separately; semantic variant representation, HIR/lowering, inference, resolver, diagnostics, and formatting remain deferred.

## 11. Implementation and regression cross-reference

The shared implementation is `crates/yu-syntax/src/grammar/type_expr/polymorphic_variant.rs`: `parse`, `commit_direct`, `drive`, `drive_payloads`, `inspect_payload`, `classify_tag_boundary`, and `consume_invalid_run`. `crates/yu-syntax/src/grammar/type_expr.rs` supplies `scan_polymorphic_variant_open` and the enclosing canonical primary/tail entry.

Regression fixtures include `polymorphic_variant_type_is_a_two_level_primary`, `polymorphic_variant_type_preserves_primary_and_ml_payload_boundaries`, `polymorphic_variant_type_uses_phase_specific_recovery_roles`, `polymorphic_variant_outer_judge_preserves_owner_boundaries_and_reentry_order`, and `polymorphic_variant_shared_driver_regression_matrix`.
