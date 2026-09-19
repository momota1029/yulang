# Standalone `TypeExpression` core

## 1. Authority and scope

This page defines the core `TypeExpression` forms in `syntax-v0`. The
Authoritative type-expression sections of the 2026-08-20 syntax architecture,
the Type contextual-boundary correction, the PathSegment and TypeCall recovery
amendments, and the accepted-input recovery authority govern this page.

It covers atoms, paths, calls, ML-style application, arrows, and parenthesized
groups. Named records, `forall`, effect rows, polymorphic variants, and bracket
rows are defined by their own pages. It does not define type meaning, lowering,
or diagnostic wording.

## 2. Accepted syntax

```text
TypeExpression := TypePrimary { TypeTightTail | TypeApplyArgument } [ TypeArrowTail ]
TypePrimary := TypeAtom | ParenthesizedTypeGroup
TypeAtom := Identifier | SigilIdentifier | Number
TypeTightTail := TypePathTail | TypeCallTail
TypePathTail := TypeChainTrivia "::" TypeChainTrivia TypePathSegment
TypePathSegment := Identifier | SigilIdentifier
TypeCallTail := "(" G* [ TypeExpression { TypeDelimitedSeparator TypeExpression } [ TypeDelimitedSeparator ] ] ")"
TypeApplyArgument := TypeApplyBoundary TypeExpressionInTypeMlScope
TypeArrowTail := TypeChainTrivia "->" TypeChainTrivia TypeExpression
ParenthesizedTypeGroup := "(" G* [ TypeExpression { TypeDelimitedSeparator TypeExpression } [ TypeDelimitedSeparator ] ] ")"
TypeDelimitedSeparator := comma | semicolon | qualifying newline
```

`Number` is a primary but not a path segment. A qualifying newline separates
delimited items. A deeper newline remains type-continuation trivia.

## 3. Admission and boundaries

The tail judge first returns at an active stop, close, or equal-or-shallower
caller boundary. Without leading trivia, it recognizes `->`, adjacent `(`, and
`::`. In a Type-ML argument, nonempty trivia first ends the nested argument;
the remaining probes can then admit a trivia-qualified arrow, path, or apply.

`List(Int)` is a call, while `List (Int)` is an apply. `F A::B` puts the path
inside the applied argument, while `F A ::B` leaves it with the outer type. An
arrow owns its complete RHS, so `A -> B -> C` is right-associative. A
same-line name-shaped path segment wins over a contextual word boundary, but a
newline-bearing contextual boundary remains with its caller. A committed call
creates a fresh nested type scope and restores the enclosing boundary after it
returns.

## 4. Direct Rowan CST

`TypeExpression` contains its primary, source-order `TypePathTail`,
`TypeCallTail`, and `TypeApplyArgument` children, and at most one
`TypeArrowTail`. `ParenthesizedTypeGroup` and `TypeCallTail` contain their
punctuation, trivia, and direct `TypeExpression` items in source order.

`TypePathTail` contains `::`, its trivia, and the segment. An apply boundary
and its argument are represented by `TypeApplyArgument`. A group has no
synthetic grouping, tuple, or separator node; literal punctuation and newline
trivia remain source-bearing children.

## 5. Recovery CST

A required primary, path segment, delimited item or separator, close, and arrow
RHS uses a zero-width `Missing` in its own slot. A malformed primary, path
segment, call item, or arrow RHS is a raw `Error` group in that slot. A valid
retry fills the same slot. No primary after apply trivia creates neither an
apply nor a synthetic `Missing`.

Path recovery does not consume a protected caller boundary. A TypeCall keeps
argument, separator, and close recovery distinct; an admitted residual after
an argument belongs to its terminal close recovery. Parenthesized groups and
effect rows use `TypeDelimitedForeignClose` only for a locally consumed
mismatched close, as defined by the foreign-close topology authority. Other
raw type recovery stays direct.

## 6. Source/CST examples

`List(Int)::Result Arg -> Out -> Final` has a call tail, path tail, apply
argument, and arrow tail in that source order. The RHS owns the second arrow.

`(A)` is a grouped type. `(A,)` and `(A;)` retain their trailing punctuation
and are tuple-like forms.

`F A -> B` is `(F A) -> B`. In `F A->B`, the nested ML argument owns the
arrow, yielding `F (A -> B)`.

## 7. Composition

The [syntax content model](../conventions/syntax-content-model.md), [Rowan CST
notation](../conventions/rowan-cst.md), and [recovery `Error` and `Invalid`
topology](../conventions/recovery-error-invalid-topology.md) define shared
`syntax-v0` notation and recovery facts. The construct pages for named records,
`forall`, effect rows, polymorphic variants, and bracket rows extend the
primary and arrow positions described here.
