# Ambient statement-owner boundary (ASOB)

## 1. Status, authority, and revision ledger

The authoritative ASOB addendum is [the parser architecture design](../../../notes/design/2026-08-20-yu-syntax-chasa-architecture.md), lines 18358–19160, finalized by `7b5ab178`. Its canonical sections are `ASOB-G` (ambient stacks, identity, barrier, and predicate), `ASOB-P` (precedence), and `ASOB-R` (recovery ownership and cardinality). Implementation spans 19 gates, from `723760c1` through `5f627f1c`; the exhaustive gate/commit ledger belongs in the forthcoming [ASOB integration matrix](asob-integration-matrix.md).

## 2. Problem statement, scope, and non-scope

ASOB closes two collision classes in a statement context when a nested delimited/layout owner has a missing close: a physical newline strictly shallower than the nearest visible statement baseline, and an active `IfExpression` companion with exact `else` or `elsif`. In those exact cases the ambient owner wins before the local item/list continuation consumes the gap.

It amends continuation/recovery authority in Struct fields, NamedRecordType, type-delimited forms, polymorphic variants, BracketRow, expression-delimited tails, Pattern-delimited forms, Forall, and colon-inline arguments. It does not change item grammar, layout-base calculation, explicit separators, matching-close recognition, AST/CST shape, recovery roles, diagnostics, ordinary same-indent statement collisions, case/catch arm authority, or non-If contextual stops.

## 3. Canonical rule and decision procedure

`ASOB-G` keeps rollback-owned ambient-owner and If-companion stacks. A braced barrier stops visible-baseline lookup and hides pre-barrier If frames; an inline canonical-statement frame is transparent to baseline lookup.

```text
AnyAmbientOwnerClaims(gap) :=
    StrictDedentFromNearestVisibleStatementBaseline(gap)
    or IfContinuationOwner(gap).is_some()

AmbientPreCommitJudge(gap, local_candidate) :=
    if AnyAmbientOwnerClaims(gap)
    then CallerOwnedBoundary
    else EvaluateExistingLocalCandidate(local_candidate)
```

Strict dedent requires a physical newline and following indentation strictly below the nearest visible root/indented baseline. `IfContinuationOwner` returns the first visible companion identity whose exact word is `else` or `elsif` and whose newline, if any, is not shallower than that frame's base. The sink-free query probes one maximal trivia run and following maximal word, then rolls all input, line, local state, and sink state back.

## 4. Authority, precedence, and ownership transfer

`ASOB-P` order is: actual local matching close or fixed caller stop; locally allowed explicit separator; ambient claim at a completed/recovered continuation gap; then existing local continuation/layout/retry logic. A literal separator remains authority and opens exactly one next slot. Otherwise an ambient claim returns the original gap unconsumed and opens no local slot.

For a bare implicit boundary, ambient and local layout predicates inspect the original unconsumed gap. Only ambient-false local success consumes it and enters `AfterOwnerSafeImplicitBoundary`; post-newline re-probing is forbidden. An If arm itself consumes a companion only when `IfContinuationOwner` returns its own identity.

## 5. Worked traces and byte ownership

| source and design-doc line | ASOB decision | required result |
| --- | --- | --- |
| `if condition:\n  struct S { x: Int\nelse: 0` (18761–18763) | strict dedent and own `else` companion claim the original newline | Struct returns one missing `}`; no missing field; newline and `else: 0` remain If-owned |
| `if condition: f(x else: 0` (18775) | active inline companion is visible before ML continuation | Call returns one missing `)` and no missing argument; `else: 0` is the ElseArm |
| `if condition:\n  { else: 0 }\nelse: 1` (18808–18810) | braced barrier suspends the outer companion inside braces, then resumes it | inner `else` remains local; outer `else: 1` is the companion |
| `if condition:\n  my [x\nelse: 0` (18833–18835) | ListPattern cannot commit a local implicit boundary | one missing `]`, zero missing pattern items, and the companion remains outer-owned |
| `struct S { x: Int,` (18709–18711) | explicit comma has local authority before terminal recovery | existing one missing field plus distinct missing `}` remain |

These are source/recovery traces. ASOB does not define a single byte-range CST tree; it preserves source trivia and recovery ownership at each participating owner.

## 6. Participating parser state and adoption matrix

| state/type | producer | query / consumer | phase | observable effect |
| --- | --- | --- | --- | --- |
| `AmbientOwnerScopeFrame` | root, indented, braced, With, and Mod scope wiring | baseline/barrier lookup | statement context lifetime | carries scope kind, baseline, and visibility floor |
| `AmbientOwnerScopeKind` | `AmbientOwnerScopeFrame` constructors | nearest-visible-baseline walk | root/indented/barrier/inline distinction | barrier stops outer baseline visibility |
| `BracedBarrierOrigin` | braced statement block or Catch braced arm entry | barrier identity | brace lifetime | suspends pre-barrier companion frames |
| `InlineStatementOwnerKind` | With/Mod inline entry | transparent inline scope | exactly-one Statement episode | preserves origin without creating a baseline |
| `IfExpressionCompanionFrame` | `push_if_expression_companion` | `if_continuation_owner` | complete If chain | captures immutable base, exact words, identity |
| `IfExpressionCompanionId` | ParseLocal ID allocator | arm-own-ID comparison | nested companion transition | prevents an inner If from consuming an outer companion |
| `ParseLocalCheckpoint` | `ParseLocal::checkpoint` | `ParseLocal::rollback` | all speculative exits | restores both stack depths and ID state |

Core queries are `any_ambient_owner_claims` and `if_continuation_owner` in `session.rs`. Production call sites span `expression.rs`, `pattern.rs`, `type_expr.rs`, `type_expr/polymorphic_variant.rs`, and `declaration.rs`.

## 7. Recovery, cardinality, and no-cascade contract

`ASOB-R` adds no recovery vocabulary or synthetic node. When an ambient claim vetoes a bare implicit candidate, no separator and no next item/field slot are committed: missing item/field is zero, while every accepted unclosed delimiter instance emits its existing one missing close. After explicit or successfully committed implicit separator, existing recovery retains one missing next item/field and one distinct missing close at an owner boundary.

The caller receives untouched trivia and boundary bytes. Nested owners may independently return the same gap and each realize their own close slot; this is per accepted construct instance, not global diagnostic deduplication. AST/direct remain lossless and one committed recovery record corresponds to one recovery node.

## 8. Lifecycle, rollback, and invariants

Root, indented, braced, and inline scopes push the exact frame and pop it on every normal/recovery exit. Braced barriers capture an If-stack visibility floor, preserve inner frames, and assert restoration on pop. One If frame begins immediately after `IfKw`, survives `elsif` transitions, and pops only after own `else` commitment or final return. The predicate itself is sink-free and exact-rollback.

Completeness is deliberately a documented, fixture-verified judge-point enumeration rather than compiler enforcement: every completed/recovered-anchor continuation that could commit a local gap must call the predicate before doing so.

## 9. Yulang2 divergences

ASOB makes strict outer dedent and active exact If companions explicit ambient authority even where a local field/item shape could also match. It introduces no new surface token, grammar production, diagnostic role, or semantic behavior.

## 10. Known residuals, exclusions, and extension rule

The addendum records four remaining owner families:

1. same-indent ordinary canonical Statement after a missing inner close;
2. braced statement-owner current-depth newline or a missing braced close;
3. Case/Catch arm-sequence newline, including CatchBraced current depth;
4. non-If contextual introducer/owner stop behind missing nested delimiter, including arm `if`/`where`, `->`, and binding `=`.

These are ASOB residuals because neither strict visible-statement dedent nor `else`/`elsif` companion identity claims them. The Cast page's four-condition predicate is a downstream specialization of this last category for a Cast-contained Pattern/TypeExpression delimiter; it is not a fifth ASOB family or a closed ASOB owner table.

A future construct must add a signed amendment when it creates a completed/recovered gap that can consume one of ASOB's two classes, and must add its judge point plus AST/direct fixtures. Extending ASOB to any other caller boundary requires a separate authority/priority design.

## 11. Implementation, fixtures, and consumer-page cross-reference

The 19 gates introduce rollback-owned scopes/predicates, wire root/indented/braced/inline and If lifetimes, then integrate expression, Pattern, TypeExpression, struct, polymorphic-variant, BracketRow, Forall, colon-inline, recovery/cardinality, residual, and restoration coverage. Representative commits are `723760c1`, `af3cce2f`, `a355058d`, `5f627f1c`, and `aa7e1cbd`; see [the ASOB integration matrix](asob-integration-matrix.md) for the complete ledger.

Representative fixtures: `operator_chain_returns_an_ambient_if_companion_gap_without_continuing`, `call_tail_preserves_ambient_if_companions_for_inline_body_and_condition`, `expression_delimited_tails_return_ambient_if_companions_to_their_owner`, `asob_known_residual_same_indent_statement_is_still_taken_by_struct_recovery`, `asob_known_residual_braced_current_depth_and_companion_suspension_remain_distinct`, `asob_known_residual_case_and_catch_arm_newlines_can_be_taken_by_call_recovery`, and `asob_known_residual_suspended_arm_guard_if_is_still_consumed_inside_list_pattern`.

Consumer summaries: [braced statement block](../expressions/braced-statement-block.md), [case/catch](../expressions/case-catch.md), [call/field/path tails](../expressions/call-field-path-tails.md), [if expression](../expressions/if-expression.md), [Pattern core](../patterns/pattern-core.md), [list pattern](../patterns/list-pattern.md), [record pattern](../patterns/record-pattern.md), [type annotation](../patterns/type-annotation.md), [TypeExpression core](../types/type-expression-core.md), [NamedRecord type](../types/named-record-type.md), [polymorphic-variant type](../types/polymorphic-variant-type.md), [BracketRow grammar](../types/bracket-row-grammar.md), [equality type](../statements/equality-type.md), [bare nominal type](../statements/bare-nominal-type.md), [derives attachment](../statements/derives-attachment.md), and [cast declaration](../statements/cast-declaration.md).
