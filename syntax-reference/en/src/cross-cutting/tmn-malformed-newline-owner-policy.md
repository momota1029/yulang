# TypeExpression malformed-newline-owner policy (TMN)

## 1. Status, authority, and revision ledger

The Pattern-annotation addendum (16042–16556) established the cross-owner problem. The authoritative TMN addendum is [the parser architecture design](../../../notes/design/2026-08-20-yu-syntax-chasa-architecture.md), lines 16557–16860, organized as `TMN-B`, `TMN-P`, `TMN-C`, and `TMN-S`; its closing signature at 16859–16860 records approval. Positional fence (16862–17289) replaces TMN's caller-boundary propagation mechanism, not TMN semantics. Implementation authority: `2c29c0d1`, `d99d49e7`, `72948621`, `13450592`, `bef9cb96`, `57afb683`, `7838355e`, `52429b94`, and `a0365f98`.

## 2. Problem statement, scope, and non-scope

TMN decides whether maximal trivia after a non-empty malformed TypeExpression prefix remains deeper continuation for the same required slot or returns untouched to an enclosing owner. It unifies that decision for mandatory primaries, Path, ArrowRhs, delimited items, forall, NamedRecord, and Pattern annotations. It changes neither surface TypeExpression grammar, primary/tail precedence, delimiter ownership, public parser options, nor AST vocabulary.

## 3. Canonical rule and decision procedure

`TMN-B` captures its base once:

```text
continues_after_newline(trivia, continuation_base) :=
    trivia has physical newline
    and indent after its last physical newline > continuation_base
```

`TMN-P` selects no implicit default:

```text
TypeMalformedNewlinePolicy :=
    ContinuationQualified { continuation_base }
  | AnyPhysicalHandoff
```

`TMN-C` classifies one maximal trivia run in priority order: no physical newline; active caller `StopKind::Newline`; any-physical handoff; continuation-qualified boundary; deeper continuation. `TMN-S` preserves the result:

```text
TypeInvalidRunDisposition :=
    RetryCurrent
  | RetryAfterTrivia(TriviaRun)
  | BoundaryCurrent
  | BoundaryAfterTrivia(TriviaRun)
```

The scanner checks current owner boundary, hard handoff, current retry candidate, maximal trivia plus `TMN-C`, deeper-trivia candidates, then another opaque malformed unit.

## 4. Authority, precedence, and ownership transfer

Active `StopKind::Newline` wins before indentation or policy. `BoundaryCurrent` leaves the current byte untouched. `BoundaryAfterTrivia` emits only the malformed prefix and leaves trivia plus following boundary to its owner. `RetryAfterTrivia` transfers one exact trivia run to the same required slot, which consumes it once and retries; direct CST emits it once between Error and retried child. Only the outer mandatory Pattern annotation forwards its captured Pattern continuation base; nested type recovery resumes the ordinary active type base.

## 5. Worked traces and byte ownership

These authoritative traces are at design-doc lines 16803–16828.

| source and design-doc line | classification | required byte ownership |
| --- | --- | --- |
| `x: @\n  Int` (16809) | `TMN-DeeperContinuation` then `RetryAfterTrivia` | one `Error(Type::Primary)` on `@`; trivia is consumed once and `Int` completes the same annotation slot |
| `A::@\n  B` (16811) | `TMN-DeeperContinuation` then `RetryAfterTrivia` | Error owns `@`; `B` retries the same PathSegment |
| `T(@\n  A)` (16813) | `TMN-DeeperContinuation` then `RetryAfterTrivia` | Error owns `@`; `A` retries and the call owner consumes `)` |
| `'[@\n  A]` (16818) | `TMN-DeeperContinuation` then `RetryAfterTrivia` | Error owns `@`; `A` retries and the row owner consumes `]` |
| `x: @\n  <EOF>` (16820) | `TMN-DeeperContinuation` then `BoundaryAfterTrivia` | Error owns `@`; trivia stays outer-owned and no same-cause Missing is added |

## 6. Participating parser state and adoption matrix

| state/type | producer | query / consumer | observable effect |
| --- | --- | --- | --- |
| `RequiredTypeRecoveryContext` | mandatory TypeExpression entry | required AST/direct adapters | private outer-role and optional Pattern-base context |
| `TypeMalformedNewlinePolicy` | each scanner caller | `classify_type_malformed_trivia` | explicit newline ownership policy |
| `TypeMalformedTriviaClassification` | `classify_type_malformed_trivia` | boundary normalization/scanner | preserves the five `TMN-C` outcomes |
| `TypeInvalidRunRecovery` | malformed-run scanner | AST/direct owner adapters | retains error range plus disposition |
| `TypeInvalidRunDisposition` | `scan_type_item_invalid_run_with_disposition` | required/delimited/forall/Path/NamedRecord recovery | determines retry versus handoff without a new AST node |
| `TriviaRun` | state-neutral trivia probe | classifier and disposition | exact raw-trivia ownership |

`pattern.rs` captures `pattern_continuation_base` on both AST/direct paths, then uses `RequiredTypeRecoveryContext::with_malformed_continuation_base` only at the outer annotation's mandatory TypeExpression entry.

## 7. Recovery, cardinality, and no-cascade contract

`error_range` is non-empty and contiguous. A boundary leaves punctuation for its owner; retry consumes no candidate byte before retry. `BoundaryAfterTrivia` never means scanner-owned trivia, and `RetryAfterTrivia` is the sole same-slot transfer. Thus `x: @\n  <EOF>`, `T(@\n  )`, and an active-Equal boundary emit Error on `@` only: no second Error or cascading Missing.

## 8. Lifecycle, rollback, and invariants

Capture continuation base once at recovery-slot entry and never recompute it from following token or EOF. Probe maximal trivia state-neutrally. An internal NamedRecord colon probe rolls back before handoff. AST/direct adapters retain disposition until retry/transfer is complete, then restore checkpoint state exactly.

## 9. Yulang2 divergences

TMN distinguishes qualifying from deeper malformed newlines instead of treating every physical newline as a raw scanner safe point. Approved polymorphic-variant any-newline behavior remains the explicit `AnyPhysicalHandoff` exception.

## 10. Known residuals, exclusions, and extension rule

There is no implicit default: each direct scanner caller chooses policy. Future bracket-row grammar retains `BracketRowAlignmentPolicy` and does not silently opt in. A future TypeExpression owner must declare policy/base, preserve `TypeInvalidRunDisposition` through owner transition, normalize raw-newline shortcuts through `TMN-C`, and fixture both retry and caller-boundary handoff.

## 11. Implementation, fixtures, and consumer-page cross-reference

Core implementation: `parse_required_type_expression_with_recovery_context`, `commit_direct_type_expression_with_recovery_context`, `classify_type_malformed_trivia`, `scan_type_item_invalid_run_with_disposition`, and `continues_after_newline`. Pattern integration: `parse_pattern_bp` and `RequiredTypeRecoveryContext::with_malformed_continuation_base`.

Fixtures: `malformed_trivia_classifier_distinguishes_all_tmn_c_outcomes`, `mandatory_type_recovery_yields_deeper_newlines_to_an_active_owner`, `malformed_delimited_items_retry_after_deeper_trivia`, `malformed_path_segment_retries_after_deeper_trivia`, `malformed_forall_body_retries_after_deeper_trivia`, and `malformed_continuation_qualified_slots_pair_raw_and_space_prefixed_newlines`.

Consumer summaries: [Pattern type annotation](../patterns/type-annotation.md), [TypeExpression core](../types/type-expression-core.md), [named-record type](../types/named-record-type.md), [forall type](../types/forall-type.md), and [effect-row type](../types/effect-row-type.md).
