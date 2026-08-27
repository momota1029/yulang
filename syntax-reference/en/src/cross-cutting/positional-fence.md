# TypeExpression malformed caller-boundary positional fence

## 1. Status, authority, and revision ledger

The authoritative positional-fence addendum is [the parser architecture design](../../../notes/design/2026-08-20-yu-syntax-chasa-architecture.md), lines 16862–17289. It preserves `TMN-C`/`TMN-S` semantics and replaces the former recursive `caller_owned_boundary` propagation mechanism. The comparison appendix at 17291–17399 records why rollback-and-return-`None` is rejected. Implementation authority: `27620be3`, `42c1544c`, `d58181df`, `3535e237`, `0aabef67`, `7210cd8a`, `de9a0f2f`, `19fc6cfd`, `648f8883`, `4f40022a`, `a090ad35`, and `2c4d7540`.

## 2. Problem statement, scope, and non-scope

TMN decides whether malformed newline trivia hands off; the positional fence makes the resulting caller-ownership fact survive arbitrary nesting without threading a bool through every success and recovery return. It is rollback-owned `ParseLocal` state, not a grammar rule, public parser option, AST field, CST field, new `StopKind`, or Pattern-specific scanner.

## 3. Canonical rule and decision procedure

The sole ambient value is conceptually:

```rust
TypeMalformedCallerBoundaryFence { trivia_start: usize }
type_malformed_caller_boundary: Option<TypeMalformedCallerBoundaryFence>
```

On a committed `TMN-CallerBoundary`, the scanner rolls back to the exact untouched trivia start, marks the fence, and returns its existing boundary disposition. A consumer first compares current cursor with `trivia_start`; only on equality does it state-neutrally probe maximal trivia and confirm both a physical newline and active `StopKind::Newline`. The guard then yields without consuming trivia/boundary. No stack is required: later marks replace inert earlier positions.

The producer normalizes raw-newline and horizontal-prefix trivia through full `TMN-C` before consulting same-line predicates. Only `CallerBoundary` marks; `Handoff`, `Boundary`, and `DeeperContinuation` do not.

## 4. Authority, precedence, and ownership transfer

The exact-position fence is provenance, not a replacement delimiter/stop judge. It wins at TypeExpression trivia-consumption, owner-classifier, and close-slot decision points only while cursor equals its start. The outer grammar owns the untouched run and following boundary. Each accepted unclosed delimited construct realizes its own zero-width missing close once; this preserves per-instance close cardinality rather than suppressing a shallow owner or losing a deep owner.

## 5. Worked traces and byte ownership

| source and design-doc line | fence effect | required ownership |
| --- | --- | --- |
| `T((@ \n  A))` (16999, 17189) | descendant `TMN-CallerBoundary` marks the trivia start | inner and outer accepted parenthesized instances each emit their own missing close; newline and `A` remain caller-owned |
| `A::@ \n  B` (16981, 17209) | full classifier precedes same-line Path predicate; no caller-boundary mark | `RetryAfterTrivia(run)` retries `B`; the space-prefixed run is not short-circuited |
| `{@ \n  a:A}` (17222) | shallow record fence reaches close drive | one RecordField Error and exactly one NamedRecord missing close; run stays untouched |
| `T(A\n  B)` (16995, 17232) | normal active-newline layout creates no fence | ordinary local sequence/layout handling remains unchanged |

These are source/recovery traces; the addendum does not provide a general byte-range CST tree for the mechanism.

## 6. Participating parser state and adoption matrix

| state/type | producer | query / consumer | phase | observable effect |
| --- | --- | --- | --- | --- |
| `TypeMalformedCallerBoundaryFence` | `mark_type_malformed_caller_boundary` | pending guard | committed caller-boundary trivia start | cursor-scoped provenance only |
| `ParseLocal` | parse session creation | scanner/owner adapters | holds optional fence | no AST/CST field |
| `ParseLocalCheckpoint` | `ParseLocal::checkpoint` | `ParseLocal::rollback` | speculative parse | restores the exact optional fence |
| `StopSet` and `StopKind` | caller grammar | pending guard | active newline confirmation | prevents false positives from ordinary multiline layout |
| `TypeMalformedTriviaClassification` | `classify_type_malformed_trivia` | scanner producer | `TMN-C` result | only caller-boundary classification marks |
| `TypeInvalidRunDisposition` | malformed scanner | AST/direct recovery | handoff after marking | remains the existing recovery result |

The production implementation is concentrated in `session.rs` and `type_expr.rs`; `declaration.rs` exercises restoration/composition rather than owning the fence mechanism.

## 7. Recovery, cardinality, and no-cascade contract

The fence does not erase the malformed Error or change its range. Pending fence blocks TypeExpression consumption, classifier advance, and close-token consumption, then each accepted unclosed delimiter owner emits exactly one Missing for its own close slot. Boundary trivia/token remains untouched for the caller. No duplicate Missing may arise from one instance, but distinct nested instances are intentionally not deduplicated.

## 8. Lifecycle, rollback, and invariants

`ParseLocal::new` starts with `None`; checkpoints copy the option and rollback restores it. Normal hot paths do one false `Option`/cursor comparison and do not rescan trivia. A fence-hit probes state-neutrally and does not clear itself; advancing past `trivia_start` makes it inert automatically. Speculative rollback removes a speculative mark.

## 9. Yulang2 divergences

This is implementation authority, not a surface-language change. Its observable consequence is preserving the approved TMN recovery ownership through deep nesting while avoiding a return-value propagation gap.

## 10. Known residuals, exclusions, and extension rule

The mechanism does not decide whether a newline is caller-owned: TMN does. It must not be used as a generic active-newline guard, because normal multiline constructs would become false positives. The appendix rejects bare `None`/cut as an alternative: it loses committed Error ownership or again requires an open-ended typed signal through recursive success paths.

A future TypeExpression recovery owner must mark only committed `TMN-CallerBoundary`, consult the shared pending guard before consuming the named trivia or close, preserve per-instance close cardinality, and include normal/recovery/rollback fixtures.

## 11. Implementation, fixtures, and consumer-page cross-reference

Core functions: `mark_type_malformed_caller_boundary`, `type_malformed_caller_boundary_pending`, `debug_assert_type_malformed_caller_boundary_not_skipped`, `classify_type_malformed_trivia`, and `scan_type_item_invalid_run_with_disposition`. Session coverage: `checkpoint_restores_type_malformed_caller_boundary_fence`. Type fixtures: `nested_caller_boundary_stops_outer_normal_item_trivia_consumption`, `delimited_recovery_classifier_yields_to_a_pending_fence_before_trivia`, `legacy_after_trivia_marks_a_caller_boundary_fence`, `malformed_record_name_speculation_rolls_back_a_caller_boundary_fence`, `nested_caller_boundary_realizes_each_unclosed_delimiter_once`, and `ordinary_multiline_type_constructs_do_not_create_caller_boundary_fences`.

Consumer summaries: [Pattern type annotation](../patterns/type-annotation.md), [TypeExpression core](../types/type-expression-core.md), [named-record type](../types/named-record-type.md), [forall type](../types/forall-type.md), [effect-row type](../types/effect-row-type.md), [bare nominal type](../statements/bare-nominal-type.md), [struct declaration](../statements/struct-declaration.md), [impl shell](../statements/impl-shell.md), and [cast declaration](../statements/cast-declaration.md).
