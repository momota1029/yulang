# Frozen Oracle multi-use constraint accumulation

Date: 2026-10-06
Status: frozen research-only bounded historical characterization; independently compiler-referee-reviewed with no findings
Yulang3 baseline: `f1fc1a6eb700b1406d6bedebb46aec7cad082774`
Frozen Oracle source: `a58eefc31e22141574b6f20c6a5748151c6d79f1` at `/tmp/yulang2-oracle-rebuild`
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective, method, and authority

Locate the old data structures that accumulate two call occurrences of one
resolved higher-order formal, and distinguish common state from retained
per-call state. The method is bounded source archaeology plus a conditional
derivation directly from assignments and guards. No candidate, solver, or
Oracle executable was run; no conclusion is inferred from a printed scheme.

Current meaning remains fixed by call-view `q1/a2` and nested-block `q1/a1`.
The governing sources are `notes/design/2026-10-05-inferred-function-call-views.md`
§§1–5, including §1.1, and
`notes/design/2026-10-06-nested-block-function-source-realization-addendum.md`
§§1–3. The first requires one source-generated shared relationship, ordinary
value evidence to resolve the approved provisional formal view, and
comparison-independent admission. The second fixes only its exact candidate's
lexical capture and returned function meaning. This note selects no additional
source meaning. Historical stack IDs and generic role predicates do not
interpret the approved current Handler view.

The three prior archaeology notes are historical dependencies, not authority.
Their broad pipeline is not reconstructed here. This follow-up adds the
explicit `call_uppers` accumulator, the first-use/reuse distinction in a
formal-keyed frame, and the boundary of what those structures establish.

## Hypotheses and claim classes

H1: the eight inspected source files equal their blobs at the frozen Oracle
SHA. All eight were byte-checked through `git archive`; the equality checks
passed. No claim relies on unverified edits in the historical directory.

H2: two name occurrences resolve to the same installed `LocalBinding`, with
`DefId = d`, value variable `v`, and `scheme = None`; both reach the ordinary
application routine. This is an explicit input-state premise. Parser acceptance,
construction of that state for a new multi-use surface program, and execution
of every historical guard are unverified. The previous source-producer note
traces the corresponding single-use lexical route.

H3: for the frame-sharing subclaim, both calls pass the unannotated-argument
guards and select the same existing defined frame `k`. For the `call_uppers`
subclaim, `local_callee_call_projection` supplies `Some(erased_upper)` for
each occurrence. Neither guard is assumed to follow from H2 alone.

Established local representation facts are limited to the cited assignments,
containers, and branching. The two-call derivation below is conditional on
H1–H3. It is not a theorem of the source language, a solver-correctness proof,
or an independently reviewed result. No new candidate transition rule is
proposed or checked.

## Common state and retained per-call state

All historical paths below are relative to the frozen Oracle tree.

| State | Concrete location | Sharing boundary |
| --- | --- | --- |
| Formal identity and live value endpoint | `crates/infer/src/lowering/local.rs:6–23`; `name_ref.rs:146–163`; `tail.rs:851–857` | The local contains `def`, `value`, and optional `scheme`; a no-scheme use returns the stored value variable. Definition lookup searches in reverse lexical order. |
| Separate application Function constraints | `crates/infer/src/lowering/expr/tail.rs:543–563` | Each application forms its own Function upper and submits `Pos::Var(callee.value) <: callee_upper` in the common inference session. Shared callee endpoint does not make the two upper endpoints identical. |
| Explicit per-formal call-upper inventory | `local.rs:13–19`; `tail.rs:603–614,690–717` | When the erased-upper guard holds, `record_local_call_upper(d, upper, frame_index)` finds the local by `DefId` and appends each upper ID absent from its vector. |
| Frame-local subtraction identity | `local.rs:178–194`; `tail.rs:740–798` | One `FxHashMap<DefId, SubtractId>` belongs to each function frame. Equal formal identity shares its ID only within the selected frame. |
| Raw weighted bounds | `crates/infer/src/constraints/mod.rs:2386–2391,2543–2555,2581–2586` | The source describes exact deduplication rather than composition in this table, and appends lower/upper entries to separate vectors. Equal type boundary with different weights is a separate inequality. This does not characterize all later propagation or simplification. |

The call-upper recorder also sets `call_erased_used = true`. A present call
frame differing from `local.call_predicate_frame` sets `call_nested = true`
(`tail.rs:707–716`). The vector's local membership test is equality of `NegId`,
not a semantic equivalence check on completed Function types. The application
also submits the erased-upper inequality when that projection exists
(`tail.rs:608–613`). Consequently this route retains both the common variable
constraint and guarded projection metadata; it does not replace all occurrences
by one chosen call record.

## Conditional two-occurrence derivation

The smallest discriminating input is two invocations of the inspected routine,
not an asserted surface program:

```text
local d: value = v, scheme = None
call occurrence 1: callee resolves to d, argument endpoint a1
call occurrence 2: callee resolves to d, argument endpoint a2
```

1. By `instantiate_local_value`'s no-scheme branch (`tail.rs:855–857`),
   both callee computations obtain `v`. Their name uses can have separate
   `RefId`s while resolving to the common `DefId`; `name_ref.rs:146–163`
   records that definition link. No independent formal freshening occurs in
   this branch.
2. Each application forms an upper `Ui` with that occurrence's argument and
   return endpoints and submits `Pos::Var(v) <: Ui` (`tail.rs:543–563`).
   Therefore the emitted constraints have a shared variable and two separate
   Function-upper contributions. This establishes constraint construction,
   not the satisfiability or principal solution of their conjunction.
3. If the projection guard holds, the same `LocalBinding.call_uppers` receives
   `U1` and `U2`, with duplicate IDs suppressed (`tail.rs:603–606,707–717`).
   This container is concrete multi-use retention beyond mere shared-variable
   aliasing. Its later consumers were not located within this budget.
4. If the unannotated guards hold and both select frame `k`, the first call
   with an absent key `d` allocates `S`, calls
   `declared_subtract_fact(E1, S, Empty)`, inserts `(d,S)`, and appends one
   `pop(S)` to the frame. The second takes the existing-key branch and reuses
   `S` (`tail.rs:769–787`). Both calls wrap their respective return-effect
   endpoints with `push(S, Empty)` (`:788–798`). Only the absent-key branch
   makes that declaration-fact call and appends that pop. This first-call
   asymmetry is a control-flow fact, not an interpretation of its semantic
   sufficiency; other propagation may matter.
5. If the selected frames differ, the two frame maps are separate even for
   the same `d`. Global sharing of subtraction identity across all captures
   or nested calls therefore does not follow from this routine. Whether the
   actual frame selector aligns those occurrences remains unverified.

This derivation discriminates three frequently conflated objects: a shared
formal variable, a vector retaining separate call uppers, and an identity
shared within a particular function frame. It supplies no current static slot,
receipt, role result, or receiver activation.

## Generalization, freshening, and endpoint-selection limit

Generalization explicitly drains pending work before the local scheme snapshot
(`tail.rs:951–955`). Its non-generic input includes the other locals' live
variables and variables occurring in their bounds (`:1014–1040`). The called
`generalize_type_var_with_boundaries` obtains a compact root and passes an
initial empty generic-role vector (`generalize/mod.rs:75–90`); other APIs in
the same file accept supplied role predicates. Quantifiers exclude
non-generic variables and variables at or below the boundary (`:900–915`).
These observations identify snapshot and quantification inputs, without
proving retention of every multi-use constraint through compact simplification.

Within one scheme instantiation, `SchemeInstantiator` contains a common variable
map and subtraction map (`instantiate.rs:198–208`). It registers type,
recursive-bound, and stack quantifiers before cloning the predicate and generic
role predicates (`:620–648`). `fresh_var` and `fresh_subtract` reuse earlier
map entries (`:732–747`); `clone_var` returns an unquantified source variable
unchanged unless preloaded or in the distinct freshen-all mode (`:750–760`).
Thus repeated identities within one instantiated scheme use the same
substitution map. Correct preservation of the full source conjunction is still
an unproved premise; the existence of a clone map alone cannot prove it.

The live callee endpoint's selection is traced: it is the local variable when
no scheme exists. The final exported/public endpoint choice is not traced.
`LocalBinding` exposes `call_public_upper`, `call_erased_upper`,
`call_projection_enabled`, `call_uppers`, and frame/nesting flags, but this pass
did not inspect their producers and final consumers. Nor did it inspect the
implementation of `unannotated_call_frame_index`. The decisive unresolved
historical seams are therefore **which frame is selected for repeated nested
uses, and how accumulated uppers feed a final public/erased endpoint**.

The inspected Function construction and generic role-predicate cloning do not
establish an old Handler/non-Handler classification rule corresponding to the
current ordinary-value determination. Such a rule may exist elsewhere; this
bounded pass does not claim absence throughout the repository. Resolving those
seams would require a separately assigned direct-reference continuation, not
semantic inference from old output.

## Independence, omitted cases, and verification

Oracle is the historical object being examined, not an independent semantics
oracle. Blob equality establishes provenance; reading two routines sharing
the same implementation assumptions does not independently validate the
source rules. H2/H3 and the previous lexical-route characterization are shared
assumptions. No checker assumes transitions and then claims to prove them.

Coverage: eight frozen files, selected ranges and exact-symbol locators;
two-call conditional input-state derivation. No seeds, randomized ranges,
mutations, bounded solver enumeration, builds, tests, Oracle processes, CLI
probes, or performance samples. Several command captures were truncated;
omitted output is not treated as inspected evidence. The final focused capture
recovered the decisive call-upper and first-use/reuse clauses and all hashes.
The machine-module locator inspection produced no decisive code excerpt; no
claim about that module's internal implementation is made.

Checks: four sequential top-level shell/read invocations; the latter three
used Python for bounded file reads. Read-only Git commands comprised one
current `rev-parse` and three `git archive` invocations: an initial six-file
source comparison, an eight-file source comparison, and a nine-dependency
comparison with the pinned Yulang3 baseline. All equality assertions passed;
all nine current dependencies matched that baseline. No Git mutation occurred.
Process count here distinguishes the four assigned read-command captures from
their short-lived Python/Git child processes. CPU time, peak RSS, and total
wall time were not instrumented; each tool-reported read invocation completed
in about 0.1 seconds. No concurrent compute, build, or formatting was started.

Failure conditions: changed source blobs invalidate locators; a scheme-bearing
formal weakens H2; a missing projection guard invalidates step 3; different
frames weaken step 4; additional consumers may refine endpoint selection.
Unverified cases include recursive groups, annotated/mixed uses, alias or
method-call dispatch, complete bound replay, compact pruning, solver
correctness, acceptance of any new multi-use surface example, and all current
`beta/Slots(beta)`, profile, typed receipt, Omega, joint `(nu,K,D)`, admission,
soundness, principality, source adequacy, and production-conformance obligations.

Recommended next action: assign one bounded direct-reference continuation for
`unannotated_call_frame_index` and the producer/consumer of `call_uppers` that
selects the public/erased endpoint, preserving the historical-only claim class.

## Frozen dependency hashes

All current dependency hashes below matched the pinned Yulang3 commit.

| Current dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-nested-block-function-source-realization/approved-answer.md` | `04ee0dc089dc6ad19a184d31775a146c08b07f2f287099d2e5b54d7d1d5a643e` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `questions/2026-10-05-nested-block-function-source-realization/receipt.md` | `e5e59e176eb865a588b2843b18137571fe9c5b6f43bf1ca349bc60c9ad90f0ec` |
| `notes/progress/2026-10-06-frozen-oracle-source-producer-archaeology.md` | `4f3cfff031dd9e5a90b5df3e2f7aded3535007f16ca5abd45c7892f6567a244b` |
| `notes/progress/2026-10-06-frozen-oracle-annotation-call-producer-archaeology.md` | `ae50f02f88d13c4af818c25761a0158b99810b22b45453881484996872aca65f` |
| `notes/progress/2026-10-06-frozen-oracle-argument-effect-contract-channel.md` | `5273989199fc5650cce144d426a0b588320335fb6a06f4d6737db36323008e0f` |

Every historical file below matched its frozen commit blob.

| Historical source | SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/local.rs` | `300bc2b12d8f13aed0ae5f65cdec93683e7de2719be38bb33724f51730e52f81` |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/lowering/name_ref.rs` | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| `crates/infer/src/typing.rs` | `b6ade453931d288c03332770fa76022abf90f1276466faeefa3d647be63bcef6` |
| `crates/infer/src/generalize/mod.rs` | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| `crates/infer/src/instantiate.rs` | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| `crates/infer/src/constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| `crates/infer/src/constraints/machine/mod.rs` | `00d4f073c1c698478471ad7f699af263b6e144ba27911bcc17acd707ee796bd9` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-frozen-oracle-multiuse-aggregation-archaeology.md`.
- Baseline SHA: Yulang3 `f1fc1a6eb700b1406d6bedebb46aec7cad082774`;
  frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none; all nine direct current dependencies matched
  the pinned baseline and all eight historical files matched frozen blobs.
- Review status: frozen, independent review pending; bounded historical
  characterization and conditional routine derivation only.
- Checks already run: four bounded read-command captures; three read-only
  archive comparisons; SHA-256 recording; source/dependency equality assertions.
  No builds, tests, executable probes, mutation, or Git writes. Primary must
  inspect the final note's exact diff and lease scope before integration.
- Proposed one-line research-checkpoint commit message:
  `research: trace frozen Oracle multi-use constraint accumulation`.
- Shared-record deltas intentionally left for primary/curator: record
  `call_uppers` retention and frame-local first-use/reuse as historical evidence;
  retain frame selection, final public/erased endpoint selection, old role
  correspondence, and all current source-producer gates as open. No edits to
  shared task, theory, index, authority, or question-board records.
