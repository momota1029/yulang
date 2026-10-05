# Frozen Oracle annotation and call producer mechanisms

Date: 2026-10-06
Status: bounded historical characterization; research-only, not independently reviewed
Yulang3 baseline: `88f1fd2bbf66caec4b161ebaf5dd0ae6378e6a5d`
Historical source: `/tmp/yulang2-oracle-rebuild`, commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Implementation and semantic authority: none

## Question and scope

The missing current producer is the source-derived, comparison-independent
original Function relation: it must associate source contracts and static
positions with a complete profile, typed paths and incidences, and the one
joint `(nu,K,D)` relation. For unannotated higher-order formals it also has to
connect the approved provisional protected Handler view with evidence from
the source uses. Existing registration attempts stop before this introduction.
This note searches the frozen Oracle for historical producer machinery nearest
to the two concrete source inputs at that boundary: annotation occurrences
and ordinary calls through resolved formals.

This is assignment-level archaeology, not an interpretation of what Oracle
means. The historical implementation, tests, inferred scheme, and runtime
results confer no authority on Yulang3. H1: the detached directory names the
historical revision above; the earlier pinned archaeology verified its
revision and inspected-source blobs. This follow-up did not modify that tree.
H2: the cited branches characterize possible machinery, not the path taken by
every candidate; no candidate was executed or instrumented here.

## Historical annotation-to-function-frame chain

For a postfix expression annotation, `lower_type_annotation_tail` builds a
temporary `AnnType` from the CST `TypeExpr`, applies any annotation-selected
effect upcasts, asks `AnnConstraintLowerer::connect_computation_detailed` to
connect the current value/effect endpoints, then appends the returned
subtraction constraints to the current function frame
(`crates/infer/src/lowering/expr/tail.rs:52–86`). A typed local binding follows
the same shape after lowering its RHS: `connect_local_binding_annotation`
builds the annotation, applies the upcasts, connects the binding value and
computation effect, and appends the resulting constraints to the frame
(`crates/infer/src/lowering/expr/block_local.rs:905–930`).

At a defined lambda boundary, the frame combines annotation-produced and
body-produced subtraction weights, then the lambda's Function return effect
and value are wrapped with those weights (`tail.rs:1058–1080`,
`lambda.rs:946–975`). The effect-upcast step resolves annotation effect paths
through the cast registry and inserts resolved `#effect-up` calls while
preserving the public value endpoint (`method_body.rs:1789–1821`). Thus the
historical producer is a sequence of local CST-to-`AnnType` elaboration,
constraint connection, frame accumulation, and Function construction. It is
not a persistent annotation-to-call-slot relation: the inspected chain does
not attach a durable source annotation ID to a complete Function profile or
its original source contribution.

## Historical unannotated-call mechanism

The application producer first creates ordinary call constraints and source
application provenance (traced in the earlier
[source-producer archaeology](2026-10-06-frozen-oracle-source-producer-archaeology.md)).
For a narrower return-effect path, `unannotated_local_callee_return_effect`
checks that the callee resolves to a local `Def::Arg`, its metadata says
`Unannotated`, and an eligible defined-function frame exists
(`tail.rs:745–767`). It reuses one `SubtractId` per formal `DefId` in that
frame, records an `Empty` declaration fact and a frame pop, then puts matching
push-weighted views around that call's return effect (`tail.rs:769–798`). The
function frame stores these subtraction weights separately from latent ones
(`local.rs:178–195`); lambda construction later exports them in its output
predicate (`tail.rs:1058–1073`).

This gives a historical example of routing a use-derived constraint through a
resolved formal identity and collecting it at a definition frame. The
mechanism is conditional on historical local/frame metadata; it is not a
source-independent proof that a complete role-indexed contract or all its
uses have been registered. In particular, the inspected branch creates no
current `beta`, `Slots(beta)`, owner/receiver or typed receipt correspondence,
and no single original joint `(nu,K,D)` relation. Its `Empty` subtractability
fact and stack weighting are not the approved current provisional Handler
seed, a role-resolution rule, or an annotation-scoped permission rule.

## What this adds and what it does not

The earlier archaeology established shared binder variables, ordinary call
constraints, environment-aware generalization, coordinated freshening, and a
separate runtime evidence environment. This follow-up makes two additional
historical producer shapes concrete: annotation constraints flow into a
defined function's output frame; and one formal's eligible call sites can
share a frame-local subtraction identity. These are useful old-side
mechanism locations for future correspondence work.

They do not fill the current missing source producer. The new lane did not
establish that Oracle has a complete static slot/profile inventory, a
comparison-independent admission judgment, a typed receipt schema, or a
correlated original source relation. Nor does the old stack mechanism settle
current handler seed admission, mixed-use aggregation, annotation permission,
receiver lifetime, principality, or soundness. No Oracle semantics is adopted
as a premise or authority. The successor must derive those objects from its
approved rules; unresolved constructors stay explicit premises/stubs.

Method budget: one bounded source/code-flow archaeology pass; no builds, tests,
Oracle runs, randomized cases, or performance measurements. Claim status is
historical characterization only; independent review remains open.
