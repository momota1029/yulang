# R40 typed Result consumer trace

Revision 2 corrects two minor factual issues identified by the independent
compiler review. Revision 1 is preserved byte-for-byte at
`notes/progress/2026-10-18-typed-result-consumer-r40-rev1-snapshot.md`, SHA-256
`eb816bb306a9a8b068bfb786f7b45d3e24a968f3c96f81972477d6692d748170`.

## Scope and result

This is a corrected, versioned source/native trace for the exact original
occurrence `q = loop y` in `helper`. It addresses the R39 MAJOR finding about
the omitted typed consumer. It is read-only evidence for the pinned worktree
path. It does not repair or alter the frozen R39 trace, introduce a source
typing rule, establish the ordinary source `Desc` for `A_q`, or close the full
inference/evaluator theorem. Parent conditions remain **0 -> 0**.

The q-specific Value Result component is admitted in a negative Function
demand, becomes the fourth typed Function child, receives
`FunctionPortOperation::Preserve` and a retained `Dependency::FunctionPort`,
and is processed through the typed Context/Dispatch drain. The helper's lambda
recipe reads its body-value endpoint as a positive Function result. Thus the
pinned native path consumes Result structurally with q occurrence provenance.
This path does not itself identify q's Result with the complete source Call
return/future schema or provide an ordinary source `Desc` owner, source sort,
introduction scope, or ordered telescope.

## Exact q selection and source production

The R39 specimen and source-identity selection are retained from the frozen
source artifact (R39 proof SHA-256
`7d4d914d111b78802517e40349d7a576f55a19399da8b85d6c53d9a3371337f5`): locate
the `outer` definition root, its `helper` local binding, then select the Apply
expression whose resolved callee is the local `loop` and whose argument is
helper parameter `y`. It is distinct from `t = loop x` in `direct` and from
the three `helper x` calls. Selection is by owner and expression occurrence,
not `calls[0]`. This is static identity evidence; R40 did not execute a source
program or inspect runtime numeric IDs.

In `candidate_source.rs:1319-1360`, Apply emission retains a
`CandidateRelation::Apply` with separate callee, callee-effect, argument,
argument-effect, `result = pos.value`, and `result_effect = pos.effect`. It
records a q-specific `ApplySourceInput` containing the exact occurrence,
`checking = ConstraintOccurrenceId(q,0)`, result component, application-effect
component, and source input backreference. In scoped mode the occurrence map
also records q to its input index. Result Value and application Effect are
distinct endpoints.

In `shadow_apply.rs:1763-1895`, Apply admission rechecks the recipe/input
backreferences, source occurrence and all endpoint identities. It converts
q's result to a negative live Value term, constructs the negative Function
demand using argument, argument effect, invocation effect and q's result, and
stores the two separately: q's negative Value endpoint in
`NativeInterface.result`, and the negative Function demand in
`NativeInterface.demand`. It records q slot 0 and passes the admitted pair to
`constrain_live_value`. This authenticates the solver input; it does not yet
claim semantic satisfaction.

## Typed propagation and consumer

The typed drain is keyed by the original `ConstraintOccurrenceId` and cause.
`candidate_context.rs:3246-3320` seeds the relation from the checking-source
reference for that occurrence and retains occurrence provenance; the scoped
call input is consulted only for its matching local slot. `lib.rs:12042-12095`
and `:12296-12324` start and run the typed drain with that same occurrence and
cause.

When a positive lower Function is compared to q's negative Function demand,
`lib.rs:12655-12705` constructs ordered children. Child 0 is the contravariant
argument Value, child 1 the argument Effect, child 2 the result Effect, and
child 3 the covariant Value `FunctionField::Result`; that last pair contains
the Result side of q's Function demand. The drain stores the children and
enters FunctionAdmission rather than treating a capture graph as the consumer.

`lib.rs:12807-12828` advances the Function dispatch and calls
`candidate_function_port_admit(task, field)` for the selected child.
`candidate_context.rs:3375-3440` maps `FunctionField::Result` to
`FunctionPortOperation::Preserve`, checks the parent relation/demand, carries
the retained parent source set and scoped flow to the child, and records
`Dependency::FunctionPort { child, parent, field, operation }` (plus a Derived
dependency when already inside a derived relation). The child is then enqueued
as a typed work item.

The actual typed drain processes the child through Transport, Context and
Dispatch in `lib.rs:12354-12436` (split-stage equivalent at `:12402-12430`).
Transport updates the relation; Context calls `candidate_context_execute`;
Dispatch calls `dispatch_live_item` on that consumed child and repeats if it
produces further Function children. This is the consumer path missing from
R39's artifact.

## Helper result and extrusion boundary

`candidate_source.rs:1409-1425` stores `endpoints[q]` as the enclosing helper
lambda's `LambdaRecipe.body_value_endpoint`. `lib.rs:11342-11361` reads that
field as a positive live Value term when constructing the helper Function's
result. This establishes the relation between q's body endpoint and the
helper's candidate Function result construction. It remains a body/result
port, not a proof that q's complete source Call interface equals the helper
Function result.

Endpoint identity is not asserted across extrusion. In the typed pair path,
`lib.rs:12588-12622` may build a `rewritten` pair by extruding a non-row
endpoint to a retained copy. If rewritten differs from the admitted pair, the
solver records the diagnostic edge, calls `candidate_context_value_rewrite`,
retains the rewrite in the original memo, and enqueues the rewritten pair.
`candidate_context.rs:3351-3372` requires the actual whole-Value rewrite,
updates the retained demand root when its negative Function is copied, carries
sources/scoped flow into the child relation, and records a Derived dependency.
`lib.rs:13052-13070` retains the rewrite for later diagnostic reconstruction.
Accordingly, the occurrence and dependency chain are preserved through a
possibly copied endpoint; raw term-ID equality is not claimed.

## Remaining source edge and parent application

The native chain establishes source emission -> q Apply input -> authenticated
negative Function demand -> occurrence-qualified typed drain -> covariant
Result child -> Preserve/FunctionPort dependency -> Context/Dispatch -> helper
Function result endpoint, with an explicit retained-copy branch for extrusion.
It does not derive the authentic original `Q_q`/Application result
introduction. R39's independently reviewed proof/source result identifies
`DeclRef(A_q)` as the first missing original supplier datum. The source
semantic connection from the admitted Result child to the complete Call
result/future `Comp(E_q,A_q),o_q` and its ordinary `Desc` remains open, as do
the declaration's actual owner, sort, scope and ordered telescope. Receiver,
invocation effect, returned provider/world, pending suffixes and W/Z arms stay
distinct from this body Result port.

No source program, compiler test, Cargo target, CLI or runtime was executed.
Checks are static inspection and exact SHA-256 verification of contract pins.
The pinned Rust files were pre-existing dirty worktree inputs with authors
UNKNOWN; this assignment changed no Rust, test, fixture, expected output or
existing artifact. No semantic rule was adopted. Parent theorem, source/native
adequacy, F1/FK1, N-Transport, complete Call/effects, soundness, principality,
termination and production gates remain OPEN.

## Inputs and runtime

Contract `tasks/agent-loop/sprints/application-result-formation-20261018-r40.md`,
SHA-256 `a1ca3da89e79c7722f2f4e4a228086db360f0279ea1ee7e31ae6b970315eaa45`.
The direct paths and hashes are listed in that frozen contract. Relevant pins:

| Input | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` |
| `crates/yu-solver/src/shadow_apply.rs` | `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137` |
| `crates/yu-solver/src/candidate_call.rs` | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` |
| `crates/yu-solver/src/lib.rs` | `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee` |
| `crates/yu-solver/src/candidate_context.rs` | `42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca` |
| R39 compiler-review evidence | `6169082ba0552c52a6ebbe71cd2caa65f7e91da48bbe9c0d8c88f0d35bc6db0b` |

Writer: `/root` (primary); requested Luna/high, observed effective
model/effort UNKNOWN/UNKNOWN. Exact output lease is the R40 note and its inbox
handoff only. Native 900-second grant charged; active duration unmetered.
No descendants or scratch outputs. Revision 1 received fresh independent
compiler review; revision 2 closes the two minor factual items by primary
inspection. The R39 edge-supplying reviewer was not assigned. `NO_SAFE_CODE_SLICE`
for the pinned unknown-author production path.

## Review finding and primary closure

Fresh independent compiler review returned **MINOR corrections required**,
with no blocking or major native-edge finding. It identified (1) the swapped
`NativeInterface.result`/`.demand` description and (2) the malformed
`candidate_call.rs` digest. Revision 2 fixes only those textual facts. Luna
compared both changes against `shadow_apply.rs:1862-1864` and the actual
`candidate_call.rs` SHA-256, then reverified all five Rust contract pins and
the frozen revision-1 snapshot. This minor-only record repair is closed by
primary inspection under `rules/orchestration-budget.pre-sprint.md` §§Finding
batching and convergence control; it changes no code or semantics. Review
substantive scope remains the independent verdict above, not a second review
of revision 2. Parent conditions remain 0 -> 0.
