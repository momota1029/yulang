# Successor source Apply/Group effect flow

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Baseline: `21504b7952a1d39fedb3fe6e660721222f4da86a`
Scope: nonshipping graph-candidate source constraint generation/admission
Authority: current Simple-sub correction, existing four-port Function variance,
and scoped Oracle application/unannotated Lambda ownership
Mode: M2; independent compiler-referee and performance-auditor
Status: reviewed implementation checkpoint; runtime behavior unverified

## Owning implementation

`CandidateInference::solve` now selects graph collection before constructing
`ConstraintBatch`. Selecting graph execution after collection would preserve
the old premature empty-effect facts. Default collection and the legacy
`CandidateValueObservation` continue selecting the prior pure recipe mode.

Group retains both its child's value and actual evaluation-effect component;
its value relation uses slot zero and effect forwarding uses slot one. Apply
retains both operands' value/effect endpoints, including the captured-local
collector. At admission it allocates one invocation-effect row at the actual
application-effect row's level, then generates:

```text
callee_value <: Function(argument_value+, argument_effect+,
                         invocation_effect-, result_value-)
callee_effect+ <: application_effect-
invocation_effect+ <: application_effect-
```

The three operations have distinct occurrence slots zero, one and two and
their actual owning causes. Effects enter the existing store, typed pair memo
and worklist. Argument evaluation enters the Function demand; no independent
argument-to-application edge is added. Graph Apply/Group receive no fixed Empty
upper. Existing mixed graph capture and fresh-use reconstruction retain these
new effect rows and bounds without a second exporter.

Formal Name fetch and Lambda construction remain pure, distinct from invocation.
The existing positive unannotated Lambda argument-effect is Empty; its result-
effect references the actual retained body component. This follows the scoped
Oracle constructors at `a58eefc31e22141574b6f20c6a5748151c6d79f1`,
`crates/infer/src/lowering/expr/tail.rs:535–627` and
`crates/infer/src/lowering/expr/lambda.rs:280–368,1244–1350`.
It does not certify the complete receiver/protection interpretation.

## Review and cost

The compiler referee traced operand identities, captured-local collection,
four-port variance, recipe scheduling, provenance, Lambda/body effect links,
graph capture/freshening and diagnostic ownership. It considered nested callee
`(f x) y`, nested argument `f (g x)`, Groups, repeated formals, outer captures
and late incoming lower bounds. No BLOCKING, major or minor finding was found
in the frozen delta. These were static traces, not executed source witnesses.

The resource auditor found no concrete blocking/major invariant violation.
Each graph Apply adds one fresh effect row and two effect-edge admissions;
Group adds one effect-edge admission. Graph mode removes the old two pure
effect facts per Apply/Group component. Source operation counts are three/two;
they do not count all propagated tasks. Enlarged recipe enum capacity is
included by the existing `size_of`-based accounting, including legacy recipes.
No separate source rescan, arena clone or recursive graph ownership is added.
Capture/replay and solver closure costs grow with reachable effects and uses;
no overall linear-time or speed-improvement claim is made.

Fallible allocation/admission aborts the consuming private solve before a
result escapes. Successful recipe completion samples include effect/store
capacities. Failed-attempt high-water accounting and effect-inclusive frontier
totals are not established. Measurement budget consumed: zero processes/samples.

## Verification

Primary owning checks passed without warnings:

```text
RUSTC_WRAPPER= cargo check -p yu-solver --features shadow-apply-candidate -j 2 --offline
RUSTC_WRAPPER= cargo check -p yu-solver -j 2 --offline
git diff --check
```

No tests, execution probes, benchmarks or workspace-wide suite ran. Existing
candidate tests mostly select the legacy observer, so their historical results
do not verify this graph-effect path.

Reviewed code SHA-256:

- `lib.rs`: `639b54b9a1f9ae3c9cde32229d932524d71da25babbb2d4e10e165675f24ee36`
- `shadow_apply.rs`: `993f06935e5dbfc49d373162da23d6e5b2f69e2a00ece08fa99fec3c3c60e2ba`

## Remaining implementation

The reference extrusion owner still needs polarity-keyed copied representatives
and directional bounds; current F5 lowering in place is not equivalent. Current
source/formal/fresh-use levels are all one, so general nested initializer
generalization and source level ownership also need an actual compiler bridge.
The source-local carrier map and extrusion implementation cut are separate
read-only planning inputs; no new registry or proof prerequisite is selected.

Runtime schemes/fresh uses, structured effect families, complete Call
receiver/protection/provider/world/image/admission/license/future behavior,
public extraction and `yulang3` F5 replacement remain open. This checkpoint
does not close any proof-DAG or complete Call/production gate. The full type
inference/F5 replacement objective remains active.
