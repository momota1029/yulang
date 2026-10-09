# Paired Function formal construction

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Baseline: `2d6cf2570f575c6563cf8e5691b334e6a705e575`
Status: bounded private implementation verified; M2 runtime and repair delta reviews clean
Authority: selected ordinary Simple-sub inference, annotation hygiene policy,
and active legacy withdrawal; no new public language decision or theorem closure
Mode: M2; semantic and source/test conformance reviews
Verification owner: primary; one bounded Cargo process at a time
Measurement budget: zero timing samples and benchmark processes

## Pre-write adjudication

Independent semantic review found the positive-bottom/open-negative realization
loses actual callback effects; the shared per-port correction closes that trace.
Distinct structural ports are allocated together, so an annotation-wide omission
cache cannot merge them. Independent source/conformance review reports no
findings in the corrected constructor and authorizes moving only the temporary
Function/named-variable unsupported fixtures into positive coverage. All other
refusal controls remain. Both reviews retain the full hygiene/principality and
wildcard scope limits; neither is runtime verification or implementation review.

## Constructor and dependency replacement

Build positive and negative annotation interfaces together before the body.
For each Function node with paired value children, allocate two distinct
ordinary levelled effect rows for its omitted argument and result effect ports:

```text
P = Fn(A_negative, q_argument_negative, q_result_positive, R_positive)
N = Fn(A_positive, q_argument_positive, q_result_negative, R_negative)
P <= body_formal_negative
body_formal_positive <= N
enclosing Function domain = N
```

Body lookup retains its ordinary formal row. Incoming actual providers compare
against N, without an additional direct provider-to-body-formal edge. Both
interfaces share each corresponding inferred effect coordinate, so actual
callback effects reach body invocation and latent returned callbacks through
ordinary Function port comparisons. Each Function occurrence has independent
argument/result coordinates. Named annotation variables retain their actual
binding scope and share ordinary rows across that binding's formals; separate
local bindings do not share rows merely because variable spelling matches.
The current top-level whole-binding annotation joins the same definition
environment as its formals. Whole-local annotation support remains a separate
missing producer. Named variables are ordinary Simple-sub rows, not rigid
concrete-type equality checks: multiple lowers can form a union, and actual
upper demands determine incompatibility.

This construction replaces calledness and observed-port reconstruction with
ordinary constraint generation and propagation. No early satisfiability check,
registry prerequisite or permission inferred from a solved Function shape is
introduced. Existing Value entry effect propagation remains part of the
enclosing Function construction.

## Rejected realization and source limits

Frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
`annotation/constraints.rs:124–138` supplies both annotation/formal comparisons.
Its omitted effect bounds at 492–497 are positive bottom and an open negative
row. Its raw formal provider connection supplies additional flow. Separating
that negative interface while keeping positive bottom loses actual callback
effects. The existing successor signature constructor's closed-empty defaults
are likewise unsuitable here. Use shared inferred coordinates instead of
copying those defaults into the separated formal interface.

Oracle `lowering/expr/lambda.rs:1247–1280` passes annotation solver-variable
maps across formal construction. Preserve binding-scoped variable identity.
No wildcard carrier exists in the current HIR annotation value enum; wildcard
support is still required by the full inference objective, not certified here.

This gate admits recursively effect-free Int, Unit, named variables and
Functions. Explicit effect rows remain the next coupled attachment/filter
constructor-consumer gate. Closed `[E]` must retain its actual filter: an open
row tail does not by itself allow unmatched F. Full annotation hygiene, Call,
soundness/principality, independently owned public schemes and default migration
remain required. No Oracle equivalence theorem follows from this constructor.

## Implementation and verification contract

Retain the negative domain association at the actual parameter recipe owner;
journal publication and scoped variable-map insertion with ordinary allocation
and bound changes. Source actions execute before body inference; completed
Lambda construction consumes the association. Capture/freshening/extrusion and
intrusion operate on the actual Function children and shared ordinary rows.
Account for retained map storage and temporary recursion/constructor storage;
work and fresh rows are linear in annotation structure, with the existing
128-depth admitted syntax boundary. No context-word proliferation is introduced.

Focused source regressions must check compatible/wrong/unused callbacks,
annotation-only body result inference, actual invocation effects, latent returned
callback effects, effectful callback arguments, nested Functions, repeated
variables across formals, local binding isolation, independent fresh uses,
recursive/open provider discovery and complete failure rollback. Assertions
must inspect actual result/effect fibers, not any matching global graph leaf.
Preserve historical controls. The former Function/named-variable unsupported
fixtures need pre-write conformance adjudication before their approved support
boundary changes.

## Initial implementation evidence and accepted repairs

The frozen implementation passed five new source integration tests, seven
primitive formal controls and the 43-test source/operation/annotation/lifecycle
matrix. Its private actual invocation-effect fiber regression also passed.
The private reused-name rollback regression failed: its checkpoint preceded a
successful transaction begin, which correctly advances the journal epoch.
Both independent implementation reviewers identified the new test boundary as
wrong; the global checkpoint assertion and generation-exhaustion contract remain
unchanged. Capture the operation checkpoint after begin and verify the returned
epoch explicitly; resetting an epoch with stale seen marks would be unsafe.

Semantic review additionally found new named-key and domain storage could be
freed by injected rollback before peak sampling observed it. Sample while the
new retained and undo payloads are live, before failure hooks; add a long-name
failure regression showing both payloads and restored retained totals. One fresh
producer owns the batched two-file repair. Runtime certification is pending the
repaired checks and fresh delta review; no full semantic gate is closed.

The first repair's stronger rollback witness exposed an owning store defect:
`ConstraintStore::rollback_route` removed only the first appended canonical fact
and first receipt. Paired admission needs all new facts/receipts removed,
including duplicate fact admissions. Repair the new suffix/receipt interval at
the store owner without scanning old entries. The resource witness also must
measure the retained sigil identifier (including its apostrophe), and sample
surviving storage after rollback rather than compare restored counters with a
stale live-allocation sample. A fresh batched repair owns these accepted delta
findings; the earlier epoch correction remains valid.

## Final bounded delivery

The accepted repairs above are complete. The store removes every new canonical
fact and consumed receipt before restoring the route; duplicate admissions,
unconsumed receipts and serial reuse have an owning regression. Repeated mutation
of a pre-existing shared row restores all logical state without rewinding the
journal epoch. Independent retained/undo-storage census covers the live payloads
and surviving containers. Final fresh semantic delta and the narrow default
feature-guard review report no remaining blocking or major findings.

The [delivery record](2026-10-10-paired-function-formal-integration.md) records
93 distinct focused tests, owning all-target/all-feature and workspace checks,
and final default-feature check and store regression. Nine new owning tests
exercise actual callback fibers and rollback/accounting. Zero timing samples
or benchmark processes were consumed. This closes only the effect-free paired
Function/named-variable implementation gate; genuine full semantics remain open.

## Remaining production seams

A pinned source audit at `2d6cf2570` identifies the actual default migration
chain: `yu-hir::lower_module`, `ConstraintBatch::collect`, ordinary session/SCC
publication/incoming uses, `SolvedModule::finish` and public result queries.
Core/backend packages do not presently consume solver results. No new CLI or
backend is required merely to migrate this chain. `SemanticImports` has only
`empty()`; `ClosedValueScheme` depends on its producing arena, and private graph
exports borrow their producing session. Independent owned export/import is
still a genuine gate: destroy the producer, install a public packet in another
session, preserve generic/fixed anchors and joint recursive sharing. A vector
clone of live row/effect-algebra indices does not satisfy that ownership.

For explicit negative concrete rows, the next coupled packet needs attachment
identity, weighted Value and Effect endpoints, contextual typed worklist/memos
and bound origins, consumed insertion filters with future-lower registration,
and a concrete negative-head/residual consumer. Mix cancels attachment words,
not concrete family support. Capture/freshening, canonical equality and rollback
must transport these exact dependencies; contextual self-edges cannot use the
current unconditional equal-row shortcut. Existing source lifetime mapping and
the repaired finite insertion model are inputs, not production certification.
Pure argument-effect passthrough and weighted-cycle resource limits need their
own exact correspondence. No second semantic registry or calledness rule is
introduced by this next packet.
