# Paired Function formal construction

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Baseline: `2d6cf2570f575c6563cf8e5691b334e6a705e575`
Status: private implementation realization; pre-write review complete, implementation active
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
