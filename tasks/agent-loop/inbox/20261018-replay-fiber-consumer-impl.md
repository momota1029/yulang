# Implementation lane handoff: Replay fiber consumer certificate

Contract: `npair-replay-fiber-consumer-certificate-20261018` rev1, SHA
`fce2f48df81227bfc427503fb785541835865f4c0970dbc27a514ff9f8cbb565`.
Baseline: `f56022c19`; proof checkpoint observed: `5d107a2bf`.
Lease was limited to the four solver files, the scoped replay example, the
progress note, and this handoff. Only the four solver files and the two
documentation/handoff files changed; the example is unchanged. No Cargo/test,
commit, push, worker launch, or lease expansion occurred.

## Frozen implementation

The exact code and file hashes are recorded in
`notes/progress/2026-10-18-replay-fiber-consumer-certificate.md`. The new gate
preserves route ownership and p1/h/q/C roots separately. It ties captured S to
the imported snapshot remap, binds FreshUse admission/emission and physical
fiber to the exact route and destination owner/lane, checks the retained
Replay recipe, scoped-flow identities, zero-step p1→h and q→C cases, and all
four typed consumer endpoint pairs. Nonzero root-changing paths fail closed.

The fixed module fixture now asserts that the first two uses have distinct
module routes, explicit p1=h and q=C identities, and physical-fiber evidence.
These positive assertions are **unrun**, so this lane does not claim the
captured roots are actually equal or either route authenticates. Two unrun
actual-record negatives mutate the captured BoundEvidence source-bound
polarity and retained source flow transformer. The previously existing
wrong-use/root/relation and override port-swap negatives remain.

## Exact unresolved evidence

1. Run the fixed two-use module fixture and expose the concrete copied p1 and
   Replay upper h IDs for each route. The code only has a zero-step p1=h path;
   if unequal, the missing owner is the Replay/relation producer that stores
   the root-changing typed edge.
2. The q→C path currently accepts only the source-confirmed zero-step case.
   If typed dispatch selects another relation, the missing record is the
   dispatch producer edge naming the consumed relation/root.
3. `BoundEvidence` records the imported snapshot and bound but carries the
   explicit `ReplayUseAntecedentsNotRetained` gap. The owner must retain the
   source-processing antecedent if this gap is to be discharged.
4. Actual dependency-kind, physical fiber-membership, and stored consumer
   endpoint mutation negatives remain undone. Add them only after reviewers
   accept that the fixed positive route authenticates and within remaining
   resources.

No new persistent allocation/storage was introduced. The runtime observation
path formats additional IDs/slot evidence; core checks scan retained objects.
No source, root, scope, constraint, or solver semantics were changed.

## Checks, resources, review target

`git diff --check` passed. Full-file `rustfmt --check` failed because the
existing solver files have broad formatting differences; it made no changes.
No Cargo/build/test was run during authoring. Parent's latest receipt estimated
about 300 seconds of the 1440-second authoring cap remaining at the beginning
of this finalization chunk; the protected 360-second runtime allocation was
not entered. Freeze this candidate now for independent review before any
runtime command. The implementation lane did not self-certify. The only
disposable state is the in-place uncommitted diff on the exact leased paths;
there is no scratch/generated path to clean.

The independent reviewer should first inspect compile/borrow correctness and
whether the public fixture's concrete p1/h roots satisfy the asserted identity.
If it does, run the positive two-use and two actual mutation tests, then add
the remaining targeted evidence mutations if budget permits. If not, retain
fail-closed behavior and report the exact first absent owner record. The
original parent theorem remains open; this candidate resolves zero theorem
conditions until reviewed evidence is integrated.
