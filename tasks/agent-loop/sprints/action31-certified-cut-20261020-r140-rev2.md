# Sprint R140 — certified backward cut for action31 Lambda replay

Status: ACTIVE after CLEAN prospective spec/compiler review and successful
baseline/live validation of the complete 39-path inherited dependency manifest.
Branch/baseline: `research/simple-sub-intrusion` / `7a584032e`.
Revision: 2 (activation amendment). Luna is primary and sole Git integrator.

## Fixed parent and outcome

Continue the unchanged computation-forwarding preservation theorem in
`notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7,
through the fixed ordinary-mode R72/R73 source and the action31 two loop-Lambda
replay families. Preserve one shared satisfying assignment, original
current-formal identities and Name arguments, arbitrary finite prefixes,
repeated calls, simultaneous receiving entries, and independent foreign-
continuation obligations. Simple-sub A/B and all source/native, inference,
evaluator and production gates remain OPEN.

The bounded success outcome is a **conditional certified cut** for both
action31 replay families: enumerate the exact source/native transition slice
needed to decide replay admission, currentness, recapture qualification, replay
products and selected slots; prove a frame condition for omitted state; and
apply the resulting premise reduction to the original parent. The cut must track
all relevant saved replay heads/cursors, acknowledgements, RelationId and raw/
canonical pair keys, physical multiplicity and fibers, memo/rewrite/group keys,
generations, allocation/interner effects, pending parents, and child products.
An unchanged endpoint, equal level, manual alias schedule, or guessed empty tail
is not a certificate. The sprint may end honestly UNFINISHED/OPEN if any state
component or transition cannot be covered.

## Exact input pins at the baseline

The live worktree must match these baseline blobs before activation:

```text
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
8bfe31e038f1c7684ac2d9dba95164f13448e150ccb08a874bea22610fc6e04f  tasks/agent-loop/sprints/helper-cut-ledger-20261020-r138-rev1.md
b9b91d5250b3f05def89891cca314ad24fcf84ec711b8c6e76c7c4dcf936c467  notes/theory/2026-10-20-r138-helper-cut-ledger.md
d7504666ab99ed3822fd91c103c056e4fbb9aad344ab10f2477567ba5a8b991c  tasks/agent-loop/inbox/20261020-r138-proof.md
8a1f531be9fb5e5f160bf4f75c6eb98bbc35ce0a30acaf06424c531840504ba4  crates/yu-solver/src/candidate_intrusion.rs
002b9d86e26cfda6fdf094ea4d161501849a7127d55c2d147d408a781b9fd28d  crates/yu-solver/src/candidate_context.rs
2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850  crates/yu-solver/src/candidate_scheme.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d  crates/yu-solver/src/candidate_extrusion.rs
cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7  crates/yu-solver/src/candidate_source.rs
19da9779e3e7866f5891e019e1cd343136ae0115bd1c47a02a7e7ee0cdfa80e0  crates/yu-solver/src/candidate_value_graph.rs
c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985  crates/yu-solver/src/lib.rs
838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543  crates/yu-solver/src/shadow_apply.rs
```

These are input pins, not claims that source transitions have already been
proved. The R138 ledger is reusable only for its reviewed prefix and must not be
presented as complete action31 coverage. Before activation and again before
freezing the proof, validate **all 39 path/hash pairs** in the R138 contract's
two dependency manifests against both baseline Git blobs and live files. This
inherits the complete constructor/consumer dependency boundary behind R138's
ordered ledger, including the source/native rules, `candidate_scheme`,
`candidate_context`, `candidate_intrusion`, `candidate_effect`, `candidate_call`,
`candidate_scope`, `lib.rs` transition orchestration, and `shadow_apply.rs`
ordinary Apply admission/drains. The explicit pins above call out the current
action31 control owners. Any mismatch stops the sprint for a versioned contract
revision; merely matching the R138 manifest file's own hash is insufficient.

## Lanes, boundaries, and outputs

- Constructive proof lane: configured Sol/high `prover`, after activation,
  writes only `notes/theory/2026-10-20-r140-action31-certified-cut.md` and
  `tasks/agent-loop/inbox/20261020-r140-proof.md`. It derives the cut, its
  frame condition, both replay families, and the exact parent application or
  missing premise. No delegation, code edits, execution, or Git.
- Primary lane: independently audits current producers/consumers for every
  retained and omitted state component and tests whether the result supplies a
  specific already-authorized code correction. R138 established
  `NO_SAFE_CODE_SLICE`; do not repeat its owner map unless R140 derives a
  concrete violation. No compiler changes, instrumentation, tests, builds, or
  expectation changes are authorized here.
- Fresh review after proof freeze: separate compiler/source and spec/authority
  reviewers inspect the frozen certificate and its exact source bridge. The
  proof author cannot review it. Reviews do not certify the original parent
  unless all its premises are discharged.

## Falsifier and stop conditions

The cut is refuted if an omitted physical duplicate, fiber, memo rewrite, saved
head, generation, interner/allocation event, pending acknowledgement, or child
product changes any selected replay transition, currentness, recapture
qualification, admission, or slot. Such a trace challenges this cut only; it
does not by itself refute the parent theorem. Missing ledger events or an
uncovered transition force UNFINISHED/OPEN. Stop on dependency drift, lease
conflict, new semantic authority, exhausted budget, or any need for an observer
or compiler execution.

## Resources, status, and next boundary

Cap: 1,500 active seconds, with 120 preparation/pin validation, 780 proof, 120
primary audit, 300 paired independent review, and 180 adjudication/closeout.
Zero Astra. No compiler/test/build process is planned. Preserve all unknown
legacy reservations and quarantined paths; do not inherit R138/R73 budget.

The implementation lane is explicitly `NO_SAFE_CODE_SLICE` unless a concrete
approved-behavior defect is derived. No code change means no compatibility claim
or production promotion. The next dispatcher boundary is sprint end, a genuine
counterexample, authority/dependency/lease/resource change, or an integration
seam.
