# Sprint R265 — consumer lineage simulation

Status: admitted under the unchanged Yulang inference soundness and Rust goal.
Revision 1; Luna admission is recorded in
`tasks/agent-loop/history/20261102-r265-admission.md`.

## Original obligation and outcome

Preserve the full accepted source domain, original parent theorems and
quantifiers, Simple-sub A/B, independent satisfying assignments, shared
witnesses, F1/FK1 and foreign continuations. Parent/A/B delta remains zero.
The unchanged edge is inference soundness → R70 copy correspondence →
`R71-RAW-CANONICAL-FIBER-COVERAGE-1`.

Derive the exact lineage required by a reached replay/scoped consumer, then
prove a time-indexed, proof-relevant simulation through the production copy
path. Start from the actual consumer obligation and trace through
`Work::Bound`, raw-key lookup, canonicalization, FreshUse, aliases, merge and
the complete selected physical prefix. Retain source occurrence, parent/copy
identities, RelationId, raw and canonical keys, FiberTransform, and
relation-local residual state. In particular, account for the transport
sampled at `post_check_context(parent)` and the relation contexts composed by
replay; endpoint equality alone does not establish their temporal equation.

Apply the correspondence at the unchanged R70 copy edge. A falsifier must be
an accepted-source reachable copying occurrence whose named consumer requires
a lineage absent from every actual candidate transport path after all
same-class slots and permitted merge paths are accounted for. Mismatched
fiber sets, endpoint equality and source-shaped sketches are insufficient.
If unfinished, freeze the first exact consumer and failed temporal equation;
do not weaken any quantifier or occurrence requirement.

ENTRY-WF, R70 drain/eventual Diagnostics, Q262-EPISODE, other R71 permitted-
history/rollback obligations, diagnostic adequacy, successful-helper
coverage, full soundness, A/B, F1/FK1 and foreign continuations stay open
unless separately discharged. This packet grants no semantic or production
change.

## Exact authority and dependencies

R255 manifest `tasks/agent-loop/sprints/source-owner-coincidence-r255.md`,
SHA-256 `f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`,
contains the only authorized Rust/HIR source paths. The 36/36 direct pins
matched at baseline `51dd6af4e6a9cdfc305cecb825cb114d7b7e47ba`. Recheck all
36 pins before any source-body read and at freeze. Read only exact pinned
paths; do not use wildcard/glob searches that can emit unpinned files, tests,
or any path outside that manifest. A pin mismatch or accidental exposure of
an unpinned source is an immediate stop and Luna notification.

Exact governing dependencies:

- occurrence principles `notes/design/2026-10-11-yulang-inference-top-level-principles.md`,
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- approved occurrence rule `notes/design/2026-10-12-intrusion-value-type-association.md`,
  `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89`
- R71 contract `tasks/agent-loop/sprints/raw-canonical-fiber-coverage-20261019-r71.md`,
  `a6bd6aa1ab369f77b728014cd51693b11c5b3f97f85aab392d6488c8834ac1fb`
- R71 theory `notes/theory/2026-10-19-r71-raw-canonical-fiber-coverage.md`,
  `620947cece53ca60a7f8a2388a398f53850b835c79afd546bfdcfd10349a876e`
- R71 closeout `notes/progress/2026-10-19-r71-closeout.md`,
  `4b5f57b27d5bfbb0b3e4f7cfa86c03488f5d02f995c7f861dbe29e0d448edd3b`
- reviewed R261 theory and hash reconciliation:
  `notes/theory/2026-11-02-diagnostic-reference-closure-r261.md`,
  `cd40dc11348513f03d24ab97c6dc410368d710990e1527d7b002415a711cef16`;
  `tasks/agent-loop/history/20261102-r261-postfreeze-hash-reconciliation.md`,
  `1fd93a85d023e6ac193409ab67efa8dc551119c8b8e0a1147a701d9e108078f4`
- reviewed R262 theory and adjudication:
  `notes/theory/2026-11-02-source-wide-drain-progress-r262.md`,
  `848cd42d99d5638060703a14b332f9e7cce4e4a7e7def56ee5565b37a68cb63b`;
  `tasks/agent-loop/history/20261102-r262-outcome.md`,
  `f057ef37b651c20a4668f006b26cfbb5bdd249d85b17a9dc094bf66e149f5a07`;
  `tasks/agent-loop/history/20261102-r262-overlap-reconciliation.md`,
  `bc0675bbc15362ffd7c38ea4e22bf5105936badff1c9c2617005fbe8b6ec9165`

Exclude R230 notes, the quarantined R261 handoff, and both quarantined R263
and R264 outputs. R264's scope deviation is recorded at
`tasks/agent-loop/history/20261102-r264-lease-deviation.md`; it supplies no
proof dependency or usable output.

## Lanes, exact leases and limits

Sole proof-trial producer: fresh registered `prover`, requested Sol/high,
identity `/root/sol_r265_consumer_lineage_51dd6af`, no descendants. Luna does
not perform proof trials. Maximum 1,200 seconds over three substantive stages:

1. Derive the exact reached consumer requirement and source-ground each
   relation/transport witness.
2. Prove the temporal lineage simulation or construct its accepted-source
   falsifier, preserving every physical slot and residual state.
3. Apply the result at the original R70 edge and freeze the first remaining
   equation, dependencies, source-pin gate and writer-stop receipt.

Only these output paths are leased:

- `notes/theory/2026-11-02-consumer-lineage-simulation-r265.md`
- `tasks/agent-loop/inbox/consumer-lineage-simulation-r265.md`

No production/source edits, tests, Lean, builds, probes, Cargo, scratch/cache,
generated outputs, runtime/quarantined reads or Git. Implementation is
**NO_SAFE_CODE_SLICE**: current extrusion and Context/replay owners show the
proof dependency but no accepted-source violation that warrants a code edit.
After freeze, a fresh independent `compiler_referee` may review for at most
300 seconds; no author or contributor may review. Reserve stage 3 for
application and freeze. Stop at a source-qualified counterexample, exact
unresolved equation, new dependency, lease/budget boundary, 1,200 seconds or
three stages. The R263 and R264 unknown/stale reservations and all four
quarantined output paths remain unchanged.
