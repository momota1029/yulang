# Sprint R264 — occurrence-required lineage coverage

Status: ADMITTED under the unchanged Yulang inference soundness/Rust goal.
Branch `yulang3`; fixed baseline `288aae38a5b10ad0ce73eec7e37b476075d05133`.
Revision 1; Luna's admission is recorded in
`tasks/agent-loop/history/20261102-r264-admission.md`.

## Original claim and exact target

Preserve the full accepted source domain, Simple-sub A/B, original quantifiers,
independent satisfying assignments, shared witnesses, F1/FK1 and foreign
continuations. Parent/A/B delta begins at zero. Immediate edge is inference
soundness → R70 copy correspondence →
`R71-RAW-CANONICAL-FIBER-COVERAGE-1`.

The authoritative occurrence rule is §1.1(2) of
`notes/design/2026-10-11-yulang-inference-top-level-principles.md`: at each
copying occurrence retain the parent and child value-variable identities
associated with the actual type-variable copies. The approved occurrence
qualification in `notes/design/2026-10-12-intrusion-value-type-association.md`
retains the origin Value, receiver Value and actual polar parent/copy pairs.
This packet proves no new occurrence convention and grants no semantic or
production change.

The reviewed R71 contract/theory/closeout establish conditional forward
preservation through successful canonicalization and copying fibers at the
exact raw key. They leave required occurrence-specific lineage, full accepted
constructor reachability and preservation over all permitted merge/rollback
histories open. R261 adds only bounded executable-fiber nonemptiness/memo facts;
R262 narrows the later episode bound. Neither discharges R71.

## Fixed outcome and falsifier

Starting backward from an actual replay or scoped consumer, derive the lineage
required by that copying occurrence. Prove a proof-relevant simulation through
the actual production path:

`source occurrence + parent/copy pair` → physical owner/side/item/slot and raw
source `BoundKey` → canonical child key → actual relation/fiber transform and
relation-local residual state → copy admission/emission → demanding consumer.

Account for third-owner aliases, merge and canonicalization order, FreshUse,
scoped/unscoped transports, the complete selected physical prefix, duplicate
same-class slots and independently introduced canonical fibers. Keep source
occurrence, parent/copy identities, RelationId, raw/canonical keys, FiberTransform
and residual state distinct. Derive every edge from current pinned constructors
and consumers; do not import historical source behavior.

Success is the occurrence-required correspondence applied at the unchanged R70
copy edge, or a production-reachable accepted-source prefix where a specific
consumer requires a lineage that every actual candidate transport path lacks
after all same-class slots and permitted merge paths are accounted for. A
mismatched fiber set, endpoint equality, empty list or diagnostic-origin gap
alone is not a falsifier. If unfinished, freeze the first exact demanding
consumer and failed transport equation, retaining all original quantifiers.

Keep full ENTRY-WF, R70 drain/eventual Diagnostics, Q262-EPISODE, other R71
permitted-history/rollback obligations, diagnostic adequacy, successful-helper
coverage, full soundness, A/B, F1/FK1 and foreign continuations open unless
separately discharged. No divergence or production defect follows automatically.

## Exact inputs and authority

R255 manifest `tasks/agent-loop/sprints/source-owner-coincidence-r255.md`, SHA-256
`f6138d36052934093328e34c01102fc9155ea9d8a0ccfd19182af6e7e2d946ef`: all
**36/36 current source pins MATCH** at admission. These 36 paths are the only
Rust/HIR source read authority. Revalidate all pins before first source-body
read and at freeze. A mismatch stops the source line and returns to Luna.

Authoritative and adjudicated occurrence inputs:

- principles `notes/design/2026-10-11-yulang-inference-top-level-principles.md`,
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- approved occurrence rule `notes/design/2026-10-12-intrusion-value-type-association.md`,
  `531a9efae0ab7e03bfbd2f41cd7da86078e2fc8e67675d2c5c941972409f4e89`
- R71 contract `tasks/agent-loop/sprints/raw-canonical-fiber-coverage-20261019-r71.md`,
  `a6bd6aa1ab369f77b728014cd51693b11c5b3f97f85aab392d6488c8834ac1fb`
- R71 theory `notes/theory/2026-10-19-r71-raw-canonical-fiber-coverage.md`,
  `620947cece53ca60a7f8a2388a398f53850b835c79afd546bfdcfd10349a876e`
- R71 closeout `notes/progress/2026-10-19-r71-closeout.md`,
  `4b5f57b27d5bfbb0b3e4f7cfa86c03488f5d02f995c7f861dbe29e0d448edd3b`

R261/R262 reviewed dependencies:

- R261 theory `notes/theory/2026-11-02-diagnostic-reference-closure-r261.md`,
  `cd40dc11348513f03d24ab97c6dc410368d710990e1527d7b002415a711cef16`
- R261 reconciliation `tasks/agent-loop/history/20261102-r261-postfreeze-hash-reconciliation.md`,
  `1fd93a85d023e6ac193409ab67efa8dc551119c8b8e0a1147a701d9e108078f4`
- R262 theory `notes/theory/2026-11-02-source-wide-drain-progress-r262.md`,
  `848cd42d99d5638060703a14b332f9e7cce4e4a7e7def56ee5565b37a68cb63b`
- R262 outcome `tasks/agent-loop/history/20261102-r262-outcome.md`,
  `f057ef37b651c20a4668f006b26cfbb5bdd249d85b17a9dc094bf66e149f5a07`
- R262 overlap reconciliation `tasks/agent-loop/history/20261102-r262-overlap-reconciliation.md`,
  `bc0675bbc15362ffd7c38ea4e22bf5105936badff1c9c2617005fbe8b6ec9165`

R230 snapshot notes are unreviewed and excluded. The R263 source-causal-episode
assignment is STALE with an absent live identity; both exact R263 output paths
remain QUARANTINED. Do not read, write, use or release them. This R264 packet
uses distinct paths and may proceed without that result.

## Lanes, leases, and resources

Sole trial producer: unique identity
`/root/sol_r264_required_lineage_288aae38a`, requested Sol/high, no descendants.
Maximum 2,400 seconds across three substantive stages:

1. Derive exact required lineages from the authoritative occurrence rule and
   identify the actual demanding consumers; map the backward obligation.
2. Trace every relevant constructor/transport path, including raw/canonical,
   scoped/FreshUse, aliases, complete selected prefix and merge history. Prove
   the correspondence or construct a permitted accepted-source falsifier.
3. Apply the result at the unchanged R70 edge and freeze the exact residual
   obligations, hashes, source-pin gate and stop receipt.

Exact write leases, only:

- `notes/theory/2026-11-02-required-lineage-coverage-r264.md`
- `tasks/agent-loop/inbox/required-lineage-coverage-r264.md`

No code, source edits, tests, Lean, builds, probes, Cargo, scratch/cache,
generated outputs, network, runtime/quarantined reads or Git. Luna owns current
state and all Git. Implementation remains **NO_SAFE_CODE_SLICE**. After freeze,
a fresh independent `compiler_referee` may review within 300 seconds; no author
or contributor may review. Reserve stage 3 for application/freeze. Stop at a
source-qualified counterexample, exact unresolved equation, new dependency,
lease/budget boundary, 2,400 seconds or three stages. Unknown identities keep
paths quarantined and the full reservation charged.

R263's 2,400-second unknown reservation remains held; no capacity override or
path release is part of R264. The existing R209 user capacity disposition
remains unchanged. R264 and review reservations total at most 2,700 seconds.
