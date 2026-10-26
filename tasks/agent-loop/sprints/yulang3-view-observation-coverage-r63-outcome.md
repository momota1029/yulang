# R63 r2 scheduling outcome: artifact loss; parent remains open

Sprint: `YULANG3-VIEW-OBSERVATION-COVERAGE-20261026/r63`, contract r2
SHA-256 `aaeeaab87c69626d9299b99783f11eabe4c31fd5c99703eedf647af6fc5507f9`.
Proof baseline: `93d08d5867015741b3588ea3df4c56903b2bbe83`.

## Frozen results retained

The proof worker handoff remains at
`tasks/agent-loop/inbox/paper-observation-coverage-r63.md`, SHA-256
`5857db1f531e6774c66973a6ee998d065f762655c4c6b02b419ef825b3e40cbe`.
It records four candidate declarations and a focused build, plus an audit
process failure (exit 1) on unsupported `pp.width`; that failure is not
converted into a pass.

The primary receipt remains at
`tasks/agent-loop/inbox/paper-observation-coverage-r63-primary.md`, SHA-256
`242e72b5806769662a78ab99aa6ecd6ac64c2074aa5a2501496af4d4b8a09f80`.
It records an independent four-call verification PASS for candidate SHA-256
`ffbef4f87b61396258a693e7a091a767c5610efbd9128024ddf108c0348c82d2`, with
exact theorem types and axiom reports. This does not replace the required
independent review.

## Reconciliation and disposition

At continuation, the review agent was absent from the live agent list and a
follow-up to its recorded identity failed because that handle was not found.
No review receipt exists. The recorded proof and primary workspaces under
`/tmp/yulang-r63-observation-coverage/{proof,primary}` were absent; the stale
Git worktree registrations were prunable and their directories did not exist.
The candidate is also absent from the current worktree and Lean build cache.

The original candidate bytes cannot be independently reviewed or substituted
from their hashes and printed audit alone. The r2 scheduling envelope is
therefore **SUPERSEDED FOR ARTIFACT LOSS ONLY** by the separately authorized
`YULANG3-VIEW-OBSERVATION-COVERAGE-REBUILD-20261026/r1` envelope. The
mathematical question was not adjudicated: finite-observation coverage,
source/native correspondence, R23, whole-language execution safety, inference
A/B and production all remain OPEN. R62 remains conditional and unchanged.

The old reviewer remains UNKNOWN. Its exact review lease
`tasks/agent-loop/inbox/paper-observation-coverage-r63-review.md` stays HELD
and quarantined; no new reviewer may reuse that path. The stopped proof
worker's and primary's lost scratch/capture paths and hashes remain listed in
the two frozen handoffs. They are no longer active writers;
the new sprint uses disjoint workspaces and handoff paths. No source, semantic,
Rust, test or expected-output change occurred in r2.

## Next evidence

The rebuild must use the original proof baseline and 30 source pins, create a
new candidate with the same four theorem statements, and obtain its own exact
primary verification and fresh non-author review. No old validation is
inherited by the rebuilt artifact.
