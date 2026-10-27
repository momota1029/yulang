# INLINE-AUTHENTIC-EXTRACTION-20261027/r2 — revision 5: compile repair only

Status: Luna-authorized, versioned continuation of the same fixed r2 outcome.
The original type-inference/executor objective, source domain, quantifiers,
semantics and all parent gates remain unchanged. Revision 5 authorizes only a
minimal compile repair and a frozen handoff. It authorizes no Cargo, Rust
compiler, test, Lean or Lake invocation.

## Inherited evidence and pins

This revision inherits r2 rev4, SHA-256
`1e99d83d65fd89705a4ce28db5da111b3d1e0fa4055faba1513b7bb8ec65ba0f`, and its
prior original/rev2/rev3 dependencies. The exact call-5 failure and raw receipt
hashes are frozen at `tasks/agent-loop/history/20261027-r2-cargo-call5-failure.md`,
SHA-256 `88fc68ea768da69a3f849ecbd616e72d69878c1730ebf6d48c67908b29a9754f`.
That receipt records the unchanged pre-repair source, manifest and lock pins,
exact Cargo command/environment/stdout/stderr/exit-time hashes, exit 101 after
17.57 seconds, ten compile errors, and absence of a trace. Invocation 5 of 6 is
spent. Invocation 6 remains held.

- Source baseline: `232b024e0d793714027170a388ab746ce0d2b429`.
- Repair checkout: `08297568389901af93c125844fe2ceba40de76b2`.
- Pre-repair `tools/inline-authentic-extraction/src/main.rs` SHA-256
  `9c484bf76e5c4d57ac616f1e8864e6bcd6fe388164f45eb3a1bc3db2ad02fa87`.
- Manifest SHA-256
  `21c64b4a22318a1ae89c346357161812a6ac313b6f0c4999853272cf73e2832b`;
  lock SHA-256
  `2ee467b8f6416aa7dda36f96f3401a0b0ae24a739ff7c6a2efccc1323777ee91`.
- Frozen source handoff rev3 SHA-256
  `72babfd8a453cc2959125db3055a98b58e6291cf70dd7790ee8566032ea54cec`.
- API owners inspected for the repair: `crates/yu-hir/src/shadow.rs`, SHA-256
  `b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e`; and
  `crates/yu-hir/src/module.rs`, SHA-256
  `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`.

## Exact implementation lease and permitted edits

Resume the same implementer identity `/root/inline_authentic_extraction_impl_r2`
on its existing implementation lease. It may write only:

- `tools/inline-authentic-extraction/src/main.rs`;
- the next sequential revision of
  `tasks/agent-loop/inbox/inline-authentic-extraction-20261027-r2-source.md`;
- existing scratch receipts under
  `/tmp/yulang-inline-authentic-extraction-20261027-r2/impl`.

The source edit is limited to the ten diagnosed compile errors:

1. Replace the three invalid `PositionId::ordinal()` calls with the exact
   artifact-position-table index of the already resolved `Position`. The
   public API `ShadowArtifact::position(&PositionId)` authenticates the ID and
   `ShadowArtifact::positions()` exposes that artifact's retained table. Find
   the exact resolved `&Position` in that table by pointer identity; fail if it
   is absent. Do not use `Position::ordinal()` for this field: that method is
   the raw-child ordinal under the parent, not the artifact-table index.
2. At the seven diagnosed `HirAvailabilityError` `?` sites, map the error into
   a standard error with the operation context and original `Debug` detail.
   Preserve failure propagation; do not default, swallow or turn errors into
   successful booleans.

No other source/schema behavior may change. In particular, do not change the
fixture, owner checks, emitted relationships, manifests, lock, compiler/HIR/
parser/runtime/API, tests, trace, Lean files or any other output. Do not
restructure the provisional extractor beyond what these compile errors need.

Before freezing, statically check each changed expression against the two
frozen owner APIs above, verify all three identity lookups preserve exact
artifact-local positions, and confirm all seven mapped errors remain fatal.
This phase produces no runtime evidence and must not claim compilation success.
Return the repaired `main.rs` hash, exact diff summary, pin checks and handoff
revision, then stop all writes and processes.

## Proof lane and execution gate

The proof identity remains STOPPED. There is no generated trace to consume, and
the unchanged finite schema has already received its permitted read-only
inspection. Do not resume Lean work or create candidate values in this phase.

After implementation stops, Luna independently inspects and freezes the exact
repaired source/schema hash. Only a separate immutable revision may authorize
Cargo call 6/6. That later contract must pin the repaired source hash, preserve
the same locked manifest/lock/graph and scratch target, and authorize at most
one `cargo run --offline --locked` under the inherited 1 CPU, 1 GiB and 120 s
limits with exact command/environment/output receipts. No Cargo call is
authorized by revision 5, and no seventh invocation is available.

If call 6 succeeds, freeze the generated trace and resume the existing proof
identity only after Cargo cessation and Luna's acknowledgement of the exact
trace and source-handoff hashes. Its inherited Lean limit remains at most 6
checker calls/360 seconds. If call 6 fails, preserve the terminal evidence and
reassess the route; do not retry or reset any budget.

## Preserved boundaries

The total r2 cap remains 3600 active seconds without reset; prior unmeasured
active time stays UNKNOWN. Cargo usage is 5/6, with the last call held; Lean
usage remains 0/6; Astra remains 0. No tests, builds, dependency resolution,
source-owner edits, semantic changes, production adoption or extra work are
authorized here. Fresh non-author review remains required after the frozen
trace and any proof handoff. Original Site/Name/declaration/root-Context/
ambient allocation, universal frontend refinement, A/B, soundness, effect
hygiene, principality, termination, source/native, whole-language, receipt,
admission and production gates all remain OPEN.
