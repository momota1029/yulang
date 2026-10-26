# Native birth-level SCC correction: frozen handoff

2026-10-26. Producer: `/root/inference_frontier`. Assigned baseline: `0f6346a2de0a8bff863f41d487eb4b29cf8fb5f3` on yulang3. This implements the existing October 24 qualification rule in the private native candidate. Independent frozen implementation review and integration remain the primary's responsibility. This packet does not certify whole type-inference soundness or production promotion.

## Actual defect and authority

The previous `candidate_value_graph::Graph::seal` computed one SCC partition of all raw reference/helper edges, and `qualifies` compared those components. No immutable Value birth was stored. The authoritative `notes/design/2026-10-24-birth-level-scc-intrusion.md` instead requires mutual reachability in the induced semantic graph at one fixed birth, with every semantic path vertex at that birth. Its implementation boundary was explicit; the native code had retained the older global-SCC behavior.

The existing source fixture is unchanged:

```yu
my loop x = { my helper y = loop y; helper x }
```

The actual source walk starts the module at 1 and plans the nested initializer at 2. Both reciprocal reference edges remain in the raw graph, but neither cross-birth occurrence is eligible for SCC intrusion. Previous internal and observer tests explicitly expected both to qualify and their actual polar pairs to merge.

Before any such assertion edit, `/root/execution_frontier` independently checked the source level rules and October 24 authority; `/root` relayed ACCEPTED pre-write spec review. The approved change removes those stale SCC/equality expectations while preserving successful inference, actual extrusion pairs, occurrence identities, groups and retained reuses. It does not assert universal parent/copy inequality, because independent legitimate constraints may still equate them.

## Implementation and exact invariants

### Immutable birth census from the existing source planner

`Graph` now retains `planning_levels: Vec<Option<u32>>` aligned with its existing vertices. For semantic vertices this is immutable source birth. For helpers it is only the actual source-expression planning level. Existing semantic identities, helper identities, raw references and occurrence associations are retained.

`retain_source` returns the fragment-index vector it already constructed. The actual `candidate_source::emit_candidate_source` walk then supplies levels; no separate source grammar or second level-inference walk was added:

- Module Values and source roots are born at the existing root level 1. This covers forward module references before their bodies are visited.
- Each `Work::Visit` records its actual expression level and the matching helper level. It never sets the birth of the Value resolved by a Name.
- Root parameters use 1. Lambda formals and record-pattern formals use the lambda's current source level. Lambda bodies/defaults keep that level.
- `Work::Initializer` records a local's birth at the already-selected enclosing level+1. Subsequent references preserve that same Local identity and birth.
- Catch/Case declaration owners record the current arm level for every binder, including unused binders and binders whose first Name appears in a deeper initializer.
- Repeated assignment must equal the original level; conflicting assignment returns collection failure. Seal refuses missing levels rather than defaulting them to a mutable row level or zero.

`record_birth` does not add isolated vertices for unused declarations. The preceding actual graph-construction walk has already interned every represented Name/receiver and all represented binding identities. Cross-module Names resolve Module identities whose source root level is fixed at 1.

The source-owner walk also now descends through FieldTail receivers and OperatorApplication operands, matching the existing inference walk. Without this, a call under a field/operator wrapper in a nested initializer could retain the outer default owner. No field/method/operator meaning, operator demand, or resolution rule was changed. A focused FieldTail fixture checks the exact nested owner.

### Helper projection and SCC computation

The proof-facing invariant agreed with the independent Lean lane is:

1. Planning level on semantic vertices is their immutable source birth.
2. Every raw edge whose destination is a helper preserves planning level. This covers semantic-to-helper and helper-to-helper edges.
3. A projected semantic reference is the nonempty raw path between semantic endpoints with only helpers internally.

The native `seal` validates complete levels and invariant 2 on every raw edge before computing components. Helper-to-semantic edges may cross levels. It then runs the same iterative two-pass SCC algorithm, skipping unequal-level edges in **both** forward and reverse traversal. The raw adjacency and reverse adjacency are not modified.

For each existing helper constructor, result-to-own-fragment has the same expression level. Fragment-to-direct-child-fragment links have the same level because the actual source planner passes it unchanged. StatementBlock fragment links exclude nested binding initializers; those are planned separately at level+1 under their own semantic Local owner. Name fragments terminate at semantic Values and may cross birth, so those raw edges remain present but are excluded from qualification traversal. Group/ascription boundaries retain the existing fragment policy.

`execution_frontier` is constructing the corresponding `BirthLevelSCC.lean` contraction/expansion theorem. Its communicated `PlanningInvariant` is exactly the native helper-entry condition. This handoff does not assert that an unfinished or unreviewed Lean file is checked. The original whole-source incidence/occurrence correspondence remains a separate obligation.

### Existing intrusion consumers are unchanged

`retain_extrusion_parent`, `finish_candidate_extrusion`, and `recapture_candidate_extrusion` continue consulting the same graph predicate for their retained actual source events. `settle_candidate_intrusion`, parent/copy merging, bounds, row-level minima, non-generic flags, provenance, replay and freshening are unchanged. Birth never reads or follows those mutable row levels.

The existing `source_events(...).any(qualifies)` policy is unchanged. This packet does not prove that its support choice equals the actual semantic receiving Value. Likewise, `Graph::resolved` still has its existing represented identity domain; full imported-Name/source correspondence was not invented in this repair.

## Focused regressions and preserved evidence

Five added graph regressions check:

1. A source declaration's birth remains fixed when referenced in a deeper initializer, conflicting reassignment is rejected, and both nested cross-birth references remain raw edges.
2. A Case binder retains its declaration/arm birth despite first use in a deeper initializer.
3. A call inside a FieldTail receiver retains its nested definition owner.
4. Same-birth endpoints connected only through a cross-birth detour do not qualify, while the same actual Value qualifies reflexively; raw edges are unchanged.
5. Missing helper census and a level-changing helper entry are rejected; the correctly levelled helper expansion preserves the SCC.

Existing graph fixtures now obtain their levels from the actual source planner before graph-only resealing. No test-only inferred birth grammar was introduced. The synthetic all-one-level SCC test supplies its explicit uniform level. Existing reference/fragment/tuple/record/variant/conditional and source-owner assertions remain intact.

The two stale nested-fixture tests retain the original source. The observer test name now states the corrected cross-birth occurrence/pair contract. Both retain real extrusion and pair-kind/provenance evidence; neither substitutes a vacuous assertion that all unrelated rows remain distinct.

## Verification and resource receipt

The primary supplied official Rust/Cargo 1.99.1 in `/workspace/scratch/f98087c7ac1a/toolchains/rust-1.99.1/bin/`. All invocations used the absolute cargo/rustc/rustdoc paths, `--locked`, `CARGO_BUILD_JOBS=1`, `CARGO_PROFILE_DEV_DEBUG=0`, `CARGO_PROFILE_TEST_DEBUG=0`, `CARGO_INCREMENTAL=0`, the primary-owned scoped `rust-cargo-home`, and scoped `rust-target`. Native sandbox escalation was explicitly authorized because of the environment's self-path limitation.

There was at most one Cargo process group at a time. Each process had a 6 GiB address-space limit. The first cold build had a 600-second limit; each subsequent focused command had 120 seconds. All three completed normally; no timeout, forced stop, failed compile, test failure, or output-matching repair occurred. One monitored rustc observation was about 1.4 GiB RSS; this is not a measured peak.

| Command suffix after the absolute cargo path | Result | Wall seconds |
|---|---|---:|
| `test --locked -p yu-solver --features shadow-apply-candidate --lib candidate_value_graph:: -- --test-threads=1` | 24/24 passed; exit 0 | 110.695665 |
| `test --locked -p yu-solver --features shadow-apply-candidate --lib candidate_intrusion::tests:: -- --test-threads=1` | 17/17 passed; exit 0 | 0.421176 |
| `test --locked -p yu-solver --features shadow-apply-candidate --test candidate_intrusion_observation -- --test-threads=1` | 3/3 passed; exit 0 | 20.278113 |

The graph command ran 24 tests, intrusion unit command 17, and public observation command 3. The lib-test and library compilations each reported 19 warnings, with no errors. No broad workspace/test suite, formatter sweep, benchmark, or additional Cargo check was run. The three focused gates exercise the modified responsibility and its actual intrusion consumers; they do not prove the entire inference algorithm.

Static cost: one retained `Option<u32>` per existing graph vertex (capacity explicitly charged by `Graph::bytes`); one source-identity index lookup for each recorded expression/declaration; reuse of the existing fragment-index vector during the source walk; one edge validation pass and constant level tests in the two existing SCC traversals. This is O(N) logical census work plus O(V+E) graph work under the existing identity-index cost model, with O(V) added retained metadata. There is no per-level full graph rescan or quadratic helper elimination. The fragment vector lives longer during collection, remains included in construction scratch accounting, and is dropped after the source emitter returns. The existing bounded-linear nested-Apply storage regression passed. No broader performance claim is made.

## Frozen output and evidence hashes

| Repository output | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_value_graph.rs` | `aaaa88a374083f898188cd390b8cf0244855d8c09c8939b9e68ee2831bc692cf` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_intrusion_tests.rs` | `12bf5b890f04a577f8fe633724d7c6ea526e4b5da744bb26aa3797d1fb444668` |
| `crates/yu-solver/tests/candidate_intrusion_observation.rs` | `9aec9745908177e2e2ebef67634444fb0d5f703732735951121db9d74e1ffc23` |

All checker evidence is under `/workspace/scratch/f98087c7ac1a/inference-native/`.

| Evidence | SHA-256 |
|---|---|
| `graph-tests-01.log` | `04fb27193bfda412cf3d2ad77c9d0d5ee55beff697faa0eddcbfa3b8f2d9c815` |
| `graph-tests-01.json` | `a520d2a12ad03a8b206dbff6984f8a6d25db15de761820df6e7970459749321e` |
| `intrusion-unit-01.log` | `eb39dd4def99546b278a1189a33ab8f94984d4923fcf226477a2625d6ed96d3a` |
| `intrusion-unit-01.json` | `116eee38eab730807c5a693f771f4d1600b187c216e485d2f21e3f37c4c2e875` |
| `intrusion-observation-01.log` | `15ef3e5bc6a44269eeffc1124c35968e44e10b2955ba9d3584854d20c62a3a94` |
| `intrusion-observation-01.json` | `ec63f8a2c09f2b0b1f0123b8d45fe1b251a39e412f77fd554f1bfa0b727739a7` |

## Remaining original obligations and ownership

The native qualification criterion now follows the existing birth rule for the represented source graph. It does not establish source-wide constraint generation soundness, complete Call realization, actual receiving-Value/support attribution, BL-JOINT's whole-telescope/full-domain transport, legality of every qualified parent/copy equality, generalization/fresh-use solution transport, combined termination, original A/B, or public production/F5 cutover. The parent must compose the independent Lean result, frozen code review and source/native correspondence without weakening those original domains.

Only the four exact leased Rust files and this handoff were written during this implementation packet. The earlier map receipt is a separately frozen output. No compiler file outside those leases, dependency/configuration/lockfile, expected output beyond the independently approved assertions, Git state, scheduling record, or other agent's file was changed. Scratch writes were only the explicitly authorized Cargo/cache/target and check evidence paths. No children were created.

The implementation is frozen for independent review. All three Cargo process groups have exited. No check is running, and no source or receipt mutation remains pending.

Writes stopped at 2026-10-26 01:16:20 UTC. Receipt SHA-256 is returned separately to the primary.
