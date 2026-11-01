# R147 independent review receipt

Status: **STOPPED — ACCEPT bounded source-boundary result; original theorem and production gates OPEN.**

Reviewer: `/root/r147_real_consumer_review`. Requested model/effort: `gpt-6.1-sol / medium`, confirmed by current assignment metadata. Observed effective model/effort: **UNKNOWN**. Budget: maximum 300 seconds; no descendants.

Read-only role: no artifact written. Intended sole artifact: `tasks/agent-loop/history/effect-permission-real-consumer-20261102-r147-review.md`. This response supplies its frozen content.

## Authentication

All required hashes matched **before semantic source or handoff inspection**. Baseline for every Rust, Lean and design source below: `3560df97dab02744da10e897c73c1cf94118f4ee`.

| Input | SHA-256 |
|---|---|
| R147 contract | `cc33e831cca0bd86717f0e4c7b995b8f89f2a5418979a66fdbcf0464bb6eeb90` |
| Latest R147 admission | `e87fd21c31b07805c64257892b64e2cc844badf8ac6d503024bc991f66b29b1f` |
| R146 outcome | `3329768d7176761310e0fffc203559b017e14fca36e76b5992e98c08284a2418` |
| R146 source handoff | `9c940ab56ccd182299833fe93b41701619d600b62c15f3af21b9b94659b694ef` |
| R147 source handoff | `d4f20f0f47d64b35416053c1f3be86daba197113b60acfb17ebf2cde9a3793ef` |
| R147 proof handoff | `f12a4cdbfe27bccb5a9a617ad40f775e7896b7c8b644f440a4b8c43f0de6a010` |
| R145 proof handoff | `da15341b46d3b7adef8cb1bd90d02bfe6dd27fc594a5fb96520f5cf84f82dcea` |
| R145 source handoff | `e543b1cd4c6d98d6fdaf912f228a8cd53e407fe72edf3338b2f1c9fca295ffba` |
| `candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `candidate_scheme.rs` | `e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814` |
| `candidate_scope.rs` | `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03` |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `shadow_apply.rs` | `2fa42a5570e660babab5da6361e0d71e0c022b234a21f7e01b78eafbfc65f278` |
| `lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| `candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `candidate_effect.rs` | `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01` |
| `NativeScopeTransformer.lean` | `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6` |
| `NativeFreshScopeTransport.lean` | `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5` |
| Compose release design | `fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679` |

Handoff names expand under `tasks/agent-loop/inbox/` as specified in the contract. No R146 proof deviation artifact was opened, hashed or used.

## Independently rederived result

**Allocator premise:** `candidate_source.rs:155–169` allocates initial scope IDs by append index; `1870–1894` allocates input IDs from call indices and records ownership. `ScopeInventory::from_plan:223–245` initializes the corresponding inventories. Successful `fresh:296–357` allocates each image from the current destination length before appending. Consequently copied images lie above the entire pre-copy range, while identity fallback on already allocated coordinates remains below it. Even repeated copied keys produce a last-write image above the cut; global injectivity over arbitrary natural numbers is neither required nor established.

The one `ScopeRemap` from `candidate_scheme.rs:4444–4451` renames transformer and demand coordinates at `4773–4796`; copied bound construction consumes the retained flow at `4888–4907`. Replay composes existing supports at `candidate_context.rs:4455–4476`. These constructors support the allocator argument for represented transformer/demand coordinates. They supply no bound or interpretation for an unidentified incoming consumer state.

Partial failed copies may consume identities before returning an error. The inspected context/intrusion rollback paths do not restore inventory lengths. This preserves append-range separation; it does not establish complete failure atomicity.

**Actual consumer:** `candidate_context_execute_relation:4219–4305` records scoped observations, processes ordinary filters and calls `candidate_apply_effect` at `4290`, or replays an already registered bound. `candidate_extrusion.rs:1147–1170` canonicalizes endpoints, inserts/replays row bounds, or calls `candidate_check_effect_operand` at `1165`.

The reached decision at `candidate_effect.rs:1437–1505` tests effect-family membership in an allowance, forwards to an allowance tail, or reports mismatch. It consumes neither input-route membership nor protection membership. Relation provenance remains available through processing/bound evidence; therefore the missing bridge cannot be inferred merely from two-argument signatures.

**Catch:** source Catch construction at `candidate_source.rs:1608–1623` propagates scrutinee and arm effects outward. `candidate_effect.rs:1252–1283` constructs continuation entry/returned rows and ordinary effect constraints. Those constraints share the candidate effect route through `lib.rs:13805–13841`. No scope-sensitive Catch subtraction or shared incoming `ScopeState` transport was established in the admitted path.

`candidate_context.rs:3280–3284` evaluates transformers over empty slices; `shadow_apply.rs:1646–1653` exposes that evaluation through observations. This is not an arbitrary incoming consumer state.

## Findings and closure requirements

**BLOCKING for source/native theorem application and production promotion — missing incoming-state/consumer bridge.**

Locations: `candidate_scheme.rs:4773`, `candidate_context.rs:4219`, `candidate_extrusion.rs:1147`, `candidate_effect.rs:1437`.

The native law requires the same maps on the transformer and the actual incoming state. The committed path establishes transformer/demand remapping and ordinary endpoint decisions, but no authenticated state carrier, state-side rename or protection-sensitive decision law. Treating demand or empty observation input as that state would omit inherited and external protections.

Governing requirements: `NativeFreshScopeTransport.lean:164–171,255–262`; authoritative compose design lines `34–56,76–82`, requiring release on corresponding occurrences inside output `'f`, retained attribution and preservation of independent protections.

Minimum closure evidence: identify the source-owned incoming contribution/state and its inventory bounds; demonstrate its transport through the **same successful FreshUse maps**; connect ordered transformer evaluation to a reachable effect/Catch decision; establish compose output-occurrence coverage. Keep the original quantifiers and independent protections intact.

This blocker is accurately disclosed by both R147 handoffs. It is **not a newly concealed submission defect**, and absence of that bridge is **not a reachable counterexample**.

No additional major or minor compiler-correctness finding established.

## Provenance classification

The R147 proof handoff explicitly records the late R146 source operation as hash-only, with no displayed or reused content. Its material conclusions are independently supported by the admitted baseline locations above. Its bytes are consistent with `ADMITTED_INPUT_HASH_ONLY / LATE_INTEGRITY_CHECK / CONTENT_NOT_USED`.

This review does not independently reconstruct the author's full runtime command history. It accepts that classification only to the extent supported by the frozen admission and author inventory; proof conclusions received independent source rederivation.

## Operations and limits

Mandatory instruction reads: root `AGENTS.md`, `AGENTS.pre-sprint.md`; current-state metadata and contract/admission used to locate authenticated inputs. Source inspection used exact baseline `git show` reads, bounded searches/windows and SHA-256 computation. Dirty working-tree Rust was not read. No files changed; no tests, builds, Rust/Lean execution, scratch/cache, environments, checkout/worktree or descendants.

Lean declaration inspection supplies no fresh checker acceptance or axiom audit. No full-language theorem, semantic approval, source-qualified counterexample or production readiness is certified.

**STOPPED.**
