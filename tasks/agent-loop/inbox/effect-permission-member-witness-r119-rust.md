# R119 Rust handoff — ordered concrete-member witness

Sprint `EFFECT-PERMISSION-MEMBER-WITNESS/20261102-R119`; contract revision 2 SHA-256 `c499fe513f2c6915049775affe5b159ae0ecdc971b172962b85dc3aaa95fc40a`. Assignment `R119-RUST`, handoff revision 1. Parent: original Simple-sub inference-soundness/effect-hygiene claims and native/source correspondence remain OPEN. Outcome class: **unapplied Rust patch candidate; uncompiled and unchecked**. No production or theorem gate is closed.

## Runtime, authority, and exact paths

- Worker identity: `/root/r119_rust_impl`. Requested model/effort: Luna/high. Observed model/effort, session receipt, wall/CPU/RSS telemetry: UNKNOWN in this worker view.
- Assignment bound: ≤480 seconds. Exact leased writes: `tasks/agent-loop/artifacts/effect-permission-member-witness-r119.patch` and this handoff only.
- No source edit/application, compiler/Cargo/test, Lean/Lake/checker, Git command or mutation, environment/storage probe, formatter, scratch/cache/worktree/temp output, or descendant was used. No source code is compile- or type-checked by this handoff.
- Paths written: the exact two leased paths above. No generated/disposable scratch paths exist. Writes STOPPED at this freeze; no descendant leases remain.

## Frozen inputs and reused evidence

Contract: `tasks/agent-loop/sprints/effect-permission-member-witness-20261102-r119.md`, SHA-256 `4f6fb5f15c40adca5fdf58b18191bd29323216729b12327a1ea90dc4a37b0f7a`.

- Immutable baseline: `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`. Prior R117 evidence pins `candidate_receiver.rs` blob SHA-256 `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2` and `candidate_effect.rs` blob SHA-256 `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41`.
- R117 patch SHA-256 `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1`; R117 Rust handoff SHA-256 `6557b368fb1f092d5c4151cb54d74c7dd61c92153105e8720b17189c1efd128e`; independent R117 review 2 SHA-256 `a47cfe5a54cc2d22b3fcd2834bed3f3c959ba85cfcb28cf38ed095db06488664`.
- R118 corrected Rust handoff/review SHA-256 `edec3e3d1747b9b4c78ea6ce19c9cc19de9db1f1ac113e4001c230db9249fd2f` / `d82023743bd5fd0c47d5baf21082aaa702359c787acd8687cc2ebd15177551f5`.
- R118 Lean proof/obstruction handoff and review SHA-256 `fa4fcadbf028846469897aa815df4f58a9daeff58740f04891efde651edf6e79` / `bee20cccf34f82388f5f68836e95865c1f878381c45f0fa7df7a95cce8d0ef7b`; Lean candidate/review pin `2ebb7797c683b2bbf51d746f89d58d9abc4be66b5520fe6c0f4c6007a70d82ab` / `bee20cccf34f82388f5f68836e95865c1f878381c45f0fa7df7a95cce8d0ef7b` as cited in the R119 contract and R118 review artifact.

I used the frozen R117 patch and its reviewed descriptions of the exact permission/projection/request fields and consumer, plus the R118 corrected Rust and Lean obstruction records. I did not read working-tree Rust. I did not independently fetch the baseline blobs in this assignment; direct Git reads were out of scope here. Accordingly, the patch is a delta to the R117 candidate and depends on that exact frozen R117 patch being applied first. I did not validate application or inspect the resulting source.

## Proposed source-to-consumption correspondence

The R117 candidate already authenticates a `FormalEntryPermission` by `permission.registration` and carries both its compact permission-vector `permission_index` and exact borrowed record pointer into the package consumer. R119 adds a distinct `permission_member_index: Option<usize>`:

1. In `ProviderNativeContextProjection::capture`, the selected provider family is read from the already-selected owner view member. `permission.concrete.iter().position(...)` records the first ordered index whose family equals that provider family. The optional value is retained without turning an absent provider-family match into an earlier capture failure.
2. That index travels on the provider projection and `InventoryCatchRequest`, beside the already-retained permission reference and packed storage position.
3. At consumption, the existing exact retained-record pointer and registration checks remain. The old `concrete.iter().any(provider_family)` guard is replaced by `concrete.get(permission_member_index) == Some(provider_family)` on that same retained record. An absent index or out-of-range index yields the same local `None` failure as a missing family did before.

The three coordinate spaces remain separate: `request.registration` selects the formal registration record; `permission_index` is the compact retained permission-vector position; `permission_member_index` is the concrete family position inside that exact record. `provider_member_index` remains the native owner-view member coordinate. No integer coordinate is equated with a family identity.

The capture-side old existence predicate for `owner.schema.provider_identity.family` is expressed as `position(...).is_some()` and retains the same success condition. The new provider-family position is optional, and consumption remains the rejecting point when it is absent. Duplicate equal concrete families select the first ordered occurrence; indexed consumption reads that same value. Existing R117 guards, formal registration lookup, operation/view checks, inference paths, suppression, diagnostics, and public behavior are otherwise untouched by this delta.

This is a source candidate correspondence only. It does not authenticate the R39 pre-constructor event, establish R45 extraction, interpret pointers/slices in Lean, or instantiate the R116 parent theorem. R118's first blocker remains: decoder/post-state evidence does not provide the authentic pre-constructor batch/effect state and source Action/row with R39's absence premises. Original source/native correspondence, whole-language inference soundness, effect hygiene, principality, termination, and production remain OPEN.

## Artifact, checks, and limits

- Patch path: `tasks/agent-loop/artifacts/effect-permission-member-witness-r119.patch`.
- Patch SHA-256: `5bc02af31d3c80ecae3848760b8723195dd568a7bf924cfc8b3b614b1227a18a`.
- This patch is a sequential delta against the R117 revision-2 candidate, not a baseline-to-final patch. It was not applied, and unified-diff application, Rust parsing/type checking, borrow checking, and runtime behavior are UNKNOWN.
- No executable checks were permitted or run. No checks establish actual Rust semantics. The checks performed were limited to recomputing SHA-256 for the named frozen R117/R118 artifacts and manual review of this patch's coordinate flow against those frozen artifact texts.
- Known omission: no independent baseline-source read in this assignment. The exact source-owner references and pinned baseline blob hashes above are inherited from the reviewed R117/R118 evidence, not freshly authenticated here.

## Mutual TODO and next related step

`R119-RUST-TO-PROOF-1`: the proof lane should model the ordered `position` result as the first matching concrete member of the exact selected permission, transport the optional index without assuming success, and derive the consumer equation `concrete.get(index) = some provider_family` from the same record. Keep formal registration, packed retained-vector position, native view/member coordinate, and concrete member position distinct. Required inputs are this frozen patch/handoff plus R117's reviewed pointer/record guards. Falsifier: a successful consumer reads a different retained record or an indexed family different from the provider family; duplicate-family coverage must establish first-match order. This TODO requests a proof/model artifact only and grants no source, Lean-file, or execution lease.

The next related step is the already assigned independent review of the frozen R119 patch and handoff, with the R119 proof candidate reviewed at the integration seam. No extension of this Rust lease is requested. Frozen handoff revision 1 SHA-256 is reported separately by Luna to avoid a self-hash cycle. Pending independent review and primary adjudication.
