# NATIVE-RESTORATION-FRAME/r4 proof handoff — revision 1

**Outcome: CONSTRUCTED, UNCHECKED local algebra; native completion bridge OPEN.**
This is a frozen candidate for source-first review. It is not a proof receipt,
independent acceptance, complete source inventory or production authority.

## Contract, identity, authority and leases

- Sprint/contract: `NATIVE-RESTORATION-FRAME/r4`,
  `tasks/agent-loop/sprints/native-restoration-frame-20261028-r4.md`, SHA-256
  `0c76993f4759bef5ff466fd039ce5d551fcec10996ab6d6c40f6643a5af87902`.
- Baseline: `2c63118937324500a41582f1c452117b819396f7` (contract baseline;
  this leaf ran no Git command).
- Assignment/author/session: `/root/native_restoration_frame_r4_proof`, active
  tool session for `NATIVE-RESTORATION-FRAME-20261028/r4`; no descendants.
- Requested registered lane: `lean_prover`, `gpt-6-sol / high`.
  Observed serving model/effort: **UNKNOWN**; runtime exposes no authenticated
  effective model/effort field to this leaf.
- ACK of contract, identity, exact leases, grant and active work was sent to
  primary before source/artifact body reads. The requested settings were
  supplemented before those reads at primary's request.
- Exact writes, and all writes by this assignment:
  `notes/theory/lean/YulangClosure/NativeRestorationFrameR4.lean` and this file.
  No scratch/generated/cache/root-import/configuration/compiler writes.
- Grant: 1,200 seconds maximum; first clock receipt 2026-10-28 08:39:30 UTC.
  This revision freezes within that grant. No extension requested.

## Original parent and governing sections

Actual original definition read: `YulangClosure.SourceProblem.InferenceSoundness`
in pinned `Contracts.lean:128`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

Original manuscript read: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1, 3–5. The source scope, lawful finite histories, retained actual polar pairs,
all correlated evidence and one jointly chosen witness remain fixed. Current
qualification comes from the authoritative birth-level design §§2–6 and its
theory §§1–7; the manuscript's cross-level examples are not current authority.
`docs/yulang-whole-proof-closure-ja.md` §1 identifies the original full-language
scope. Top-level inference principles, approved effect policy §1 and current
soundness-progress original-goal/open-bridge sections were read. Research
drafts are not adopted semantics.

The primary supplied the two ambiguous contract locators without changing their
already pinned content:

- Effect policy: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`,
  `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`.
- Soundness progress: `notes/progress/2026-10-26-inference-soundness.md`,
  `fd5ff5eb032e3fe276deab0213ede2e073fe0f6bf43c32daca19b6e258ba84b1`.

## Frozen artifact and dependencies

Artifact: `notes/theory/lean/YulangClosure/NativeRestorationFrameR4.lean`.
SHA-256: `b2c185413cf537b22a91c04c97bdd5c30ce0f44afe83c91cbbc2eff1e32708f0`.
Imports are only the leased input modules `Contracts` and `NativeScopeTransformer`;
no public-root import edit was made.

Actual `sha256sum` exits were 0. All ten enumerated Rust source hashes matched
the contract; no R4 Rust output body was read:

| Root source | SHA-256 |
| --- | --- |
| candidate_scheme.rs | `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707` |
| candidate_effect.rs | `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab` |
| candidate_context.rs | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| candidate_extrusion.rs | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| candidate_intrusion.rs | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| candidate_scope.rs | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` |
| candidate_source.rs | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| shadow_apply.rs | `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff` |
| term.rs | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| lib.rs | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |

The four pinned Lean-module hashes also matched:
`Contracts` `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`;
`NativeFreshScopeTransport` `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5`;
`NativeScopeTransformer` `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`;
`OriginalEffectHygiene` `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`.
The last two non-imported module pins were inventoried, not treated as proved
concrete native/source instances.

Toolchain/configuration read and hash matches: `lean-toolchain`
`ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`;
`lakefile.toml` `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`;
`lake-manifest.json` `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`;
`README.md` `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3`.

## Represented local write inventory

The following is the **represented local footprint inventory**, not a claim
that every successful call/branch in the source cone has been translated.
`Write` overapproximates these footprints; several native branch guards and
auxiliary owner records are still absent from the state projection.

| Source owner / branch | Native condition and write | Candidate representation |
| --- | --- | --- |
| candidate_context.rs:775 `admit` | Successful reserve; duplicate and new origin paths both append one admission, update group head/coverage and reverse evidence | `Write.admission` retains full admission content; auxiliary group/reverse updates omitted |
| candidate_effect.rs:711 `candidate_bound_origin_with_evidence` | Scoped FreshUse requires mapped relation and validates its source association; scoped BoundTransport has no admitted relation; owner/extrusion/unscoped derive relation; both duplicate paths admit | Cause and mapped/admitted relation remain distinct fields; source branch-to-sequence translation OPEN |
| candidate_context.rs:829 `emit` | Appends at old emission length after physical readback; updates group head | `Write.emission`, `emit`, `emit_lookup`; group-head update outside projection |
| candidate_extrusion.rs:702 `insert_bound!` | Canonical owner/item; typed owner/lane selection; eight value/effect × lower/upper × row/atom append branches; journal/reserve must succeed | `insertionLane`, `Write.physical`, `appendPhysical`; flags/counters/journal not represented |
| candidate_extrusion.rs:648 `candidate_physical_slot_bound` | Eight valid RowKey × lane cases, all crossed cases return None | `laneFits`, `physicalAt`, `physicalKey`; fixed raw owner/item reread, no forest recanonicalization |
| candidate_context.rs:3062 `relation_with_scoped` | Default flow uses logical id 0; existing flow/key reused; fresh nondefault flow/record appended | `Write.flow`, `Write.relation`, `reuseFlow`, `reuseRelation`; key/hash/source/context validity guards OPEN |
| candidate_context.rs:2795 `intern_scope` | Identity returns 0; hash-chain hit reuses; otherwise append nonidentity at old length + 1 | `rawTransformer`, `Write.transformer`, `reuseTransformer`; hash/inventory/resource guards OPEN |
| candidate_intrusion.rs:505 `compress_candidate_forests` | Rewrites parent pointer to current representative, saves journal when transactional | `Write.compress`; root/path correctness and journal authentication OPEN |
| candidate_intrusion.rs:599 `merge_candidate_rows` | Equal representative returns; otherwise copies both selected sides before parent redirect; source storage remains intact | Physical appends plus `Write.merge`; complete child ordering, transfer/canonicalize/reopen/replay translation OPEN |
| lib.rs:10456/10487 fresh rows | Appends empty physical owner and metadata | `Write.freshEmptyRow` only the empty-vector projection; real owner count/forest allocation OPEN |
| candidate_extrusion.rs:1004 restoration | At n=count returns the saved emission; else starts replay or advances after successful replay | `ModelDriverReturns` control with fixed saved emission/count; native restoration-map/control authentication OPEN |

`ValueEndpoint` includes all pinned endpoint constructors, including records,
variants and tuples; `EffectEndpoint` includes contributions, allowances,
supports and annotation members. Term/view/source handles are opaque Nat
identities; finite-word conversions and their native interpretation are not
proved. `Flow Demand` retains the entire demand through an arbitrary type
parameter, with no deletion of demand content. The empty default flow and raw
identity transformer use logical id zero; physical rows use successor ids.

## Candidate declarations and exact evidence status

All names below have prefix `YulangClosure.NativeRestorationFrameR4.`.
Every declaration has an in-module fully qualified `#check @...` and
`#print axioms ...` command. **All printed types/axiom results are NOT_RUN.**
There is no actual Lean diagnostic, accepted theorem, axiom-free claim or
checker receipt in this revision.

| Declaration | Stated local conclusion / premises |
| --- | --- |
| `at_append_of_some` | Existing list lookup survives arbitrary suffix; premise is old lookup |
| `at_append_end` | Singleton append lookup at old length |
| `appendPhysical_old` | Existing addressed slot survives one physical append |
| `appendPhysical_new` | New addressed slot at old lane length contains appended item |
| `Frame.refl`, `Frame.trans` | Reflexive/transitive identity-indexed frame |
| `Frame.physical_key` | Derived raw physical key frame |
| `Frame.raw_transformer`, `Frame.scoped_flow` | Existing lookup frames, including logical zero |
| `Write.frame` | Cases over explicit candidate write constructors derive all six projection frames |
| `Sequence.frame` | Induction over the explicit candidate sequence |
| `Readback.frame` | Preserves the exact same `ReadbackWitness`, not a sibling witness |
| `emit_lookup` | Emitted id computed as old emission length; no lookup premise |
| `emit_readback` | Builds creation-side join from pre-emitter admission/relation/flow/transformer/physical inputs |
| `bootstrap_admission`, `bootstrap_physical` | Computes new admission and physical slot lookup from appends |
| `bootstrap_emit_readback` | Joins those two computed lookups to existing relation/flow/transformer inputs |
| `ModelDriverReturns.frame_and_return` | Induction yields frame and out=saved; no preservation/lookup field |
| `model_completed_emission_lookup` | Computed emitted id plus explicit modeled run yields completed emission row lookup |
| `model_completed_readback` | Creation readback plus modeled run preserves exact chain |
| `emitted_model_completed_readback` | Emitter local inputs plus modeled run yield out=old length and final exact readback |

The full type bodies in the artifact are the candidate statements, not actual
printed checker output. `Readback` is a proposition indexed by one immutable
`ReadbackWitness`; its identity and physical fields cannot be reselected.
`ModelDriverReturns.operation` is a fixed index but is not authenticated against
the native restoration map. This is a material remaining premise.

## First missing branch, parent application and owner

**NATIVE-R4-IDLE-CHILD-1 (OPEN):**
`candidate_context.rs:4097 candidate_context_step_replay_child`,
`ReplayChildWait::Idle` with `Some(item)`, calls `lib.rs:14186 start_typed_drain`.
There is no proof translating that successful call's seed/enqueue/attribution
updates, then its Transport/Context/Dispatch and structural child stages, into
the explicit `Write` sequence while authenticating this saved restoration's
operation/emission/count. The corresponding first nonterminal dispatcher is
`lib.rs:14289 step_typed_drain`. This is source coverage still to construct,
not a missing preservation assumption to add to `DriverReturns`.

Owner: Luna's native/source constructive continuation under a future exact
lease; this leaf cannot assign it. Required input: full successful child writer
inventory and exact call-to-projection equations. Required output: a concrete
simulation from the original successful driver through each child to
`ModelDriverReturns` (or replace this model by a fully authentic construction).
Falsifier: any successful child rewrites a referenced admission/emission/
relation/flow/transformer row or addressed raw physical slot, or returns an
emission associated with a different invocation. A native owner absent from
the pin set requires a Luna-authored amendment before its body is read.

Conditional parent application: if these local declarations are accepted and
the missing authentic native sequence/creation bridge is supplied, the exact
returned emission chain can be framed across that represented sequence.
At present no native-success premise of `SourceProblem.InferenceSoundness` is
discharged. Source generation → lawful source judgment/shared `sameScoped`
witness remains OPEN, as do prepared-root temporal preservation, all FreshUse,
A/B, effect hygiene, principality, termination, executor and production gates.

Transactional errors are separate: `TransactionFailure.rollback` returns a
checkpoint and can remove newly appended rows. No success frame or emission
lookup is asserted for it; this is not a proved rollback theorem either.

## Actual commands, resources and stop receipt

- Executed only read/hash commands (`pwd`, `cat`, focused `sed`/`rg`,
  `sha256sum`), exact-path `apply_patch` writes and UTC clock reads. Recorded
  successful reads/hash commands exited 0; no mathematical failure evidence
  was generated. Some combined terminal output was truncated; later focused
  reads supplied the relevant exact sections/definitions.
- Lean/Lake/helper/Cargo/tests/builds: **NOT_RUN**, as required by the packet's
  fresh source-first review gate. No version executable was invoked; actual
  runtime version and every axiom list remain UNKNOWN/NOT_RUN. Read pin is
  `leanprover/lean4:v4.35.0`; package has no external dependencies and project
  args are `-j1 -M1024`.
- After source-first acceptance only, primary owns the permitted pinned
  invocation/checker/cache and complete printed types/axiom inspection. If
  rejected, the contract closes R4 incomplete and prohibits those checks.
- No heavy processes, installation, network, Git, global defaults, dependency
  changes, nested CLI or other worker-file writes. CPU/RSS not measured;
  wall-clock grant is the controlling resource receipt.
- **Writes stopped after this frozen revision. No descendants or generated
  output leases.** Review/integration/checking and all status changes return
  to Luna. This candidate is not commit-ready proof closure.
