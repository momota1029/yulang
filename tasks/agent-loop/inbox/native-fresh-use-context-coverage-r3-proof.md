# NATIVE-FRESH-USE-CONTEXT-COVERAGE/r3 — proof handoff

Assignment `/root/native_fresh_use_context_coverage_proof_r3`, revision 1.
Base contract SHA-256 `d6fc97fde87e8c8a0c0eb0cb8afb140029a0428aedcde6f82b1f162c4bc21725`.
Amendment 01 SHA-256 `dc7389b53d773c4c742af556f4b6d5123821df84bdddb7df97afd7a0ac549fc4`.
Requested `lean_prover`, Sol/high; observed model/effort UNKNOWN. The actual
worker identity is the assignment ID above. Both contract and amendment were
acknowledged before their source-body reads. No descendants or coauthors.

Outcome: **constructed, UNCHECKED conditional event-projection lemmas** and a
**local configuration obstruction**. No checked theorem, broad native Context
coverage proof, successful FreshUse counterexample, or parent closure is claimed.

## Original claim and source correspondence

The original parent is `YulangClosure.SourceProblem.InferenceSoundness`,
`Contracts.lean:128–130`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

This is a proposition definition. Its scope and shared source witness are
unchanged. Original source-preservation manuscript
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5 retains
every supported original program, lawful finite construction history and actual
retained extrusion occurrence, with typing, principal coverage, progress and
termination. The birth-level correction in
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6 remains binding.
`docs/yulang-whole-proof-closure-ja.md` §§3–4 separates conditional kernel
composition from the still open concrete source interfaces. Research drafts
do not grant semantic authority. This packet applies no manuscript safety
theorem and makes no claim about the whole original Simple-sub theorem.

Relevant native Context literature inspected:
`2026-10-26-native-context-readback.md` §§1–3 (publication is not completed
Dispatch, fixed-table interpretation is a separate boundary), and
`2026-10-26-native-context-tables.md` §§1–4 (identity zero, six constructors,
interner and old-frontier rename check). Those modules were not imported as
new proof dependencies or treated as native execution certification.

Source-to-event map, using the fixed baseline:

| Native source | Constructed projection / unresolved boundary |
| --- | --- |
| `candidate_scheme.rs:4417–4449` | Preparation obtains actual relation roots before the map starts empty. |
| `candidate_context.rs:1566–1683` | `Step.expand` erases the ready bit but retains the parent; `Step.finish` requires each immediate child lookup and records a map key. `Run` composes successful loop boundaries. Native failure/payload/frontier guards can remove projected runs. Rust-to-`Run` erasure remains unproved. |
| `candidate_context.rs:1590–1609` | All children have lower IDs, identity has no stored expression. `Expr.children` includes all six constructors and identity; `FiniteDag` states the checked shape. No termination theorem is delivered. |
| `candidate_context.rs:1167–1245` | Borrowed input selects relation stored keys, touching dependency endpoints, Context children and weights. `observationRoots` computes a subset of context seeds from initially selected parents and directly touching transport targets. It does not assume that the full selected set equals the exact rename domain. |
| `candidate_context.rs:4278–4289` | Fresh transport constructs a relation with its supplied mapped Context and retains the parent/child dependency. This supports only the context actually attached at admission. |
| `candidate_scheme.rs:4263–4273,4695–4708` | Each bound drives a restoration before the next bound; admission rereads `relation_context`. Preparation and admission equality is not established. |
| `candidate_context.rs:1691–1694,3297–3302,3876–3883` | `postCheck` exactly projects stored versus discharged/residual lookup, and the discharge publication can change the result. |
| Amendment `candidate_extrusion.rs:966–1076` | Restoration inserts, saves the opposite count, drives each live opposite replay, and rereads canonical representatives. No local guard in this driver excludes a later captured original parent from being newly discharged by a replay descendant. Whether that can actually happen requires a trace argument, not this observation. |

## Constructed declarations and exact intended types

Module / namespace prefix for every declaration below:
`YulangClosure.NativeFreshUseContextCoverageR3`.
These are source types, **not printed kernel output**. The module imports only
the already pinned `YulangClosure.NativeFreshScopeTransport`.

```lean
step_keeps_marked {children : Children} {before after : Scan}
  (step : Step children before after) {id : Nat}
  (marked : Marked before id) : Marked after id

step_keeps_closed {children : Children} {before after : Scan}
  (step : Step children before after) (closed : Closed children before.keys) :
  Closed children after.keys

step_keeps_sound {children : Children} {roots : List Nat} {before after : Scan}
  (step : Step children before after)
  (sound : ∀ id, Marked before id → Reach children roots id) :
  ∀ id, Marked after id → Reach children roots id

run_keeps_marked {children : Children} {before after : Scan}
  (run : Run children before after) {id : Nat} :
  Marked before id → Marked after id

run_keeps_closed {children : Children} {before after : Scan}
  (run : Run children before after) :
  Closed children before.keys → Closed children after.keys

run_keeps_sound {children : Children} {roots : List Nat} {before after : Scan}
  (run : Run children before after) :
  (∀ id, Marked before id → Reach children roots id) →
  ∀ id, Marked after id → Reach children roots id

completed_exact_domain (children : Children) (roots keys : List Nat)
  (run : Run children ⟨roots, []⟩ ⟨[], keys⟩) :
  ∀ id, id ∈ keys ↔ Reach children roots id

completed_identity_key (children : Children) (roots keys : List Nat)
  (run : Run children ⟨roots, []⟩ ⟨[], keys⟩) (identityRoot : 0 ∈ roots) : 0 ∈ keys

completed_empty_domain (children : Children) (keys : List Nat)
  (run : Run children ⟨[], []⟩ ⟨[], keys⟩) : ∀ id, id ∉ keys

attached_target_observed (children : Children) (stored : Nat → Nat)
  (parents : List Nat) (transports : List (Nat × Nat)) {parent child : Nat}
  (selected : parent ∈ parents) (transport : (parent, child) ∈ transports) :
  LogicalObservation children (observationRoots stored parents transports)
    (stored child)

undischarge_reads_stored (stored : Nat) (residual : Option Nat) :
  postCheck stored false residual = stored

discharge_reads_residual (stored residual : Nat) :
  postCheck stored true (some residual) = residual

discharge_can_change_root :
  postCheck 2 false none = 2 ∧ postCheck 2 true (some 1) = 1 ∧
  postCheck 2 false none ≠ postCheck 2 true (some 1)

LocalWitness.completed_source_scan :
  Run LocalWitness.children ⟨[1], []⟩ ⟨[], [1, 0]⟩

LocalWitness.reachable_avoids_two {id : Nat}
  (reachable : Reach LocalWitness.children [1, 0] id) : id ≠ 2

LocalWitness.prepared_image_can_escape_changed_root_closure :
  LocalWitness.map 1 = 2 ∧ postCheck 1 false none = 1 ∧
  postCheck 1 true none = 0 ∧
  ¬ LogicalObservation LocalWitness.children [1, 0] (LocalWitness.map 1)
```

The completed-domain theorem derives soundness and coverage by induction over
the three successful transition constructors; no transitive coverage or exact
domain hypothesis is supplied. `finish` contains only immediate child lookups,
which the pinned rename executes. Shared DAGs, duplicate roots, identity and
empty roots remain available. The theorem does not prove an accepted Rust
execution erases to this projection or prove that a finite run exists.

The local witness has identity 0, old `PrefixLeft(oldWeight,0)` at ID 1 and
renamed `PrefixLeft(newWeight,0)` at ID 2. Preparation map: `{0↦0,1↦2}`.
If the old parent is discharged to identity between reads, admission attaches
0; borrowed closure from stored parent key 1 and fresh child key 0 observes
neither context 2 nor its weight. This is a constructor-consistent local
configuration, **not** a reachable successful restoration counterexample.
It shows why arbitrary discharge monotonicity is insufficient for map-image
coverage; exact source noninterference or another observability path is needed.

## First remaining premise and parent application

1. Native trace erasure: every successful empty-map rename has a finite `Run`
   with exact source roots and all native key insertions accounted for. Weight
   and certificate checks, allocation/interner reuse and rollback are not yet
   connected to the event projection. Owner: primary/native proof intake.
2. Restoration noninterference or compensating readback: for each later graph
   bound, prove earlier bound restorations cannot newly discharge its captured
   original relation, or construct an authentic observation path for every
   prepared map image when admission uses a residual root. The driver itself
   does not establish this. Owner: primary restoration/native proof intake.
3. Actual `CircuitEvidence` fixed-point/weight completeness, observation lifetime,
   authentic map values, and module/local completion erasure remain open. A
   suspended local use has no completed run/post-bound attachment evidence;
   it cannot instantiate the completed theorem and requires Partial/Unavailable.

No result here proves correct transformed payloads or that a map chooses the
right observable target. No `FreshUse` validation, returned-root image theorem,
source/native correspondence, complete original effect hygiene, principality,
termination, production promotion or `SourceProblem.InferenceSoundness` follows.
`H_u` remains AUTHORITY_BLOCKED. Original language features/quantifiers/shared
witnesses were not changed; their concrete interpretation was not attempted.

## Pins and artifact receipt

Research base `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`, primary baseline
`1d59e3accb3d6c2a6ead91ebc0c6a471c671c981`. Rust locators refer to the
baseline bytes, not the sibling's new coverage implementation. The scheme
source seam was rechecked against the immutable selected-module overlay.

| Input | SHA-256 |
| --- | --- |
| candidate_scheme.rs baseline overlay | `33235b840c42be38be1df634291e309c0d143fa62f412afa633768be9b40aa0e` |
| candidate_context.rs | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| candidate_source.rs | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| candidate_effect.rs | `8d80a98b4fe22bd91409b645dbac3d5bcd10eed4b45bbe6f5c17a773e65874f6` |
| shadow_apply.rs | `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff` |
| term.rs | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| lib.rs | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| candidate_extrusion.rs Amendment 01 | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| workspace Cargo.toml | `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a` |
| workspace Cargo.lock | `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5` |
| yu-solver Cargo.toml | `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed` |
| NativeFreshScopeTransport.lean | `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5` |
| NativeScopeTransformer.lean | `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6` |
| Contracts.lean | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| OriginalEffectHygiene.lean | `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f` |
| lean-toolchain | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| lakefile.toml | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| lake-manifest.json | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| Lean README.md | `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3` |
| original source-preservation manuscript | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| birth-level correction | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| whole-proof closure manuscript | `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5` |
| native Context readback note | `d3322e58a178d9939609518d986c467a5fdcadd6bad6a24399f42220865b636f` |
| native Context tables note | `2333038f316391be3cdceb3d732d12ffe23cb10e7055462fb1b2e2b786383d86` |
| top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

Changed artifact `notes/theory/lean/YulangClosure/NativeFreshUseContextCoverageR3.lean`,
SHA-256 `735c0711151c4605d40b338792327f30af80e9740cce346b65517df722543d46`.
The handoff's own hash is supplied in the final message after freezing.

## Commands, checking and stop receipt

Read-only commands: `cat`, focused `sed -n`, `rg`, `rg --files`, and `sha256sum`;
all completed with exit 0 except one intentionally searched nonexistent
historical note path (rg exit 2, no source reliance). Inspected exact list lemma
signatures in installed
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/Init/Data/List/{Basic,Lemmas}.lean`.
The changed-file source search for `sorry|admit|axiom|skipKernel|native_decide`
matched only the explanatory word “axiom” in a comment. This is not an axiom
audit. No proof hole, project axiom or bypass was introduced.

**Lean/Lake invocations: 0. Actual tool versions: NOT RUN. Printed theorem
types: NOT RUN. Complete transitive axiom audits: NOT RUN for every delivered
declaration.** The fixed packet reserves execution to the primary after fresh
review acceptance. No checker/model/runtime success is invented. The primary
can audit the exact module and every theorem above with the skill checker,
using its exclusively leased scratch/cache and the remaining contract caps.
Any elaboration failure must be retained and repaired under a new write grant.

Only the two exact leased files were written. No scratch files, generated
outputs, caches, compiler files, task state, root imports, Git or descendants.
Approximate producer wall budget used: under 900s of the original 1,000s;
at least 100s relinquished unspent, no carryover. Heavy-process budget used: 0.
Worker STOPPED, writes stopped on both leased paths at this frozen revision.
Fresh independent review and primary checking/integration remain pending.
