# NATIVE-COMPLETED-EMISSION-READBACK/r3 — proof handoff r1

Frozen outcome: INCOMPLETE / REQUIRED_UNPINNED_CHILD. Constructive source
inspection only; no Lean declaration constructed, checked or certified.

## Assignment and authority

- Contract: `tasks/agent-loop/sprints/native-completed-emission-readback-20261028-r3.md`,
  SHA-256 `d1c194c85c54d7ea2016c64e60d51d7805e480ae7c824b167f0bc86fee94d71e`.
- Worker: `/root/native_completed_emission_readback_r3_proof`; session
  `NATIVE-COMPLETED-EMISSION-READBACK-20261028/r3`. Initial active-work ACK sent
  through `collaboration.send_message` before all source/artifact body reads.
  Admission subsequently confirmed requested `gpt-6-sol` / `high`; effective
  model and effort are UNKNOWN. The initial ACK's inherited-request description
  was corrected by a separate ACK supplement before native/Lean body reads.
- Grant: 1,000 active seconds, no renewal; primary owns verification/cache,
  fresh source review, any checks, integration and Git.
- Exact leases: `notes/theory/lean/YulangClosure/NativeCompletedEmissionReadbackR3.lean`
  and this handoff. Only this handoff was created. The Lean path was not created
  or modified; no scratch or generated outputs, descendants or other authors.
- Primary baseline: `84e95affbfc96df92a8053092f3044189cbde33c`;
  research base: `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d` (contract locators,
  no Git command run).

## Original claim and correction

Original manuscript/specification locators read:
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5;
`docs/yulang-whole-proof-closure-ja.md` §§1–4;
`notes/design/2026-10-24-birth-level-scc-intrusion.md` §§1–6;
`notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–5;
`notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1, 1.2.
The birth-level correction uses induced graphs with all path vertices at one
immutable Value birth level. Local equality lifting does not provide the joint
source strategy. Permission, actual inflow and subtraction residual are distinct.
No research draft is treated as semantic approval.

The actual definition read at `Contracts.lean:128` is
`YulangClosure.SourceProblem.InferenceSoundness`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

All original quantifiers, supported source constructors, lawful histories,
retained occurrences and the same shared witness remain unchanged. This
handoff proves no instance of that proposition. Original A/B, complete Call,
effect hygiene, generalization/use, principality, termination, executor and
source/native boundaries remain OPEN.

## Native dependency frontier and material evidence

All hashes below were compared by actual `sha256sum` with the contract before
native/Lean source body inspection; all matched (command exit 0):

| Pinned input | SHA-256 |
| --- | --- |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `NativeFreshScopeTransport.lean` | `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5` |
| `NativeScopeTransformer.lean` | `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6` |
| `OriginalEffectHygiene.lean` | `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f` |
| `candidate_scheme.rs` | `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707` |
| `candidate_effect.rs` | `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab` |
| `candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `candidate_scope.rs` | `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a` |
| `shadow_apply.rs` | `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff` |
| `term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |

Source trace inspected:

1. `candidate_scheme.rs:4669`, `begin_candidate_fresh_bound`, keeps
   `mapped_relation` separate from subsequent admission and passes the actual
   antecedent, use origin and source bound to `candidate_begin_bound_restoration`.
2. `candidate_extrusion.rs:702`, `candidate_insert_bound_with_evidence`, appends
   at the exact physical vector index, reads it with the existing eight-lane
   `candidate_physical_slot_bound` reader (`:648`), compares the complete key,
   and emits evidence (`:863`). This establishes a constructor-time check in
   the inspected Rust; no temporal preservation theorem is inferred.
3. `candidate_extrusion.rs:988`, `candidate_drive_bound_restoration`, returns the
   actual emission from `candidate_step_bound_restoration`. Its child branch
   calls `candidate_context_drive_replay` (`:1034`). The later comment at
   `:1043` expressly allows earlier children to append bounds or redirect the
   owner representative.
4. `candidate_context.rs:4206`, `candidate_context_drive_replay`, calls
   `candidate_context_consume_replay_child`, whose provenance branch loops over
   `candidate_context_step_replay_child` (`:4169`). The Running branch executes
   `step_typed_drain` (`:4129`).
5. Pinned `lib.rs:14289`, `step_typed_drain`, includes the successful Transport
   branch with no current item and an empty typed worklist. At `lib.rs:14311`
   it invokes mutable `self.settle_candidate_intrusion(...)` before child
   completion. The retained-child path cannot be covered while omitting this
   branch.

Required unpinned owner candidate:
`crates/yu-solver/src/candidate_intrusion.rs`, module declared by pinned
`lib.rs:225`; filename existence was discovered with `rg --files`. That file
is absent from the r3 pin set. Its body was neither read nor searched.
The first unresolved mutable entry/write frontier is the call at
`lib.rs:14311`; the callee's exact defining location and first physical write
site are UNKNOWN because identifying them requires reading an unpinned body.
The module ownership is inferred from its name/declaration, not certified by
an unperformed definition search. No pin or source scope was silently expanded.

## Parent application and exact remaining obligation

No new mathematical lemma is available to apply to the parent. Constructor-time
readback and a returned emission ID do not establish completed readback.
First required native premise, owner Luna/native proof lane: authorize and pin
the actual owner of `settle_candidate_intrusion`, locate its write branches,
and derive preservation (or expose mutation) of each retained admission/emission
row, mapped/admitted relation association, current relation and scoped flow,
raw transformer lookup and the addressed physical slot across that branch and
its successful children. Further child-owner boundaries may then arise.
This is an open source/native premise, not a supplied `DriverReturns` law.

Even completed native readback would leave the original source-scoped joint
strategy/construction premise of source-preservation §5 OPEN with its original
owner; no arbitrary native assignment, new source restriction or independent
per-use witness is added.

Represented: inspection of scoped/unscoped admission routing, constructor-time
eight-lane physical lookup and actual restoration/replay control path.
Omitted/unproved: all temporal child footprints, completed raw lookup,
authentic executable scoped/unscoped/duplicate witnesses and mutation rejection.
No finite native evidence or whole-language proof is claimed.

## Commands, resources and stop receipt

- Read-only commands: `cat`, focused `sed -n`, focused `rg -n`, `rg --files`,
  `sha256sum`; all actual calls exited 0. Some broad tool output was truncated;
  focused reads supplied the claim and decisive native branch above.
- `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` and relevant README
  material were read. Project pin is Lean 4.35.0 with no external packages.
  No executable version was observed: Lean/Lake/version/checker/build commands
  were NOT RUN, as the contract requires fresh accepted source review first.
- Delivered theorem names/types: NONE. `#print axioms` results: NOT RUN / no
  declarations delivered. Kernel acceptance, independent review and production
  authority are NOT ESTABLISHED. No fabricated diagnostics or checker receipts.
- No `sorry`, `admit`, project axioms, LocalLaws instance claim, checker bypass,
  dependency installation, configuration edit, test or Git operation.
- First recorded UTC clock: `2026-10-28 08:23:01 UTC`; dependency frontier
  recorded at `08:24:07 UTC`. Active elapsed/CPU/RSS were not instrumented and
  are UNKNOWN; this early source-boundary stop is inside the 1,000-second grant.
  Heavy processes/check budget used: zero. No descendants or cache writes.
- Mutual TODO `R3-PROOF-UNPINNED-INTRUSION-1`: Luna owns any versioned pin
  amendment before that source body is read. Required input is the exact
  successful child writer and hash; proposed evidence is its concrete write
  footprint and preservation proof/counterexample, falsified by any changed
  required completed lookup. This request grants no lease or authority.
- WRITES STOPPED after this frozen r1 handoff. No automatic continuation or
  additional reads/checks. No commit-ready proof milestone; parent OPEN.
