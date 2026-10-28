# Sprint NATIVE-RESTORATION-FRAME/r4 — child-frame preservation to completed readback

Status: CANDIDATE until Luna admits this contract and exact leases in
`tasks/agent-loop/current.json`.
Branch `yulang3`; baseline and origin `2c63118937324500a41582f1c452117b819396f7`.
The Rust workspace starts from that commit plus the three exact frozen source
overlays below. R3 artifacts are refusal history only and are not inputs.

## Original parent and fixed boundary

Keep the original `YulangClosure.SourceProblem.InferenceSoundness` claim and
quantifiers unchanged:

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

Keep the supported-source domain, lawful finite histories, retained extrusion
occurrences, shared witness, source/native correspondence, Simple-sub A/B,
effect hygiene, principality, termination and executor obligations fixed and
OPEN. The approved effect policy remains unchanged. This packet grants no
semantic, API, production, expected-output, golden or diagnostic change.

R3 is `CLOSED_INCOMPLETE`, not refuted semantically. Its source-read deviation
is permanently non-waivable for R3. Its implementation is not a source input.
R3 outcome SHA-256:
`32ad18a9a0358cca686192bc226dc9c03c5c4bb060dae471d5e785681f7ca040`.

## Bounded outcome, construction and falsifiers

Derive completed bound readback from successful native child transitions. The
native chain is:

```text
invocation and source witness
  → driver's returned BoundEmissionId
  → its BoundEmission / BoundAdmission
  → admitted RelationId and current ScopedFlow
  → flow transformer ID → raw ScopeTransformer
  → addressed PhysicalBoundSlot → completed vector reread
```

The proof must model the actual successful write branches and their conditions,
then establish a frame invariant for each previously referenced identity and
physical slot. Relevant source writes include forest compression/merge,
copied-bound append and emission, relation/flow/transformer insertion or
reuse, replay and typed-drain completion. Prove only the required locations and
references are preserved; do not assume all solver state is globally
unchanged. Handle transactional failure separately: a successful driver's
returned emission is the success boundary, and no `DriverReturns` field may
assume the desired post-state preservation or completed lookup.

Construct an explicit transition sequence from every relevant successful native
branch in the pinned source cone. For each constructor, name its source owner,
write location, condition, state footprint and represented native action. A
reviewer must be able to compare the complete branch inventory to the source.
If a required child owner is absent from the pin set, stop at its first call
boundary and request a Luna-authored amendment before reading that body.

The Rust observer is a separate finite native witness. It must bind each
invocation to its own expected source witness and actual driver-returned
emission; inspect the post-driver admission, relation, scoped flow, raw
transformer and reread addressed physical slot. Include genuine scoped,
unscoped and duplicate invocation cases. Mutate antecedent, returned emission
ID, invocation reassociation, mapped/admitted relation association, duplicate
ownership, flow root, transformer identity and addressed slot; rerun the full
completed predicate and require rejection for every non-vacuous named mutation.
No `.any`/set/count match may let a sibling invocation satisfy another's
expected record. Root 0 is logical identity, never a physical row.

The Rust instrumentation remains `cfg(test)`. Use an exhaustive, type-correct
owner/lane match and short-lived borrows; the source review must verify all
`RowKey × BoundLane` combinations and the mutation loop's borrow boundaries.
No production/API/semantic/expected-output change is authorized.

Success is a checked and independently reviewed bounded native/Lean bridge.
It does not close prepared-root temporal preservation, all FreshUse routes, the
original parent, or production. A changed addressed slot, lost/changed
invocation association, incorrect raw lookup, omitted successful write branch,
or unexamined child writer is a falsifier or exact blocker, not a reason to
weaken the frame invariant.

## Authority, baseline and exact input pins

Governing sources:

- `rules/goal-driven-sprints.md`: `e57c5c23e1956e09ea0da130a137ac50ce723ce5f0a90323adb17da88dab68b7`
- `notes/design/2026-10-16-goal-driven-sprints.md`: `2dfeb555c913d3142078de535ee4b7f68e9a27f2b91a5f0bb82d4d867db4fc4e`
- top-level inference principles: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- approved effect policy: `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`
- intrusion source-preservation proof: `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`
- whole-proof closure: `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`
- birth-level SCC design/theory: `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` / `67c2a44b7a4009a96424dc329ed4385fffdbc6d6661bf4155408cfbd62de3bfa`
- inference soundness progress: `fd5ff5eb032e3fe276deab0213ede2e073fe0f6bf43c32daca19b6e258ba84b1`

Frozen Rust source inputs (SHA-256):

- `candidate_scheme.rs`: `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707` (frozen overlay)
- `candidate_effect.rs`: `1715046b29b760fe70b3c2fb05665dad23e7f95ad05883c39d06d4da37b925ab` (frozen overlay)
- `candidate_context.rs`: `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`
- `candidate_extrusion.rs`: `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`
- `candidate_intrusion.rs`: `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`
- `candidate_scope.rs`: `9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a`
- `candidate_source.rs`: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
- `shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff` (frozen overlay)
- `term.rs`: `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`
- `lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`
- workspace `Cargo.toml` / `Cargo.lock`: `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a` / `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`
- solver `Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`

Lean 4.35.0 and theory inputs:

- `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `NativeFreshScopeTransport.lean`: `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5`
- `NativeScopeTransformer.lean`: `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`
- `OriginalEffectHygiene.lean` (seam only): `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`
- `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `README.md`:
  `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`,
  `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`,
  `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`,
  `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3`.

Any added dependency needs a Luna-authored versioned amendment before its body
is read. The complete source-body read set is the exact pinned Rust files and
Lean project/theory files listed above, plus the exact governing documents
listed above. Bodies of other files are outside the lease; code output that
incidentally displays sibling bodies from one of these pinned files remains
inside this packet's source set. Use focused reads for relevant branches. ACK the
exact contract SHA and all assignment leases before source or artifact body
reads. No procedural deviation is waivable in this packet.

## Parallel assignments and exact leases

**Constructive proof — registered `lean_prover`, Sol/high, 1,200 seconds.**
Write only:

- `notes/theory/lean/YulangClosure/NativeRestorationFrameR4.lean`
- `tasks/agent-loop/inbox/native-restoration-frame-r4-proof.md`

Define state projections for admission/emission rows, relation/flow/transformer
records and physical bound vectors. Encode every relevant successful native
write branch from the pinned source cone as a transition constructor. Prove a
frame lemma for existing identity-indexed records and the addressed physical
slot, by cases over those constructors, then induct over the actual completion
sequence and derive completed lookup from the returned emission. Keep the Lean
claim conditional only on explicitly represented native source inputs; do not
assume transition preservation, returned-ID correspondence or desired lookup.
If a full transition inventory does not fit the grant, freeze the checked local
lemmas and exact first unrepresented source branch. No `sorry`, `admit`, project
axiom or unchecked theorem claim.

**Implementation — registered `implementer`, Luna/high, 1,000 seconds.**
Write only:

- `isolated/native-restoration-frame-r4/crates/yu-solver/src/candidate_scheme.rs`
- `isolated/native-restoration-frame-r4/crates/yu-solver/src/candidate_extrusion.rs`
- `tasks/agent-loop/inbox/native-restoration-frame-r4-rust.md`

Start from the pinned baseline and frozen overlays; do not copy or edit R3
artifacts. Build the smallest test-only observer joining invocation/source
witness to its actual returned emission and completed native readback. Preserve
the actual mapped/admitted distinction and test authentic scoped, unscoped and
duplicate routes. Run every named mutation against the whole completed
predicate. Make owner/lane matching exhaustive and keep immutable borrows short
before state mutations. This source work stays provisional until reviewed and
checked.

**Independent review — fresh `compiler_referee`, Sol/medium, 700 seconds.**
Write only `tasks/agent-loop/inbox/native-restoration-frame-r4-review.md`.
ACK before reads. Source-first compare every successful write branch to the
Lean transition inventory and Rust readback/mutation paths to the fixed
contract. Return ACCEPT_FOR_BOUNDED_CHECKS or REJECT. On rejection, no compiler,
Cargo, Lean/Lake or tests run. If accepted, Luna may run up to two focused Cargo
attempts (aggregate 120 seconds, 2 GiB RSS, 1 CPU) and one pinned Lean 4.35.0
check (`-j1 -M1024`, aggregate 180 seconds), one heavy process at a time. The
same reviewer then appends a sequential final-review revision authenticating
logs, complete theorem types/axioms and source correspondence. Any rejection or
failed check closes R4 incomplete.

Total envelope 3,600 seconds: proof 1,200 + implementation 1,000 + review 700 +
primary 700. Astra 0. No renewal or scope expansion. Peak new assignments: two
producers and one reviewer; preserve all UNKNOWN workers, reservations and
quarantined paths.

## Stop, review and integration boundaries

Proof and implementation ACK their requested and observed settings separately;
unobservable serving model/effort stays UNKNOWN. No descendants, Git operations
or checks by workers. The primary owns exact-path setup, state synchronization,
review admission, all checks and Git.

At completion record exact artifact hashes, resource/runtime receipts, review,
check status, parent application and remaining source branches. Run only the
specified static sprint checker before admission and at closeout; that checker
is not evidence of compiler correctness. Only Luna stages intended paths,
inspects the entire outbound range and upstream, and pushes a coherent
checkpoint. Never stage unrelated dirty/untracked files, touch quarantined
paths, force-push, alter frozen `main`, or claim production promotion.
