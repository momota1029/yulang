# R64 outcome — owner carrier and source-fact reader obstruction

Status: **CLOSED_INCOMPLETE**. The fixed extraction gate was not achieved.

## Accepted partial evidence

R64 produced a pinned Lean 4.35.0 stdin audit for a mathematical structural
carrier. The retained `R64-CONSTRUCT-7` audit exited 0 and includes all 18
theorem types with complete transitive axiom reports; the only axioms are
`propext` and `Quot.sound`. The frozen Lean module is
`notes/theory/lean/YulangClosure/BrandedInventoryOwnerR64.lean`, SHA-256
`790b1ac0a99f8a1582c442edfb352614e72cac28f13a9158c4e81a396474e86b`.
Its proof receipt is
`tasks/agent-loop/inbox/effect-permission-owner-carrier-r64-proof.md`, SHA-256
`863901cf7b14f0eef4331996a9f76e4fb61b4eb9405a40c5163461a0edd0cff0`.

Fresh independent review was **BLOCKED** for the fixed outcome. The complete
report is
`tasks/agent-loop/inbox/effect-permission-owner-carrier-r64-review.md`,
SHA-256 `bb5065a5f90e0e5106749b2ae8df90f42ee4fac4f4154f0438ba928f6d2b9bbd`.
It authenticated the retained stdin and all 18 theorem/axiom outputs. It found
two source type errors, absent actual Rust-to-Lean construction/authentication,
and a major mismatch between source-occurrence lookup and identity-only formal
readers.

After that reviewer STOPPED, Luna made two minimal source-only corrections in
the same `candidate_receiver.rs` file: use the iterator-taking fallible
provenance collector, and remove a `u32` entry-effect ordinal from the `Term`
seed array. The exact current candidate hash is
`ff03bb9cfa1222a61f7c9594f437049e470b7a2fb6d69af00ef74c8625b4a63e`.
The corresponding R64 Rust handoff, including the repair record, is
`tasks/agent-loop/inbox/effect-permission-owner-carrier-r64-rust.md`, SHA-256
`4b71bc5663ed81aa57687c08f17cbc6a23c113132360480440656360b0847567`.
These two edits have not been independently re-reviewed or compiled and are
not accepted as an integrated Rust change. The R64 contract prohibited builds,
tests, Cargo and formatter runs; none were run.

## Exact blockers

The Lean `Carrier` and its `Owner`/`Call` are assembled from mathematical
tables supplied to Lean. Field equations prove equality to those supplied
tables, not that the tables came from the actual Rust `InventoryPackage`.
No finite-table owner-token encoding, round trips, scoped injectivity,
namespace separation, actual Rust `Term`/child-coordinate mapping, or
source-call/schema authentication is established. R64 does not instantiate
R63 for the actual Rust owner.

Multiplicity remains intact in the Rust and Lean candidate inventories. That
exposes the reader seam: Rust selects a provenance edge at an exact
`(HirOccurrenceId, slot)`, while R55 `routeFact` and R57 `factRead` select
globally by semantic FactId and reject two rows with that identity. R57's
occurrence-qualified `sourceFact` can select one distinct source coordinate,
but that alone does not establish `factRead`, `rootTask`, arrival, or outer
successful `Run`. The Lean witness is a mathematical discriminator only.
Actual multiplicity for the selected native Internal fact is UNKNOWN; no
native runtime or original-parent counterexample is claimed. No occurrence is
discarded and no global uniqueness assumption is introduced.

The R64 fixed gate, actual outer successful `Run`, resource/failure
correspondence, original A/B, effect hygiene, whole-program soundness,
principality, termination, full hygiene, and production remain OPEN. The
conditional R63 consumer theorem does not close any of those parents.

## State and Git

The live roster confirmed `/root/r64_rust`, `/root/r64_proof`, and
`/root/r64_review` STOPPED. Their final acknowledgements and exact artifact
hashes are recorded above and in the frozen handoffs/review. Their resolved
worker rows and R64 leases were archived by this closeout and removed from the
compact snapshot; all 32 pending items and every UNKNOWN/quarantined
reservation remain. The static sprint checker passed; it is not independent
review or compiler evidence.

R64 created no additional worktree, environment, cache, target, scratch, or
build directory. Only the Lean artifact, handoffs, review, this outcome, and
their exact state/progress records are eligible for the incomplete closeout
checkpoint. The Rust source candidate remains outside the checkpoint pending a
new admitted review/source packet.

## Successor

The next bounded packet targets the formal source-fact reader seam. It must
select all provenance candidates at the exact source occurrence/slot, reject
ambiguity at that same key, then resolve the single semantic FactId in a
separate semantic-fact table. Distinct source occurrences may share one
semantic FactId. R55 and R57 remain frozen until a separately reviewed model
successor establishes faithful source lookup behavior. No language semantic
change, production permission, or parent closure follows from this disposition.
