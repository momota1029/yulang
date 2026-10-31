# R73 outcome — owner-exact completed instance

**Disposition: `CLOSED_INCOMPLETE / FIXED_GATE_REJECTED`.** The combined R73 gate is rejected because the frozen Rust source calls a method that does not exist on `ConstraintStore`. This is a source-inspection finding; no compiler was run.

## Blocking finding

`crates/yu-solver/src/candidate_receiver.rs:1058` and `:1573` call `hir_for_occurrence` on `session.store` / `store`. `ConstraintStore` defines `require_owned` but not this accessor. The only solver methods with that name belong to `FrozenInferenceData` and `InferenceSession`. The frozen Rust bytes therefore fail method resolution with the feature enabled.

The next repair should implement the selected-HIR lookup at `ConstraintStore` ownership, using the exact admitted `hirs` inventory and matching `require_owned` indexed lookup plus fallback. Preserve the complete artifact identity and the occurrence's retained artifact coordinate. A mechanical receiver substitution is insufficient without proving the lookup refers to this exact store inventory. Update the Rust handoff and obtain independent delta review. No R73 Rust retry/build is authorized by its exhausted contract.

## Accepted bounded Lean result

The independent review found no additional correctness issue in the finite Lean model. The final frozen artifact checks exact ordered component positions, separates experiment/view/HIR identities, selects readbacks through the owning experiment, matches admitted-artifact ownership, preserves complete provenance and competitors, and applies the existing same-R66-witness theorem without constructing its `Root`.

- Lean artifact SHA-256: `afed53ee5ebb82bbe87c171c6ac2808919976046df4cb2e0fdeb774f618a6e87`.
- Proof handoff SHA-256: `44bb2f9cbaea9a641f01cc9402d9383da2fd703a5d5e39dd653b5f94c9081a53`.
- Final retained stdin exit 0; 29 theorem types and complete transitive axiom reports. Axioms are `propext` and `Quot.sound`; no final `sorryAx`, project axiom, or `Classical.choice`.
- Four probes exhausted, exits `0/1/1/0`; all failure evidence retained. Total measured Lean runtime 60.193632369 seconds; peak RSS 1,036,132 KiB. No further Lean run occurred.
- Independent reviewer decoded the four receipts in memory and verified their hashes and final theorem/type/axiom counts; no rerun occurred.

## Rust lane and review

- Rust source SHA-256: `eb35c73ead829ed439a347d3cb665d52d3aa4b45b242c1155cfd4377a68d6415`.
- Rust handoff SHA-256: `6e2e7e1961ed4f0a22e8615bbdf48e932e05d163b72ce304ef0b3adb5eca40f1`.
- Rust author reported 44/44 input pins matched and `git diff --check` passed. No Rust build or tests ran; compilation/runtime remain unverified.
- Independent review SHA-256: `696f49242fa2163987043073db915ba3bebfa3135f285a66a1c1546907d31a36`.
- Review disposition: BLOCKING for the combined R73 submission; reviewer STOPPED / WRITES STOPPED.

## Procedural deviation and open obligations

The proof author invoked `lake --version`, violating the categorical No Lake contract. The command is recorded; no build/environment/cache action is claimed. This deviation does not erase Lean evidence.

Physical pointer/slice/map and admitted-Arc identity, Rust-to-Lean extraction, Rust runtime/resource correspondence, genuine R66 `Root` construction, original A/B, manuscript §5, whole-language effect hygiene/soundness/principality/termination, and production remain OPEN. The project objective continues; this rejected sprint does not close it.

R72 attempt-1 completion remains UNKNOWN and its time remains unrefunded. Preserve 32 pending items, unrelated UNKNOWN/quarantined leases, and the existing capacity override; no such lease or pending item changed in R73.
