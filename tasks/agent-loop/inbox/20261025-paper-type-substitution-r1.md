# FULL-PAPER-TYPE-SUBSTITUTION-20261025/r1 — primary handoff

Contract: `tasks/agent-loop/sprints/paper-type-substitution-20261025-r1.md`, SHA-256 `b509bb3313a8e225dacfe97c89af0b36e3dc7ed2e9e44d862283863117c0dcaf`.
Parent: original executor safety `thm:safety` and immutable graph extension at `docs/yulang-operational-type-safety-ja.tex:980,1140`; original Simple-sub/evaluator A/B parents remain OPEN and unchanged.
Baseline: `e8f133657b98d47d789a52fa64aee8f102393452`.
Outcome class: conditional foundational proof artifact; primary-authored, no child agent ran and no independent review occurred.
Primary/session: `/root`, exact runtime session UNKNOWN; requested/observed model and effort UNKNOWN. Eight pre-existing historical/foreign worker observations remain UNKNOWN and quarantined; no lease was reclaimed.

Frozen artifacts and direct dependency hashes:

- Lean module `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean`: `a2faf4dc7765724cd033fd1014b0acb0e87c58902ac71ede157d2e268ba7ad83`.
- Paper `docs/yulang-operational-type-safety-ja.tex`: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`.
- Existing syntax `notes/theory/lean/YulangClosure/HigherOrderSyntax.lean`: `ea727d33692bdcbe6b40245b960d01225b556b5334ffab649eea2699930d5972`.
- Existing term substitution `notes/theory/lean/YulangClosure/HigherOrderSubstitution.lean`: `19910452c45b20761ec06dc7e15f94c94b95014ff00f3f5296af005b9adf6f30`.
- Root import/audit `notes/theory/lean/YulangClosure.lean`: `aeb4b99af2a786363446c49a07cf1df4ac631c411c93305b110f6868078b8641`.
- Lean README: `231a6cccb03efee4a2dc2fd3e8fb70e85ec2f9eb960492e04e39ae7163dc4ec1`.

## Result

`notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean` defines a de Bruijn type syntax for base, top/bottom, union/intersection, tuple/record/variant sequence encodings, nominal arguments, `mu`, thunk, callable and `forall`/`poly`. It proves variable-renaming identity/composition, substitution identity/composition, capture-avoiding binder lifting for both `mu` and `poly`, compatibility of substitution with renaming, and the same substitution laws for operation instances carrying type arguments, payload and response together. Sequence nodes are explicit right-associated encodings in the same inductive `Ty`; the module does not provide a formation judgment that equates these helper encodings with the paper's list notation.

These are algebraic premises only. They do not establish the paper's typing rules, substitution preservation of those rules, substitution through declaration/environment/plan records, the embedding into existing `HigherOrder.Ty`, source inference, executor preservation, native behavior, or any Simple-sub A/B quantifier. The parent theorems remain OPEN. The type language and operation data match only the stated constructors; all omitted distinctions remain unclaimed.

## Checks and proof status

- `lake env lean -j1 -M1024 YulangClosure/PaperTypeSubstitution.lean`: exit 0 after rename.
- `lake build`: exit 0, all 13 jobs including the root import and `#print axioms` audit.
- `subst_id`, `subst_comp`, and operation-instance composition use Lean standard axioms `[propext, Quot.sound]`; no project axiom, `sorry`, or `admit` occurs in the artifact.
- Existing `ControlComposition` emitted three unrelated unused-simp warnings; this result did not edit that module.
- No Rust/Cargo/native probes or expectation changes.

## Application and next owner

No original theorem closes yet. The exact next proof obligation is to define formation/instantiation for type-indexed declarations and plans, lift this substitution action to those records and environments, then prove preservation of the paper's actual typing judgments by induction. The primary owns specification correspondence and this application. A fresh nonauthor reviewer must review this frozen algebra before it can be promoted. The exact HigherOrder syntax and the metadata/runtime relation remain separate bridges; the dispatcher's `runtime/program.rs` and `runtime/machine.rs` inspection found no authorized safe code slice for this contract.

## Runtime, leases and integration

Current worker capacity was already over the sprint cap due eight retained UNKNOWN historical/foreign observations. The only live supporting worker was the read-only dispatcher, which completed its start consultation. No proof producer, implementation worker, or reviewer was launched. This was bounded primary-only work (Lean checks only), and no historical reservation or lease was reclaimed. The four changed paths are the new Lean module, `YulangClosure.lean`, this README, and the contract/handoff/current-state/outcome records. All are to be frozen after hashes are recorded.

No Git operation has occurred yet. The original goal remains active; this milestone is unreviewed research preservation, not theorem acceptance or program completion.
