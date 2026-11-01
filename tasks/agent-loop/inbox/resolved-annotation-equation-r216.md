# R216 primary handoff — annotation equation boundary

Status: **FROZEN FOR INDEPENDENT REVIEW; INCOMPLETE MODEL.**

Original parent: `Contracts.SourceProblem.InferenceSoundness`, unchanged:
`∀ s x d a, supported s → generates s x d → solves d a → ∃ e,
sourceJudgment s x e ∧ sameScoped s x e a`.

## Artifacts and dependencies

- Contract: `tasks/agent-loop/sprints/resolved-annotation-equation-r216.md`
  SHA-256 `55b181c8f2f04422c5b9ff10428cbf380b7fae61b4731c27e34979c58885a09c`.
- Model: `notes/theory/2026-11-02-resolved-annotation-equation-r216.md`
  SHA-256: `f6af81c33a321cd194b625b74ec8a448d5af8527c5be257617f36c3860d07514`.
- Author: `/root` (primary only); no coauthor.
- Exact original source atom: `OriginalSourceGeneration.sourceRules` Lambda
  branch `:130–141`, atom `sourceFormalRole formal.site formalContext`.
- Parent and dependencies are hash-pinned in the model note.

## Result and parent application

The note gives concrete equations for fixed signature lookup, constructor-
directed generation, same-assignment denotation, and the original `Kernel.atom`
application. It then identifies the first missing owner: no pinned original
source/signature elaboration and annotation-formation law maps raw annotation
occurrences to the complete scoped annotation data used by generation and
typing. `OriginalSourceSyntax.Annotation` is only `Nat`; the source atom remains
parameterized by a caller-supplied Kernel; `SimpleSub.Store` has no source
coordinates. Rust carries an annotation grammar but its correspondence and
coverage are explicitly unproved. R208 assumes the coordinates/tree and proves
only its own classification relation.

No annotation semantics or coverage restriction was invented. The original
Lambda atom premise remains open; parent delta 0, roots 0/4, packages 0/5.
No new Lean declaration, theorem, axiom audit, Rust change or test exists.
No Lean build ran in R216. The cache is user-authorized and remains in the
existing pinned project only.

## Review request

Fresh independent `compiler_referee` review, message-only, up to 600 seconds.
Review whether the missing source/signature equation is the first exact owner
boundary under the pinned Source-Generalize and hygiene authorities; check
that no original supported source form was excluded, that the claim is not
overstated as semantic underdetermination, and that the exact original atom and
parent delta are reported correctly. PASS permits only this incomplete stop
artifact to be checkpointed; it cannot admit a theorem or close soundness.

All author writes are stopped. No child worker was launched; the contract's
Lean lane is not admitted before the model equations pass their gate. Luna owns
review adjudication, current-state synchronization and any Git operation.

## Independent review receipt

Initial fresh `compiler_referee` review: PASS for this incomplete stopping
artifact only; no blocking or major findings. One minor evidence attribution
finding at model lines 123–126 was repaired. Its delta review PASSed the repaired
model and updated handoff, with no new blockers or claim expansion. The corrected
source is precisely pinned in the model note and directly supports its statement
at `notes/theory/2026-10-26-original-source-generation-construction.md:84–99`.
Both review rounds verified their frozen target hashes. Parent delta remains 0;
roots 0/4 and packages 0/5. No theorem was admitted. Reviews were read-only and
used no Lean, builds, tests, cache writes or Git.

## Sprint-end selection

The read-only `next_action_selector` selected R217: construct a fixed
source/signature annotation-elaboration model, mapping each raw occurrence
through binder/declaration resolution to complete type/effect data and the
source-selected Value/Computation entry. The source signature stays outside
the solver assignment. Success requires concrete definitions and a coverage
argument, not a lookup hypothesis or another blocker inventory. A fresh
600-second review is the seam; implementation remains `NO_SAFE_CODE_SLICE`.
Any new annotation grammar/variance/formation choice beyond existing authority
must be surfaced as a material decision before adoption. Parent accounting
remains 0/4 roots and 0/5 packages.
