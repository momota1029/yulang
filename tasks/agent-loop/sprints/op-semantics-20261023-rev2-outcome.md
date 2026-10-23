# Operational semantics: full refined paper derivation

Status: **PAPER DERIVATION WRITTEN; INDEPENDENT REVIEW PENDING.**
Claim class: candidate complete paper derivation for the explicit normative
typed language defined in the manuscript. This is not repository theorem-gate
certification, implementation approval, or proof of the current compiler.
Author: current primary alone; no subagents, independent reviewer or proof
assistant were used. The user's proof-before-implementation request governs.

## Parent application

Revision 1 proved only an execution-type projection and left the full effect
connection open. Revision 2 supplies that connection in the same manuscript.
Theorem 9.7 now concerns explicit derivations of `A ! Phi`, including immediate,
latent and reentry ports, source profiles and joint assignments. Its premises
are syntactic typing, finite relation/table inclusions and typed open inputs.
Inference success, solver termination, principality, `BuildLocal`, semantic
primitive adequacy and an assumed safe resumption are not premises.

The full mathematical derivation is written for this explicit declarative
calculus. Independent review remains required before a repository gate can
be marked closed. The original inference/source/native A/B obligations,
compiler elaboration, Oracle equivalence, Q1–Q8 integration and production
remain OPEN. No claim is made that every previously named certificate or
smaller informal effect row already satisfies the now-explicit local rules.

## Construction and proof

- All 13 expression and 11 pattern forms receive declaration-directed View,
  transport, source profile and receipt construction. The linked root has a
  fresh owner; generated recursive adapter templates have no invented source
  receiver. A native list has a finite vector skeleton even if its elements
  refer to recursive values.
- Concrete queries use one shared path/instance/observation witness for a
  grant. Owner activity is a conjunct of eligibility itself, as required by
  the existing typed-boundary draft. Hiding it only inside incidence would
  wrongly enable a dead owner's handler when protection becomes false.
- Concrete path queries enumerate finite history routes and finite inverse
  images of primitive prefix correspondences. Regular profiles use automata;
  nonregular nominal arguments use finite guarded templates checked on the
  actual finite path. No infinite monomorphization is assumed finite.
- Complete-cell concretization and finite transfer generation are explicit.
  Value/profile facts are separate from operation facts; a permission cannot
  introduce an operation seed. Unknown retains all consistent cells.
- Resume uses action-tagged interfaces. Saved packets and future reads receive
  the same bound renaming; the resumer's ambient packet stays fixed. Old and
  fresh owner points may coexist. Hidden-region splitting accounts for both;
  same source labels do not establish equality across these actions.
- Pending handler activations belong to wait-frame binders. Pending events
  preserve their immutable emission observation list per interpretation;
  branches do not globally merge observations merely by original event ID.
- Reentry effects are constructed from the grammar of actual evaluation-frame
  cuts. Its monotone function summaries and ordinary port facts have a finite
  simultaneous closure. Selected shallow handlers are excluded, forwarding
  handlers included, failed attempts retained and eligibility reobserved.
- Substitution, qualified instantiation, graph extension, totality, frame
  composition, handler selection/forwarding, raw resumption and every machine
  transition are connected to preservation and finite-prefix safety. Empty
  immediate effect implies no outward request; returned latent code retains
  its own contract. Named language failures and divergence remain permitted.

These fill the manuscript's operational/typing definitions. They do not
authorize a compiler to change ordinary accepted source behavior. A compiler
must still generate such derivations and implement the stated transitions.

## Frozen inputs and output

- Baseline: `44c75a95c21db66a393e00f16d6123aa90940a1d`.
- Original user TeX, unchanged and unstaged:
  `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65`.
- Existing typed-boundary draft, unchanged:
  `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb`.
- `docs/yulang-operational-type-safety-ja.tex`:
  `7d71399381509b97cc080406401dafc06506a1fec614bf1b0ce4a8f1c95a87b4`.
- Revision-1 contract/outcome remain unchanged; the revision-1 manuscript is
  preserved at the baseline commit. No review of those frozen bytes was active.

## Checks and runtime

XeLaTeX produced a 33-page PDF at
`/tmp/yulang-op-20261023/yulang-operational-type-safety-ja.pdf`.
The final build has no undefined references or overfull boxes; underfull table
notices remain. Page 31, containing the transition proof and theorem opening,
was visually inspected. `git diff --check` and `python3 tools/agent_sprint.py check`
passed. The latter is static record/tooling evidence only. These checks are
not proof checking. No compiler implementation, compiler build, semantic test,
executable proof probe or background service was run.

The primary's start clock observation was 2026-10-23 11:57:16 UTC; the final
manuscript observation was 12:51:11 UTC. This is within the 7,200-second
single-primary envelope. Actual runtime model/session IDs are unavailable.
All four prior-session UNKNOWN identities and their reservations remain
quarantined. The R349 proof/handoff files were neither consumed nor changed.
The original untracked user documents remain separate.

Next boundary: independent review of these frozen definitions and proofs,
then a separate compiler-to-derivation and machine-realization argument before
dependent implementation. No automatic continuation or background work is
claimed. Manuscript authoring is stopped for integration of exact owned paths.
