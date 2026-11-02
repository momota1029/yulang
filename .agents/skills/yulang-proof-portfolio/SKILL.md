---
name: yulang-proof-portfolio
description: Plan and delegate substantial Yulang Lean work from an unchanged parent theorem, with progress measured by proved and applied parent obligations rather than local lemma count.
---

# Keep proof work attached to its parent

Use this skill for multi-step Yulang inference proofs, stalled theorem programs,
or work that needs proof tasks split across agents. For a single local Lean repair,
use `yulang-lean-proofs` directly. This skill changes task selection and handoff
quality; it does not grant semantic, production, Git, or delegation authority.

## Start at the original obligation

1. Read the exact parent declaration and governing source/specification. Record
   its quantifiers, supported syntax, shared assignment/witness, conclusion,
   and current application gap. Keep the parent statement unchanged.
2. Trace the proof backward from that conclusion. For each edge, classify the
   evidence as: checked and applied; checked but not applied; conditional on an
   open premise; only a definition/model; or refuted. Name the first unresolved
   premise and the source/model owner that could establish it.
3. Search existing artifacts for that exact premise and consumer. Reuse results
   only with their actual hypotheses. Do not restart settled questions or make
   another equivalent local lemma when prior attempts left the same edge open.

## Select useful assignments

Prefer packets that can close or materially reduce an edge in the unchanged
parent proof. A packet may also be useful when it establishes a decisive source
equation, supplies a concrete falsifier, or removes an evidenced dependency
from the critical path. Lemma count, sprint count, model size, notes, and passing
tests are not progress measures by themselves.

Separate methods when their inputs and outputs are genuinely independent:

- **Proof construction:** prove the exact source/algorithm obligation and show
  its application at the named parent proof edge.
- **Source or model construction:** establish the independent meaning and
  constructor-to-carrier map needed by that proof, without assuming the target
  typing judgment or solver success.
- **Adversarial audit:** try to falsify the exact implication with arbitrary
  satisfying assignments, missing source cases, wrong endpoints, or lost
  scope/effect/witness data. Report a concrete counterexample or the exact
  surviving gap.

Do not split one dependency chain into several workers that all need the same
unfinished model. The primary owns admission, leases, coordination, review,
adjudication, records, and Git. Children are leaves unless the governing
orchestration rule explicitly grants its bounded proof-coordinator exception.
Use only roles available in the live session; repository agent profiles are
configuration for a later loaded session and do not hot-reload active agents.

## Assignment packet

Every delegated packet names:

- unchanged parent theorem and the exact proof/application edge;
- fully qualified target declaration, quantifiers, assumptions, and conclusion;
- source authority and exact definitions/constructors/consumers to inspect;
- frozen dependency revisions and exclusive output/handoff paths;
- the expected parent-edge delta and how to demonstrate it;
- a concrete falsifier or adversarial question;
- verification owner, bounded commands/resources, and stop condition;
- first unresolved premise and its owner if the packet cannot close.

Keep proof, source/native correspondence, and production status separate. A
conditional theorem is useful evidence, but it does not close its parent edge
until its premises are independently justified and the theorem is applied.
Do not replace an arbitrary-solution quantifier with a selected solution, add
the desired source judgment as a hypothesis, drop source constructors, or lose
effects, endpoints, scope, or a shared witness to make a packet pass.

## Measure and hand off

Report one of these outcomes for each parent edge:

- **CLOSED:** checked theorem, every premise justified, and application shown
  in the unchanged parent proof;
- **REDUCED:** an applied intermediate edge is smaller, with the exact remaining
  premise named;
- **CONDITIONAL:** theorem checked but one or more assumptions remain open;
- **REFUTED:** a source-qualified counterexample refutes the exact claim;
- **BLOCKED:** evidence identifies the exact missing definition, authority, or
  source equation and its owner.

Give the before/after parent proof shape, not a count of local declarations.
Include exact theorem types, checker/toolchain results and axiom audits for Lean
proofs, plus review status. If two materially different attempts leave the same
premise untouched, stop that route and change the method or investigate the
premise's owning construction. Never relabel a renamed lemma as parent progress.

For Yulang sprint work, also follow `yulang-sprint`, `yulang-next-action`, and
`yulang-lean-proofs` at the boundaries and work types those skills govern.
