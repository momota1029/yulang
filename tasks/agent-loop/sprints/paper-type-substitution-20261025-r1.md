# FULL-PAPER-TYPE-SUBSTITUTION-20261025/r1

Status: PRIMARY-ONLY CANDIDATE; no child leases issued because eight historical/foreign assignments remain UNKNOWN and the active-assignment ceiling is exceeded.
Branch: `research/simple-sub-intrusion`
Baseline: `e8f133657b98d47d789a52fa64aee8f102393452`
Authority: user goal (Lean/specification primary); `docs/yulang-operational-type-safety-ja.tex` §§2, 8–9; `notes/design/2026-10-11-yulang-inference-top-level-principles.md`; `rules/goal-driven-sprints.md`.
Dispatcher start consultation: `/root/sprint_dispatch`, completed read-only proposal; no worker launch.

## Original outcome and success evidence

Original goal remains complete Lean proofs of Yulang type inference and executor semantics, preserving original source scope, Simple-sub A/B quantifiers, paper semantics, source/native correspondence and independent review. This continuation targets a foundational fragment of the original executor safety theorem `thm:safety` (`docs/yulang-operational-type-safety-ja.tex:1140`) and the immutable graph extension lemma (`:980`): define the paper's execution-type syntax with type variables and binders, then prove capture-avoiding simultaneous substitution algebra. This is a necessary typing-substitution premise, not executor safety, inference soundness/principality/termination, source correspondence, or production closure.

Success evidence: Lean kernel checks the complete type AST and substitution identity/composition/lifting laws, with no `sorry`, `admit`, or project axioms; state which parts of the paper type grammar and binder-bearing records the artifact covers. Falsifiers include any omitted paper constructor, wrong binder lifting, or operation payload/response type arguments that fail substitution compatibility.

Open original premises remain unchanged, including full source/inference roots, type-indexed environments/plans/operations, actual executor constructors and preservation, native correspondence, and all Simple-sub A/B obligations. No semantic or source-domain change is authorized.

## Lanes and exact permissions

Proof: primary owns the standalone Lean artifact `notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean`, imports it into `notes/theory/lean/YulangClosure.lean`, documents its boundary in `notes/theory/lean/README.md`, and records the handoff at `tasks/agent-loop/inbox/20261025-paper-type-substitution-r1.md`; related stages may refine this theorem within the same grammar and frozen dependencies.

Implementation: `NO_SAFE_CODE_SLICE`. The dispatcher's inspected runtime owners (`runtime/program.rs`, `runtime/machine.rs`) expose a separate pending-cell republication issue; no runtime replacement or semantic choice is authorized here.

Reads: the baseline paper, current Lean syntax/substitution modules, Lean README, and the frozen bounded source-generated outcome. No shared modules, production code, tests/expectations, config, manifest, question, or other worker path may be edited. No additional probe/process beyond one Lean checker/build owner. No child or reviewer is assigned under current capacity. A fresh independent review is required before any theorem promotion.

Budget: primary-only, at most 600 seconds active construction/checking, one Lean process at a time, no Cargo/native probes. Historical UNKNOWN reservations remain quarantined and consume capacity. Stop on budget, material counterexample, missing/ambiguous authoritative paper rule, dependency change, or need for lease expansion.

Git: primary may integrate only the explicit artifact, handoff, contract, compact state/outcome paths after checks and whole-range review; normal non-forced push only. The theorem and parent gates remain OPEN pending independent review and later application to the original typing/executor development.
