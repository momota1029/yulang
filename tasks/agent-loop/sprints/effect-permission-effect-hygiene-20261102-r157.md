# R157 source effect join and original App admission

Status: COMPLETE as a bounded source-only research packet under the standing
user-authorized Rust/Lean goal; this does not close the parent obligation.
Baseline: `ead05a34e8aba32a1ca1d66e72109877d4b37e0e` (`origin/yulang3`).
Parent: original Yulang inference/source soundness and effect hygiene. Keep the
original source domain, quantifiers, semantics and production gates fixed.
Budget: 2400 seconds aggregate; no new worktree, target or persistent cache.

## Fixed evidence and goal

R156 is complete as a read-only audit and pushed. `candidate_operation`
retains operation declaration/owner/use provenance; `CandidateSourceCall`
retains native invocation/application Terms; `CandidateGraphFreshUse` exposes
rows, but no public route-scoped relation connects operation-bearing nodes,
retained FreshUse mappings and the exact outer Apply consumer. A fresh
compiler-referee review found that committed `candidate_scheme.rs` already
retains node-indexed FreshRoute terms and effect-operand maps, while the
existing provider observer rejects an Apply whose callee is itself an Apply.
Do not read dirty worktree `candidate_scheme.rs`; immutable HEAD only if needed.

Rust success: add a borrowed candidate-only observation in
`shadow_apply.rs` that follows existing retained constructor relations, if
they suffice, for the exact operation use through capture, FreshUse mapping,
and the outer Apply invocation/application effect. Preserve full operation
declaration identity, source owner, occurrence, row kind and exact call
occurrence. Never infer a join from family/effect equality or graph reachability.
If any edge is not retained, return NO_SAFE_CODE_SLICE with the precise missing
producer relation. No solver algorithm or language behavior change.

Lean success: constructively attack the original App admission gap identified
in R156 using R112/R114's exact witnesses and the original source constructors.
Preserve descriptor/interface choice, both operands, Local premises, descriptor
formation, both finite Checking judgments and optional singleton-formal origin.
Do not encode App preservation as an assumption or narrow quantifiers. Also
prepare a module-faithful R104/R105/R112/R114/effect-hygiene runner plan for
fresh review; do not execute Lean in this sprint.

## Exact assignments and review

- Rust implementer write lease: `crates/yu-solver/src/shadow_apply.rs` only.
  Read committed `candidate_effect.rs`, `candidate_call.rs`, and immutable-HEAD
  `candidate_scheme.rs`; do not edit them. No tests, Cargo, or build invocation.
- Lean prover write leases: `notes/theory/lean/YulangClosure/SourceAppAdmissionR157.lean`
  and `tasks/agent-loop/inbox/effect-permission-source-app-r157-lean.md`.
  Read exact frozen modules listed in R156; no Lean invocation or source edits.
- Primary owns this contract and `tasks/agent-loop/current.json`. Fresh
  independent compiler-referee review of the frozen Rust diff must attack
  wrong Apply occurrence, wrong FreshUse map, wrong operation declaration and
  missing consumer-bound evidence. Fresh independent Lean review must inspect
  the theorem statement, source correspondence, runner plan and complete axiom
  audit plan. No worker commits or pushes.

## Limits and stop conditions

No Cargo while held receiver/scheme diffs are present. Do not read or alter
`candidate_receiver.rs`, dirty `candidate_scheme.rs`, quarantined runtime
files, or unrelated untracked artifacts. No test addition/run, Lean execution,
Lake/default build, toolchain/dependency change, worktree, target/cache growth,
or semantic promotion. Existing `.olean.tmp.<pid>` runner failure requires a
new exact review before any future execution. Keep all parent theorem and
production gates OPEN. STOP on a missing retained relation, invented premise,
review rejection, resource/lease conflict, or unknown lease.

Primary stages only explicit reviewed paths and pushes a coherent source-only
checkpoint. Next dispatcher trigger: exact constructor obstruction, cross-lane
integration seam, or material authority/dependency/resource change.

## Frozen outcome and review

- Rust source-only observer is frozen in `shadow_apply.rs` at SHA-256
  `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5`.
  Independent compiler-referee review: PASS for the narrow structural
  observation after correcting the callee-expression type, negative native
  effect polarity, and ordered positive Support-lower to negative Effect-Row
  upper relation with exact `BoundKey`. It exposes no solver behavior claim.
- Lean file SHA-256
  `98cf8e4948ce1f9a72ebdcca7d5d2488b052df33c62947e067b10a616af5c00f`;
  handoff SHA-256
  `c4ffed123a67939bd5914b2c227a916f3f69718290933dd3a15c6357bd951ca9`.
  Independent Lean review: PASS for source-only candidate and handoff. Seven
  candidate theorem roots remain unchecked; no kernel types or axiom audits
  were executed. The runner plan is reviewed as a plan, not run evidence.
- No Cargo, build, tests, Lean/Lake/checker, or generated outputs were run.
  Both implementation/proof producers and both reviewers stopped; no writes
  remain active. No unrelated or quarantined paths entered the checkpoint.
- The exact next source obstruction is an original law constructing lawful
  descriptorFormation/admission at the original App binder while preserving
  every Local premise, both finite checks, both operands, and the chosen
  descriptor/interface. Full effect hygiene and all parent theorem and
  production gates remain OPEN.
