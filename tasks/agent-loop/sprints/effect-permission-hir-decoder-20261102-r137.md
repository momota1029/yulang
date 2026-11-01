# R137 — authenticate the HIR permission inventory

Status: admitted, source mapping first; proof depends on frozen source handoff.
Goal: continue the user's Yulang soundness and effect-hygiene objective.
Parent gates: `SourceProblem.InferenceSoundness` and effect-hygiene H remain OPEN.
Baseline: `4c1d58a646a1101c080659ebfed6ae7862d8aded` (= `origin/yulang3`).
Direct dependency: R136 outcome `tasks/agent-loop/history/effect-permission-adapter-and-constructor-20261101-r136-outcome.md`, SHA-256 `5ac7e90477c4ea44b819b4988cefe7d5a6559051d407c914b022202ac440bf0f`.

## Outcome

Determine whether every supported committed HIR annotation constructor maps,
with source identity, order, multiplicity, polarity, structural path, row
position and member identity preserved, to R136's Lean permission inventory
and the successful native constructor output. Include output publication and
identity/resource failure boundaries. Do not reduce the supported source
domain or treat partial publication after failure as a successful result.
Success is an authenticated correspondence or a source-qualified exact
counterexample/blocker naming the first omitted constructor/equation. Either
outcome must state how it changes the original parent and the next source owner.

## Source assignment (first)

One Luna/high implementer assignment, 600 seconds. Exact write lease:
`tasks/agent-loop/inbox/effect-permission-hir-decoder-r137-source.md` only.
Read committed baseline blobs only; do not inspect or modify dirty solver files,
quarantined runtime files, R103/module-supplier artifacts, or run Rust builds or
tests. Freeze all HIR annotation branches, constructor dispatch and output
publication point, along with identity/resource failures and their rollback or
partial-publication behavior. The R136 abstract inventory is a direct input,
not a substitute for source equations. No Rust source edits are authorized by
this packet.

After source handoff freezes, a fresh independent compiler-referee review gets
240 seconds and read-only access to that handoff plus its exact committed source
dependencies. Blocking findings must be repaired as a sequential revision and
reviewed before proof admission.

## Proof assignment (dependent)

After source review PASS, one registered `lean_prover` gets 600 seconds and
exact write leases `notes/theory/lean/YulangClosure/FormalPermissionHIRDecoderR137.lean`
and `tasks/agent-loop/inbox/effect-permission-hir-decoder-r137-proof.md`.
State a decoder over the actual supported HIR cases and prove its inventory
matches the frozen Rust constructor equations. Do not assume native-output
equivalence or move it into a hypothesis. Report theorem types and complete
transitive `#print axioms` for each named theorem. A fresh independent
`lean_prover` review gets 240 seconds after freezing. A direct check is allowed
once, at most 120 seconds, 1 CPU and 1 GiB RSS, only in the already pinned Lean
environment after Luna confirms it exists.

## Limits and falsifiers

Total envelope 1,800 seconds; Astra, Cargo, Rust build/test, new environments,
and storage probes: zero. Preserve exact source domain and all existing pending
questions. Stop with the first exact equation if a supported source constructor
cannot be represented, a branch or metadata field is omitted, identity changes,
or a failure can publish state later mistaken for success. Keep abstract proof,
source/native correspondence, runtime consumption, effect hygiene and
production status separate. Only Luna owns state integration and Git.
