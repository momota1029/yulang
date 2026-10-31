# R122 outcome — computation-entry PRE-state

Contract: `tasks/agent-loop/sprints/effect-permission-entry-prestate-20261102-r122.md` (`b0611e6bfaf5633887fcf566faeaeb5c7f29d7b8d68e6b09fece50fddb6cdcf7`). Admission baseline: `f648047e17206665f986bea880ff89f0a90a3adf`; source pins and manifest are recorded in the contract/admission.

## Result

**PASS for conditional source audit evidence only.** At the immutable `candidate_effect.rs` constructor, passing both explicit absence guards establishes `formal_domains` and `formal_entry_permissions` are absent immediately before that invocation. The audit follows the local writers, checkpoint/rollback journal removal, entry publication, cursor/frame behavior, and scalar `FormalEntry` before `FormalAnnotation` ordering.

The result does not establish universal first-entry/reuse reachability. An annotated record-pattern domain write can precede Entry if that pattern is admissible; authentic HIR formation and outer-row admissibility are not established in the pinned source. Safe caller transaction/discard/reuse ownership is also outside the pinned files. No source-reachable counterexample was proven. R39 can receive only the conditional constructor facts: actual same-state identity and collection projections into Lean remain unauthenticated. The nested callback `[Result]` row and R121 consumer read equation remain separate obligations.

## Frozen evidence and review

- Source handoff: `tasks/agent-loop/inbox/effect-permission-entry-prestate-r122-source.md`, SHA-256 `a9191683817369d96c94c74ffe737825ab83e7ee5a5ca3ee2eb491574ff20612`.
- Proof handoff: `tasks/agent-loop/inbox/effect-permission-entry-prestate-r122-proof.md`, SHA-256 `abd69016f9177a09b7a56cc6c3499aef661cca5db5a08ea0e9cc24cdab294489`.
- Independent `compiler_referee` review: **PASS**, no blocking/major/minor findings. It independently checked pinned source and Lean bodies before reading the handoffs, authenticated all source and handoff hashes, and confirmed the conditional scope and open owner/reachability obligations. Reviewer performed read-only work and wrote no file; this outcome is the primary's review receipt.
- All R122 source/proof/review workers are STOPPED: `/root/r122_entry_source`, `/root/r122_prf`, `/root/r122_independent_review`.

No compiler/Lean model or theorem was added. No builds, tests, checker, execution, storage probe, source edit, or quarantined/dirty source read was performed. Static consistency check only: `python3 tools/agent_sprint.py check` passed; this is not proof or independent review evidence.

## Disposition

Close R122 conditionally. Keep R111 verification-resource wait, R121 actual indexed-read interpretation, HIR admissibility, caller lifecycle/reuse ownership, parent soundness, effect hygiene, and production OPEN. Rust source integration is not authorized by this packet. Next admitted work should obtain exact HIR/caller ownership evidence or select another safe immutable-source Rust lane; do not create another conditional Lean model for this same gap.

Git packet is limited to this outcome, the two frozen handoffs, and the primary-owned R122 contract, input manifest, admission and current-state record. No dirty solver/runtime files or unrelated untracked artifacts are included.
