# R159 outcome: original App law and Rust effect route

Sprint: `EFFECT-PERMISSION-SOURCE-APP/20261102-R159`
Contract: `tasks/agent-loop/sprints/effect-permission-source-app-20261102-r159.md`,
SHA-256 `ac7b61c03de0d1adae68452e9ae5df88e8500f890af96700719e828873abe7fc`
Baseline: `d3ed59fc63713e5cbe90332be5c9df74e730aa55`
Integration commits: `796d0841b`, `661e130d0`, `6b5e8f592`, plus this outcome
checkpoint.

## Fixed objective and evidence

The R159 objective retained the original App source domain and quantifiers,
including both annotation alternatives, all Local premises, both finite
Checking judgments, arbitrary operands, selected descriptor/interface writes,
the exact ViewLogic occurrence/extension, and conditional singleton-formal
origin. It did not authorize a semantics change or production promotion.

Lean artifact `notes/theory/lean/YulangClosure/SourceAppAdmissionR159.lean`
SHA-256 `5e948a1f8a3aab66028f885ebf16b6ffeed81999039e8a5a4e9c3caf84464408`
and proof handoff `tasks/agent-loop/inbox/effect-permission-source-app-r159-proof.md`
SHA-256 `6eccc4abadd82877f9b0d6c9d8782d39b9e7b2fb56962c4c56f92163e4e65c2c`
were independently reviewed PASS for the exact decomposition and conditional
interface separation. Pinned Lean 4.35.0 built R159 successfully; direct Lean
check and all 11 type/axiom audits passed. Axioms were limited to
`propext`, `Classical.choice`, and `Quot.sound`; `rejectApp_elsewhere` used no
axioms. The full theorem types and audit are in the frozen handoff.

The proof applies `app_admission_iff` to the actual App root and exposes the
separate original profile-formation P and logical-admission A supplier as the
first remaining premise. `InterfaceModel.separation` demonstrates the gap in
the abstract supplied interface while preserving the stated operands,
premises, checks, occurrence, extension, annotations, and writes. Independent
review confirms that this is **not** an authentic source-qualified
counterexample and supplies no source P/A construction. Those source meanings
remain OPEN at primary source/Checking intake.

The inherited R157 artifact remains unchecked because its import path fails in
unchanged `SourceLogicalOwnerBridgeR105`: the pinned build reports a type
mismatch at 107:10, parser errors beginning at 239, and failed `rfl` goals at
270/279. R105 and R157 are outside the successful R159 import cone; neither was
edited. The exact commands, versions, outputs, and resource receipt are in the
proof handoff.

Rust artifact `tasks/agent-loop/inbox/effect-permission-source-app-r159-source-native.md`
revision 1, SHA-256
`eb23cb7433fb40fb5a6212325dfa552c256005bc6bbcdd0fc69caa796cbf6445`, received
independent technical PASS for its bounded `NO_SAFE_CODE_SLICE` result. It
traces source Apply operands, candidate provenance, native Function/effect
rows, and the clean FreshUse/BoundKey consumer. Separate invocation and
application effect records retain polarity and identity. This observer remains
structural and does not prove source admission, permission, or effect
soundness. The actual FreshUse-map constructor in dirty/quarantined
`candidate_scheme.rs` was excluded.

The Rust handoff's role metadata was inaccurate. The primary correction at
`tasks/agent-loop/history/20261102-r159-source-native-dispatch-correction.md`,
SHA-256 `3cb6db96b315802e1d96379091af2505a2a0c6399a9a3a31faf5a7bf19f1545f`,
preserves the handoff bytes and distinguishes intended `compiler_referee`
Sol/medium routing from the actual `implementer` dispatch. The actual worker
was `/root/r159_source_native`; runtime session, observed model, and effort
remain UNKNOWN. A fresh registered compiler referee passed the technical map;
the metadata finding is resolved by the primary correction only.

## Exclusions, source state, and next owner

No Rust source, Cargo, tests, or Rust build was changed or run. Dirty
`candidate_receiver.rs`, `candidate_scheme.rs`, runtime files, and untracked
quarantined artifacts remain untouched. No new worktree, target, or cache was
created. Lean verification used the existing project/build only; its existing
`.lake/build` grew from 48 MiB to 89 MiB while building required imported
modules. The workspace filesystem still reports 769 GiB available. This build
cache remains in place for subsequent proof work.

R159 completes its bounded interface/source-owner result, not the continuing
Rust/Lean soundness goal. The next owner is primary source/Checking semantics:
define or select a concrete constructor that ties descriptor/profile P and
independent admission A to the same App witness and telescope, then prove that
constructor's bridge into native ports and effect keys. Any semantic change
requires its own reviewed design decision before compiler implementation.
Whole-program soundness, effect hygiene, Rust implementation, and production
promotion remain OPEN.

Independent review is complete; all assigned writers and verification
processes stopped. Static sprint check passed. Only the explicit outcome,
contract, reviewed R159 handoffs/correction, and compact current-state records
are in the R159 commit range. No blanket staging or force-push was used.
