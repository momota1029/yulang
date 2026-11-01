# R160: original App profile and admission constructors

Status: ADMITTED by Luna under the continuing Rust/Lean soundness and effect-hygiene goal
Baseline: `6b5e8f592c222c41df88bfe1cb99a0830fe7c760` (`yulang3`, pushed)
Parent: original source App obligation decomposed in R159; whole effect hygiene and soundness remain OPEN.

## Fixed outcome

From the original typed-core/source-contract definitions, construct the original
descriptor/profile formation premise P and independent logical-admission premise
A at the same App binder and telescope, then apply them to the exact R159
decomposition. Preserve every original quantifier and premise: all Local fields,
both finite Checking judgments, both arbitrary operands, both annotation
alternatives, descriptor/interface writes, exact ViewLogic occurrence and
extension, and the conditional singleton-formal origin. If a constructor
cannot be derived, freeze the first exact undefined source clause or missing
owner evidence. A Lean scaffold that merely assumes P/A is not a result.

Rust remains a bounded source/native mapping lane. It may trace only the parts
of P/A that the approved source meanings actually provide into the existing
`OriginalGenCall0Input`, source Apply ports and native effect keys. No Rust
source edit, new semantic rule, changed accepted program set, or production
promotion is authorized by this packet. If no constructor evidence authorizes a
code change, record `NO_SAFE_CODE_SLICE` with the exact missing owner.

## Authority and fixed meanings

Use the user-approved natural-definition direction and the existing scoped
source definitions. Do not define P or A through successful whole-App
admission, native observer success, or the supplied proposition fields whose
independence is under examination. Do not drop source forms or strengthen
premises. If two complete interpretations consistent with current authority
produce different observable, acceptance, or principal outcomes, stop and
return the concrete example for a user decision before selecting semantics.

Frozen R159 inputs:

- `tasks/agent-loop/inbox/effect-permission-source-app-r159-proof.md` SHA-256
  `6eccc4abadd82877f9b0d6c9d8782d39b9e7b2fb56962c4c56f92163e4e65c2c`.
- `tasks/agent-loop/inbox/effect-permission-source-app-r159-rust.md` SHA-256
  `cd1c4d5b356313a88740fa81aebbd024fddbacd16b38c47cff1328ff05632ce8`.
- `notes/theory/lean/YulangClosure/SourceAppAdmissionR159.lean` SHA-256
  `5e948a1f8a3aab66028f885ebf16b6ffeed81999039e8a5a4e9c3caf84464408`.

Governing definition references:

- `notes/design/2026-10-08-source-generalize-definition.md` SHA-256
  `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`.
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` SHA-256
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.
- `notes/design/2026-10-05-inferred-function-call-views.md` SHA-256
  `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1`.

## Exact output leases

- Proof note: `notes/theory/2026-11-02-original-app-pa-r160.md`
- Lean artifact: `notes/theory/lean/YulangClosure/OriginalAppConstructionR160.lean`
- Proof handoff: `tasks/agent-loop/inbox/effect-permission-source-app-r160-proof.md`
- Rust source/native handoff: `tasks/agent-loop/inbox/effect-permission-source-app-r160-rust.md`
- Luna owns integration, `current.json`, review assignment, staging and Git.

Existing Rust read inputs are frozen by baseline and exact hashes:

- `crates/yu-hir/src/module.rs` `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`
- `crates/yu-hir/src/module/local_source.rs` `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`
- `crates/yu-solver/src/candidate_source.rs` `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`
- `crates/yu-solver/src/shadow_apply.rs` `99d67895c250e5d79fb774728867fe2fc88c4dc22df9bfc38ac9fd1aeb0908e5`
- `crates/yu-solver/src/candidate_call.rs` `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`

No lease is granted for dirty/quarantined `candidate_receiver.rs`,
`candidate_scheme.rs`, runtime files, or untracked quarantined artifacts.

## Lanes, resources, and review

- Proof lane: constructive Sol/high, up to 1800 seconds, on the three proof
  outputs above. Use the pinned existing Lean project/build only; no new
  worktree, environment, target or cache. Verify against the R159 Lean freeze
  and report theorem types and complete axiom audits for every claimed result.
- Rust lane: Luna primary, up to 600 seconds, on the exact Rust handoff only.
  Read-only source mapping; no Cargo, Rust build, tests, scratch output or code
  edits in this packet.
- Fresh proof and source reviewers: up to 1200 seconds total, assigned after
  frozen handoffs. Authors do not self-review.
- Total sprint ceiling: 3600 seconds; Astra assignments: zero. Existing
  `.lake/build` is the only Lean build directory and must be retained.

Proof review falsifier: either required conclusion is derived from the same
original telescope without circular use of whole-App success or an omitted
premise, or the handoff identifies the first exact clause that prevents it.
Rust review checks the source-to-native joins only against the frozen sources;
this is not whole-language soundness evidence.

## Stop conditions and boundary

Stop at a frozen constructor/application, a source-grounded obstruction, a
material semantic alternative requiring the user's choice, dependency/hash
drift, lease conflict, or the resource ceiling. A bounded source-law result
does not close other effect rows, permission ownership, executor behavior,
principality, whole-language soundness or production readiness.
