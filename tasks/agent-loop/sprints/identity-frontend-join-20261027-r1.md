# Sprint IDENTITY-FRONTEND-JOIN-20261027/r1 — original Identity to HIR join

Status: **CANDIDATE** until Luna records the contract hash in `current.json` and grants the exact leases below.
Branch / baseline: `yulang3` / `9074c03a65be121376d943e49fa2b81e785fa910`.
Authority: persistent full inference/executor goal and original A/B claims; `IDENTITY-ENTRY-ORIGIN-20261027/r1` reviewed outcome; the actual pinned HIR builder and identity/source-owner evidence below.

## Fixed outcome

Remove the first missing frontend join found by the predecessor: construct both the original source `Identity` and its runtime/HIR operands from one authentic parsed occurrence. Follow the branded frontend root/index, retained `LocalSource`, inline formal registration and resolution, Lambda/Apply children, occurrence/site assignment and generated labels. Derive the equations needed to apply the reviewed identity source constructors and Callee prefix only when their owners and indices match.

Success is either:

1. Checked, source-grounded constructor equations from one common frontend origin to the original `Identity`, formal/body Name, enclosing Apply, HIR/runtime root/index and corresponding labels, plus an exact application of the existing parent operands where justified; or
2. The first exact HIR owner equation or invariant that cannot be derived, with the original parent premise and next owning module identified.

A hand-written record whose fields assume the desired correspondence, a new convenient `Identity`, free Raw/program tables, ordinal equality, or an unverified simulation premise is not success. A bounded `NO_SAFE_CODE_SLICE` is acceptable for the read-only implementation lane absent an evidenced defect.

## Hard boundaries

Original A/B quantifiers, supported source domain, lexical/type/event scopes, complete Call, Effect hygiene and shared witness remain unchanged. Do not add receipt semantics, admission laws, source restrictions, compiler/Rust/test edits, proof-only root imports, production promotion or parent closure. Keep lexical Closure environment distinct from Apply caller environment. Distinguish root/index ownership, occurrence artifact identity, labels and numeric ordinals. Foreign parse mixing, shadowing, sibling restoration and reordered occurrences are explicit falsifiers, not cases to assume away.

## Proof lane — registered `lean_prover`

- Starting evidence: `OriginalIdentityEntryOrigin` and its exact pinned handoff; actual `yu-hir` branded source/index constructors; `OriginalCalleeDelayProvenance` only under its established conditions.
- Construct a source-grounded interpretation of the relevant authentic frontend data. Derive the original Identity/formal/body and enclosing Apply from that same construction; derive label, body/argument, binder-resolution and environment equations from owning constructors. Apply these to the reviewed source equations and Callee prefix wherever justified.
- Do not define correspondence as a record of desired conclusions or assume a Rust-to-Lean simulation. If the Lean source model cannot establish correspondence to the pinned frontend owner, freeze that exact owner gap.
- Output: `notes/theory/lean/YulangClosure/OriginalIdentityFrontendJoin.lean`, `notes/theory/lean/AuditOriginalIdentityFrontendJoin.lean`, and `tasks/agent-loop/inbox/identity-frontend-join-20261027.md`; isolated scratch `/tmp/yulang-identity-frontend-join-20261027/proof`.
- Use pinned Lean 4.35.0, one checker process, `-j1 -M1024`; at most six calls and 360 aggregate checker seconds. Print all originating theorem types and a complete transitive axiom audit. Enumerate and hash the complete imported project-source cone before checking.

## Implementation lane — registered `implementer`, read-only

Trace one unannotated inline identity occurrence through HIR formation, `local_source_for`, `main_runtime_roots`, source labels, Lambda allocation and Apply/Callee selection. Inspect the relevant tests as evidence only; do not run tests. Return exact owner equations and rejection boundaries for parse/root/index branding, local-source retention, inline parameter registration, lexical binding/restoration, occurrences and labels. Compare same-spelling shadowing, sibling-scope restoration, reordered occurrences and foreign-artifact mixing. No Rust edits, tests or builds.

## Independent review and integration

After both producers stop and proof bytes freeze, assign a fresh non-author reviewer. Challenge authentic common-origin provenance, owner branding, shadowing/restoration, occurrence order, labels, lexical versus caller environment, the parent application and the falsifiers above. Reviewer performs no build/check or writes. Luna records the outcome and exact gate status. Only reviewed evidence may be called an accepted partial result.

## Exact leases

- Primary: `tasks/agent-loop/current.json`, this contract, `tasks/agent-loop/sprints/identity-frontend-join-20261027-r1-outcome.md`.
- Proof: `notes/theory/lean/YulangClosure/OriginalIdentityFrontendJoin.lean`; `notes/theory/lean/AuditOriginalIdentityFrontendJoin.lean`; `tasks/agent-loop/inbox/identity-frontend-join-20261027.md`; scratch `/tmp/yulang-identity-frontend-join-20261027/proof`.
- Read-only implementation handoff: `tasks/agent-loop/inbox/identity-frontend-join-20261027-source.md`.
- Fresh review after both producers stop: `tasks/agent-loop/inbox/identity-frontend-join-20261027-review.md`.
- No wildcard, other path or historical quarantined path is leased. Do not modify predecessor evidence.

## Budget and stop conditions

3600 active seconds total: proof 1800, implementation 600, primary 480, review 540, dispatch 180. At most one checker/heavy process; no Cargo work. Astra 0. Two producers plus Luna, with review/integration capacity reserved. The user's nine-slot capacity release affects accounting only; every legacy UNKNOWN observation and quarantined historical path remains unchanged.

Stop at the first exact owner mismatch, authentic occurrence counterexample, pin mismatch, unowned semantic field, unexpected writer/path conflict, resource bound, or user STOP/session end. A source model without established owner correspondence is conditional and cannot close the parent. Routine internal steps stay inside this packet; consult the dispatcher at a material obstruction/counterexample, authority/dependency/lease/resource change, frozen integration seam or sprint END.

## Frozen input pins

All bytes must match at admission. The proof handoff additionally enumerates and hashes its full imported project-source cone.

| Source | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalIdentityEntryOrigin.lean` | `9df7fccfe03becec491665a28a7fb65760e1245d76e68330fc9626da5533163e` |
| `notes/theory/lean/AuditOriginalIdentityEntryOrigin.lean` | `dc2eaa3f53d9b841c108040fd2a4d7bb6f05d8eac52bd4b37e4957d1a79583b2` |
| `tasks/agent-loop/inbox/identity-entry-origin-20261027.md` | `35d3332f210f686cf814f50fa4100295b2a2bad6bd5e7bf7fe619ab6d76d81fd` |
| `tasks/agent-loop/inbox/identity-entry-origin-20261027-source.md` | `4474e4a12b0d723302e7ee3986ce817628c47af7083dc03060c1ef00d91dde06` |
| `tasks/agent-loop/inbox/identity-entry-origin-20261027-review.md` | `9174117df1271bc49cb6aa9f901022434f609d997a6aeeb42630eb3ce34a0432` |
| `tasks/agent-loop/sprints/identity-entry-origin-20261027-r1-outcome.md` | `dad349834d439bd6d7a6c7ef80bd4cfb6bd05c0d8d5b4d417ea5c70bccd7c40f` |
| `notes/theory/lean/YulangClosure/OriginalCalleeDelayProvenance.lean` | `3acb041c530b19e78703b3f3030edd1b304ab7c20329974f0afc2d387428dbfe` |
| `tasks/agent-loop/sprints/callee-delay-provenance-20261027-r1-outcome.md` | `a158f502b625a0bacbfa9b66a575d8758f78f75c2fe7f453872c7e830af8c345` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `crates/yu-hir/src/source_identity.rs` | `4bd5fa4066a1fd445a9757374c44d602decd1d791a394cd81c6066efa063fb23` |
| `crates/yu-hir/src/shadow.rs` | `b964bab6dcdb7ebeca9f964c134ac8fb041c928c20ce0a895fea6b6af0fbb93e` |
| `crates/yu-hir/tests/inline_lambda_local_source.rs` | `1fe9cc2e03ffb4d633dab22d2d9c8f6a9682d8013feded572fb2251a77442899` |
