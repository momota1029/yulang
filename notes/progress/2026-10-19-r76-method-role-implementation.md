# R76 method/role source projection implementation receipt

Status: implementation candidate frozen; the single bounded HIR verification is pending. This is an inert source projection in `yu-hir`, with no parser, type inference, evaluator, solver, dispatch or accepted language behavior change.

## Result

`ShadowArtifact::pending_field_tail_sources` now enumerates every retained `FieldTail` in preorder and either returns a complete inventory or refuses the call. Each entry carries artifact-branded identities for the tail, its enclosing `OperatorChain`, and the direct member `Identifier`. It validates the exact two raw children `Dot`, `Identifier`, the retained parent relation, and the ordinal-indexed child slot. `PendingFieldTailSource::receiver_prefix` checks those IDs against the supplied artifact and borrows the whole preceding raw child prefix, including prior tails and trivia. This keeps record storage O(F), where F is the number of field tails, rather than copying each longer prefix.

`ShadowArtifact::pending_role_impl_sources` enumerates exact retained `RoleDeclaration` and standalone `ImplDeclaration` nodes in source preorder, retaining the branded `PositionId` and syntax kind. Checked lookup recovers range, parent, ordinal, and children. These records do not identify semantic `RoleId`s or implementation eligibility.

The new HIR tests cover one member access with role/impl source declarations, token spelling and range, retained expression parent, receiver prefix, and chained field prefixes. Parser diagnostics are refused by `ShadowArtifact::from_parsed`; unsupported selected FieldTail shapes refuse the whole inventory rather than returning partial success.

## Source path and limits

Parser constructors (`field_tail_normalized`, `role_declaration_normalized`, `impl_declaration_normalized`) → raw CST nodes/tokens → `ShadowArtifact::retain` → the two pending source APIs → checked artifact lookup and borrowed receiver-prefix access.

This is a source-to-HIR prerequisite for future method/role inference, independent of effect/handler closure. No generated inference constraint or execution path is added. An approved rule connecting lexical member/role/impl occurrences and receiver types to the complete eligible candidate/evidence set and generated constraints is still missing; the proof packet correctly returns `NO_SAFE_ROLE_SOLVER_SLICE` at that rule owner. Forwarding preservation, evaluator correspondence and Simple-sub A/B remain OPEN 0→0; R50 remains NOT_ADOPTED.

## Frozen source snapshot

- Contract: `tasks/agent-loop/sprints/method-role-source-projection-20261019-r76-rev2.md`, SHA-256 `38142e65fa9a73e9efa073208ec5456da5e9fec22f984baf83b65e3e28b84ff8`.
- Baseline: `d21c8eb3a87e43dd441474c9f138e71b1d8372ff`.
- `crates/yu-hir/src/shadow.rs`: `7fce00d94303e83b08d1dbd132b278489a0af85224f751d3e2a00de4b9804593`.
- `crates/yu-hir/src/lib.rs`: `8f6e2b688418dbdb4e2c551cbd9b7b58c809623d492f2da6f7d29cc64189d8d8`.
- `crates/yu-hir/src/tests/shadow_method_role_source.rs`: `0b1e570845b62237ac8e19b94b29facc42b40b5bcb943676078b8e5c33eed53a`.

Proof note: `notes/theory/2026-10-19-r76-method-role-source-proof.md`, SHA-256 `04b36001d9ccaaace8930d6304745928b03906f9e4e0a2d041f47223f543b275`; proof handoff SHA-256 `3fcde5d72bbea4c97a454799978ddc542d4cde7c58cde9bca514357aae191ac1`. It is a candidate constructive argument; fresh compiler/spec reviews and Luna adjudication remain pending.

Static `git diff --check` and `python3 tools/agent_sprint.py check` passed. No compiler command has run. The contract authorizes exactly one HIR-only command after this implementation and proof snapshot are frozen: `CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib shadow_method_role_source -- --nocapture`. Any failure is recorded without retry or repair under this revision.

## Verification addendum, revision 2

The one contracted command completed: `CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib shadow_method_role_source -- --nocapture`. It reported `2 passed; 0 failed; 130 filtered out` in 0.00s after a 6.79s compile. The crate emitted three dead-code warnings (`AssociationProvenance::{Token,Synthetic}` payloads and `replace_admission_root`); there were no compilation errors. This is focused implementation evidence, not proof of whole-language coverage or semantic correctness. No retry or source repair occurred. The source snapshot and proof binding hashes are unchanged.

Next: assign fresh independent compiler and spec reviews against the exact frozen source/proof hashes above. Their review remains pending.


## Evidence hash correction, revision 3

Primary adjudication of the compiler/spec review reports: the actual test source hash is `0b1e570845b62237ac8e19b94b29facc42b40b5bcb943676078b8e5c33eed53a`, confirmed by direct `sha256sum`; the proof note already records this correct value. Revision 1/2 of this implementation receipt, the revision 1/2 handoff, and `current.json` had a transcription typo `...943576...`. No source changed after the successful test run, so the 2-pass command receipt applies to the current test bytes. The implementation/proof source hashes are unchanged. The spec review's claim that the proof note hash was wrong is refuted by direct bytes; the compiler review correctly identified the primary receipt mismatch. Corrected receipt hash is recorded in the current state and this sequential handoff revision. Both original receipts remain recoverable by their previous hashes in current-state history.
