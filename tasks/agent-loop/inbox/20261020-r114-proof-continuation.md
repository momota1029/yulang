# R114 proof continuation handoff

Handoff ID: `R114-PROOF-CONTINUATION-20261020`; revision: **1**; **FROZEN**.
Author: `/root/r114_source_identity_proof`; sole author, no descendants.
Requested: Sol/high. Observed: UNKNOWN/UNKNOWN (no visible runtime receipt).
Writer: **STOPPED** after this freeze; no child/background work or pending write.

## Outcome and parent application

**INPUT_MISMATCH / STOP**. Rev2 contract
`tasks/agent-loop/sprints/cli-wrong-family-permission-20261020-r114-rev2.md`
matched SHA-256 `ad2bf83a1e0769745cb8901cceb182aa75f5c7f7f85bba1ed3d20bb23dd9fc49`.
Rev1 contract matched `7e268bf4c7fe316ce7e729ae586e7b6618bc91107b6a3e661ab923ec1642637c`.
Both contracts, all 19 rev1 inputs, all 11 rev2 inputs and exact 195-byte source
were checked. Seven inherited rev1 pins mismatch; all rev2 pins matched at
startup. Under the contract this consumes the continuation boundary without
repair, retry, pin expansion or theorem promotion.

P-ID remains OPEN: authentic unequal declaration keys for the exact `signal`
and `other` nodes and their implication for unequal SourceEffectIds have not
been proved/applied. The unchanged rev1 conditional Machine/CLI argument gains
no discharged premise. Original preparation, annotation/formal projection,
actual runtime and CLI observations remain subject to their existing evidence
gates. No general theorem, forwarding/rejection claim, or production authority.

| Changed input | Actual SHA-256 |
|---|---|
| `crates/yu-hir/src/module.rs` | `153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907` |
| `crates/yu-hir/src/module/local_source.rs` | `d7c02fb7ba08fa389229064c6c12504a237fbd15687858431738cb2b2939a5ce` |
| `crates/yu-solver/src/candidate_source.rs` | `cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7` |
| `crates/yu-solver/src/shadow_apply.rs` | `838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543` |
| `tools/inference-playground/src/runtime/program.rs` | `28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d` |
| `tools/inference-playground/src/runtime/primitive.rs` | `da1beeb825ffe5263733a88955d3061372e34b74cd585bb4006a070f7adefc57` |
| `tools/inference-playground/src/runtime/machine.rs` | `4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd` |

## Frozen result and evidence

Artifact: `notes/theory/2026-10-20-r114-source-identity-completion.md`.
Revision 1; SHA-256
`8f2a79d5c3a4c7f458da787d18927414d747a93315ccb35356c9677bca43e925`.
It includes both expected and actual hashes, source/consumer owner locators,
retained premises and exact stop evidence. No independent certification.

Matching identity dependencies:
`source_identity.rs` = `7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3`;
`full_parse.rs` = `24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8`.
The already-issued startup source read showed parse-brand/green/start equality
and parse-owned key traversal; no exact-source proof followed the mismatch.
The map observation is not parent closure or executable/native evidence.

Prior work: rev1 proof author `/root/r114_proof`, SHA-256
`447875018fee0f7a7e131658223ea9e7066b860fe8e8c3c35513877edf795f92`, reused only
for its exact P-ID and conditional calculation. Rev1 handoff matched
`1e557c2adbcf53861701fa0a11679124fde1ebf87606a35624c923be6eba3f18`.
Frozen CLI test and implementation handoff also matched. Historical assertions
and unverified test source supply no current execution proof.

Checks/resources: read-only hash calculations and source reads; zero tests,
builds, compiler/CLI commands, formatting, Git, delegation, or Astra.
Budget cap 240 seconds. First observed clock: `2026-10-19 15:16:02 UTC`;
last observed before artifact write: `15:17:17 UTC` (75 measured seconds,
unmeasured startup/finalization additional). Conservatively retain/charge the
full 240-second lane reservation; **remaining authorized work: 0 after STOP**.
No reservation is reclaimed by this receipt.

Mutual TODOs: Luna reconciles seven changed dependencies and decides whether
a new frozen contract is warranted; this worker cannot repair/re-pin. Future
proof work needs explicit new grant and complete matching input table, then
actual key authenticity/inequality and application to P-ID. Future source/runtime
review must account for changed owning module, LocalSource, candidate,
projection, bypass and Machine inputs. No production implementation TODO arises
from byte mismatch alone. No in-scope continuation remains under rev2.

All new paths: the artifact and this exact handoff. Scratch paths: none.
**STOP receipt:** no descendants, no pending mutation, writer ceased at freeze.
Luna alone owns review, state, commands, authority, closeout, and Git.
