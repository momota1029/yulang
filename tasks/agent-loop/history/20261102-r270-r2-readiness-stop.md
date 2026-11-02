# R270-r2 readiness stop: declaration-selection source owners

Date: 2026-11-02. Contract R270 revision 2:
`tasks/agent-loop/sprints/source-qualification-authentication-r270-r2.md`,
SHA-256 `71742111d143af273c18f8b2722b2524321a3cad0d288609ecfa8ba263fff20c`.

## Exact stop

Sol `/root/sol_r270_source_qualification_auth` resumed under a fresh GO in
coordination session `01a1873a-a93b-7dc3-a8ce-028a7b543a80`, with its exact
identity and two output leases confirmed. After its 146-pin gate (including
36/36 R255 and all 42 R270-r2 syntax additions), the source trace reached the
authorized `binding.rs::binding_statement_selected_lexical` owner. That
function unconditionally calls these unlisted selectors after the use test:

- `crates/yu-syntax/src/declaration/mod_decl.rs`, SHA-256
  `6adf9945e096ee027886a05857f6c187134a5331e4ab37493d95304255760741`;
- `crates/yu-syntax/src/declaration/struct_decl.rs`, SHA-256
  `7b36b18fc6ef3e149e756a37b0f74719a5ae40be195c6986efe2c44d57fa3de4`;
- `crates/yu-syntax/src/declaration/type_decl.rs`, SHA-256
  `e01d1f30c1dca051fb590a9fddac1686621fc789444f9cb053dcc269e746c134`.

Normal return through those owners is needed to authenticate the concrete
`my outer` header decision. The producer did not open these unlisted paths and
did not treat the expected keyword behavior as evidence. Luna performed a
bounded locator pass of only those exact selector functions; they consume
already pinned lexical observation/lexer owners and do not call additional
declaration owners. This is a readiness finding only, not source proof.

## Cessation, budget and result boundary

Sol confirms all reads, searches, hashing, proof work and writes stopped; no
descendants, processes or scratch/generated/cache outputs remain. Across R270
r1 and r2, both exact theory/inbox output paths remain untouched and uncreated.
Requested Sol/high; observed model/effort UNKNOWN; actual time UNKNOWN; child
UUID UNKNOWN. R270-r2's full 1,500-second grant is charged; R270-r1's 1,500
seconds remain charged. Cumulative Sol charge is 3,000 seconds, with no reset
or refund. The 600-second fresh reviewer reservation remains unissued and
unspent pending the next admitted packet. No proof, accepted-source
authentication, clause defect, counterexample or parent closure is claimed;
parent/A/B delta remains 0→0 and `NO_SAFE_CODE_SLICE` remains.

The prior primary readiness audit in
`tasks/agent-loop/history/20261102-r270-r2-readiness.md` prematurely concluded
that no further source owner was needed. This r2 source trace falsifies that
closure claim; preserve the audit as historical evidence and supersede its
readiness conclusion before any further proof GO. No tests, builds, probes,
Lean, Cargo, source edits or Git operations occurred.
