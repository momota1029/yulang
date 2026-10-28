# Outcome — EFFECT-PERMISSION-IDENTITY-REPAIR-20261028/r1

Status: **CLOSED_INCOMPLETE**. Objective remains Yulang inference/executor
soundness and effect hygiene. This bounded packet repaired its two known build
blockers and completed the Lean event-history audits, but it did not establish
the required same allocated-row witness through canonical capture to the exact
owner's exported permission port. No parent, native, effect-hygiene, A/B,
principality, termination or production gate closes.

Contract: `tasks/agent-loop/sprints/effect-permission-identity-repair-20261028-r1.md`,
SHA-256 `2008579471df100926ca41be4cd6fac780a7c2cc53ae5f5b1555bdec50c19c39`.
Baseline `29b85224b` plus the exact frozen overlay in the contract.

## Evidence

**Lean.** The final extension file
`FormalPermissionConstructorRealization.lean` (SHA-256
`70a89e7ea4589951e5f5e9323b4b2b415003c5868dc3f53ce16129fa67eafdd9`)
passed complete theorem-type and transitive-axiom audits for all 11 extension
declarations. The proof handoff SHA is
`78c610644f143a575e9e179cd1b9a30c4b1d897824a68170760967886f8b4c76`. It reuses
the audited 12 declarations in `FormalPermissionSourceOrigin.lean` at SHA
`db37f9d83e450a450d689b9eed46311108e635eb846d268b7a3a567dcee624fd`. The
declarations remain conditional on explicit event-history premises. Successful
native constructor decoding, allocation freshness, actual view/bound insertion,
discovery recurrence, canonical transport, live capture completion, exact
native export, and the original parent remain open.

**Rust.** Final sources:

- `candidate_effect.rs` —
  `85d624cd2a1c5b4f821b58aa30f4dbf4fb59c1f4c9650f88b51382c07cc95d3a`
- `candidate_scheme.rs` —
  `9eaee3528f36fcac180fe3b0e0428c8f353c2911fb0b854e621e57e08720e4d7`
- `shadow_apply.rs` —
  `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`

Both exhaustive test `Graph` literals now initialize
`formal_capture_trace_id: None`. The exact feature-correct Cargo invocation
compiled the library and reached both ordinary solve/export paths, but both
focused tests failed in their owner/source-event lookup assertions: **0 passed,
2 failed, 816 filtered out**. Exit 101; 65.83 s wall, 58.91 s user, 4.61 s
system, 96% CPU, 1,659,572 KiB max RSS, zero swaps. Invocation allowance
exhausted; no retry. Exact argv SHA
`5ac9f05783b1f35077b3382c3319eeff02c0db5d9605f1d1482aa9e7a010e316`, stdout
SHA `72744a0f9dc4f8c1bba006815ffd3b3a6b37f95a00b8851e75f3f78b1f8c0927`, stderr
SHA `a4c61c4db3ac87bd2c188fffbee787c34239a7e96c044802414ce53dc53f22c8`.
Rust handoff SHA
`7c724916d590b06a52cd55f160b2e2ddf84fce6edf9bd02ea599b839b36adf99`.

## Independent review

Fresh non-author `compiler_referee` review is recorded in
`tasks/agent-loop/inbox/effect-permission-identity-repair-review.md`, SHA-256
`22ad978a5c1907d11ebe7434f77406c76f98bcc67c43da4e77d83e1a7844e5f8`.

Findings:

1. **BLOCKING:** owner lookups format bare `DefinitionRootId`, while producer
   events format `SourceRootId::Definition(owner)`. Both failed tests stop
   before the decisive identity checks. A new packet must correct this and
   capture full diagnostics; r1 has no retry.
2. **Major:** current export checks ignore source row/path and do not equate
   canonical endpoint or intern/export node indices. Swapping sibling exported
   ports can pass after fixing owner lookup; the second origin is never joined.
3. **Major:** canonicalization loses the allocated-to-representative relation;
   tests require the representative number to equal the allocated row. The
   recorder also identifies symbolic tails but not the two delegated signature
   port allocations, and does not assert the required parameter-row offset.

The reviewer verified all pinned artifacts, feature-correct raw Cargo receipt,
all 11 extension audit blocks and all 12 reused SourceOrigin audit blocks. The
review was read-only, with no builds or remaining processes.

## Disposition and next seam

Keep the Rust recorder/test changes provisional and test-only. No solver,
preflight, recovery, API, semantic or expected-output change is authorized by
this result. Preserve the three new reviewer findings for the next bounded
packet: fix owner identity diagnostics; relate every original occurrence/path
to the actual exact-owner export including canonical node/port identity; record
the allocated-to-canonical transport and each delegated port allocation. Keep
the universal native/source bridge and original parent OPEN. No source-qualified
counterexample or theorem closure was found.

Static `python3 tools/agent_sprint.py check` passed after synchronizing the
frozen worker/reviewer receipts and exact lease hashes. The source lane's
`git diff --check` passed. These checks are not independent review or proof of
compiler semantics. Only the primary performs Git integration.
