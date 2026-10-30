# R34 Rust owner-token handoff

Assignment: `/root/effect_permission_r31_rust`. Exact write leases:
`tools/inference-playground/src/runtime/program.rs`,
`tasks/agent-loop/artifacts/native-snapshot-owner-r34.patch`, and this handoff.
Sprint: `EFFECT-PERMISSION-NATIVE-SNAPSHOT-OWNER/20261031-R34`.
Requested model/effort: `gpt-6-luna` / `high`; observed model/effort: UNKNOWN.
Fresh Rust cap: 1,600 seconds. Active interval was not instrumented and is
UNKNOWN; no R33 time was transferred. No descendants were started. Writes are
stopped.

## Implemented source owner

`RuntimeProgram` now stores a private `HirSnapshotToken(Arc<HirModule>)` beside
its existing `_hir: Arc<HirModule>`. The sole struct construction in
`from_hir_with_roots` clones both fields from the same received `hir` Arc.
`from_hir` forwards to that constructor, and `from_candidate_world` also
forwards to it after building its evidence/roots. Thus all construction paths
retain the same source HIR allocation for the ordinary owner and token.

The token exposes only `identifies_same_snapshot`, implemented with
`Arc::ptr_eq`, and `RuntimeProgram::hir_snapshot_token`, which returns an
owner-issued clone. The tuple field is private; the type has no `Debug`,
structural `Eq`, serialized-index, or spelling-derived identity. Cloning a
token clones the strong Arc and keeps the exact HIR allocation alive. A token
made from a separately allocated but structurally equal `HirModule` compares
foreign by `Arc::ptr_eq`. The existing operation-v1 numeric raw pointer is not
reused as this token.

## Source and integration evidence

Baseline `program.rs` SHA-256 was
`6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907`; current
source hash is reported in the parent receipt. The pinned HIR module dependency
remains SHA-256
`6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`.
R30 archive SHA-256 is
`5c3c991dec9e54ad3e2665a1c722a0abf2d80a9efe719664606824558351a790`;
member hashes are `machine.rs`
`b74c8345e6e07155f482440bb9299b5fc12763accb666ca8f543156dd4a87425` and
`receiving.rs`
`55b468cda3c3cf8180647a6429da28fc70badf7a371bf1b327539c8556b9b0f2`.
Those archive members were streamed without extraction. The live quarantined
`machine.rs` and `receiving.rs` were not read or touched.

The patch artifact contains the exact `program.rs` source diff and a clearly
separate future integration proposal based only on those pinned archive
members. That proposal attaches cloned owner tokens to the request, selected
Catch, and callback-route evidence records; checks all tokens against the
machine's owner before HIR-relative lookup; and replaces panic/default lookup
with checked family/operation failures and whole-row fallible preservation.
This integration is not applied or compiled. The opaque Arc token itself has
no JSON representation in this patch; binding an offline Lean/certificate token
to the Rust capability remains OPEN and needs its own source-grounded design.

Artifact-only correction: regenerated the owner-diff section directly from the
exact current `git diff -- tools/inference-playground/src/runtime/program.rs`,
restoring the omitted `Some(dictionaries)` context and correct hunk counts. The
quarantined-consumer proposal suffix was preserved byte-for-byte. `program.rs`
was not modified by this correction and remains SHA-256
`9823cd8d5c972e0c6ec2766d66f9d21c6564727317bc2646d2480a9e85132f74`. Corrected
patch SHA-256: `2e8de543a4c721d33a775102961c930b82754d47411ae6c4f3ec4ea39b2004c3`.

The selected arm remains a typed `SourceNodeKey` internally, but the archived
serializer renders it with Debug, which omits parse identity, green allocation,
and source start. The token does not repair that lossy arm serialization. The
patch proposal keeps this boundary explicit.

## Checks and limits

Read-only checks: verified the pinned `program.rs` and `HirModule` source
hashes; inspected all `RuntimeProgram` constructor paths and confirmed the one
struct initializer in `from_hir_with_roots`; inspected the token field,
accessor, clone, and `Arc::ptr_eq` implementation; streamed and hash-checked
the pinned archive members for the quarantined integration proposal. No Cargo,
compiler, test, runtime, Lean/Lake, target/cache, extraction, worktree/copy,
scratch, log, environment, external directory, or Git mutation was used.

No native serializer integration, compilation/runtime result, source-to-Lean
proof, authenticated request/Grant/History, original A/B closure, whole-
language hygiene, soundness, principality, termination, or production result
is claimed. Independent review is pending; this producer has not self-reviewed
or certified the result.
