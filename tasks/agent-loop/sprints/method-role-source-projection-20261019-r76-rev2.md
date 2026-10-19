# R76 rev2: method and declared role/impl source projection

Status: **ACTIVE**. Luna activated after source-authority and lease reconciliation. Baseline HEAD and origin: `d21c8eb3a87e43dd441474c9f138e71b1d8372ff`. R75 is CLOSED_UNFINISHED; preserve its frozen snapshot and all 21 worktree-manifest entries. No R75 work, elapsed time, leases, or failed verification carries into this sprint.

## Goal and parent contribution

Advance breadth in the ongoing compiler implementation by producing a constructor-owned, inert HIR source input for selected method/member syntax and declared `role`/`impl` source occurrences, with a constructive correspondence proof. This is an independent prerequisite for later method/role inference, not a direct closure of computation-forwarding preservation, evaluator correspondence, or Simple-sub A/B. Those parents remain OPEN 0→0; R50 remains NOT_ADOPTED.

The user's portfolio direction authorizes this broader research outcome. It does not settle ordinary effect/handler semantics or adopt method dispatch, declared-role selection, receiver typing, candidate eligibility, or implementation resolution. The charter's semantic-selection gate remains in force.

## Fixed source cases and boundary

Use only these parser-produced cases from a caller-selected `ShadowArtifact`:

1. A complete `FieldTail` containing exactly the accepted dot and identifier tokens, attached within its enclosing expression/`OperatorChain`; preserve the tail's artifact-branded position, spelling, exact member-token range, full tail range, parent/child order, and the raw preceding receiver structure. Do not classify it as method dispatch.
2. Direct `RoleDeclaration` and standalone `ImplDeclaration` nodes, preserving their artifact-branded occurrence identity, exact range, parent, and source order. Expose source forms as unresolved declarations; do not infer membership, ownership outside the retained syntax tree, or role identity in the semantic `RoleId` sense.
3. Malformed/recovery nodes and unsupported receiver shapes remain explicit refusals; they are not silently omitted or repaired into accepted cases.

The projection may index the exact parser-owned positions already retained by `ShadowArtifact`; it must not synthesize identities from labels, ranges, or successful solver output. Scope is the authentic lexical/syntax parent chain retained by the parse artifact, not a resolved namespace. Reverse reconstruction claims cover retained syntax structure and identities only, not source text, typing, or runtime behavior.

## Required outcome and proof

Expose one immutable HIR-facing source input with exact, checked lookup/enumeration for the fixed constructors above. Prove source-to-projection coverage and reconstruction for those cases, including identity equality, receiver association, token spelling/range, declaration occurrence and lexical-parent preservation. Prove unresolved cases stay unresolved. State the first unavailable premise for any candidate typing/selection constraint and stop that investigation there; no constraint or semantic rule is added by this sprint.

Falsifiers: omitted or duplicated selected occurrence; wrong preceding receiver structure; unequal positions collapse; spelling, range, child order, or parent/scope changes; malformed input becomes accepted; field syntax is labeled dispatch; declared Role/Impl position is treated as resolved semantic identity; or proof obtains ownership from its own output labels.

## Exact leases

Luna implementation and integration owns:
- `crates/yu-hir/src/module/local_source.rs`
- `crates/yu-hir/src/shadow.rs`
- `crates/yu-hir/src/module.rs`
- `crates/yu-hir/src/lib.rs` (only the exact HIR test-module registration)
- `crates/yu-hir/src/tests/shadow_method_role_source.rs` (new)
- `notes/progress/2026-10-19-r76-method-role-implementation.md`
- `tasks/agent-loop/inbox/20261019-r76-implementation.md`

Sol proof owns:
- `notes/theory/2026-10-19-r76-method-role-source-proof.md`
- `tasks/agent-loop/inbox/20261019-r76-proof.md`

The independent fresh compiler and spec reviewers receive read-only access to one frozen R76 snapshot and write only their separately assigned handoffs. No path in the R75 manifest or any other source path is leased. No directory or wildcard lease is implied.

## Verification and resources

One HIR-only command is authorized after the implementation and proof packet is frozen:
`CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-hir --lib shadow_method_role_source -- --nocapture`
A failed command is recorded with its exact exit and first failure; no retry or repair under this revision. This command does not touch the R75 solver feature path. Static formatting/hash checks are bounded to the leased outputs.

Total cap: 2400 seconds, zero carryover. Luna implementation/integration 900 seconds including the one bounded command; Sol proof 600; fresh compiler review 300; fresh spec review 300; integration/reconciliation reserve 300; Astra 0. Stop projection on a coverage/fidelity failure, verification failure, dependency drift, or resource boundary. Stop selection investigation at the first exact missing authority premise; independent projection work may continue within the fixed lease and budget.

## Pinned authority and implementation inputs

Baseline and source pins are inherited from the frozen R76 proposal `tasks/agent-loop/sprints/method-role-source-inference-20261019-r76-proposal.md` (SHA-256 `a04509d5a4291fe2dc94fddd3ad9c57da7a88cae9ff9b9d108c3bd3a02544cbd`) and its R75 worktree manifest (SHA-256 `110fdb37e691fc6014b5177e40b0d406d9c32c65d4eed94a75f3aaa694235418`). Inherited authority/source pins were checked against live bytes at activation. Additional controlling inputs:
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md` SHA-256 `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- `crates/yu-hir/Cargo.toml` SHA-256 `a97f52fc6b9e577f23be4160ecdda9693bec8fe48c626d0e9b7c0e3b0c6fe8d1`.

The frozen design charter keeps selection/resolution at a later gate. The syntax reference only defines `.identifier` as `FieldTail` and excludes resolution, types, and execution. Architecture index keys are not selection laws. No approved method or declared-role selection law has been found; R76 does not depend on finding one before projection begins.
