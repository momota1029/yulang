# R160 implementation packet — Rust types and anonymous joins

Status: frozen for independent prospective review. Archive creation, hash verification, and path inventory were completed by Luna before any R160 implementation write. No compiler, tests, builds, or sample commands ran.

## Exact inputs

- Contract: `tasks/agent-loop/sprints/yulang2-types-console-registration-observer-20261020-r160.md` (exact SHA-256 in `current.json`).
- R159 review: `notes/progress/2026-10-20-r159-code-review.md` (hash in `current.json`).
- R159 closeout: `notes/progress/2026-10-20-r159-closeout.md` (hash in `current.json`).
- R157 CLEAN source registration taxonomy: `tasks/agent-loop/inbox/20261020-r157-observer-taxonomy.md`, SHA-256 `43990cc91363d3a909d06b6deb613ad17dfeaea5475dedf381a0801940fbd3f4`.
- Immutable pristine tree: `/tmp/yulang2-r160-observer/baseline/`.
- Working tree: `/tmp/yulang2-r160-observer/oracle/`.
- Y2 commit and original source/manifest pins are listed in the R160 contract.
- R159 candidate overlay hashes verified before transfer: sources `4b1d110923f0d1e885fbdbbb98c16e8ea7e7a0d68093a5c93b277c1733cdd1c9`; module_map `3e545e6f1412fde1287e9a916314995d42f730bf018f3a25213ea07757fca2ee`; finish `33f3e33b051a56f9e96aa601ccae0350f0b94d2020067fdf609ee07eba54b891`.
- After overlay, recursive baseline/working comparison shows exactly the three permitted source paths differ; no `.git` or `target/` exists.

## Exact writes and output allowlist

Write only:

- `/tmp/yulang2-r160-observer/oracle/crates/sources/src/lib.rs`
- `/tmp/yulang2-r160-observer/oracle/crates/infer/src/module_map/mod.rs`
- `/tmp/yulang2-r160-observer/oracle/crates/infer/src/module_map/finish.rs`

The environment variable remains `YULANG_LOADED_WITNESS_OUT`; only `/tmp/yulang2-r160-observer/out/types.jsonl` and `/tmp/yulang2-r160-observer/out/console.jsonl` are valid future values. This allowlist is a path validation only; no output directory/file creation or observer invocation is authorized.

## Required fixes

1. In the registration DTO constructor, keep the owned `ModulePath` local alive and pass a reference matching the field type. Confirm the serialization lifetime/type from pinned source; do not stringify or alter compiler ownership to silence the mismatch.
2. In CST recursion, accept the pinned Rowan `GreenNodeData` reference yielded by `children()`. Preserve balanced node enter/token/leave shape, token kind, exact text/range, and order. Do not flatten the tree.
3. For each event, keep actual `ModuleId`. Authenticate a named module path only when the module ancestry has a real declaration join. Anonymous role-implementation scopes made by `new_anonymous_child_module` have no named declaration and default band; mark module-path and loaded-band joins explicitly unavailable in these cases. Do not treat an empty/truncated path or default band as available identity. Do not guess from source span/name. Preserve established joins for named modules.

Retain the R158/R159 accepted behavior: all twelve registration appends; correct event order, DefId, visibility, span, and copied-source provenance; no observer-only clone/traversal/DTO allocation/lock before enabled branches; structurally unambiguous CST; bounded best-effort `observer_failure` under the already-held usable sink without recursive logging; failure latch and stderr marker; exclusive `create_new` output semantics; unchanged compiler diagnostics, results, registration behavior, and errors.

## Review seam and stop rule

After writes stop, freeze SHA-256 values and recursively compare the working tree against the immutable pristine tree. Any difference outside the three leases is blocking. The fresh independent reviewer must inspect exact code against the R159 review findings, pinned type definitions, named and anonymous scope constructors, and all twelve taxonomy sites. No builds, tests, parser/CLI/sample execution, output capture, manifest changes, or extra paths. Stop if another owner/path or semantic change is needed.
