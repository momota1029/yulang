# R159 implementation packet — correct provisional observer

Status: frozen for one prospective independent review. No source changes occurred during packet preparation. Archive/path inventory was read-only after copying the hash-pinned R158 candidate into the fresh working extraction.

## Exact inputs and scratch layout

- Contract: `tasks/agent-loop/sprints/yulang2-types-console-registration-observer-20261020-r159.md` (rev1; exact SHA-256 is recorded in `current.json`).
- R158 closeout: `notes/progress/2026-10-20-r158-closeout.md` (exact SHA-256 in `current.json`).
- R158 independent review: `notes/progress/2026-10-20-r158-code-review.md` (exact SHA-256 in `current.json`).
- R157 registration taxonomy: `tasks/agent-loop/inbox/20261020-r157-observer-taxonomy.md`, SHA-256 `43990cc91363d3a909d06b6deb613ad17dfeaea5475dedf381a0801940fbd3f4`.
- Fresh pristine Y2 extraction: `/tmp/yulang2-r159-observer/baseline/`.
- Fresh working Y2 extraction: `/tmp/yulang2-r159-observer/oracle/`.
- Pinned source blobs, baseline hashes, overlaid candidate hashes, and read-only manifest hashes are fully enumerated in R159 contract rev1.
- The baseline and working trees were compared recursively after overlay. Exactly three paths differ: `crates/sources/src/lib.rs`, `crates/infer/src/module_map/mod.rs`, and `crates/infer/src/module_map/finish.rs`. Neither tree contains `.git` or `target/`.

## Exact write and future output paths

Implementation may write only:

- `/tmp/yulang2-r159-observer/oracle/crates/sources/src/lib.rs`
- `/tmp/yulang2-r159-observer/oracle/crates/infer/src/module_map/mod.rs`
- `/tmp/yulang2-r159-observer/oracle/crates/infer/src/module_map/finish.rs`

The environment variable remains `YULANG_LOADED_WITNESS_OUT`; only the future values `/tmp/yulang2-r159-observer/out/types.jsonl` and `/tmp/yulang2-r159-observer/out/console.jsonl` may be accepted. These output paths are frozen solely so the observer helper rejects all other values. This packet does not authorize creating output files, invoking the helper, or running either sample.

## Required code corrections

1. **Move-after-use:** at the R158 `module_map/mod.rs` value-binding producer, do not move a `Name` and then borrow it. Preserve compiler-owned name data exactly; make only an enabled-branch observer snapshot if required.
2. **Disabled-mode noninterference:** audit all twelve producers and LoadedFile construction. Branch on the exact observer-enabled state before every observer-only `Name`/`SourceSpan` clone, source/CST traversal, operator-table sort, DTO allocation, ordinal lock, serialization, or path/file operation. The disabled branch must execute the original compiler operation and avoid observer work.
3. **Unambiguous CST:** serialize enough structure to distinguish every tree with the same token sequence. Prefer balanced node-enter/node-leave events, or include exact child counts and nesting depth. Preserve node/token kind, exact token text/range, and traversal order.
4. **Failure DTO:** add a tagged `observer_failure` record. On serialization/write failure, latch the witness invalid, emit the required stderr marker, preserve partial output, and make one bounded best-effort attempt to append the failure DTO directly through the already-held usable sink without recursion or re-locking. Do not require an in-stream record if sink creation fails or the handle is unusable. Never change source diagnostics, return values, registration order, or compilation outcome.
5. **Module/band/source join:** for each registration event, record the actual module/file and band identity when available from the producer context. When no join exists at a site, emit an explicit unavailable status; never infer a module or band from the span. Keep these joins separate from direct/source-derived/synthetic/copied provenance.
6. **Path provenance:** preserve the R158 exact output `create_new(true)` rule: one invocation owns one file; existing path => failure marker and invalid witness, without append, truncate, delete, or retry. Keep each successful JSON record and newline under one mutex and preserve actual stored `ModuleOrder` independent of sink ordinal.

Retain the complete R157 twelve-site mapping, duplicate records, visibility, DefId/name, exact span state and copied-mode suppression precedence. Compiled insertion stays excluded.

## Review and stop rules

After implementation, freeze exact hashes and run a read-only recursive baseline-vs-working comparison. Any difference outside the three leased files is a blocking path-scope failure. The independent reviewer must inspect the actual code and verify each correction above against the exact R158 findings, not infer closure from a summary. No tests, builds, CLI, parser, sample, or output runs are authorized. Stop on unclear owner data or any need for another path/dependency.
