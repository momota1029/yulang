# R163 fresh-output loaded-registration witness packet

Status: revision 1, frozen for independent prospective review. Only packet preparation and hash-preserving archive creation occurred; no R163 build or sample command has run.

## Exact R162 evidence retained

- R162 build binary SHA-256 `302c06e00dcb683471e670c55df359419ae6bd2eae2c75678a87642c3fa7df60`, build status 0.
- Partial Types JSONL `/tmp/yulang2-r160-observer/out/types.jsonl`, SHA-256 `413fd2e4a260f9a16b5a58b811cf391f349ded5095c09a9eccfd38992a279eda`, 730 complete JSON lines: 41 loaded-file records plus 689 registration events, last ordinal 729. Capture timed out at 60s (status 124); do not treat registration events as complete or reuse/overwrite/delete this path.
- R161/R162 logs and scratch remain preserved. No R149 runtime host-output claim was observed.

## Source/proof analysis lease

Read only the R162 JSONL, exact R161 sample/library inputs, and R152–R154 relations. Write only `notes/theory/2026-10-20-r163-r162-loaded-file-audit.md`. Authenticate each `loaded_file` by reconstructing token text and UTF-8 byte spans, checking balanced CST nesting and `source_bytes`, matching 40 library hashes to the exact manifest, and matching the Types loaded source to `use std::prelude::*\nmod std;\n` plus the exact pinned Types input. Report the partial registration prefix separately; no census, inference, runtime, or parent-theorem closure claim. Do not run compiler/tests or edit sources.

## Fresh candidate and allowlist

- New oracle archive `/tmp/yulang2-r163-observer/oracle/` differs from the reviewed R162 candidate only in two output-path string constants in `crates/sources/src/lib.rs`.
- R163 `sources/src/lib.rs` SHA-256 `b73cc664f01757f2fa29a8b67f260edbde782ea586719c8fef17005d3b76ff6a`.
- Frozen module map SHA-256 `0b8bddf74564fa754c9cf3df891396d7c1b793d9773f117c292a84223348727f`; finish SHA-256 `33f3e33b051a56f9e96aa601ccae0350f0b94d2020067fdf609ee07eba54b891`; Cargo.lock SHA-256 `11b30ff69e3c27978cba1e827cb322a641666f19602a80d42ce7242c14eac6cb`.
- Fresh observer outputs are `/tmp/yulang2-r163-observer/out/types.jsonl` and `console.jsonl`, absent. R160/R161/R162 outputs and scratch are immutable.
- Inputs remain the exact Types/Console samples and 40-file closure in `/tmp/yulang2-r161-witness/`; pinned hashes are in the R163 contract.

## Conditional exact execution

Independent CLEAN review is required before a fresh Luna grant. Scratch: `/tmp/yulang2-r163-witness/{cargo-home,target,tmp,logs}/`, copied offline cache and fresh target/tmp/logs. One `cargo build --offline --locked -p yulang`, 480s timeout, one process/job; then, only on build success, Types and Console `dump-poly-std` serially, up to 300s each, using `--no-cache --std-root /tmp/yulang2-r161-witness/lib`, exact input paths and new R163 allowlist. New scratch cap 8 GiB. Preserve inventory; no retries or cleanup.

A Types timeout may be followed by Console only after process cessation is confirmed and the failure is invocation-local. No rerun of Types. Observer/schema/provenance failure stops both. These commands establish static source/lowering evidence only; they do not execute host writes. No test suite or `run-mono-std`.

Reviewer checks the exact two-constant diff, R162 prefix hash/count, loaded-file/source/manifest/CST authentication, sample and dependency pins, exclusive output absence, command/write bounds, 1,800-second arithmetic, timeout continuation rule, and static/runtime evidence separation. Parent gates remain OPEN.
