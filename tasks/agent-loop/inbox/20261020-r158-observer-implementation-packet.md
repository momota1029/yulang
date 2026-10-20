# R158 implementation packet — JSONL observer sink

Status: frozen implementation detail for independent prospective review. No source files edited and no build, test, CLI, parser, or sample execution performed while preparing this packet.

## Identity and exact reviewed inputs

- Contract R158 rev1: `tasks/agent-loop/sprints/yulang2-types-console-registration-observer-20261020-r158.md` (hash recorded in `current.json`; contract must be updated with this packet hash before review).
- R157 CLEAN taxonomy: `tasks/agent-loop/inbox/20261020-r157-observer-taxonomy.md`, SHA-256 `43990cc91363d3a909d06b6deb613ad17dfeaea5475dedf381a0801940fbd3f4`.
- R157 closeout: `notes/progress/2026-10-20-r157-closeout.md`, SHA-256 `55123adc13a96a8bf57c42917017f7ac6321240b28d3b56eef9af242124e9416`.
- Y2 oracle commit: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- `crates/sources/src/lib.rs`: blob `38d85d7dbb76bca11917963af52f72b17769e3c8`, SHA-256 `1738881e4e177c3d54cfc6f258c3ed1e2fe6d38df85738e3d49a78472721bbdf`.
- `crates/infer/src/module_map/mod.rs`: blob `0e20fedcfef410b647b3fc90e70afa3fc0cb73e6`, SHA-256 `05415473b824ce540207e694bf35883536cb5ef0ec67e8dae12f943411388134`.
- `crates/infer/src/module_map/finish.rs`: blob `d7f12816d99d1e410daf2fc7323598082ba39a33`, SHA-256 `e66f9cf348a6d382288d05d368530a04ec7da0d8bd4073fd19191b36ab2708e6`.
- Read-only `crates/sources/Cargo.toml`: SHA-256 `dee68364690ddb824a9d335abf927821cc32ba1ecf876e803be8e661fb4ddd23`.
- Read-only `crates/infer/Cargo.toml`: SHA-256 `3cd89c9b52a3e0d4d0e74c985b53f9b29b41f426141703a30a58486a3fc8d330`.

The three source files at `/tmp/yulang2-r156-observer/oracle/` still match these hashes. The `infer -> sources` dependency and existing `serde`/`serde_json` declarations establish the serialization seam. No Cargo manifest or lockfile path is writable.

## Exact output and sink API shape

Use one process-global sink in `crates/sources/src/lib.rs`, shared by `LoadedFile` and `infer` callsites through the existing crate dependency. Expose a small API equivalent to:

```rust
pub fn loaded_witness_enabled() -> bool;
pub fn write_loaded_witness<T: serde::Serialize>(record: &T) -> Result<(), LoadedWitnessError>;
```

`loaded_witness_enabled` reads `YULANG_LOADED_WITNESS_OUT` and returns true only for the exact two path strings `/tmp/yulang2-r156-observer/out/types.jsonl` and `/tmp/yulang2-r156-observer/out/console.jsonl`. With the variable absent or any other value, return disabled; do not open/create a file. Callers check this before constructing, sorting, traversing, or serializing observer DTOs. The write API revalidates the same path and uses the same process-global state.

The sink owns one lazily initialized append-only `File` and one `Mutex` protecting each full record write. While holding the lock, serialize with `serde_json::to_vec`, write all encoded bytes, then write exactly one newline. Do not interleave bytes from concurrent LoadedFile and registration events. Preserve the real source/registration chronology produced by the call order; do not sort registration events after capture. Assign an event ordinal under the same lock if the record schema uses it, while preserving the actual stored `ModuleOrder` separately.

Records are serde DTOs with a tagged `event` field and three variants: `loaded_file`, `registration_event`, and `observer_failure`. Keep schema field names and meanings from the CLEAN R157 taxonomy. A `loaded_file` DTO retains module path, band path, exact UTF-8 source string and byte length, deterministic initial operator table entries, and a structural CST preorder of node/token kinds and exact token text. A registration DTO retains site ID, event kind, module/path and band join when available, name, DefId, visibility, actual returned/stored ModuleOrder, event ordinal, exact span or span-status, and the separate `origin_provenance` tag. Preserve all twelve producer sites exactly as mapped in R157; copied mode's `suppressed_by_copy` status has precedence. Source spans are locations, not proof of direct declaration authorship.

## Failure behavior and noninterference

No observer failure becomes a source diagnostic, return-value change, altered registration order, or changed compiler success/failure. On serialization, lock, open, or write failure, return an error to the callsite, emit a clear stderr marker prefixed `YULANG_LOADED_WITNESS_FAILURE`, and mark that witness invalid. Best-effort append an `observer_failure` DTO through the same sink if the sink remains usable; never claim a complete witness after any failure. Keep partial output for diagnosis. Do not panic, silently skip an event, or change normal compiler error handling.

When observation is disabled, callers must branch before allocating observer DTOs, walking CSTs, sorting operator entries, acquiring locks, or touching the output path. This observer is diagnostic-only and must not affect public APIs beyond the narrowly scoped helper, source values, parser state, module contents, or compiler result.

## Exact write lease and stop conditions

Implementation writes only these three files in `/tmp/yulang2-r156-observer/oracle/`:

- `crates/sources/src/lib.rs`
- `crates/infer/src/module_map/mod.rs`
- `crates/infer/src/module_map/finish.rs`

One `implementer` receives 360 seconds only after independent CLEAN review. No build, test, CLI/parser/sample execution, dependency edits, Y3 edits, expected-output edits, or extra paths. Stop before expanding scope if the pinned source does not support the stated API or a behavior-preserving callsite cannot be maintained. Freeze the exact diff and changed-file hashes for fresh independent code review.
