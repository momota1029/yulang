# R157 Stage A — twelve-site observer taxonomy

Status: frozen read-only preparation artifact. No source edit, build, test, parser/sample execution or output file creation occurred. R156 implementation was stopped before writes and its isolated archive still matches the exact three source hashes below.

## Identity and reviewed inputs

- R157 contract rev2 SHA-256: `cffe8c7aef6eb285db4f1f83ce3e84e9dfb1ca50f71db0df5926c03eb325ef8c`.
- R156 closeout SHA-256: `3601d3dbde75387dca4984e4282ac523f291e8d288e00ef1d5dce95b3c5b3078`.
- R156 source/input packet SHA-256: `a7eeb9d5087bd0d219a8601c497cc35205f7107fb54486de6631d2e2df375fa3`.
- Y2 oracle: commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- `crates/sources/src/lib.rs`: blob `38d85d7dbb76bca11917963af52f72b17769e3c8`.
- `crates/infer/src/module_map/mod.rs`: blob `0e20fedcfef410b647b3fc90e70afa3fc0cb73e6`.
- `crates/infer/src/module_map/finish.rs`: blob `d7f12816d99d1e410daf2fc7323598082ba39a33`.
- Shared storage `module_table/mod.rs`: blob `1b54bd6c9335fbaa1f8b56de9b5014f3d0d17558`.
- Compiled-route control `module_table/compiled.rs`: blob `51d49ff880e4059819a5ae7c869d1ac1bcbb56cb`.

All three source files at `/tmp/yulang2-r156-observer/oracle/` have SHA-256 equal to the R156 stop artifact and Git blob IDs equal to the Y2 baseline. The source observer component is limited to the first three files; the compiled control is read-only and its insertion route stays excluded.

## Event taxonomy — every append, provenance kept separate

Every row below emits a `registration_event` after the actual `insert_value_with_span` append. `producer_site` records physical location and `event_kind` records the enclosing producer. Neither field by itself claims direct source authorship. Preserve `module`, `name`, `DefId`, `visibility`, exact returned/stored `ModuleOrder`, event ordinal, and exact `SourceSpan` or explicit `span_status`.

| Site | Enclosing producer | `event_kind` / origin evidence |
|---|---|---|
| `module_map/mod.rs:393` | OpDef lowering | `operator_decl`; direct CST range `info.source_range` |
| `module_map/mod.rs:519` | `register_binding_values` | `binding_value`; optional CST name range |
| `module_map/mod.rs:634` | role implementation method | `role_impl_method`; optional method-name range |
| `module_map/mod.rs:666` | role implementation binding | `role_impl_binding`; optional binding-name range |
| `module_map/mod.rs:1141` | `register_synthetic_value_with_span` helper | `synthetic_value_helper`; caller-dependent exact span or `absent` |
| `module_map/mod.rs:1205` | role companion method | `role_companion_method`; optional method-name range |
| `module_map/mod.rs:1240` | role companion binding | `role_companion_binding`; optional binding-name range |
| `module_map/mod.rs:1335` | act companion operation | `act_companion_operation`; record exact Direct/CopiedSourceExport/CopiedSourceInternal mode and span status |
| `module_map/mod.rs:1364` | act companion method | `act_companion_method`; record exact mode and span status |
| `module_map/mod.rs:1402` | act companion binding | `act_companion_binding`; record exact mode and span status |
| `module_map/finish.rs:88` | type companion method | `type_companion_method`; optional method-name range |
| `module_map/finish.rs:120` | type companion binding | `type_companion_binding`; optional binding-name range |

Use separate `origin_provenance` values `direct_cst`, `source_derived`, `synthetic_helper`, `copied_source`, `span_unavailable`, and `unknown` only where established by the exact producer and evidence. Preserve the physical `producer_site` for every event even when origin is unavailable. For copied-source modes, retain the actual mode and set `span_status=suppressed_by_copy` with precedence even though the stored span is `None`; do not omit or reclassify the event as a direct source declaration. For other events with `source_span=None`, retain the append and record `span_status=absent`. Span presence alone is evidence of location, not proof that a generated value is the direct declaration named by that span.

The source registration stream is **not** a census of only directly authored declarations. It is the complete ordered stream for this reviewed source-route component, with identity/provenance uncertainty explicit. No completeness claim is made for callsites outside these pinned files or for compiled insertion.

## Loaded source and identity records

At each actual `LoadedFile` construction, emit module path, band path, exact UTF-8 source string, source byte length, initial operator table entries in deterministic key order, and a structural CST walk (preorder node/token kinds and exact token text). The captured source string and CST structure allow an independent verifier to compute SHA-256; do not claim an in-process SHA-256 because the pinned `sources` crate does not depend on a hash crate. Keep the initial loaded `op_table` separate from parser-local operator updates. Map source spans back to the exact loaded source file/range; retain absence rather than guessing.

JSONL variants: `loaded_file`, `registration_event`, and `observer_failure`. The observer is environment-gated by `YULANG_LOADED_WITNESS_OUT`; only the exact R156 allowlisted values `/tmp/yulang2-r156-observer/out/types.jsonl` or `/tmp/yulang2-r156-observer/out/console.jsonl` are accepted. With the variable absent, output is empty and compiler behavior is unchanged. Serialization/write errors must produce an explicit stderr failure marker and invalidate the artifact; they may not silently skip records. Use `serde_json` in `sources` where already pinned; `infer` has no `serde_json` dependency, so any manual serialization/escaping must be independently reviewed. No Cargo manifest or lockfile edits are in scope.

## Exact candidate implementation and later invocation

Only these three exact files may be modified in the isolated Y2 archive:

- `/tmp/yulang2-r156-observer/oracle/crates/sources/src/lib.rs`
- `/tmp/yulang2-r156-observer/oracle/crates/infer/src/module_map/mod.rs`
- `/tmp/yulang2-r156-observer/oracle/crates/infer/src/module_map/finish.rs`

No `.git` metadata or `target/` is present in the archive. Future exact sample bytes, 40-file closure, and the source-only route are those in the R156 packet. Per sample, later use `cargo run --offline --manifest-path /tmp/yulang2-r156-observer/oracle/Cargo.toml -p yulang -- --no-cache --std-root /tmp/yulang2-r156-observer/lib dump-poly-std /tmp/yulang2-r156-observer/input/{Types,Console}.yu`, with the exact allowlisted output variable. Preserve stdout, stderr, exit status and partial JSONL. CLI exit status alone does not establish error-free lowering. One process at a time; a later execution requires separate authorization and a fixed wall limit. No command is run in R157.

R157 Stage A resources are 120 seconds preparation; no implementation, build or execution grant is included. Independent Stage B review is next. All parent theorem and production gates remain OPEN.
