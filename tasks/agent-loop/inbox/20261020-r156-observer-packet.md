# R156 Stage A — exact observer implementation packet

Status: frozen preparation result for prospective independent review. No code, scratch directory, build, test, parser/sample execution, or expected-output change was made. Y2 source tree remained read-only.

## Contract and input identity

- R156 contract rev2 SHA-256: `eb3c281dc0777d5517510327c2bcc14700eee88bb8c063056ea09bce03071f62`.
- Y2 immutable baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Sample source: `web/playground/src/main.ts`, blob `e6bec9fe44d673ccbf98af078ef4562c9267ef6c`.
- Exact extracted Types bytes: 142 bytes, SHA-256 `8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`.
- Exact extracted Console bytes: 92 bytes, SHA-256 `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`.
- Standard-library input set: exact 40-file closure in `tasks/agent-loop/sprints/yulang2-types-console-20261020-r149-rev10.md`, SHA-256 `31214917352b673c7467873b60d5db8e470e4d16c8370d882c266a7fcef5b3e9`. Each source blob matches the Y2 commit; no files outside that closure are added.

## Exact pinned source owners

All paths below are from the immutable Y2 baseline. Hashes are Git blob IDs.

| Path | Blob | Observation role |
|---|---|---|
| `crates/sources/src/lib.rs` | `38d85d7dbb76bca11917963af52f72b17769e3c8` | LoadedFile construction, bytes, band/module paths, initial operator table, CST |
| `crates/yulang/src/main.rs` | `1e56d89b9b5ac3128d019963b30f5359d39037d9` | Existing `dump-poly-std` command entry |
| `crates/yulang/src/support.rs` | `72cc35be6757a3cbb1f80e44d3db548d84af7a6c` | Existing standard-source collection route |
| `crates/yulang/src/source/mod.rs` | `6472d8fb4268bdd08757eef4aeaf1bf65fedc2b0` | Collected source to loaded source to lowering route |
| `crates/infer/src/lib.rs` | `3c967f3641f381330c47ce487ee2df3c6265ade4` | ModuleTable and identity types |
| `crates/infer/src/module_map/mod.rs` | `0e20fedcfef410b647b3fc90e70afa3fc0cb73e6` | Source declaration registration producers |
| `crates/infer/src/module_map/finish.rs` | `d7f12816d99d1e410daf2fc7323598082ba39a33` | Source declaration registration producers |
| `crates/infer/src/module_table/mod.rs` | `1b54bd6c9335fbaa1f8b56de9b5014f3d0d17558` | Shared ordered append, visibility, DefId storage |
| `crates/infer/src/module_table/compiled.rs` | `51d49ff880e4059819a5ae7c869d1ac1bcbb56cb` | Compiled route, to exclude from source records |
| `crates/parser/src/op.rs` | `8aae15f3a188bbed9fe6c48656f7bc4969235774` | Initial OpTable entry representation |

`LoadedFile.op_table` is the initial table supplied to full parsing. Parser-local operator updates happen during parsing; the candidate must label initial table identity/content separately and must not claim final parser state. Source records originate in `module_map/mod.rs` and `module_map/finish.rs`; `insert_value_with_span` is shared with compiled insertion and is not independently source-qualified. The existing no-cache `dump-poly-std` route collects real standard sources and lowers those sources, avoiding compiled-cache insertion.

## Candidate exact observer paths and output

Isolated copy root: `/tmp/yulang2-r156-observer/oracle/`, a content-identical export of the pinned Y2 commit with no `.git` metadata and no copied `target/`. Only these copied files may be modified:

- `/tmp/yulang2-r156-observer/oracle/crates/sources/src/lib.rs`
- `/tmp/yulang2-r156-observer/oracle/crates/infer/src/module_map/mod.rs`
- `/tmp/yulang2-r156-observer/oracle/crates/infer/src/module_map/finish.rs`

Instrumentation is gated by `YULANG_LOADED_WITNESS_OUT`; absent that variable it emits no records and takes no branch affecting compiler state. The only accepted output values are the two exact allowlisted paths `/tmp/yulang2-r156-observer/out/types.jsonl` and `/tmp/yulang2-r156-observer/out/console.jsonl`; reject any other value before opening a file. Record variants:

1. `loaded_file`: ordinal, exact module and band paths, source UTF-8 byte length and SHA-256, initial operator table entries in deterministic key order, CST kind/text-derived source mapping identity (node kind plus byte range/text hash), parse errors if available.
2. `source_registration`: source caller kind (`module_map` or `finish`), owning module path/band join, DefId, name, visibility, ModuleOrder, and original source span/range when present. Emit after every real append, retaining duplicate names and chronological order.
3. `failure`: phase and error, without truncating earlier records.

The reviewer must check JSON escaping, stable ordering, operator entry traversal, source identity joins, and no output-directory writes when the env var is absent. The shared `compiled.rs` path is not instrumented. No record is reconstructed from `dump-poly` text.

## Exact future invocation (not run or authorized here)

After copying the two exact extracted strings to `/tmp/yulang2-r156-observer/input/Types.yu` and `Console.yu`, and materializing only the pinned 40-file closure under `/tmp/yulang2-r156-observer/lib/`, use one source-only invocation per sample:

```sh
YULANG_LOADED_WITNESS_OUT=/tmp/yulang2-r156-observer/out/types.jsonl \
cargo run --offline --manifest-path /tmp/yulang2-r156-observer/oracle/Cargo.toml \
  -p yulang -- --no-cache --std-root /tmp/yulang2-r156-observer/lib dump-poly-std \
  /tmp/yulang2-r156-observer/input/Types.yu
```

Repeat once with `YULANG_LOADED_WITNESS_OUT=/tmp/yulang2-r156-observer/out/console.jsonl` and `Console.yu`. The explicit `--no-cache` is required because CLI global options default cache use on; it forces the source-loading path through the observer. This is a future witness capture, not a test suite or general build. Preserve both stdout/stderr, exit status, partial JSONL and exact input hashes. One Cargo process at a time; 240-second wall bound for a later separately authorized run. No automatic retries. Any source, input, or expected-output hash mismatch aborts before execution.

## Cleanup and remaining authority

The sole scratch owner is Luna. Remove only `/tmp/yulang2-r156-observer/` after a separately reviewed witness and its hashes are preserved, or retain the exact patch as a frozen provisional candidate for further work. No scratch root exists yet. This packet grants no implementation, build or execution lease. Independent Stage A review is the next step; implementation remains conditional on that review and Luna’s exact-path grant. Parent gates remain OPEN.
