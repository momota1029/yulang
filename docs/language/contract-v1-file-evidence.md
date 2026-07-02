# Contract v1 File Evidence

This page records evidence for
[Contract v1: File Resource](file-resource-contract.md).

Status on 2026-07-03: **open, Stage 2 native protocol bridge covered**. The
contract box and tag policy exist, and the `file-resource` manifest subset now
covers the public `file::load` / `file::store` / `file::meta` Stage 0 surface,
the Stage 1 source-mock `text_with` protocol fixtures, and the first native
registry parity cases over the same public protocol. Remaining legacy raw /
snapshot operations stay a compatibility window, not the Contract v1 center.
Integer error-code translation has been removed from the `std::io::file` host
bridge. Contract v0 remains closed in
[contract-v0-evidence.md](contract-v0-evidence.md).

## Current Evidence

The repository already has migration canaries for the file host bridge and
public surface:

- `std::io::file::read_text` / `write_text` now project to public
  `file::load` / `file::store` result operations. Source mock handlers can
  intercept those operations under `--host unsupported`, and the native CLI
  host executes the same public operations through the runtime host registry.
- `file_meta { kind, size, readonly }` is now the public metadata shape, and
  the public `file::meta` operation has native registry coverage. `exists`,
  `is_file`, and `is_dir` are pure Yulang wrappers over `meta.kind`; they no
  longer occupy separate host operations.
- The old private `file::meta_raw` integer-code operation has been removed from
  `std::io::file` and from the runtime host manifest. Metadata now enters the
  public surface through `file::meta`.
- `file::read_at` and `file::write_at` now return typed `result ... io_err`
  values at the host act boundary. The public wrappers keep their existing
  throwing surface, but no longer decode integer error codes for range reads
  and writes. Their host manifest surface is `raw-compat` because exact range
  semantics remain provisional rather than the Contract v1 center.
- The contract manifest now mirrors that boundary with a `raw-compat` tag for
  current executable range/raw/snapshot helper canaries, so manifest queries can
  separate compatibility evidence from protocol-center evidence.
- `file::open_text_raw`, `file::open_text_snapshot_raw`, `file::file_flush`,
  and `file::file_snapshot_commit` also return typed `result ... io_err`
  values at the host act boundary. This removes `legacy_err_from_code` from
  `lib/std/io/file.yu` and removes the runtime integer error-code helper.
- `debug host-act-manifest` now exposes a `surface` column. Current operations
  are separated into `contract` and `raw-compat`, so legacy snapshot operations
  are observable as compatibility surface instead of being mixed into the
  Contract v1 protocol surface.
- `debug host-act-manifest` also exposes the supported host operation tier ids:
  `sync`, `suspend-one-shot`, and `suspend-multi-shot`. Current console/file
  operations are still all registered as `sync`; the suspend tiers are the
  manifest vocabulary needed before server branches enter the registry.
- The Evidence VM now owns a root `RuntimeHostScheduler` branch table. It does
  not execute server operations yet, but unit tests lock the first scheduler
  rules needed by the structured concurrency decision: suspended child cancel
  drops the branch, running cancel becomes pending, and parent extent close
  enqueues child cancels. The same table also assigns branch-local operation
  sequence ids so record/replay can identify host operation instances without
  retrofitting the scheduler later.
- `tests/yulang/cases.toml` includes `file_meta_kind`, a
  `file-resource` / `metadata` / `mock-host` runtime canary that checks the
  new public `file::meta` operation under `--host unsupported`.
- `io_err::wrap` converts failed file reads and writes into typed result
  boundaries. The `not_found` and `failed` constructors observed by runtime
  typed-failure cases also have public signature canaries.
- `open_text`, `open`, and `open_in` remain as legacy native snapshot canaries
  for Stage 2 migration, but they are not substitutes for the Stage 1 protocol
  fixtures.
- `file_buffer` is now ambient-only. It exposes `ambient_get` / `ambient_set`
  for unscoped `file::text` and no longer has scoped `get` / `set` operations,
  reperform transfer arms, or path-matching `same_path` checks.
- The native runtime host registry now registers
  `std::io::file::file_buffer.ambient_get` and
  `std::io::file::file_buffer.ambient_set` as a separate `file_buffer` host act.
  Unscoped `file::text` uses a handler-extent ambient ledger in the native
  runtime and flushes it at the end of a successful run.
- `text_with` is the four-line state-passing protocol:
  load initial text, run a callback `str -> ('a, str)`, store the final text
  only if the callback returns, then return the callback result. The integrated
  IO resource spec now records this protocol shape instead of the earlier
  `ref` callback sketch; future `\my &text ->` sugar should desugar to the same
  protocol.
- `tests/yulang/cases.toml` includes the Stage 1 source-mock protocol set:
  `file_text_with_commit`, `file_text_with_rollback_on_error`,
  `file_text_with_undet_last_write_wins`,
  `file_text_unscoped_handler_discharge`,
  `file_text_mock_matches_native_shape`, and
  `file_text_with_nested_cross_file`.
- Rollback and multi-shot evidence now run through `--host unsupported` source
  handlers over public `file::load` / `file::store`; they no longer depend on
  native temp files or legacy `open_in` snapshot operations.
- `tests/yulang/cases.toml` includes `file_native_protocol_load_store_meta`,
  a native CLI host case that calls public `file::load`, `file::store`, and
  `file::meta` directly, checks the compact roots, and verifies the backing
  temp file contents after `store`.
- `tests/yulang/cases.toml` includes `file_native_meta_file`, which proves
  native `file::meta` and the predicate wrappers report a normal file as
  `file_kind::file` with the expected byte size.
- `tests/yulang/cases.toml` includes `file_native_meta_missing`, which proves
  native `file::meta` reports a missing target through `file_meta.kind` and that
  `exists` / `is_file` / `is_dir` are wrappers over that metadata result rather
  than separate throwing host probes.
- `tests/yulang/cases.toml` includes `file_native_meta_directory`, which proves
  the same public metadata and predicate wrappers report native directories as
  `file_kind::dir` without asserting environment-dependent directory size.
- `tests/yulang/cases.toml` includes `file_text_with_native_commit`, which
  proves production `text_with` commits through public `load` / `store` under
  the native CLI host.
- `tests/yulang/cases.toml` includes
  `file_text_with_native_rollback_on_error`, which proves a callback abort does
  not reach the protocol `store`, leaving the native backing file unchanged.
- `tests/yulang/cases.toml` includes
  `file_text_with_native_undet_last_write_wins`, which proves native
  `text_with` follows the same branch-local buffer / arrival-order
  last-write-wins behavior already covered by the source mock protocol case.
- `tests/yulang/cases.toml` includes
  `file_text_with_native_nested_cross_file`, which proves nested native
  `text_with` sessions over two backing files commit independently while the
  inner callback can still close over the outer entry snapshot.
- `tests/yulang/cases.toml` includes
  `file_text_with_native_nested_state_var`, which proves that the native
  protocol also supports a callback-local `&` state variable while an inner
  `text_with` callback mutates it through lexical capture.
- `tests/yulang/cases.toml` includes
  `file_text_unscoped_native_handler_extent`, which proves unscoped
  `file::text` reads through the native ambient `file_buffer` act, keeps the
  backing file unchanged during the handler extent, and writes the dirty buffer
  back at successful run completion.
- `tests/yulang/cases.toml` includes `file_read_write_at_native_result`, which
  proves native range read/write helpers execute through the typed result host
  boundary. Exact range slicing semantics remain provisional.
- `tests/yulang/cases.toml` includes
  `file_native_protocol_typed_failures`, which proves native `file::load` and
  `file::store` operation failures produce domain `io_err` constructors
  (`not_found`, `failed`) instead of exposing an integer error-code bridge.
- `tests/yulang/cases.toml` also includes
  `file_native_helper_typed_failures`, which proves public `read_text` /
  `write_text` wrappers preserve those typed failures through `io_err::wrap`.
- `tests/yulang/cases.toml` also includes
  `file_native_invalid_path_typed_failure`, which proves native
  `InvalidInput` / `InvalidData` host failures are classified as
  `io_err::invalid_path` through both public protocol operations and text
  helpers instead of falling through to the generic `failed` constructor.
- `cargo run -q -p yulang -- --std-root lib contract --contract file-resource
  tests/yulang/cases.toml` passes the current file-resource subset.
- `scripts/package-release.sh --version contract-v1-file-metadata-predicates --target
  x86_64-unknown-linux-gnu --binary target/release/yulang --out
  target/release-contract-v1-file-metadata-predicates` followed by
  `scripts/release-archive-smoke.sh
  target/release-contract-v1-file-metadata-predicates/yulang-x86_64-unknown-linux-gnu.tar.gz`
  passes. The archive smoke expands the packaged binary, uses the bundled
  standard library, and runs the filtered `file-resource` manifest subset.
- public signature canaries cover the current file helper surface, carry the
  `file-resource` tag, and reject private evidence in projected types.
- The Evidence VM host operation table now carries explicit act and operation
  tier metadata for the current console and file operations. This is not the
  final host act manifest / registry, but it gives that migration one runtime
  metadata boundary instead of another scattered path-matching chain.
- The runtime registry now preserves the resolved operation spec through host
  execution and has a manifest-view canary for stable act id, operation id, sync
  tier, and path reconstruction. Known host act prefixes with an unregistered
  operation are classified as capability failures; unrelated user effects still
  fall through to escaped-effect behavior.
- The runtime registry now resolves through an explicit `RuntimeHostManifest`
  owner for the current static operation table. This keeps the existing escaped
  request semantics while making the future lowering-produced host manifest a
  single replacement boundary.
- `yulang debug host-act-manifest` prints the current runtime host manifest
  view from the release binary: stable act id, operation id, sync tier,
  reconstructed path, and provisional argument/result signature for console/file
  operations. This is still the interim
  runtime manifest, not compiler-generated `host act` lowering output, but it
  makes the current registry surface observable outside unit tests.
- `scripts/release-smoke.sh` now checks representative console/file manifest
  lines, so release and archive smokes cover the debug manifest surface through
  the packaged binary path. It also checks that the suspend multi-shot tier is
  visible in the packaged binary manifest output.
- `scripts/release-smoke.sh` also runs a focused `file-resource` contract set
  through the smoke binary and the installed standard library. The focused set
  covers the Stage 1 state-passing protocol cases, native load/store/meta,
  native typed operation/helper/invalid-path failure, native `text_with`
  commit/rollback/nondet/nested session cases, file/meta/ambient
  unsupported-host capability failure, and native ambient missing-file
  `host-io-error` failure.
  Full `--contract file-resource` remains the archive-smoke and local validation
  gate because it is materially heavier than a release smoke.
- The Evidence VM also has a deny path for known native host operations:
  disabling native host operations in the runtime context reports
  `UnsupportedHostCapability` instead of collapsing into a generic escaped
  effect.
- `tests/yulang/cases.toml` includes `file_unsupported_host`, a
  `file-resource` / `host.unsupported` runtime-failure case. It runs through
  `yulang contract`, passes `run --host unsupported`, and proves that file
  helpers do not fake success when native host capabilities are unavailable.
- `tests/yulang/cases.toml` also includes `file_meta_unsupported_host`, so the
  metadata path goes through the same unsupported-host capability failure
  instead of returning fake metadata under a sandboxed host.
- `tests/yulang/cases.toml` includes `file_read_text_unsupported_host`, so the
  public `read_text` helper also reports unsupported host capability instead of
  returning fake file contents under a sandboxed host.
- `tests/yulang/cases.toml` includes `file_write_text_unsupported_host`, so the
  public `write_text` helper also reports unsupported host capability instead
  of pretending to write under a sandboxed host.
- `tests/yulang/cases.toml` includes `file_text_unsupported_host`, so unscoped
  `file::text` / `file_buffer::ambient_get` also reports unsupported host
  capability instead of returning fake text under a sandboxed host. This is
  structured failure evidence; typed ambient `io_err` is still a Stage 2
  blocker.
- `tests/yulang/cases.toml` includes
  `file_text_native_missing_host_io_error`, so native unscoped `file::text`
  over a missing backing file reports `yulang.host-io-error` instead of
  pretending the host I/O failure is an unhandled effect.
- `tests/yulang/cases.toml` includes `file_mock_read_text_handler`, a focused
  `file-resource` / `host-act` / `mock-host` canary that runs with
  `--host unsupported` and handles `std::io::file::file.load` in Yulang. It
  proves that source handlers still intercept file host acts before the host
  registry, even when native host capabilities are unavailable. This is
  mock-host evidence for act routing, not resource-lifetime mock evidence.
- `tests/yulang/cases.toml` also includes
  `file_mock_read_write_text_handler`, which handles both public `read_text`
  and `write_text` helper paths through source-level `load` / `store`
  arms while the native host is disabled. This keeps mock-host evidence on both
  read and write directions without making raw snapshot operations public.
- `tests/yulang/cases.toml` includes `file_mock_public_ref_view_commit`, which
  proves the inline public managed-ref view shape over pure Yulang state.
- `tests/yulang/cases.toml` includes `file_mock_text_with_function_commit`,
  which proves the same public managed-ref view shape through a reusable
  `text_with_mock(backing, f)` function boundary. This case also fixes the
  previous no-cache/cached split: normal cached contract runs now observe the
  same roots as a full build.
- `tests/yulang/cases.toml` includes
  `file_mock_text_with_rollback_on_error`, which proves that the same public
  helper shape can discard dirty callback-local buffer updates when the callback
  exits through a user error.
- `tests/yulang/cases.toml` includes
  `file_mock_text_with_nondet_branch_buffers`, which proves that the same public
  helper shape gives each `nondet.each` branch an independent callback-local
  buffer.
- `tests/yulang/cases.toml` includes `ref_update_local_buffer_public`, a
  `stable-core` runtime case proving that direct public `ref.update` over a
  public `ref { get, update_effect }` view backed by local `$buffer` state is
  executable. The same source has a CLI std-prefix cache regression so cached
  execution keeps matching a full build.

Those canaries are still `migration-canary` evidence. They do not complete
Contract v1 because raw / snapshot host operations remain as compatibility
operations, native unscoped ambient read/write failures do not yet have a typed
file error policy, and the raw/provisional operations have not yet moved behind
a public session replacement.

## Missing Evidence

Contract v1 is complete only after the manifest contains the remaining
executable `file-resource` cases for:

| Slice | Required evidence |
| --- | --- |
| Mock host | complete for the Stage 1 protocol fixture set |
| Native host | eventual removal or raw/provisional isolation of legacy snapshot operations |
| Unsupported host | unsupported capability is a typed failure or structured diagnostic, never fake success |
| Public signatures | exact types for the resource entrypoints without `#...`, `AllExcept(...)`, `Unknown`, or placeholder-like `Any` |

## Known Blockers

The Stage 1 callback residual blocker is closed by the protocol rewrite:
`text_with` no longer passes a scoped `file_buffer` ref into the callback.
Callback state is carried explicitly as `(result, final_text)`, so user effects
compose through the callback row rather than through a handler-local file buffer
effect.

The remaining blockers are Stage 2 host-boundary cleanup items:

- replacing native unscoped ambient read/write failures with typed `io_err`
  without leaking private row constraints. Structured runtime error coverage
  exists for missing native ambient reads;
- replacing or retiring `raw-compat` snapshot operations with a public session
  boundary.

Do not solve Stage 2 by restoring scoped `file_buffer` operations, transfer
arms, `same_path` checks, raw snapshot public operations, or weaker public
signature canaries.

Probe reductions should also avoid `catch { ... }:`. A raw brace block in the
catch scrutinee is not valid Yulang surface syntax. Binding an effectful file
call before passing it to a handler runner is not equivalent either: the binding
executes before the handler can catch the host act.

## Acceptance Gate

When the first executable slice lands, use a filtered contract run:

```bash
cargo run -q -p yulang -- --std-root lib contract --contract file-resource tests/yulang/cases.toml
```

Release evidence should run the focused smoke set through `scripts/release-smoke.sh`
and the full tag filter through archive smoke with the packaged binary and
bundled standard library.

As of the Stage 2 native protocol bridge plus native parity evidence on
2026-07-03, the local checkout passes the filtered `file-resource` subset with
source mock handlers, native CLI protocol cases, native nondet/nested
`text_with` parity, native missing/file/directory metadata coverage, native
typed operation-failure coverage, and native unscoped ambient handler-extent
coverage. The latest local full tag run reports `contract cases ok: 54` after
adding `io_err.not_found` / `io_err.failed` public signature canaries.
Release/archive smoke also passes against the packaged binary and bundled
standard library for the same `file-resource` subset.

## Rollback Conditions

Stop implementation and return to the semantic documents if any of these happen:

- commit / rollback expectations need to be changed to match implementation
  output;
- multi-shot branches cannot keep independent managed buffers;
- unsupported hosts need fake success to keep examples passing;
- file helper spellings are promoted to `stable-api` before resource lifetime
  semantics are executable;
- public signatures leak private stack evidence or use `Any` / `Unknown` as
  fallback.
