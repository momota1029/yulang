# Contract v1 File Evidence

This page records evidence for
[Contract v1: File Resource](file-resource-contract.md).

Status on 2026-07-03: **Stage 2 closeout covered for the file-session-free
Contract v1 slice**. The
contract box and tag policy exist, and the `file-resource` manifest subset now
covers the public `file::load` / `file::store` / `file::meta` Stage 0 surface,
the Stage 1 source-mock `text_with` protocol fixtures, and the first native
registry parity cases over the same public protocol. `file::text` now performs
an eager `file::ambient_touch`, so missing native text resources become typed
`io_err` at lens creation time while the returned ref remains `ref '[file] str`.
Remaining `raw-compat` surface is limited to provisional `read_at` / `write_at`
range helpers, not legacy snapshot sessions.
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
  current executable range helper canaries, so manifest queries can separate
  compatibility evidence from protocol-center evidence.
- `file::open_text_raw`, `file::open_text_snapshot_raw`, `file::file_get`,
  `file::file_set`, `file::file_flush`, `file::file_snapshot_get`,
  `file::file_snapshot_set`, and `file::file_snapshot_commit` are retired from
  `lib/std/io/file.yu` and from the runtime host manifest. Their public helper
  entrypoints `open_text`, `open`, and `open_in` are retired with them.
- `debug host-act-manifest` now exposes a `surface` column. Current operations
  are separated into `contract` and `raw-compat`, and the only file
  `raw-compat` operations left after Stage A are `read_at` and `write_at`.
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
- `open_text`, `open`, and `open_in` are retired with the legacy native
  snapshot operations. Stage 2 migration evidence now goes through
  `text_with`, ambient `file::text`, and the public protocol operations.
- Ambient text operations are integrated into the `file` act as
  `ambient_touch`, `ambient_get`, and `ambient_set`. The former separate
  `file_buffer` act is retired, so `file::text` exposes one `[file, io_err]`
  entry row and returns `ref '[file] str`.
- The native runtime host registry now registers
  `std::io::file::file.ambient_touch`,
  `std::io::file::file.ambient_get`, and
  `std::io::file::file.ambient_set` under the unified `file` host act.
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
  native temp files or legacy snapshot operations.
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
  inner callback can still close over the outer entry text.
- `tests/yulang/cases.toml` includes
  `file_text_with_native_nested_state_var`, which proves that the native
  protocol also supports a callback-local `&` state variable while an inner
  `text_with` callback mutates it through lexical capture.
- `tests/yulang/cases.toml` includes
  `file_text_unscoped_native_handler_extent`, which proves unscoped
  `file::text` reads through the native ambient `file` act operations, keeps
  the backing file unchanged during the handler extent, and writes the dirty
  buffer back at successful run completion.
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
- `scripts/release-smoke.sh` also runs a focused `host-act` contract set for
  console: unsupported-host denial, source-handler mock routing, and exact
  public signature projection. This keeps release binaries from proving only the
  file side of the host-act registry.
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
  `file::text` / `file::ambient_touch` also reports unsupported host
  capability instead of returning fake text under a sandboxed host.
- `tests/yulang/cases.toml` includes `file_text_native_missing_typed_io_err`,
  so native missing-path `file::text` creation is caught as typed
  `io_err::not_found` rather than leaking as a runtime host IO error.
- `tests/yulang/cases.toml` includes
  `file_ambient_get_untouched_missing_host_io_error`, so direct
  out-of-protocol `file::ambient_get` on an untouched missing path remains a
  structured `yulang.host-io-error`.
- `tests/yulang/cases.toml` includes
  `file_text_mock_ambient_typed_not_found`, so source handlers can still return
  typed ambient failures by handling `file::ambient_touch` before the native
  host registry.
- `tests/yulang/cases.toml` includes `console_unsupported_host`, so
  `std::io::console::out.write` also reports unsupported host capability under
  `--host unsupported`. This keeps the host capability denial shape shared
  across console and file acts rather than making file support a one-off.
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
- `tests/yulang/cases.toml` includes `console_mock_out_handler`, which handles
  `std::io::console::out.write` in source while the native host is disabled.
  This proves source handlers can intercept console host acts before the host
  registry in the same way the file mock cases intercept `load` / `store`.
- `tests/yulang/cases.toml` includes
  `std_console_out_write_public_signature`, so the console host-act boundary
  also has an exact public type canary and rejects private evidence fragments.
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

Those canaries are still `migration-canary` evidence. They close the Stage 2
typed ambient and snapshot raw-compat blockers for the file-session-free
Contract v1 slice. Remaining range helpers still carry provisional
`raw-compat` semantics and are not the final session API.

## Missing Evidence

Contract v1 is complete only after the manifest contains the remaining
executable `file-resource` cases for:

| Slice | Required evidence |
| --- | --- |
| Mock host | complete for the Stage 1 protocol fixture set |
| Native host | snapshot raw-compat retirement is covered; native ambient typed failure remains |
| Unsupported host | unsupported capability is a typed failure or structured diagnostic, never fake success |
| Public signatures | exact types for the resource entrypoints without `#...`, `AllExcept(...)`, `Unknown`, or placeholder-like `Any` |

## Known Blockers

The Stage 1 callback residual blocker is closed by the protocol rewrite:
`text_with` no longer passes a scoped file-buffer ref into the callback.
Callback state is carried explicitly as `(result, final_text)`, so user effects
compose through the callback row rather than through a handler-local file buffer
effect.

The Stage 2 host-boundary blockers are closed under the D3 decision that
`file_session` is post-v1:

- snapshot raw-compat operations and `open_text` / `open` / `open_in` are
  retired;
- unscoped `file::text` performs eager `ambient_touch` and reports missing
  native paths as typed `io_err::not_found`;
- direct untouched `file::ambient_get` remains structured `HostIoError`, as
  specified for out-of-protocol use.

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

As of the Stage 2 closeout implementation on 2026-07-03, the local checkout
passes the filtered `file-resource` subset with source mock handlers, native CLI
protocol cases, native nondet/nested `text_with` parity, native
missing/file/directory metadata coverage, native typed operation-failure
coverage, integrated `file::ambient_*` handler-extent coverage, typed
missing-path `file::text` creation, and structured out-of-protocol
`file::ambient_get` failure coverage. The latest local full tag run reports
`contract cases ok: 57`, and the focused release smoke now also includes
console host-act denial, mock routing, public-signature canaries, and the
integrated ambient file act cases. Release/archive smoke also passes against
the packaged binary and bundled standard library for the same `file-resource`
subset.

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
