# Contract v1 File Evidence

This page records evidence for
[Contract v1: File Resource](file-resource-contract.md).

Status on 2026-07-03: **open, Stage 2 native protocol bridge covered**. The
contract box and tag policy exist, and the `file-resource` manifest subset now
covers the public `file::load` / `file::store` / `file::meta` Stage 0 surface,
the Stage 1 source-mock `text_with` protocol fixtures, and the first native
registry parity cases over the same public protocol. Legacy raw / snapshot
operations and integer error-code translation remain a compatibility window,
not the Contract v1 center. Contract v0 remains closed in
[contract-v0-evidence.md](contract-v0-evidence.md).

## Current Evidence

The repository already has migration canaries for the file host bridge and
public surface:

- `std::io::file::read_text` / `write_text` now project to public
  `file::load` / `file::store` result operations. Source mock handlers can
  intercept those operations under `--host unsupported`, and the native CLI
  host executes the same public operations through the runtime host registry.
- `exists`, `is_file`, and `is_dir` still run through the native CLI host.
  `file_meta { kind, size, readonly }` is now the public metadata shape, and
  the new public `file::meta` operation has native registry coverage.
- `tests/yulang/cases.toml` includes `file_meta_kind`, a
  `file-resource` / `metadata` / `mock-host` runtime canary that checks the
  new public `file::meta` operation under `--host unsupported`.
- `io_err::wrap` converts failed file reads and writes into typed result
  boundaries.
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
  only if the callback returns, then return the callback result.
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
- `tests/yulang/cases.toml` includes `file_text_with_native_commit`, which
  proves production `text_with` commits through public `load` / `store` under
  the native CLI host.
- `tests/yulang/cases.toml` includes
  `file_text_with_native_rollback_on_error`, which proves a callback abort does
  not reach the protocol `store`, leaving the native backing file unchanged.
- `tests/yulang/cases.toml` includes
  `file_text_unscoped_native_handler_extent`, which proves unscoped
  `file::text` reads through the native ambient `file_buffer` act, keeps the
  backing file unchanged during the handler extent, and writes the dirty buffer
  back at successful run completion.
- `cargo run -q -p yulang -- --std-root lib contract --contract file-resource
  tests/yulang/cases.toml` passes the current file-resource subset.
- `scripts/package-release.sh --version contract-v1-file-buffer-ambient --target
  x86_64-unknown-linux-gnu --binary target/release/yulang --out
  target/release-contract-v1-file-buffer-ambient` followed by
  `scripts/release-archive-smoke.sh
  target/release-contract-v1-file-buffer-ambient/yulang-x86_64-unknown-linux-gnu.tar.gz`
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
  the packaged binary path.
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
Contract v1 because legacy raw / snapshot host operations still carry integer
error-code translation, native unscoped ambient read/write failures do not yet
have a typed file error policy, and raw/provisional isolation is still open.

## Missing Evidence

Contract v1 is complete only after the manifest contains the remaining
executable `file-resource` cases for:

| Slice | Required evidence |
| --- | --- |
| Mock host | complete for the Stage 1 protocol fixture set |
| Native host | remaining multi-shot native parity and eventual removal or raw/provisional isolation of legacy snapshot operations |
| Unsupported host | unsupported capability is a typed failure or structured diagnostic, never fake success |
| Public signatures | exact types for the resource entrypoints without `#...`, `AllExcept(...)`, `Unknown`, or placeholder-like `Any` |

## Known Blockers

The Stage 1 callback residual blocker is closed by the protocol rewrite:
`text_with` no longer passes a scoped `file_buffer` ref into the callback.
Callback state is carried explicitly as `(result, final_text)`, so user effects
compose through the callback row rather than through a handler-local file buffer
effect.

The remaining blockers are Stage 2 host-boundary cleanup items:

- removal of legacy int error-code translation from the public file path;
- replacing native unscoped ambient read/write escaped-effect fallbacks with a
  typed or structured file failure policy;
- raw/provisional isolation for legacy snapshot operations and range helpers.

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

Release evidence should run the same tag filter through the packaged binary and
bundled standard library.

As of the Stage 2 native protocol bridge on 2026-07-03, the local checkout
passes the filtered `file-resource` subset through `cargo run` with source mock
handlers, native CLI protocol cases, and the first native unscoped ambient
handler-extent case. Release/archive smoke also passes against the packaged
binary and bundled standard library for the same `file-resource` subset.

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
