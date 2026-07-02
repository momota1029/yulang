# Contract v1 File Evidence

This page records evidence for
[Contract v1: File Resource](file-resource-contract.md).

Status on 2026-07-02: **open**. The contract box and tag policy exist, and the
`file-resource` manifest subset now has the first public `file_buffer` /
`file::load` / `file::store` / `file::meta` Stage 0 surface. The current
production `std::io::file::text_with` path can be source-mocked for the normal
commit case, while rollback and multi-shot cases still use the legacy native
`open_in` snapshot route until the callback residual blocker is fixed. Contract
v0 remains closed in [contract-v0-evidence.md](contract-v0-evidence.md).

## Current Evidence

The repository already has migration canaries for the file host bridge and
public surface:

- `std::io::file::read_text` / `write_text` now project to public
  `file::load` / `file::store` result operations. Source mock handlers can
  intercept those operations under `--host unsupported`; native registry
  support is a Stage 2 item.
- `exists`, `is_file`, and `is_dir` still run through the native CLI host.
  `file_meta { kind, size, readonly }` is now the public metadata shape; native
  registry support for the new `file::meta` operation is a Stage 2 item.
- `tests/yulang/cases.toml` includes `file_meta_kind`, a
  `file-resource` / `metadata` / `mock-host` runtime canary that checks the
  new public `file::meta` operation under `--host unsupported`.
- `io_err::wrap` converts failed file reads and writes into typed result
  boundaries.
- `open_text`, `open`, and `open_in` remain as legacy native snapshot canaries
  for Stage 2 parity.
- `text` and `text_with` now expose the Stage 0 `file_buffer` view shape.
- `tests/yulang/cases.toml` includes `file_text_with_commit`, the first
  production `text_with` source-mock case. It runs with `--host unsupported`,
  catches `file::load` / `file::store` in Yulang, and observes normal scope
  exit commit.
- `tests/yulang/cases.toml` includes `file_text_with_rollback_on_error`, a
  legacy native `open_in` rollback canary. The callback reads and updates the managed
  text ref, exits through a user error caught by `E::wrap`, and the temp backing
  file remains unchanged.
- `tests/yulang/cases.toml` includes
  `file_text_with_nondet_branch_snapshots`, a legacy native `open_in`
  multi-shot canary.
  The callback branches through `nondet.each`; each resumed branch reads the
  original `"start"` buffer, writes an independent branch-local text value, and
  commits in arrival order with last-write-wins final file contents.
- `cargo run -q -p yulang -- --std-root lib contract --contract file-resource
  tests/yulang/cases.toml` passes the current file-resource subset.
- `scripts/package-release.sh --version contract-v1-smoke --target
  x86_64-unknown-linux-gnu --binary target/release/yulang --out
  target/release-contract-v1` followed by
  `scripts/release-archive-smoke.sh
  target/release-contract-v1/yulang-x86_64-unknown-linux-gnu.tar.gz` passes.
  The archive smoke expands the packaged binary, uses the bundled standard
  library, and runs the filtered `file-resource` manifest subset.
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
- `notes/bugs/file_text_with_callback_residual_blocker.yu` records the
  remaining Stage 1 blocker: a production `text_with` callback that touches
  `file_buffer` and then raises another user effect still hits a residual-row
  conflict.

Those canaries are still `migration-canary` evidence. They do not complete
Contract v1 because rollback, multi-shot, unscoped ambient discharge, and
native parity have not yet moved onto the new `file_buffer` surface.

## Missing Evidence

Contract v1 is complete only after the manifest contains the remaining
executable `file-resource` cases for:

| Slice | Required evidence |
| --- | --- |
| Mock host | production `text_with` through a public mockable session boundary, multi-shot branch commit, handler-extent discharge |
| Native host | parity with mock shape |
| Unsupported host | unsupported capability is a typed failure or structured diagnostic, never fake success |
| Public signatures | exact types for the resource entrypoints without `#...`, `AllExcept(...)`, `Unknown`, or placeholder-like `Any` |

## Known Blockers

The private snapshot mockability blocker is narrowed but not closed. Stage 0
replaces production `text_with` with a public `file_buffer` transaction handler
and public `file::load` / `file::store` operations. This is enough for the
normal commit mock-host canary.

The remaining blocker is callback residual composition. A callback that touches
`file_buffer` and then raises another effect still conflicts during type
checking. `notes/bugs/file_text_with_callback_residual_blocker.yu` records the
reduction. Until that is fixed, rollback and multi-shot canaries remain on the
legacy native `open_in` route and do not count as the final Contract v1
`text_with` evidence.

Do not solve the remaining gap by making raw snapshot operations public, by
putting handler-local mutable state back into `text_with`, or by weakening the
public signature canaries. The fix must keep `file_buffer` public and preserve
callback residuals without leaking private evidence.

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

As of the Stage 0 rewrite on 2026-07-02, the local checkout passes the filtered
`file-resource` subset through `cargo run`. Release binary and archive evidence
must be refreshed after Stage 2, when the native registry is moved to the new
`file::load` / `file::store` / `file::meta` surface. Full production
`text_with` rollback, multi-shot, and unscoped mock resource-lifetime parity
remain open.

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
