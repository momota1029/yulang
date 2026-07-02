# Contract v1 File Evidence

This page records evidence for
[Contract v1: File Resource](file-resource-contract.md).

Status on 2026-07-02: **open**. The contract box and tag policy exist, and the
`file-resource` manifest subset has native normal-commit and unsupported-host
cases. Native rollback on user error and branch-local multi-shot buffers are now
covered in debug, release, and packaged archive smoke routes. Pure mock
resource-lifetime behavior remains open. Contract v0 remains closed in
[contract-v0-evidence.md](contract-v0-evidence.md).

## Current Evidence

The repository already has migration canaries for the file host bridge and
public surface:

- `std::io::file::read_text` / `write_text` run through the native CLI evidence
  VM route.
- `exists`, `is_file`, `is_dir`, and the current `file_meta { kind, readonly }`
  shape run through the native CLI host. `meta` is non-throwing in the public
  type: missing, denied, and other inaccessible paths are represented by
  `file_meta.kind` rather than `io_err`.
- `tests/yulang/cases.toml` includes `file_meta_kind`, a
  `file-resource` / `metadata` / `host.native` runtime canary that checks the
  file and missing metadata kinds through the manifest runner.
- `io_err::wrap` converts failed file reads and writes into typed result
  boundaries.
- `open_text`, `open`, `open_in`, `text`, and `text_with` have basic whole-file
  text-ref get/set coverage.
- Native `open_in` / `text_with` now use a scoped snapshot handle for the normal
  path: the buffer changes during the callback, the backing file is unchanged
  while the callback is running, and normal scope exit commits the final buffer.
- `tests/yulang/cases.toml` includes `file_text_with_commit`, the first
  `file-resource` / `resource-lifetime` / `host.native` manifest case. It uses
  runner-managed temp files and checks both CLI output and final file contents.
- `tests/yulang/cases.toml` includes `file_text_with_rollback_on_error`, a
  native `text_with` rollback case. The callback reads and updates the managed
  text ref, exits through a user error caught by `E::wrap`, and the temp backing
  file remains unchanged.
- `tests/yulang/cases.toml` includes
  `file_text_with_nondet_branch_snapshots`, a native `text_with` multi-shot case.
  The callback branches through `nondet.each`; each resumed branch reads the
  original `"start"` buffer, writes an independent branch-local text value, and
  commits in arrival order with last-write-wins final file contents.
- `target/release/yulang --std-root lib contract --contract file-resource
  tests/yulang/cases.toml` passes the current native file-resource subset:
  normal commit, user-error rollback, nondet branch-local snapshots, and
  unsupported-host failure.
- `scripts/package-release.sh --version contract-v1-smoke --target
  x86_64-unknown-linux-gnu --binary target/release/yulang --out
  target/release-contract-v1` followed by
  `scripts/release-archive-smoke.sh
  target/release-contract-v1/yulang-x86_64-unknown-linux-gnu.tar.gz` passes.
  The archive smoke expands the packaged binary, uses the bundled standard
  library, and runs the filtered `file-resource` manifest subset.
- public signature canaries cover the current file helper surface and reject
  private evidence in projected types.
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
  view from the release binary: stable act id, operation id, sync tier, and
  reconstructed path for console/file operations. This is still the interim
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
  `--host unsupported` and handles `std::io::file::file.read_at` in Yulang. It
  proves that source handlers still intercept file host acts before the host
  registry, even when native host capabilities are unavailable. This is
  mock-host evidence for act routing, not resource-lifetime mock evidence.
- `tests/yulang/cases.toml` also includes
  `file_mock_read_write_text_handler`, which handles both public `read_text`
  and `write_text` helper paths through source-level `read_at` / `write_at`
  arms while the native host is disabled. This keeps mock-host evidence on both
  read and write directions without making raw snapshot operations public.
- `notes/bugs/file_text_with_mock_resource_lifetime_blocker.yu` records the
  current pure mock blocker: `text_with` relies on private snapshot helper
  operations that outside source cannot catch, while a public-only local-ref
  rewrite is now contract-covered through a reusable public function boundary.

Those canaries are still `migration-canary` evidence. They do not complete
Contract v1 because they do not yet prove pure mock resource-lifetime parity.

## Missing Evidence

Contract v1 is complete only after the manifest contains the remaining
executable `file-resource` cases for:

| Slice | Required evidence |
| --- | --- |
| Mock host | pure handler commit, rollback, multi-shot branch commit, handler-extent discharge |
| Native host | parity with mock shape |
| Unsupported host | unsupported capability is a typed failure or structured diagnostic, never fake success |
| Public signatures | exact types for the resource entrypoints without `#...`, `AllExcept(...)`, `Unknown`, or placeholder-like `Any` |

## Known Blockers

The native user-error rollback gap was narrowed to the thin `text_with` wrapper:
direct `open_in` already worked, while `text_with(path, f) = open_in path f`
split the callback residual during specialization. `text_with` is now a direct
alias of `open_in`, and the rollback case is executable.

The native multi-shot blocker is resolved by Evidence VM file snapshot
continuation frames. The runtime now carries managed file buffers with resumed
continuations, executes synchronous host file requests inside the restored
branch state, and lets `file_snapshot_commit` consume the normal-return snapshot
sidecar. This keeps abortive exits as rollback while allowing callback-local
updates to reach the surrounding managed-lens commit.

Do not collapse this back into runner-global `file_snapshots`: it regresses
multi-shot branch isolation.

Pure mock resource-lifetime parity is still blocked. The current native
`text_with` path is mockable at the public `read_at`/`write_at` act level only
for thin helpers; full `text_with` uses private snapshot helper operations.
Making those raw helpers public would be the wrong fix. The next fix should
either provide a mockable public host-act/session boundary for file resources or
provide a documented public language-level ref view shape that carries the right
residuals through callbacks. `notes/bugs/ref_constructor_public_path_blocker.yu`
records the old fully-qualified constructor attempt. It is not evidence of a
specialize2 bug: `dump-poly` reports the external
`std::control::var::ref { ... }` value constructor as unresolved. The corrected
constructor reduction is `notes/bugs/ref_constructor_short_value_probe.yu`:
after importing `std::control::var::*`, the short `ref { ... }` constructor
resolves to `d171:"std.control.var.ref"` in `dump-poly` and runs successfully
when written with current mutable-binding syntax (`my $text = ...`).

The public ref-view function boundary is now contract-covered by
`file_mock_text_with_function_commit`. The reduced source originally lived in
`notes/bugs/file_text_with_mock_function_boundary_blocker.yu`: it proves that a
reusable `text_with_mock(backing, f)` helper can pass a public record-shaped
`ref` view to a callback and commit callback-local assignment at helper exit.
That case used to pass only with `--no-cache`; the CLI now falls back to a full
build when a std-prefix cache route introduces a specialize/control error, so
the normal cached contract runner observes the same roots.

The real `std::io::file::text_with` path also still uses private snapshot
helper operations, and a source-level outer handler cannot fully mock that
private callback path. `open_text_snapshot_raw` can be caught by a local
handler, but `file_snapshot_get` performed through the callback escapes the
same public mock handler. Do not solve this by making those raw snapshot
operations public.

`notes/bugs/ref_update_local_buffer_public_probe.yu` remains a separate
`.update`-method residual probe: direct `r.update` over a public ref view backed
by local `$buffer` state still fails, while callback assignment through
`&text = ...` is executable and contract-covered in the function-boundary
reduction.

## Acceptance Gate

When the first executable slice lands, use a filtered contract run:

```bash
cargo run -q -p yulang -- --std-root lib contract --contract file-resource tests/yulang/cases.toml
```

Release evidence should run the same tag filter through the packaged binary and
bundled standard library.

As of 2026-07-02, `scripts/hardening-smoke.sh` and
`scripts/release-archive-smoke.sh` run the filtered `file-resource` subset
through the release binary surface. The local release binary passes the current
native subset including rollback and multi-shot branch buffers. A locally built
release archive also passes the same subset through bundled std. Mock-host
resource-lifetime parity remains open.

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
