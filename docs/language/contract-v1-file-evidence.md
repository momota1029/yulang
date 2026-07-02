# Contract v1 File Evidence

This page records evidence for
[Contract v1: File Resource](file-resource-contract.md).

Status on 2026-07-02: **open**. The contract box and tag policy exist, and the
`file-resource` manifest subset has its first native normal-commit case.
Rollback, branch-local multi-shot buffers, pure mock host behavior, unsupported
host failure, and release archive parity remain open. Contract v0 remains
closed in [contract-v0-evidence.md](contract-v0-evidence.md).

## Current Evidence

The repository already has migration canaries for the file host bridge and
public surface:

- `std::io::file::read_text` / `write_text` run through the native CLI evidence
  VM route.
- `exists`, `is_file`, `is_dir`, and the current `file_meta { kind, readonly }`
  shape run through the native CLI host.
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
- public signature canaries cover the current file helper surface and reject
  private evidence in projected types.
- The Evidence VM host operation table now carries explicit act and operation
  tier metadata for the current console and file operations. This is not the
  final host act manifest / registry, but it gives that migration one runtime
  metadata boundary instead of another scattered path-matching chain.
- The Evidence VM also has a deny path for known native host operations:
  disabling native host operations in the runtime context reports
  `UnsupportedHostCapability` instead of collapsing into a generic escaped
  effect. There is not yet a public `host.unsupported` manifest case or
  playground/wasm route for this behavior.

Those canaries are still `migration-canary` evidence. They do not complete
Contract v1 because they do not yet prove rollback, branch-local buffers,
unsupported-host failure, pure mock parity, or packaged-release parity.

## Missing Evidence

Contract v1 is complete only after the manifest contains executable
`file-resource` cases for:

| Slice | Required evidence |
| --- | --- |
| Mock host | pure handler commit, rollback, multi-shot branch commit, handler-extent discharge |
| Native host | temp-file rollback, multi-shot branch-local buffers, and parity with mock shape |
| Unsupported host | unsupported capability is a typed failure or structured diagnostic, never fake success |
| Public signatures | exact types for the resource entrypoints without `#...`, `AllExcept(...)`, `Unknown`, or placeholder-like `Any` |
| Release | packaged binary plus bundled std runs representative `file-resource` cases |

## Known Blockers

The first native slice deliberately stops short of rollback and multi-shot
contract cases. A callback that reads or writes the provided file ref and then
escapes through an outer error or nondet handler currently exposes a solver
row-combination gap:

```text
conflicting type candidates: [std::io::file::file, edit_err] vs [edit_err]
conflicting type candidates: [std::control::nondet::nondet, std::io::file::file] vs [std::control::nondet::nondet]
```

The conflict is specific to the provided ref's `file` effect under the outer
handler. Plain file residuals under `edit_err::wrap` and plain file residuals
under `.list` both work. Do not paper over this with a fixture-specific
fallback; the next fix belongs near callback residual inference or the future
host act/resource operation separation.

The current native snapshot storage is runner-local, not branch-local. It is
adequate for normal scope-exit commit but is not evidence for multi-shot
branch-local buffers.

## Acceptance Gate

When the first executable slice lands, use a filtered contract run:

```bash
cargo run -q -p yulang -- --std-root lib contract --contract file-resource tests/yulang/cases.toml
```

Release evidence should run the same tag filter through the packaged binary and
bundled standard library.

As of 2026-07-02, `scripts/hardening-smoke.sh` and
`scripts/release-archive-smoke.sh` run the representative
`file_text_with_commit` case through the release binary surface. This is release
evidence for normal native scope-exit commit only; rollback, multi-shot branch
buffers, mock-host parity, and unsupported-host behavior remain open.

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
