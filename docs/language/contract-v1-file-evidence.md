# Contract v1 File Evidence

This page records evidence for
[Contract v1: File Resource](file-resource-contract.md).

Status on 2026-07-02: **open**. The contract box and tag policy exist, but the
`file-resource` manifest subset is intentionally empty until executable cases
observe the resource lifetime semantics. Contract v0 remains closed in
[contract-v0-evidence.md](contract-v0-evidence.md).

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
- public signature canaries cover the current file helper surface and reject
  private evidence in projected types.

Those canaries are `migration-canary` evidence. They do not complete Contract v1
because they do not yet prove snapshot transaction behavior, branch-local
buffers, rollback, unsupported-host failure, or packaged-release parity.

## Missing Evidence

Contract v1 is complete only after the manifest contains executable
`file-resource` cases for:

| Slice | Required evidence |
| --- | --- |
| Mock host | pure handler commit, rollback, multi-shot branch commit, handler-extent discharge |
| Native host | temp-file commit, rollback, multi-shot parity with mock shape |
| Unsupported host | unsupported capability is a typed failure or structured diagnostic, never fake success |
| Public signatures | exact types for the resource entrypoints without `#...`, `AllExcept(...)`, `Unknown`, or placeholder-like `Any` |
| Release | packaged binary plus bundled std runs representative `file-resource` cases |

## Acceptance Gate

When the first executable slice lands, use a filtered contract run:

```bash
cargo run -q -p yulang -- --std-root lib contract --contract file-resource tests/yulang/cases.toml
```

Release evidence should run the same tag filter through the packaged binary and
bundled standard library.

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
