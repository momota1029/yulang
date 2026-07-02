# File Resource Contract

This page defines the next public contract slice after
[Yulang Contract v0](stable-core.md).

**Contract v1: File Resource** is not a reopening of the stable core. It is the
first standard-resource contract: files should behave like durable `&`
variables under the same language-level resource model in mock handlers, the
native CLI host, and unsupported hosts.

The semantic sources of truth are:

- [spec/2026-07-02-io-resource-api.md](../../spec/2026-07-02-io-resource-api.md)
- [spec/2026-07-01-file-resource-api.md](../../spec/2026-07-01-file-resource-api.md)
- [notes/design/2026-07-02-resource-lifetime-decisions.md](../../notes/design/2026-07-02-resource-lifetime-decisions.md)
- [notes/design/2026-07-02-host-act-ffi-decisions.md](../../notes/design/2026-07-02-host-act-ffi-decisions.md)
- [notes/todo/contract-v1-file-resource-priority.md](../../notes/todo/contract-v1-file-resource-priority.md)

## Core Promise

File resource APIs should be explainable with one model:

```text
host act + session + managed view + raw escape hatch
```

For files, the user-facing version is:

```text
file = durable & variable
```

A managed text or bytes lens is a snapshot transaction:

1. Scope entry reads the backing file and creates a branch-local buffer.
2. Edits update that buffer.
3. Normal scope exit commits a dirty buffer.
4. Effect abort before scope exit rolls the branch back.
5. Multi-shot branches own independent buffers.
6. Multiple commits are ordered by arrival at scope exit, so the final backing
   value is last-write-wins.

Managed lenses do not expose `close`, `save`, `flush`, or `sync`. Ending the
write scope is the public way to end editing. Low-level synchronization belongs
under `raw`.

## Manifest Policy

`tests/yulang/cases.toml` remains the executable source of truth. Do not add
TODO, ignored, or expected-failure placeholders to the manifest.

File resource cases use these contract tags:

- `file-resource` for the Contract v1 slice itself;
- `resource-lifetime` when the case observes commit, rollback, handler-extent
  discharge, branch-local buffers, or last-write-wins;
- `metadata` when the case observes non-throwing metadata behavior such as
  missing / denied / other targets represented by `file_meta.kind`;
- `host-act` when the case observes source handlers intercepting host act
  operations before the native host registry;
- `mock-host` for pure Yulang mock host behavior;
- `host.native` for the native CLI host surface;
- `host.unsupported` for wasm, playground, sandbox, or other unsupported host
  behavior.

Rules:

- Do not combine `stable-core` with `file-resource`.
- Do not combine `stable-api` and `migration-canary`.
- Any `standard-api` file case still carries exactly one of `stable-api` or
  `migration-canary`.
- A runtime file-resource case declares a host scope. Native and unsupported
  host cases choose exactly one of `host.native` or `host.unsupported`;
  mock-host cases use `mock-host` and normally also set `host.unsupported` so
  the native registry cannot satisfy the operation first.
- A `host.unsupported` run case sets `host = "unsupported"` so the manifest
  runner exercises the public `run --host unsupported` CLI route.
- Each case must fix one compact observation: runtime output, typed failure,
  public signature, or structured diagnostic payload.
- Existing `std::io::file` helper canaries stay `migration-canary` until they
  observe this resource lifetime contract.

## Contract v1 Slices

### F1. Mock File Handler

The first executable slice is pure and should not touch the host filesystem.
It proves the language semantics before native host behavior is tightened.

Required observations:

- `file_text_with_commit`: normal scope exit writes back.
- `file_text_with_rollback_on_error`: effect abort before scope exit does not
  write back.
- `file_text_with_undet_last_write_wins`: multi-shot branches edit independent
  buffers and commit in arrival order.
- `file_text_unscoped_handler_discharge`: unscoped resources commit at the
  supplying handler extent.
- `file_text_mock_matches_native_shape`: mock and native paths expose the same
  public surface shape.

Current executable mock evidence:

- `file_mock_read_text_handler` and `file_mock_read_write_text_handler` prove
  that source handlers intercept the public `load` / `store` host act
  operations before the native host registry.
- `file_text_with_commit` proves the first production `text_with` source-mock
  path over `file_buffer`, `file::load`, and `file::store`.
- `file_mock_public_ref_view_commit` proves the inline public ref-view commit
  shape over pure Yulang state.
- `file_mock_text_with_function_commit` proves that the same public ref-view
  shape survives a reusable `text_with_mock(backing, f)` function boundary and
  callback assignment through the normal cached contract route.
- `file_mock_text_with_rollback_on_error` proves that the same public helper
  shape discards dirty callback-local buffer updates when the callback exits
  through a user error.
- `file_mock_text_with_nondet_branch_buffers` proves that the same public helper
  shape gives each `nondet.each` branch an independent callback-local buffer.

Remaining F1 evidence needs rollback, nondet/multi-shot, and unscoped ambient
discharge on the real `std::io::file::text_with` / `file::text` surface. The
current blocker is recorded in
`notes/bugs/file_text_with_callback_residual_blocker.yu`.

### F2. Native Host Parity

The native CLI host can initially avoid OS-level locking. It must still match
the snapshot transaction model:

- normal `text_with` scope exit updates the temp file;
- effect abort leaves the temp file unchanged;
- multi-shot branches own independent buffers;
- public signatures do not leak private stack evidence;
- `read_text` and `write_text` remain helper wrappers, not the center of the
  stable API story.

### F3. Unsupported Host

Unsupported host behavior is part of the contract. A sandboxed or wasm host must
not fake success, return empty data, or silently ignore writes.

The contract distinguishes:

- capability unavailable or unsupported;
- capability denied by policy;
- operation failure such as missing file, invalid path, or permission denied.

### F4. Release Evidence

The contract is complete only when representative `file-resource` cases run
through a packaged binary with bundled std, not only through a development
checkout.

## Out Of Scope

These are not part of Contract v1 File Resource:

- HTTP framework behavior;
- server request/response resources;
- direct native ABI FFI;
- remote package registry behavior;
- parser DSL or Yumark runtime exposure;
- benchmark-specific file or VM special cases.

Host act FFI registry work is the next infrastructure track. Contract v1 may
start on the current host bridge, but the final host boundary should migrate to
manifest-backed host act dispatch rather than perform-time string matching.
