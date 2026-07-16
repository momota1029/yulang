# Contract v1: File / Host Resource priority memo

Status: this memo is now a status snapshot, not a broad next-slice plan.
The core file-resource contract and its last immediate parity slice are closed.
No further immediate Contract v1 file-resource slice is queued here; broader
work remains in the post-v1 deferred list below.

## DONE

Evidence commits:

- File contract closure: `79b4836d`, `b190f3d9`, `55c0d50`, `ef2cfaff`,
  `724d60f4`, `86e069e3`.
- Host manifest / registry: `fd90d094`, `0b77edc3`, `2d3f18eb`,
  `425122d0`, `02a88f2f`, `357d57e4`.
- Server / suspend first slices: `c9196ba0`, `2adf2afd`, `a5d631e2`,
  `b79de22f`, `c3719344`, `f7a4b01d`, `6d235422`, `255a7942`.

Closed work:

- Mock file-resource fixtures: commit, rollback, nondet last-write-wins,
  unscoped discharge, and nested cross-file behavior.
- Native file-resource parity: load / store / metadata, typed failures,
  `text_with` commit / rollback / nondet / nested / state-var behavior, and
  unscoped ambient text.
- Unsupported-host coverage: file helpers, metadata, ambient text, console,
  and structured host failures.
- Legacy snapshot / session helpers retired; raw-compat is limited to
  `read_at` / `write_at`.
- Host act manifest / registry landed: `pub host act`, compiler-produced
  manifests, hash / column / symbol / surface / tier data, plan manifest
  registry, `HostOpFn` / `BoundaryValue`, and console / time / file / net
  routing.
- Server first slices landed: mock-server driver, unscoped `net::serve`, typed
  double respond, and native TCP startup alpha.
- Release smoke covers representative file-resource, host-act, manifest, and
  state-protocol sugar cases.
- Ambient line-editing parity closed on 2026-07-16: the existing native and
  source-mock update-chain cases now have an unsupported-host sibling at
  [`file_ref_lines_each_update_chain_unsupported_host.yu`](../../tests/yulang/regressions/runtime/file_ref_lines_each_update_chain_unsupported_host.yu).

## NEXT SLICE — CLOSED 2026-07-16

- Source-mock and unsupported-host parity for the unscoped ambient line-editing
  idiom (`$doc.lines.each` style) is closed.

No replacement immediate slice is named in this memo. Do not promote bytes /
range / directory / server expansion from the deferred list without a separate
priority decision.

## DEFERRED / POST-V1

These are not blocking beta and are not the immediate next slice:

- Bytes / range semantics.
- Directory listing.
- Portable metadata expansion.
- Lock policy.
- Future public `file_session` / raw API.
- Raw-compat range helper completion.
- Remaining server work: `l.requests`, `serve_with`, connect-side `conn`
  forms, real HTTP adapter, cancellation surface, termination, timeouts, and
  backpressure.
- Static route Stage 1. This remains blocked on Stage M1 profile results; do
  not loosen the classifier to force progress.
