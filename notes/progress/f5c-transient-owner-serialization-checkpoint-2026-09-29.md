# F5c transient-owner serialization checkpoint — 2026-09-29

## Scope and authority

This checkpoint closes only the authorized test-and-feature-only serialization
gate. The exact suppressed owners are non-transferring `WalkerLane` kinds
54–56 and 116. The 219-row online ledger continues to observe every capacity
transition, and the full identity trace for `FlatDraft` kinds 12–17 remains.
The gate is authorized by the active task and the F5 Authoritative §§26/34
resource contract, with the exact-kind scope recorded in the
[`shared-acyclic checkpoint`](f5c-shared-acyclic-hit-mismatch-checkpoint-2026-09-29.md).
No language semantics, public API, production execution path, or resource cap
changed.

## Implementation

`crates/yu-solver/src/f5c_draft_heap.rs` returns before borrowing the sidecar
writer for the four exact kinds, after asserting that such an owner never
transfers. All online lane and composed session ledger updates still run. The
sidecar emits a fixed-width interval certificate before the next retained
event when excluded owners changed. The certificate contains excluded current
capacity/bytes and the co-temporal maximum during that interval. Four terminal
lane rows, an owner subtotal, and a session subtotal are written at close.
Count and checksum cover written records only.

`tools/check_f5c_resource_matrix.py` folds the interval certificates with the
retained identity trace to reconstruct joint current and peak values. It
checks excluded lane terminal rows, all retained physical rows, staged
same-ID transfers and releases, session baselines, finalizer peaks, and
terminal owner/session summaries. An opt-in full-event witness mode keeps the
four kinds serialized so the small complete trace can compare the hybrid
replay against the existing per-owner replay. This complete-trace oracle is
the independent lifecycle check for suppressed IDs; a scale hybrid trace does
not encode those IDs or their individual events.

## Review and finding disposition

Mode: M2, because the observer crosses Rust sidecar production, Python replay,
and same-time test accounting. Pre-write review used `spec_auditor` and
`performance_auditor`; post-write delta review used the same two roles. The
initial exact-kind filter proposal was not accepted as sufficient because the
existing replay derived owner current and peaks from every event. A read-only
architect review confirmed that interval certificates plus terminal summaries
are a local protocol choice inside the approved gate; no new user decision was
needed. Both post-write reviewers found no blocking, major, or minor issues in
the changed diff and direct dependency cone.

The performance review found one kind-code branch and TLS flag read before
return for each suppressed serialization call. Existing online adjustments
remain O(1); excluded tracking adds fixed checked arithmetic on capacity
changes. Dirty interval state is fixed-size, and at most one 64-byte
certificate is emitted before a retained record or at close. Close writes
four 64-byte lane rows plus two 64-byte terminal records. The Python replay
adds fixed-size lane/family work per record and does not rescan event history.
The focused test reads its whole small sidecar in O(E) time and space; it is
not a scale entrypoint.

## Verification

The implementer reported these focused checks passing:

- `RUSTC_WRAPPER= cargo test -p yu-solver --features f5c_resource_probe --offline -j 2 f5c_walker_online_shadow_witness -- --nocapture`
- The corresponding `f5c_joint_session_replay_witness` command.
- Both focused witnesses and Python replay in normal suppression mode and
  `F5C_FULL_WALKER_EVENTS=1` oracle mode.
- Mutation checks for altered lane and owner terminal records, with recomputed
  checksum; the checker rejected both inputs.
- Python AST parsing of `tools/check_f5c_resource_matrix.py` and
  `git diff --check`.

The walker witness wrote 412 records / 26,376 bytes in suppression mode and
434 / 27,784 bytes in full-event mode. The live session witness wrote 942 /
60,296 bytes and 957 / 61,256 bytes, respectively. Its online counters were
E=553 owner adjustments/transfers, S=33 samples, and F=3 finalizers. These are
small witness counts, not scale evidence. No timing or RSS sample was taken.

## Remaining limits and next gate

No resource/scale process, diagnostic, or matrix row ran. The Python matrix
replay path was updated but not exercised against a captured matrix row. A
hybrid trace cannot independently recover suppressed owner IDs or exact
per-owner inter-boundary peaks; the complete small oracle establishes replay
parity while interval certificates preserve co-temporal aggregate peaks.

The measurement plan at
[`f5c-no-cap-scale-measurement-plan`](f5c-no-cap-scale-measurement-plan-2026-09-28.md)
was rechecked. Its isolated D=32/K=32 invocation is consumed, and it grants no
further process budget. Before any scale, diagnostic, or matrix process, the
next gate is to produce and independently review a fresh plan with the exact
input, process/sample budget, host floors, timeout, and stop criteria. The
earlier timed-out sidecar remains unusable; corrected-scale completion remains
open.
