# F5c global session composition checkpoint — 2026-09-29

## Scope and authority

This checkpoint closes the test-only global co-temporal composition gate. It
does not close F5c's serialization reduction or corrected-scale campaign.
The implementation is confined to:

- `crates/yu-solver/src/f5c_draft_heap.rs`
- `crates/yu-solver/src/lib.rs`
- `crates/yu-solver/src/tests/f5c_resource_probe.rs`
- `tools/check_f5c_resource_matrix.py`

The governing contract is the current `tasks/current.md` gate, the F5c
Authoritative designs indexed by `notes/design/INDEX.md`,
`notes/design/2026-09-25-f5c-flat-indexed-stack-independent-draft.md`
§§5/7/15, `notes/design/2026-09-26-f5c-shared-walker-flat-sink-draft.md`
§22, and the approved no-numeric-resource-caps addendum. No language
semantics, public API, production resource cap, or production execution path
changed.

## Implementation

The fixed online shadow retains all 219 owner rows. At each successful
existing resource sample, it records the independent inference-session
current, exact online-owner current, exact closed-type current, and the sum of
the six already-sampled route lane currents. Checked subtraction derives the
remaining session owners; checked recomposition must equal the independent
session current. This rebases other session lanes at every existing sample.

At each successful indexed finalizer, the ledger requires checkpoint-before
to equal the closed-type baseline. It combines the other-session residual,
online-owner current, route current, and that call's
`peak_bytes_during_call()` once, then replaces the closed current with
checkpoint-after once. It does not add historical finalizer or lane peaks.
The hook runs after successful resource-ledger publication and before mapped
draft drop or the following `DraftMember` sample.

The live fixture records 33 sample boundaries, 3 successful finalizer calls,
and 553 online owner adjustment/transfer operations. It exercises two actual
source/indexed overlaps during finalization, route capacity growth and
decrease, a `DraftMember` residual rebase, and a historical-peak
non-co-temporal counterexample. Each baseline and finalizer record is 64
bytes, for `64 × (33 + 3) = 2,304` added boundary bytes. The full owner trace
remains available, including staged kinds 12–17. The prior synthetic witness
still reconciles all 219 exact owner rows. All new hooks and the finalizer
export use `cfg(all(test, feature = "f5c_resource_probe"))`.

The Python replay now maintains indexed/source live-owner counters so the
finalizer overlap predicate is O(1) per event instead of scanning all live
owners at each finalizer. It also unpacks each fixed-width event once.

## Review and finding disposition

Mode: M2 cross-layer test-contract and resource-observer gate. Pre-write and
post-write review used one `spec_auditor` and one `performance_auditor`; one
batched implementer repair pass followed accepted findings.

- The first post-write specification review found a major cfg mismatch: the
  finalizer call was feature-gated while its export was test-and-feature-only.
  The guard now matches at both call sites and export.
- The first performance review identified per-owner-event composition work
  (aggregate O(E+S+F)) and an O(F × live owners) replay scan. The approved
  protocol already required O(1) current/peak updates at each owner event;
  the implementation now reports E explicitly, and the replay scan was
  replaced with incremental counters.
- The final performance delta review found no material remaining issue. It
  reports E=553, S=33, F=3 and `64 × (S+F)=2,304` boundary bytes. Route
  aggregation visits only six fixed lanes at a successful sample. The added
  state is test-only; the source feature check covers non-test compilation.
- The final specification delta requested an additional `E > S+F` assertion.
  Primary adjudication rejected this predicate as outside the approved
  contract: the contract requires actual E/S/F accounting and exact boundary
  record volume, but establishes no inequality between them. The witness
  reports E from its direct test-side counter; replay does not independently
  reconstruct E, and no independent-replay claim is made.

## Verification

Passed:

- `RUSTC_WRAPPER= cargo check -p yu-solver --features f5c_resource_probe --offline -j 2`
- Focused `f5c_joint_session_replay_witness` (1 test) and its Python sidecar
  replay: E=553, S=33, F=3, 2,304 added boundary bytes.
- Focused `f5c_walker_online_shadow_witness` (1 test) and its Python replay:
  417 full events and 219 exact lane rows plus the joint subtotal.
- Python AST parse of `tools/check_f5c_resource_matrix.py`.
- `git diff --check`.

No resource/scale process, diagnostic, or matrix row ran. No timing or RSS
measurement ran; the performance conclusion for this gate is static cost
accounting plus the focused observed E/S/F counts. The separate resource/scale
campaign and any production-readiness conclusion remain open.

## Next gate

Suppress serialization only for non-transferring WalkerLane kinds 54–56 and
116. Preserve the full FlatDraft trace for kinds 12–17, keep the online owner
shadow and composed witness, then perform the fresh review and refresh the
resource measurement plan before any resource/scale process.
