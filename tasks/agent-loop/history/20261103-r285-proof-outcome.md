# R285 producer outcome — inventory complete, preservation open

Producer `/root/sol_r285_storage_closure` STOPPED / WRITES_STOPPED with no
descendants. Charge the full 2,400s reservation; CPU, RSS and total active wall
time were not measured. The Lean module and handoff are frozen pending fresh
independent review.

## Frozen artifacts and checks

- Contract `tasks/agent-loop/sprints/extrusion-storage-closure-r285.md`,
  SHA-256 `77d26a9082294f73a2f6aca12fbccfe5e9a76307705c8673328193b8745857f7`.
- Input manifest SHA-256
  `931a1fa15351521aeb2f325b0e1822ffe6c8cbd3395b33c0846b8d38281d2ef8`;
  all 27 exact paths matched at construction and final recheck.
- Lean module
  `notes/theory/lean/YulangClosure/OriginalExtrusionStorageClosureR285.lean`,
  SHA-256 `3000b88435c4cc43a1be5844c1c938470553a30217e351799f50f01bb9f8b9cb`.
- Handoff `tasks/agent-loop/inbox/extrusion-storage-closure-r285.md`,
  SHA-256 `8dc58cf3bd03bc0a1b9b9181690928ad56d6178750b0a06592b1113b908e4afe`.
- Pinned Lake build and direct Lean check exited 0. The bundled checker audited
  19 declarations, returned 19 PASS entries, and printed full types/axioms.
  No `sorry`, project axiom, or kernel bypass appeared. `leaf_refs_transfer_pushed`
  reports `Classical.choice` together with `propext` and `Quot.sound`; the
  handoff marks two other frame lemmas as axiom-free. Independent review has
  not yet adjudicated these uses.
- One temporary diagnostic `/tmp/yulang-r285-step-attempt.log` was created
  outside the exact leases. After Luna's scope correction, the producer copied
  the relevant goal into its leased inbox, removed only its own exact temp file,
  and reported no other scratch artifacts.

## Inventory and candidate invariant

The handoff contains the finite inventory for every `State` field and all
eight `Work` constructors. It distinguishes raw `V r`/`E r`, kind-separated
canonical `qv`/`qe`, term labels, published view IDs and offsets; current vs
latent consumption; queue/publication/external transfer; and model write
owners. Captures and published Effect view tails are included. Caller
endpoints in `operation` and saved Parent operations are marked as opaque
transferred `Request` data, not locally dereferenced.

`StorageClosed` combines R283 `RowsValid` with capture, view-tail, leaf,
bucket, memo-kind, parent-kind and view-reference clauses. The producer proves
it implies R284 `CaptureComplete`, excludes both reviewed `captureGap` and
`viewTailGap`, and holds for `Computed.rowInput caller` for arbitrary callers.
Allocation/canonical/queue and read-only Work transfer lemmas are checked.

The universal step target is **OPEN**. The temporary theorem attempt failed at
the selected-work branch, leaving exactly:

```lean
∀ funds s, StorageClosed s →
  StorageClosed (resultState (perform funds popped task))
```

after `select s = some (task, popped)`. The `select = none` case closed. No
step-preservation theorem, finite `runPrefix` theorem, or computed-prefix
application was delivered. Partial failure publication still requires
closure proofs through every `perform` constructor.

## Kernel-checked caller-boundary result

`CallerRowsValid` validates both Value endpoints in
`State.operation.caller`. The concrete `invalidCaller.lower = .row 99` is
out of bounds in `Computed.rowInput invalidCaller` (two Value rows). The
kernel-checked `computed_rowInput_invalid_caller` and parametric
`no_universal_computed_input_with_caller` prove that any predicate implying
`CallerRowsValid` cannot hold for every arbitrary computed row input.

This refutes the conjunction of (a) validating externally copied caller row
payloads as local row storage and (b) assumption-free initialization for all
`Request caller`. It is not a counterexample to the delivered local-read
`StorageClosed`, not a refutation of its possible preservation, and not source
reachability. Whether externally transferred caller payloads belong inside
this storage-safety obligation remains an adjudication point for Luna and the
independent reviewer; no scope narrowing is presumed.

## Parent application

R285 does not close unchanged R70 entry-to-return safety. It supplies a
complete model consumer inventory and a bounded set of checked transfer
lemmas, but its central universal step obligation and all finite-prefix
application remain open. It also identifies a boundary mismatch for any
variant that validates copied caller endpoints while assuming arbitrary
computed requests. Rust/source initialization, publication and mutation
correspondence remain open. Parent/A/B stays 0->0; R70 and production remain
OPEN; `NO_SAFE_CODE_SLICE` remains. Fresh independent review is pending.
