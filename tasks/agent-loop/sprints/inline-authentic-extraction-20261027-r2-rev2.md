# INLINE-AUTHENTIC-EXTRACTION-20261027/r2 — revision 2: lock reconciliation gate

Status: admitted by Luna as a versioned resource/dependency adjustment within
the same r2 sprint. This revision preserves the original goal, source domain,
trace outcome, exact author leases and all proof/implementation boundaries in
`inline-authentic-extraction-20261027-r2.md` (SHA-256
`af6c0f6e462f6ad414f7c82572216422925fe9ff3a68c1fe8d99df8f1605672e`). It
incorporates the frozen stage-1 receipt `inline-authentic-extraction-20261027-r2-stage1.md`
(SHA-256 `e12c60217b8a5c4baf9e0cf78074234b4a1449ccad7fabcf2bbbfeb15ea2e13b`).
No previous spend, failed call, receipt, or parent obligation is erased.

## Baselines and preserved owner pins

- **Source baseline:** `232b024e0d793714027170a388ab746ce0d2b429`; the r2 direct
  HIR/syntax/Lean source hashes remain authoritative and matched in phase 1.
- **Initial implementation checkout:** `1cc8406e3a70c29b04c0e48991b00cbf8812677b`,
  which included the r2 admission contract after the source baseline.
- **Reconciliation checkout:** `374f58d5f` (stage-1 artifacts and current-state
  receipt). Changes since the source baseline are scoped to r2 documents,
  current scheduling state and the isolated research package; source-owner
  hashes remain pinned.

## Exact lock correction and metadata validation

Stage 1 established that the 26-node isolated graph contains no `yu-solver`.
Its only pin mismatch is `rowan` 0.15.19 vs root-lock 0.15.17 and `unicode-ident`
1.0.27 vs root-lock 1.0.24. The existing `yu-syntax` requirements (`rowan =
"0.15"`, `unicode-ident = "1.0"`) admit the pinned root versions. The compared
rowan dependency sets agree; the root lock's `hashbrown 0.14.5` qualifier
selects the isolated graph's sole hashbrown package.

The implementation worker may now edit **only** the leased isolated
`tools/inline-authentic-extraction/Cargo.lock`: replace the `rowan` and
`unicode-ident` package records with the exact corresponding package records
from pinned root `Cargo.lock` SHA-256
`de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`. Do not
change the isolated manifest, dependency edges, root manifest/lock, or any
compiler/source/Lean files in this phase.

Then run exactly one validation command, with no compilation:

```sh
cargo metadata --offline --locked --format-version 1 \
  --manifest-path tools/inline-authentic-extraction/Cargo.toml
```

Limit: 30 seconds, one CPU, 1 GiB. Stop if the lock would change, a package is
unavailable, or the full resolved graph differs unexpectedly. Freeze the new
isolated lock, full graph, command/stdout/stderr/exit/duration hashes and compare
all 22 registry `(name, version, checksum)` tuples to root `Cargo.lock`. Confirm
one isolated workspace member and no `yu-solver` in packages, nodes or edges.
Return a sequential revision-2 implementation handoff to Luna. This phase
authorizes **no** extractor code changes, compile, run, test or Lean work.

## Preserved resources and next gate

All 3 Cargo calls from r2 stage 1 remain charged (failed lock generation, lock
generation, metadata). The sprint maximum is explicitly revised to **6 Cargo
invocations total**: 3 spent, this single metadata validation, then at most 2
locked offline extractor compile/run calls (each <=120 seconds, 1 CPU/1 GiB)
after Luna freezes the updated lock/graph and issues another contract
acknowledgement. The remaining process allowance is at most 270 seconds. The
3600-second sprint envelope is unchanged; unmetered active time is not refunded.
Lean remains <=6 calls/360 aggregate seconds after trace freeze, one verification
owner; Astra 0. No concurrent Cargo/Lean verifier. No tests are authorized.

The proof worker's frozen phase-1 handoff
`inline-authentic-extraction-20261027-r2.md` (SHA-256
`afc9346b4653d111b30ad40a820a576a5e86aca7bc8dbc99722367e08b46298c`) remains
valid. It identifies the original `Site`/`Name`/declaration/root-`Context`/
ambient-telescope equation as OPEN, locally to the inspected owners. The proof
lane waits for the authentic executed trace; it may not substitute a hand-made
trace or invented Nat allocation.

The `next_action_selector` was reconsulted on the material lock/resource
obstruction. It recommended this same-sprint staged revision and no new worker,
resource reset or compile authority. After Luna verifies the adjusted graph,
another immutable revision must pin its exact hashes before extractor code or
compilation. Full original A/B, soundness, effect hygiene, principality,
progress/termination, source/native and production gates all remain OPEN.
