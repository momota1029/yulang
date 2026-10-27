# EVENTPROOF-FULL-INTEGRATION-20261028/r1 outcome

**INCOMPLETE.** Pinned Lean 4.35.0/Lake 5.0.0; `check_lean.py --full` ran once and exited 1 after 182.41s. The selected `OriginalEventProofCut` target built successfully (23 jobs). The default-target build failed because the copied scratch project lacks the root `YulangClosure.lean`: Lake reports “some modules have bad imports or could not be read” and “no such file or directory” for that target. Therefore the helper did not reach its theorem audit phase.

Resource receipt: 4/5 internal Lean/Lake calls reached, one verifier, CPU `[0]`, peak RSS 909,140 KiB, Cargo/tests/Astra 0. Full log: `/tmp/yulang-eventproof-lifetime-20261028/integration-check/verifier-full.log`, SHA-256 `0e3cc4a06d1df76a657e1356cc429268596ec33c7ff7dfb7515460fdc70ac27b`. No retry or output modification occurred under this packet.

This failure concerns an incomplete integration scratch copy, not the checked proof module. The module, theorem audits, exact original quantifiers, 18-field generated-cut application, and fresh independent review PASS remain unchanged. The required full integration gate remains OPEN. Source/native correspondence, parent soundness, effect hygiene and production gates remain OPEN.

The boundary dispatcher recommends only a separately authorized r2 integration packet: copy the complete committed Lean project including root files, verify a complete input manifest, and run one fresh `--full` check within a new 600-second / five-call ceiling. The existing 240-second r1 packet permits no retry or transfer. The dispatcher states that the new allowance requires Luna approval; it has not been granted.


## Bounded native owner investigation

Read-only inspection of the committed `58b9e9cbb` sources found concrete native owners for identity and routing only. `receiving.rs` constructs views and receipts keyed by execution owner, view, optional formal, and retained `SourceSite`; execution validates receipt/view identity and callback-specific owner/site conditions; observation records an authentic execution with observer/event IDs. `program.rs` emits resolved Name consumption and Lambda parameter IDs, roles, and schemas from source parameters/sites. These constructors do not project semantic assignment, witness, scope, authority, incidence, or dictionary values.

The first unsupported `ReturnAlignment` component is `views`: native handles do not establish `seed.views = event.eta.views`. `fiber` and `eta0` preservation is available only inside the abstract Lean `RuntimeReadout` constructors, without a native root/readout realization. `shared` likewise needs the semantic witness readout. The seven `readback` equations require packet history plus the actual eta/witness/scope/authority/incidence/dictionary readout at the Return; only history is packet-owned. Thus these inspected native owners yield **NO_SAFE_CODE_SLICE** for closing alignment. Two readouts may agree on every inspected native identity and still return different semantic fields; this blocks inference from handles alone without refuting an actual provider. Parent/source/native and integration gates remain OPEN.

Investigation was read-only; no builds, tests, theorem edits, or integration retry.
