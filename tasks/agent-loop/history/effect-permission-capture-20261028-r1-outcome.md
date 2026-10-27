# EFFECT-PERMISSION-CAPTURE-20261028/r1 outcome

**Status: INCOMPLETE.** The user's continuing goal remains Yulang inference and
executor soundness, effects, principality and termination. This bounded packet
does not narrow that goal or close any parent or production gate.

## Frozen evidence

- Sprint contract:
  `tasks/agent-loop/sprints/effect-permission-capture-20261028-r1.md`,
  SHA-256 `5150233fa70a25ab5afb960a00bc18620bc645f030026dc19a1a1a9168daa93a`.
- One corrected-run amendment:
  `tasks/agent-loop/sprints/effect-permission-capture-20261028-r1-amendment-01.md`,
  SHA-256 `35e1a4e9f9859886fd7324abca59089da7f5e2c7d71c0fe12b544c396d4d13d9`.
- Lean artifact:
  `notes/theory/lean/YulangClosure/FormalPermissionCaptureConstruction.lean`,
  SHA-256 `181d5075e2fa3ed5f4adfe4029b368461638b6ac6f62341ec165e6e3980ee13c`.
- Lean handoff:
  `tasks/agent-loop/inbox/effect-permission-construction-proof.md`,
  SHA-256 `eaac7c2db38ef17493ae5cf8a5cd8e6733f063176aafbdef543ab214e5f87331`.
- Rust extraction at reviewed commit `81fb62297`:
  `crates/yu-solver/src/shadow_apply.rs`, SHA-256
  `2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d`.
- Rust handoff:
  `tasks/agent-loop/inbox/effect-permission-construction-rust.md`, SHA-256
  `5c1bad68921ad95e3707ca90f4a9e559d01f385771ceacbe3f72829b3c2e7189`.
- Corrected Cargo receipt:
  `tasks/agent-loop/inbox/effect-permission-capture-rust-retry.md`, SHA-256
  `d3627c13b41dd86064d42521f40250b5ac4f6c909bc80eac8862975c4d221358`.
- Primary transcription of the independent review and addendum:
  `tasks/agent-loop/inbox/effect-permission-construction-review.md`, SHA-256
  `0b0f511e38aab148c761c967f92a2c7a2b8f8bac794547a41737d1ac200dc5d4`.

## Lean result

The pinned Lean 4.35.0 check exited 0. The checker audited all 16 delivered
theorem types and transitive axioms. `allocation_shared` has no axioms;
`origin_nonempty` uses `propext`; four catalog constructors use
`propext, Quot.sound`; the other ten use
`propext, Classical.choice, Quot.sound`. No `sorryAx`, project axiom or bypass
was found. The module imports only `Std`; root/default-target integration was
not run. Checker RSS was 969,156 KiB.

This proves a finite catalog-interner model conditional on a structural
`Shape` and `Origin`. It does not derive `Origin` from actual recursive Rust
construction, nor prove catalog numbering simulates `Capture`'s LIFO endpoint
drain interleaved with row/bound discovery. Canonical representative transport,
index stability, endpoint arrival and negative formal root publication remain
OPEN at `candidate_scheme.rs:2670–2703,2784–2799`. The independent reviewer
accepted the conditional model and found no hidden port-image equality premise.

## Rust result and resource deviation

The implementation extracts the existing Function/Tuple traversal into a
private `captured_formal_permission_port` helper. Independent static review
found the same success/error behavior, metadata order and rejection order as the
baseline. The existing focused tests passed after adding the required
`shadow-apply-candidate` feature:

- `negative_concrete_formal_permission_recovers_its_shared_port_and_rolls_back`
- `tuple_formal_permissions_keep_element_paths_and_transaction_ownership`

The command exited 0 in 41.22 seconds; 2 passed, 814 filtered out. However,
maximum RSS was 1,652,828 KiB, exceeding amendment 01's 1 GiB cap by 604,252
KiB. Under amendment 01 this is a resource-cap breach and makes sprint
verification **INCOMPLETE**, despite the passing tests. No further Cargo run,
retry, or code repair is authorized here.

The first misconfigured Cargo attempt exited 101 because it omitted the feature;
zero tests ran. Amendment 01 records its exact command and outcome, but no raw
first-attempt compiler log was retained or authenticated. The frozen Rust lane
handoff predates that attempt. The corrected receipt now points to amendment 01
for first-attempt evidence and records this limitation.

## Independent review and disposition

Fresh reviewer `/root/effect_permission_capture_review` conditionally accepted
the finite Lean model, identified actual source/live-capture as the blocking
proof boundary, and found the Rust extraction statically behavior-preserving.
Its addendum accepts the two passing tests as bounded evidence while requiring
INCOMPLETE status because the RSS cap was exceeded. The reviewer also found and
corrected the first-attempt evidence locator issue. The report was delivered in
read-only messages and transcribed by the primary under the exact lease.

Outcome: **INCOMPLETE**, with bounded Lean proof and Rust regression evidence
retained, but no verified Rust resource-compliant test receipt and no
constructor-to-live-capture bridge. Whole Simple-sub A/B, effect hygiene and
subtraction, complete Call, whole soundness, principality, ordinary progress,
termination, source/native correspondence and production remain OPEN. Preserve
the unrelated UNKNOWN runtime writer and all QUARANTINED leases.

The next packet should derive the actual permission constructor and capture
worklist correspondence at its Rust owners, and independently select a
resource envelope that can execute the focused candidate-feature tests without
exceeding its RSS cap. Consult the dispatcher at the sprint boundary before
admitting that packet.
