# Sprint EVENTPROOF-FULL-INTEGRATION-20261028/r1

Status: READY after primary checkout and hash gate. This is a separate, verification-only integration packet following the reviewed EVENTPROOF-CUT-APPLICATION-20261028/r1 result. Baseline is committed `yulang3` HEAD `fbb3ffc97`; the proof artifact remains on `/tmp/yulang-eventproof-lifetime-20261028`, branch `research/eventproof-cut-application-20261028-r1`, launched from `8b93abb3ad45fa01daf7b6080095209f683bccb4`.

## Fixed objective

Run the `yulang-lean-proofs` integration checker once with `--full` for the already reviewed `YulangClosure.OriginalEventProofCut` module and its two checked theorems. This packet adds no declarations, changes no proof/source semantics, and does not reopen the completed independent review. Preserve the accepted module SHA-256 `a89e00cffcdb4172688807636a871a47e47ee25b2be197cdf6f4d1be99b1a448`, the proof handoff and frozen manifest unchanged. The r1 proof, verifier and audit receipts remain the governing theorem evidence; this packet supplies only the skill-required default-target integration build.

The earlier r1 ceiling was exhausted for verifier allocations: its six Lean/Lake calls and one selected-module verifier are frozen. This is a separately budgeted packet for one `check_lean.py --full` invocation: five internal Lean/Lake calls total (Lake version, Lean version, selected-module build, default-target build, theorem type/axiom audit), one verifier, ≤240 seconds, one CPU and 1 GiB RSS target. Cargo=0, tests=0, Astra=0. No retry or budget transfer; preserve a failed receipt and stop.

## Exact write lease

Only new `/tmp/yulang-eventproof-lifetime-20261028/integration-check/`, containing a fresh project copy, checker output log, and a primary integration receipt. Create exclusively after confirming absence. Build caches and temporary checker files stay under this new scratch root or the checker's own temporary directory. The r1 `proof/`, proof module, handoff, frozen manifest, source dependencies, original `notes/theory/lean/.lake`, root imports, and all compiler/runtime files are read-only. No Git action in the isolated proof branch.

Copy the previously verified `proof/project` as the starting project and verify its pinned toolchain, lakefile, manifest, all 24 contract dependency hashes, and proof-module hash before running. The selected module is `YulangClosure.OriginalEventProofCut`; theorem roots are `body_consumer_actual_fields` and `generated_value_body_actual_fields`. Use the installed native Lake 5.0.0 for Lean 4.35.0. The one allowed command is the bundled `check_lean.py` with those two `--theorem` arguments, `--full`, absolute `--project` and `--lake`, and `--timeout 240`.

## Acceptance and scope

Accept only exit 0, both full theorem audits, default-target build completion, exact input hashes and a resource receipt within the packet ceiling. A failure, timeout, hash mismatch or unexpected write yields INCOMPLETE. Reuse the fresh reviewer PASS only for the byte-identical proof artifact and dependencies; do not claim that this checker is a second independent review.

Original source membership, native/Rust-to-Decoded correspondence, Native.World lifetime/permission, full raw-admissions conservativity, original parent soundness, A/B, effect hygiene, implementation and production gates remain OPEN.
