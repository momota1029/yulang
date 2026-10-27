# EVENTPROOF-FULL-INTEGRATION-20261028/r1 outcome

**INCOMPLETE.** Pinned Lean 4.35.0/Lake 5.0.0; `check_lean.py --full` ran once and exited 1 after 182.41s. The selected `OriginalEventProofCut` target built successfully (23 jobs). The default-target build failed because the copied scratch project lacks the root `YulangClosure.lean`: Lake reports “some modules have bad imports or could not be read” and “no such file or directory” for that target. Therefore the helper did not reach its theorem audit phase.

Resource receipt: 4/5 internal Lean/Lake calls reached, one verifier, CPU `[0]`, peak RSS 909,140 KiB, Cargo/tests/Astra 0. Full log: `/tmp/yulang-eventproof-lifetime-20261028/integration-check/verifier-full.log`, SHA-256 `0e3cc4a06d1df76a657e1356cc429268596ec33c7ff7dfb7515460fdc70ac27b`. No retry or output modification occurred under this packet.

This failure concerns an incomplete integration scratch copy, not the checked proof module. The module, theorem audits, exact original quantifiers, 18-field generated-cut application, and fresh independent review PASS remain unchanged. The required full integration gate remains OPEN. Source/native correspondence, parent soundness, effect hygiene and production gates remain OPEN.

The boundary dispatcher recommends only a separately authorized r2 integration packet: copy the complete committed Lean project including root files, verify a complete input manifest, and run one fresh `--full` check within a new 600-second / five-call ceiling. The existing 240-second r1 packet permits no retry or transfer. The dispatcher states that the new allowance requires Luna approval; it has not been granted.
