# R27 amendment 02 — select the companion main result

Sprint: EFFECT-PERMISSION-OWNER-CERTIFICATE/20261030-R27. Luna remains primary. This revision preserves the original outcome, source domain, accepted semantics, schema r2, resource envelope, exact worker paths, stop conditions, and production boundary.

## Evidence prompting the amendment

The corrected R2 callback baseline completed with status 0, stdout `1`, and elapsed time 25.426 seconds. The corrected companion invocation using `--run-module` completed with status 0, empty stdout, and elapsed time 0.626 seconds; its raw capture is `isolated/ep-owner-certificate-r27/project/build-target/r27-companion-baseline-r2.json`, SHA-256 `a1d4406c811cbd79b67fbbd4b133586d291a0d118dd089f8c6cf5be394ac1c37`.

The pinned CLI help in `tools/inference-playground/src/main.rs` defines `--run-module` as running the module schedule without selecting a definition. The README documents `--run main` as the selected-definition route. Therefore the empty output does not establish the companion's expected result 23. Keep that invocation as a successful module-route observation, not as selected-main evidence. No candidate compile/runtime was run.

## Exact sequential correction

1. Inputs revision 3 changes the companion baseline command to `cargo run -q -p yu-playground --bin yu-playground -- --run main tools/inference-playground/examples/original-suffix-outer-receiver.yu`. It preserves the callback result and records both R2 observations and the raw capture identity.
2. Run this one corrected baseline serially on the existing Rust `build-target` lease, recording status, stdout, stderr, elapsed time, and raw-capture hash. The expected selected-main result remains 23.
3. Keep schema r2 unchanged. The proof lane remains paused for Lean/Lake until this Cargo process has ended and Luna grants the serialized Lean audit window. Candidate compile/runtime remains prohibited until fresh independent exact-hash ACCEPT and separate Luna authorization.

No source transition or expected result is inferred from the empty R2 stdout. No semantic, schema, source-domain, budget-cap, lease, or production authority changes.

## Frozen revisions and current accounting

Base contract r1 remains SHA-256 `2cc9c8ae08a6fcbf98f237e6a1640ceb042a456a6beaadc448fa0a0308b431f0`; schema r2 remains SHA-256 `84187379d1a81b1965c34c027e7532198bebc4c4110eaa1c05808bada6bf6d8c`. Inputs r3: `tasks/agent-loop/sprints/effect-permission-owner-certificate-20261030-r27-inputs-r3.json`, SHA-256 `06fcdb4292b3364b9a40b75dcb9b57419ff0bfb50628d422cd5ec69ad0e5c6bc`. It supersedes inputs r2 SHA-256 `0ea399f056c95861277ed5dc4717dc678a8e0b4cc3d0782f6875dfa789d8ac99`. This amendment is immutable; no prior record is overwritten.

At 2026-10-29 20:55 UTC the live roster showed Rust paused with no Cargo/rustc process and proof paused with no Lean/Lake process; both confirmed write cessation. Rust has 1,070/1,550 seconds remaining after a conservative 120-second charge for resumed work and the two corrected baseline invocations. Lean has 120/800 seconds remaining per the proof author's conservative report. Reviewer remains 1,000/1,000 seconds. Luna has 3,200/3,850 seconds remaining after a conservative 290-second primary-work charge. Aggregate Cargo cap remains 360 seconds and aggregate Lean audit cap remains 120 seconds; no R26 budget transfer occurred. Requested/effective child model metadata remains exactly as recorded in current state.
