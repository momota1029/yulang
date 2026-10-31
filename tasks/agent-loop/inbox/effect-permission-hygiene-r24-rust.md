# R24 Rust handoff — revision 2 (test observer and validator freeze)

Assignment: `/root/effect_permission_hygiene_r24_rust`  
Sprint: `ANNOTATION-HYGIENE-TRANSITIONS/20261030-R24`  
Contract SHA-256: `4fc63b868a8e61f8b4a5c1c59e6dccc4e8b6aa4e8e9afa24985c0408654ac39b`  
Isolated base: `9a74a70a32ebda716a00c7203d8e606343cf442a`  
Schema R1: `686c96c8f8b5417b075a18954f773ad4071996e51e809d65040a87441c342c3c`  
Authenticated receipt: `isolated/ep-hygiene-r24/project/receipts/hygiene.json`, SHA-256 `e455690d6873880567ddadbe7cd5273da424f1e0fbffc2c80ebee59676b98b1e`

## Frozen source targets

All instrumentation and validator code is under `#[cfg(test)]`; no solver, execution decision, fixture, expected output, or source example was edited. Schema R1 meaning is unchanged.

| Path | SHA-256 |
|---|---|
| `tools/inference-playground/src/runtime/machine.rs` | `31509af5722c75443fecb632b1a7c7f6e6e565c39b6a7919a90a3aea2f7d9b57` |
| `tools/inference-playground/src/runtime/receiving.rs` | `a7878778b87b2857b7a3bf5204319bfaa65adbec2436c0bf95b296937f19ae45` |
| `tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |
| `receipts/hygiene.json` (frozen R1) | `e455690d6873880567ddadbe7cd5273da424f1e0fbffc2c80ebee59676b98b1e` |

`HygieneTrace::record` mints monotonically increasing observation ordinals at the owning hooks. The validator checks ordinal continuity/order and joins permission schema, callback entry, distinct formal and Name receipts, direct Name/body Apply, callback execution, request event/op/payload, exact Catch owner/handler/arm key/range, result, and shallow-discard. The companion validator connects the unchanged inner signal request/Catch to a distinct retained write request and its separate outer Catch, and distinguishes captured continuation from shallow discard.

Authored rejection cases cover invocation owner mutation, ModuleRun, entry/use/Name-view/formal-receipt, absent permission, schema mismatch, payload/arm/arm-range/Catch-owner/event mutation, each missing callback transition, request/Catch and Catch/discard reordering, shallow retirement lifetime mutation, companion signal/write lifetime changes, disconnected or missing write, and missing outer consumer. These are authored assertions only; none has been executed.

## Evidence and provisional boundary

Reused only as diagnostics: R23's owner-minted ordinal approach and its rejected four blockers (Option-closure `?`, mixed `usize`/`ExecutionOwner`, inadequate mutation rejection, and substring/Catch-arm plus disconnected companion evidence). No R23 implementation was copied or restored. The source-to-runtime hooks are static implementation evidence pending an independent exact-hash review and authorized execution. No runtime trace or result is claimed.

Falsifier: an independent reviewer finds a disconnected owner/source join, missing required rejection family, or non-test semantic effect; later authorized compile/test may also falsify the authored code. Cleanup owner: Luna, as sole integrator, can remove or revise these provisional test-only hooks if falsified. Any source change invalidates this freeze and its review hashes.

## Checks, resources, and next step

No Cargo/Rust compiler/tests, formatter, Lean/Lake, or runtime process was launched. No raw test trace exists. `program.rs` and R1 receipt remain byte-identical to the isolated baseline/R1. No scratch or generated paths were created; `build-target` is untouched. No Git operation was performed.

Requested model/effort: Luna/high. Observed model/effort: UNKNOWN from worker runtime metadata. Active budget was 2,010 seconds at resumed authorization; approximately 330 seconds have elapsed since the latest recorded progress at 2026-10-29 18:28:42 UTC, so the conservative remaining bound is about 1,680 seconds. Worker remains active; no stop receipt.

Next in-envelope step: obtain a fresh independent `compiler_referee` review of the exact frozen hashes and proposed argv. Do not launch Cargo without its explicit ACCEPT. The compile-only ACCEPT can authorize only the contract's `cargo check --tests --locked --offline -p yu-playground` gate. Runtime tests require a separate fresh exact-hash full ACCEPT after that gate and review of both routes. Coordinate the heavy window with Luna and serialize against Lean.
