# R26 active-work receipts

At 2026-10-29 19:40:26 UTC, `/root/r24_rust_compile_review` resumed as the read-only `compiler_referee` for R26. Current-session assignment: `ANNOTATION-HYGIENE-NATIVE-EVIDENCE/20261030-R26`. Requested `gpt-6.1-sol/medium`; observed model/effort UNKNOWN. Stage 1 is capped at 200 seconds (within its 1,000-second total) and covers only the exact frozen R25 candidate against baseline. No write lease or compile/test authorization. Opaque tool session ID was unavailable.

At 2026-10-29 19:40:39 UTC, `/root/r24_lean` resumed as the registered `lean_prover` for R26. Requested and observed model/effort UNKNOWN. It accepted only its four exact R26 leases: the correspondence module, project `.lake`, `isolated/ep-hygiene-r26/lean-scratch`, and its proof handoff. Fresh cap: 600 seconds, at most two audits and 120 seconds combined. At receipt, the worker had made no writes and started no Lean/Cargo process. Opaque tool session ID was unavailable.

Both fresh current-session receipts were received after admission commit `2a67427c7f12650e69a5ca3c23fc4f8799714532` and ACK commit `cd1f8ca739e1332329f613c45735faa5d3ad3f33` were pushed and verified at `origin/yulang3`. Rust author remains WAITING for the initial independent review. No heavy compiler process is active yet; reserve one heavy-process window for Lean or Cargo at a time. All R24/R25 paths remain frozen and root quarantines untouched.

## Stage-1 referee result and Lean progress

The referee completed stage 1 with **REJECT: no compile gate**. Active interval 19:40:26–19:41:53 UTC; conservatively charge 100 seconds including report. Opaque session ID was unavailable. Requested `compiler_referee`, `gpt-6.1-sol/medium`; observed effective settings UNKNOWN. Contract and input-manifest hashes matched. Frozen candidate hashes matched: machine `1d8ec9ac5ce4cb4a25e24dd81a2d15b901efd27107e047140676f27fd070ea40`, receiving `dffb3fa5ce3d9437b347840e56fe5da80a143b358745f251838f66fa3065a23f`, program `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907`. R25 delta is limited to machine/receiving; fixtures, expected output and pinned project files remain unchanged. No process remains from review.

Blocking findings in frozen R25 `machine.rs`:

1. Lines 499, 515, 521 dereference plain `usize` locals `ri`, `ki`, `ei` (bound at 453–461), preventing test compilation. Correct value/reference handling and re-review.
2. Line 278 names `yu_hir::SourceNodeKey`; the available public path is `yu_hir::shadow::SourceNodeKey`. Use the actual exported path and re-review.
3. The callback helper invokes `machine().start()`, which unwraps a `main` definition, but the exact callback source defines `answer`. Its embedded bytes also omit the authoritative blank line after the operation declaration. Both route helpers assert only `Completed`, not selected integer results `1` or `23`. Select `answer` via the correct scheduling route, pin exact source bytes, and assert actual values.
4. Lines 498–499 conflate operation-carrier construction with request execution. `ReceiverReturn` closes the fresh construction invocation before `OperationResultConsumer` executes the carrier; `Request.owner` at 3620 is the restored caller owner. Instrument distinct owners without changing runtime semantics.
5. The companion validator demands that the initial signal request already contain a continuation template minted later by its Catch (`None` at request creation versus `Some` in commit). It also equates continuation-application parent with both write-request owner and inner-Catch owner, which are different phases. Join initial request to later capture through actual event/source/owner transitions, then link application to the retained write through the actual owner path.
6. Mutation coverage omits swapped entry, Name-view, formal receipt, exact arm-key and premature-owner-retirement cases. Deleting all `OwnerClose` checks only missing evidence; it does not test premature retirement. Companion tests label signal/write as the first two observed requests rather than resolving source owners. Add the required cases and source anchors.

The delta adds useful result-view, owner-open/close, continuation and retirement coordinates; however owner-phase joins remain unsound as evidence. The reviewer found no hash mismatch and inspected no compiler/test process. This REJECT authorizes no Cargo invocation.

Lean progress at its active receipt: inputs/pins matched; R24 candidate copied into R26 and nine redundant source-State binders were removed from two preservation proof case blocks. Definitions and all 22 theorem statements are unchanged. Current candidate SHA-256 `0621f43739c12ce1e7919a50de129414a4748d8359bf46740babd69f4854011e`. Frozen checker SHA-256 `a4f10b70297cbf4d8b5bc0c7526bc29783eaf417f1f70e53eeea341d1150dde6` was copied to R26 scratch; wrapper/theorem list prepared. Audits remain 0/2; no result or axiom report exists yet.

At 19:42:15 UTC Luna checked for `cargo`, `rustc`, `lake`, and `lean`; none was active. With Rust still gated, Luna granted the Lean author a serialized heavy window for at most two pinned audits, 120 seconds combined, one at a time. No Rust/Cargo process may overlap.

## Lean audit 1 resource stop

The first R26 Lean audit stopped before its memory guard. `lake env lean` built the selected module successfully under Lean 4.35.0 (two jobs), then the bounded wrapper exited 130 after 8.063953784 seconds when sampled process-tree RSS reached 1,109,495,808 bytes, above its 1 GiB guard. `audit1.log` SHA-256 is `bd95bb5cb08c1a8151f2096098e3cd3444a568a0b15aa358bc72cc9c3aee207e`; resource record SHA-256 `774829a9c74472d73dc75079dcd35c72a139d01aae5d65cfedb3630c17e46816`; command record SHA-256 `dce71f0fc6551ecc6511446bed53f8cdc6e048251dbd3e00750f2c8cf8d2eb13`. Peak RSS and elapsed match the raw resource samples.

Four complete type/axiom blocks were emitted: `checked_use_inversion` has `[]`; `checked_catch_inversion`, `checked_catch_installed_arm`, and `checked_catch_port` each have `[propext, Quot.sound]`. Pretty-printing `permission_preserves_actual` was interrupted; later declarations have no complete report. Therefore the checker did **not** pass and the full set of 22 declarations is not axiom-audited. All audit processes are stopped; the author is WAITING and will not launch audit 2 until Luna's resource-seam disposition. No Cargo process was active.

Luna consulted `/root/next_action_selector` on whether to retain the 1 GiB per-probe guard and partition remaining checks or narrowly raise the local process-tree cap while keeping the fixed 600-second Lean envelope, two-audit maximum, 120-second combined audit cap, pinned `-j1`/`-M1024`, and one-heavy-process rule unchanged. Dispatcher response is pending.

## Resource-seam amendment

Dispatcher `/root/next_action_selector` recommended a one-time external process-tree RSS guard of 1,342,177,280 bytes (1.25 GiB) for audit 2, retaining every time/count/toolchain/`-M1024`/single-heavy-process limit. Luna approved amendment `tasks/agent-loop/sprints/effect-permission-native-evidence-20261030-r26-amendment-01.md`, SHA-256 `e5a0b0b90843c71eca1a87ac43a155e007c05b4bf79b6ad0ba3b6fc9122f752a` before execution. Audit 2 is limited to 90 seconds and the smaller of remaining combined allowance (111.936s) and actual assignment time after handoff reserve. If it fails or omits any requested block, stop; no third audit or further increase.
