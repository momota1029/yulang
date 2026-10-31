# Amendment 01 — authenticated site export invocation target

Sprint: `EFFECT-PERMISSION-AUTHENTICATED-SITE-EXPORT-20261028/r1`  
Base contract SHA-256: `4088b7dc1d357f1eb531d76ea01951630e8baf2b092856936c4e0a65f2ed77b9`  
Authority: Luna, following the material-blocker selector consultation at the invocation-1 boundary.

## Adjudicated invocation-1 outcome

Cargo invocation 1 compiled and ran the frozen identity-plus-delegation wrapper once. It exited 101 after 61.11 seconds with peak RSS 1,671,992 KiB and no timeout. The same-HIR constructor snapshot, independent source-tree/Effect-port visit comparison, both origin joins, exact owner/capture/export row checks, bounded identity equality and sibling-port swap assertions passed. The fixture then failed at the unrelated consumer assertion `state remains in the returned computation`, before the wrapper reached the two-site delegated observations. That consumer-path result remains unexplained and OPEN; it neither proves nor refutes effect hygiene.

Invocation 1's frozen source was `candidate_effect.rs` SHA-256 `3e44df6b089beabf7b8c6c0e85d7985131979f167d3ac14cfa447d8b0710d848`; `candidate_scheme.rs` remained the admitted intake SHA `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`. Its exact receipts remain under the frozen invocation-1 directory and must not be overwritten.

## Remaining invocation

The sole remaining Cargo attempt will run the repaired combined identity-and-two-site-delegation observation. The identity-only path may return after its own bounded identity/source/capture/export assertions. Preserve the consumer assertion in the original unequal test path and preserve the original `r != q` assertion verbatim; do not make either claim pass by weakening or deleting those obligations. The two-site delegated test must then execute and report its actual reached assertions. If the consumer path or unequal transport is not executed, report it OPEN.

Freeze a new source SHA, complete input inventory, argv, launcher, and separate raw receipt paths before execution. Use the existing feature-correct offline/locked CPU0 one-job/thread envelope and isolated target directory. Keep invocation 2 at its frozen 30-second timeout; invocation 1 used 61.11 seconds, and the aggregate ceiling remains 180 seconds. Luna must issue a fresh release after independently rechecking the revised source, argv, inventory, available memory and zero active heavy processes. No third attempt or automatic renewal.

Fresh independent review must inspect that the identity branch separation preserves both original obligations, authenticate the executed two-site keys and all reached native falsifiers, and retain the invocation-1 consumer-path failure plus unequal transport as OPEN. All parent, source/native, A/B, hygiene, principality, termination and production gates remain OPEN.
