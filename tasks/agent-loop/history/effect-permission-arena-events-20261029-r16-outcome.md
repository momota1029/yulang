# R16 outcome: constructor-event derivation

Status: **CLOSED_COMPLETE_CONDITIONAL**. Adjudicated by Luna under the unchanged Simple-sub inference/executor goal. No production or source/native closure is claimed.

## Delivered result

`YulangClosure.FormalPermissionArenaEvents` supplies a checked protocol for live-variable and positive/negative function constructor event suffixes. It derives the ordered suffix from fixed operation stages, explicit reserve outcomes, capacity-change observations, cache status, active-journal status, page need, child validation, and publication outcome. It retains an arbitrary existing event prefix and proves its combined six-slot bound only under explicit `Fits`.

The artifact is 10,043 bytes, SHA-256 `02ef97716d882073ccb2e53c53bbf8046c80e82a517253898db5d1c02cd1b8b3`. Its proof handoff is SHA-256 `e138820b2bd603768f8acbd2f0ab5f1d41815cc5379f52f0dce8239dd5eba8d1`; the source handoff is `812a2b7b75f2c52171accad8640affbd800523b74fd85bf48776d8a94fcef814`.

Primary Lean 4.35.0 Audit 2 passed all 56 roots: 38 inherited R12/R13/R15 roots and 18 R16 roots. It printed all theorem types and transitive axiom reports. The new roots use no axioms in two cases, only `propext` in fifteen, and `propext` plus `Quot.sound` in one. The audit took 4.553 seconds with maximum RSS 1,003,004 KiB. Audit 1 failed on parsing/proof construction and remains preserved; its repair was limited to Sublist notation, a reserved binder name, and a membership proof. See the evidence record for complete raw receipts and the failed diagnostics.

Fresh nonauthor review: **PASS** for the bounded conditional protocol, no blocking or major findings. The reviewer authenticated all 174 manifest entries, 18 copied project files, all 56 theorem/axiom blocks, and source branch order. One minor evidence metadata error (`pass_lines: 0`) was corrected by a separate authenticated supplemental receipt; no original audit receipt or raw output was modified. Review SHA-256: `f30295751cd5cfae2534b4f72ee55997ad751a8b235e7efa56437964e112f939`.

## Remaining gates

The protocol does not certify Rust allocator/reserve behavior, truthful observations, initial-buffer provenance or `Fits`, page identity authenticity, sampler availability/execution, actual constructor execution or returned-result correspondence. Tuple and structural-backed constructors remain outside this packet. Source/native correspondence, the original all-program parent, effect hygiene, consumer residual, soundness, principality, termination, and production remain **OPEN**.

No tests, Cargo, runtime instrumentation, source edits, or Git staging/commit/push were performed. The R15 source-hash Git disposition remains in force.

## Next bounded action

The sprint-end selector recommends a checked event-buffer lifecycle packet: prove the six-slot `Option` buffer's occupied-prefix/empty-suffix invariant, exact ordered drain/reset, safety of the R16 suffix after an empty entry, and preservation of empty entry state through consecutive selected wrapper calls, including constructor and early sampler failures. Initial emptiness must remain conditional on the actual source call path; arbitrary prefixes and interleaved mutations remain explicit. Selector recommendation: `/root/r21_closeout_selector`, sprint-end consultation after Audit 2 and independent review.
