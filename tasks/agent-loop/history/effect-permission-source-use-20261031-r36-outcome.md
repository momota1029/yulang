# R36 outcome — source-owned callback use and permission-row selection

Status: **CLOSED_PASS (bounded gate)**. Luna adjudication after frozen evidence and independent review.

Sprint: `EFFECT-PERMISSION-SOURCE-USE/20261031-R36`
Baseline: `1388bdc476e5dc0c0bb96532715c7280aa95b10e`
Contract SHA-256: `c471c7dd5d8ef2515022f4665f1ef2151577141a3f0942ea107489ecd86c5ac0`
Input manifest SHA-256: `cf03b01ba1cb057972303540dd7deb881e0cfff2f8dbafd93e4912035bee37e4`

## Required gate and adjudicated result

**PASS after primary repair and independent delta review.** The source-owned Rust lookup derives direct resolved parameter Name-to-Apply-callee uses from the retained HIR snapshot and binds them to the R35 Function.result row at exact negative polarity. Lean's 13 theorem types passed the producer and independent pinned 4.35.0 stdin audits; all theorem types and complete axiom sets are retained in the proof/review handoffs. Review found and independently closed one Rust field-path blocker by verifying the one-line repair against the pinned source declaration and prior frozen hash.

Reviewed artifacts:

- `program.rs`: SHA-256 `b3fc1daacdba9fa9618b9b741e4f85d8e9ea0dcd5e859540204d09200d23a65d`.
- `SourceCallbackUseR36.lean`: SHA-256 `9e15cb4982248cf90d7a11ef0c66ee7ee95ec0abe99c217d8187c31c488731de`.
- Rust handoff r2: SHA-256 `df72f3c643b1267f4d9ff40e737890d45fe4059f4c9e5b75a7c246bb5d480ec5`.
- Proof handoff r1: SHA-256 `0d1a5d7e4c31ff6722269c6d894f301950c87b34c641b395e11c8360aebd8558`.
- Independent review, final technical PASS: SHA-256 `2b2f8bb23727c82fc572046e36d2aba64b63ac2020cbb491151b871ee3779afe`.

The exact source/proof artifacts and handoffs are committed in `38abc73b9` (`feat: add source callback use witness`). The central receipt follows in the next commit; outbound range inspection and push are required before this checkpoint is reported pushed.

## Disclosed source-read incident

The Rust producer's broad recursive `rg` emitted matching line text from the quarantined `runtime/machine.rs` and `runtime/receiving.rs` into its output/context. This was an unauthorized read-boundary violation. Primary adjudication retained both path quarantines. Fresh independent review reconstructed the approved source derivation without reading those paths and found no technical dependency on them. The incident remains recorded and is not described as compliant; no path lease is released.

## Limits and remaining gates

This closes only R36's source-planned-use and conditional Lean projection gate. Rust compilation was not observed; no Cargo/build/tests/formatter ran. Rust-to-Lean HIR extraction, ownership-map validity, vector/list enumeration and empty-inventory simulation remain OPEN. Runtime execution, Name receipt, callback invocation, permission consumption, Grant/Catch, propagation, selected-arm/observation provenance, invocation lifetime, native Step/History, original Simple-sub A/B, whole-language hygiene/soundness, principality, progress, termination and production remain OPEN. The user's policy and original source domain are unchanged.
