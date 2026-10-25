# LEAN-CALL-ENTRY-SPINE-20261025/r1 outcome

Status: **FAILED_VERIFICATION / UNACCEPTED**. This outcome records an elaboration failure in the frozen P candidate; it is not a counterexample to the proposition. The original user goal and all parent gates remain OPEN.

## Frozen scope and evidence

The frozen r1 contract is `call-entry-spine-20261025-r1.md`, SHA-256 `77affc0d4d0765c8fffd92fc41653a154ab66bb6598c31c039e4e518d449d4d9`. P and Q authors STOPPED before Luna's composition. Exact frozen candidates:

- P `CallEntryTyping.lean`: `21850ac899060ade9f9db5139b20e5e1779b4f18b67d6d1127501827ec146ba2`; handoff `20261025-call-entry-typing.md`: `4e39371d8e46f722e025e203247a913a76aac8da4e5bccb7d5ea411bea8a1cd4`.
- Q `CallPeelingTyping.lean`: `f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44`; handoff `20261025-call-peeling-typing.md`: `70f2d41c9a785fb5d7d1cee065322c6b68c41bab2ff927f401218c79f20f865b`.
- Luna composition candidate `CallEntrySpine.lean`: `6c6bd7b4c912e86196434465a94a1ada02fe1d28cc8c0e5343b247a2dd7961b6`.
- Exact query source `.lake/call-entry-spine-r1-check.lean`: `3a51fe2832d496516071f0e677be40433a35cf046bad1d28c1a44fbbe891ac5e`.
- Full JSONL verification receipt: `20261025-call-entry-spine-verification.jsonl`, SHA-256 `642ea38398b282b31c6a1f1e66809af52f7ad1c08047f66459787a8777efb360`.

All pinned source/toolchain inputs matched the frozen contract. Five accepted r3 modules were reused only after each source hash and both `.olean`/`.ilean` hashes matched the prior accepted r3 receipt. The first new invocation compiled P with Lean 4.35, `lake env lean -j1 -M1024`, and exited 1 after 2.807 seconds. Complete stdout/stderr and command details are in the JSONL. The reported elaboration failure centers on a dependent `match mode` whose discriminants accumulate across `hbody`, `hentered`, and `hinput`, producing type mismatches at the entry derivation, consumer bind, and final simplification.

Per the contract, verification stopped at that first compile failure. Q, composition, and signature/axiom query were **NOT_RUN**; no successful P/Q/composition output hashes exist. No independent theorem review was started. No tests ran. The source/native, operational Call, effect, inference A/B, and production gates remain OPEN.

## Application and next evidence

The exact P proposition remains unchanged and is not yet established. Q's candidate has no compiler evidence; its existence and preservation claims remain unchecked. The r3 typed-plugging result remains accepted and supplies no missing operational/source premise.

The dispatcher proposed a fresh r2 repair envelope: author a new `CallEntryTypingRepair.lean` with the exact P proposition and a proof split on `mode` before constructing branch-specific computations; keep frozen P/Q/r1 composition unchanged; check repaired P, unchanged Q, a composition importing repaired P and Q, then query signatures and axioms. This is a proposal until Luna freezes a new contract and leases. No automatic repair continuation or r1 budget carryover is authorized.

## Resource and Git receipt

P and Q author grants are conservatively charged in full (900s and 1,200s). Luna's composition source was written within the 600s cap; serialized verification stopped at its first invocation (2.807s). Review and integration grants were not spent. No Astra, test, or implementation work occurred. The r1 failure evidence is preserved as a research artifact and makes no theorem-closure claim.
