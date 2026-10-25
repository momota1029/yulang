# LEAN-CALL-ENTRY-SPINE-20261025/r2 outcome

Status: **FAILED_VERIFICATION / UNACCEPTED**. P and Q compiled; the primary composition module failed Lean elaboration. The syntax theorem, broader semantics/type-inference goal, and every parent gate remain OPEN. The failure is not a mathematical counterexample.

## Frozen evidence and exact result

Frozen contract `call-entry-spine-20261025-r2.md`, SHA-256 `0f81f286dd3910f48b3f7b49d4f61a6c7a415609a16f0e473fe093bf567c18d4`, baseline `3199f25f0`:

- P repair source `CallEntryTypingRepair.lean`: `f90c2192422e35cc7f85716e29199c9587976e230e12543aff0609eedcc49c39`; handoff `20261025-call-entry-typing-repair-r2.md`: `cf35a45c656146fd182e5c7b90ea0eb5d69d072696a301a6c4f543de28e856cd`.
- Unchanged Q source `CallPeelingTyping.lean`: `f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44`; handoff `20261025-call-peeling-typing.md`: `70f2d41c9a785fb5d7d1cee065322c6b68c41bab2ff927f401218c79f20f865b`.
- Luna composition candidate `CallEntrySpineRepair.lean`: `ad4a2e1b49b13dc71b77b079b80b0c6c6355327915a4be343276b9b9497f7d89`.
- Signature/axiom query source `.lake/call-entry-spine-r2-check.lean`: `4b2722280ad703f81ce172f7426a3cc694083459f74bf14121b1cfe2d3da45ed`; it was not executed.
- Complete JSONL receipt `20261025-call-entry-spine-r2-verification.jsonl`: SHA-256 `91d4ff52fd157478e4c55d4cb48c61d91e1d9886422853885793a30646dc413b`.

The r3 accepted dependencies and their `.olean`/`.ilean` outputs were revalidated before compilation. Serialized order and evidence:

1. `CallEntryTypingRepair`: exit 0, 2.625s; `.olean` `0417fe931dda913d46712a601369424799963710c40cd1749afcc6b450e8de1e`, `.ilean` `967866bbd5badbe7b8deeb7d5bb4cd464ed95cbecf3d496702aab94fede1e7c5`.
2. Unchanged `CallPeelingTyping`: exit 0, 0.262s; `.olean` `de469ab6f25559f8c79b0f5242c310620b170e202dbdbebfba37f9343fa22df5`, `.ilean` `5d6b7afd92956b7ffe6ac715bf5e29aea0e49aea5a8fdb36601bc445179e5b4d`.
3. `CallEntrySpineRepair`: exit 1, 0.241s. Exact stdout reports unknown `consumer'` / `consumer'.output` in both lambda cases at lines 37, 40, 45 and 48. Complete command, inputs, stdout and stderr are in the JSONL; no successful composition output exists.

The contract required stopping at the first failed module. Query, axiom inspection, fresh review, and integration review were **NOT_RUN**. P/Q successful compilation is not independent review or parent theorem closure. All operational/source/native, effects, Call A/B, inference A/B, and production gates remain OPEN.

## Next step and resource receipt

The exact parent theorem remains the frozen `completeCallEntry_typed`. No P/Q repair is indicated by this diagnostic. The dispatcher has been consulted for a new primary-owned composition-only packet with a fresh exact output path, unchanged theorem, complete receipt/query, and independent review. Any proposed repair remains unapproved until Luna freezes its contract and leases. r2's failed composition bytes remain unchanged.

P author grant charged 600s. Luna composition grant charged 240s conservatively. Serialized Lean work used 3.128s across P/Q/composition, after required pin and artifact checks. Review/integration were not run; no budget carries over. No tests, Astra, or implementation changes occurred.
