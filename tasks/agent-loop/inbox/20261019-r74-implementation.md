# R74 implementation handoff

Handoff ID: `R74-C1-IMPLEMENTATION-1`; revision 1; author/owner `/root`; state FROZEN pending fresh review. Sprint R74 revision 2 SHA-256 `3f120e183639c63315cbf22897a56a4215ac4c88ed7c96bfd0e26ffc5f0a3bf3`; baseline `d21c8eb3a87e43dd441474c9f138e71b1d8372ff`.

## Outcome

Implemented a test-only C1 observer, exact `by_output` key/group read projection, and one focused fixed-source test. The hook is after candidate graph capture, FreshUse preparation and LocalUse push, before the first Local step. The test resolves the helper through the existing HIR local/source occurrence, asserts exactly one helper C1 observation and default cursor, prints one simultaneous full-state ledger, and completes candidate execution. A separate test-only repair supplies the existing `capture_forest` field to two `Graph` fixtures; no assertions changed.

The first authorized attempt failed before tests ran because those two initializers omitted the test-only field. R74 revision 2 authorized one additional identical focused command. It exited 0 with 1 passed, 0 failed; no further retry is authorized. Ledger: `notes/progress/2026-10-19-r74-c1-ledger.txt`, SHA-256 `c0b8b21269e4ce997bc698c3ead5793d9a175bbf2bc309e27db7cfa5d8b8af91`, 1,155,684 bytes. Exact C1 identity: helper local ordinal 2, occurrence ordinal 14, slot 2, value 27, level 2; cursor `(0,None,false)`.

## Proof and parent application

Proof producer `/root/r74_proof` STOPPED with a conditional erasure lemma and the exact missing `by_output` read accessor. The frozen note/inbox hashes are `08d7982542ce3119839c71405c2a78597bd124d4adc1050a9e66185ca06c92bb` and `74d9d5f8ae831407a3020d647dd434bdf3fbef08a285330add5bffe83220ad3c`. Its contract-hash transcription is wrong; primary verified and records the actual revision-1 contract SHA as `9b225304040b8ff11b1f1cb79876de136ce0400d69c68fef87bf07288f2c8a25`. Revision 2 controls the added write path and verification retry.

The observer output is still an implementation result pending independent review. C1/suffix completion, consumer/provider lineage, parent preservation theorem, full type inference/evaluator, Simple-sub A/B and production remain OPEN 0→0; R50 NOT_ADOPTED. No source law, API, expected output or production code behavior was changed.

## Frozen output / review seam

See `notes/progress/2026-10-19-r74-c1-observer.md` for the complete owner map, execution receipt and code hashes. Fresh compiler/source and spec/conformance reviewers must review the same frozen code, full ledger, this handoff, the conditional proof artifacts and both R74 contract revisions. Required checks include test-only gating, immutable borrow/read semantics, exact by_output key/order capture, exact helper identity and initial cursor, field completeness/provenance, no control/order changes, unchanged expectations, and no claim beyond observed C1. Producer does not self-certify. The worker and primary are STOPPED only after the review/integration checkpoint; Luna remains sole Git owner.
