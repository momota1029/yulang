# R128 rev4 independent recovery compiler/source review

Verdict: **CLEAN for prospective recovery of the exact frozen candidate**. This does not change the rev3 MAJOR / not CLEAN verdict or erase its verification-order breach. Reviewer `/root/r128_recovery_compiler`; read-only source/hash inspection, no tests, builds, probes, formatter, or Git mutations. Only this receipt is written. Charge the full 80-second allocation conservatively; reviewer stopped with no descendants.

## Authenticated submission

Independently computed SHA-256 values match the assigned frozen inputs:

- Rev4 contract: `dbb6c40e4add69394fbb13696e09765af1167fb652005e5cce45782076a9585a`.
- Recovery receipt: `db8d79d86b07d262b7e26fea348a3287b2c654807c3c204442d29f34a55596d6`.
- Proof: `3d1ffc3f2fa32b7b3a663235c1d8abfbef7ad42880b308fd098dc05c7e9ae786`.
- Complete test blob at `72700e3b1e5ebb46045604aa0ec7ecc9c3c09a9d`: `1e4ffaa52e14008716da3a790808cf6bae7aea5b165b71df4283d94c7c7f9571`.
- Complete test blob at `58d5507d400385d7b4affbda1e7c9b51779ce019`: `65de2d91ff14af0c5408fc1f1770deefd4a4e611d7bd327d4c3bfc55b58e98fb`.

The pre-repair commit independently reports subject `Checkpoint` and parent `b37e7ab9defb1b2142976c1bef782c08a3ba6b31`. Comparing its complete test blob with the final blob yields exactly six replacements, at final test lines 377, 418, 421, 439, 443 and 454: each adds `&` to the argument of `artifact.position(...)`. Removing those six added borrow characters reproduces the complete earlier blob. No assertion, fixture, root, source key, control, or expected value changed. This repairs the Rust call-site borrowing cause without weakening the structural checks. Git authenticates byte lineage; personal authorship of Luna's edits remains attributed by the primary's explicit receipt rather than inferred from blob identity.

All 20 rev3 input hashes were independently recomputed from baseline `8bad5d05f17b433b2c5164b91248462de3f7a6fe` and match. Full pinned blobs at the final checkpoint equal baseline for all inputs except the intended test file. The source/production owners remain unchanged. The recovery receipt therefore addresses the prior compiler review's actual provenance discrepancy without changing the reviewed compiler behavior.

## Source correspondence and limits

I inspected the complete final test and frozen proof, then checked the relevant immutable parser, HIR and solver owners, with governing design authority, top-level inference principles and charter §§21/24. The prior compiler/source conclusions remain applicable: `operator_chain.rs:688` and `tails/fixed_access.rs:196–213` construct the PathTail; `module/local_source.rs:861–969` separates that first tail and constructs the remaining Apply edges in reverse traversal with preserved operand pointers. The test at `shadow_method_role_source.rs:350–455` uses the original fixture and authentic answer root, checks outer operand 2 and inner operand 1 with their original keys, and checks the unresolved operation with the original PathTail key. Its independent Act control at lines 457–488 makes no cross-parse identity comparison.

`module/source_annotation.rs:134–144` registers only Act declarations; `module/local_source.rs:1091–1102` resolves operation identities through those namespaces. It supplies no Role/Impl executable target. `module.rs:1970–1976` leaves unsupported root declarations as error plans. The first Role error fails `shadow_apply.rs:392–411` before answer preflight; `candidate_source.rs:478–482` rejects an unresolved operation only conditionally upon reaching that consumer. The later whole-module gate remains distinct. This is source reasoning under the proof's explicit formation premises, not a newly observed solver result. The submission establishes bounded structural evidence and leaves the method-target cause unresolved honestly; it claims no repair of that production gap.

The earlier regression CLEAN remains applicable to exactly the final test SHA above: its reviewed candidate is byte-identical, all pinned production owners are unchanged, and the recovered six edits introduce no additional regression surface. No fresh regression execution or general AST/CST, solver, runtime or native coverage is claimed.

## Permanent chronology and prospective gate

The immutable `58d5507d4:tasks/agent-loop/current.json` explicitly records one PASS after the six borrowing repairs while independent final reviews remain NOT_RUN. This independently corroborates the historical rev3 order violation; neither this CLEAN recovery review nor a later PASS makes rev3 CLEAN.

Rev4 permits a **second** exact execution only after this receipt and a fresh spec/authority CLEAN are both frozen, and Luna confirms prior regression applicability to the same bytes. This compiler receipt satisfies only its own review condition. The second execution must retain its own chronology and outcome; the first cannot be relabeled. Candidate changes, failed review or verification require the contracted stop/adjudication. R119 M/T/A, R85 adoption, effect-hygiene parents and original A/B remain OPEN. No compiler correctness finding was established in this bounded recovery review.
