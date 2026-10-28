# NATIVE-RESTORATION-FRAME/r4 — Rust lane handoff

## Frozen assignment and identity

- Contract SHA-256: `0c76993f4759bef5ff466fd039ce5d551fcec10996ab6d6c40f6643a5af87902`.
- Assignment: Rust implementation only, exact writes limited to the two R4 Rust source files and this handoff.
- Initial ACK preceded source/artifact body reads. The initial ACK handoff revision was `a0b303c12c98da6e90711c8e92049c9c8dd0bb1cef2999fa9979b168bf4c1dbf`.
- Requested route: registered `implementer`, Luna/high. Observed serving model and effort: UNKNOWN. The dispatcher confirmed the requested route and reported no known mismatch.
- Grant: 1000 seconds, starting 2026-10-28 08:39:24 UTC; finite bound 08:56:04 UTC.
- No R3 artifact was used as an input.

## Outcome and frozen source hashes

Implemented a provisional `cfg(test)` observer at the candidate bound-restoration driver return, plus an exact post-driver readback helper and route/mutation fixture. Production behavior, APIs, semantics, source domains and expected outputs were not intentionally changed.

Frozen hashes:

```text
isolated/native-restoration-frame-r4/crates/yu-solver/src/candidate_scheme.rs
2573e66766f54bae5f10a9f645976b16c27b770d4db0c2f0fe3be76eb26906af
isolated/native-restoration-frame-r4/crates/yu-solver/src/candidate_extrusion.rs
85f45d14b88ca777b94abcaa254983e5bd7e72d6d452aa226c002c3c541fc50d
```

The observer records the invocation's input source `BoundKey`, occurrence and `CauseId`; admission cause and restoration ID; actual returned `BoundEmissionId`; admitted relation and relation pair; flow; transformer ID; physical slot; and readback. It joins by the returned emission ID and checks its retained restoration/admission/source fields. Transformer ID zero is treated as logical identity, without requiring a physical raw-transformer row. Physical slot reads enumerate all 16 `RowKey × BoundLane` combinations, returning `None` for invalid owner/lane pairs.

The fixture expresses scoped and unscoped routes plus duplicate FreshUse routes, and its mutation matrix applies antecedent, returned-emission ID, source-witness association, mapped/admitted relation, duplicate `use_origin`, flow root, transformer ID and physical-slot changes to the completed predicate. No `.any` or set/count-only sibling join was added; mutable borrows are scoped before later mutation.

## Source review findings and unresolved blockers

The admitted source-first reviewer reports two blocking source-level findings; the pair remains frozen pending primary disposition:

1. The recording wrapper is not reached by the actual source execution route. The source path is `begin_candidate_fresh_bound` → `candidate_drive_bound_restoration`; it bypasses the wrapper. Consequently, the fixture's nonempty-invocations assertion cannot currently be satisfied by the real source route, and the scoped/unscoped/duplicate route witnesses are not authenticated as actual driver invocations.
2. The FreshUse relation-pair predicate compares `context.relation_pair(mapped)` to the pair derived from `source_bound`. The source/destination relationship is mismatched: the mapped relation is associated with the target bound in the pinned reuse path, while a FreshUse `source_bound` can differ. Authentic routes may therefore be rejected.

These findings mean no end-to-end source witness currently passes the completed predicate. The mutation matrix is source-present but has no successful actual invocation to mutate; mutation rejection is not established. No repair was attempted because the source-first review had already frozen the pair. Required next work, if reauthorized through the existing primary process: place observation on the actual `begin_candidate_fresh_bound` → driver path, correct the FreshUse association to the source-supported target/source relation, then freeze a new snapshot for independent review before any checks.

The observer is provisional and does not prove preservation across later state transitions. Parent theorem, native preservation/source correspondence, and production gates remain open. The existing parent concern about mutation/preservation is not discharged by this instrumentation.

## Evidence, checks, and remaining premises

- Source correspondence was examined against the pinned R4 owner path and existing context/readback accessors; the reviewer independently identified the unreachable wrapper and FreshUse mismatch.
- No R3 source or artifact was used to justify this implementation. R2 prior evidence informed the shape only: actual returned-emission identity was retained, while the earlier incomplete admission-only matching was rejected.
- No tests, builds, Cargo, formatter, checker, or Git command was run. The pre-review prohibition on checks remained in force; source review rejected the current pair before that gate.
- No executable witness or mutation result is claimed. There is no checked proof that the referenced relation, flow, transformer, or physical slot is preserved across child transitions.
- No additional paths or scratch files were created.

## Writes-stopped receipt

Final handoff revision records the frozen Rust source hashes above and the reviewer findings. Writes stopped after this handoff was finalized. No source pair edits, tests/builds/Cargo/formatter/checks, Git operations, descendant launches, or out-of-lease writes occurred in this assignment. No path lease is released by this receipt.
