# R44 independent review — frozen, STOPPED

Verdict: **PASS for the bounded `NO_SAFE_CONSUMER_SLICE` result.** No open BLOCKING, major, or minor findings. This review grants no consumer implementation or production authority.

## Closed provenance finding

**minor — CLOSED, formatting-only contract hash reconciliation.** The source handoff records contract hash `4342109c2c6ff5fde25a69b38b267bfc41e692189cf3fd330caf35dfe9177df1`; the current contract and proof handoff identify `07cee599c23258ee9266cc8b523f92246ee13df0783555a785e1f4ff281fa29c`.

Authority: R44 contract, “Frozen inputs” and “Independent review”; `rules/design-authority.md`, “Authority order.”

Closure verified independently: SHA-256 of current contract bytes is `07cee599…`; appending exactly one LF produces `4342109c…`. The difference is one trailing blank line, with no scope or semantic difference. Preserve the frozen historical handoff bytes. Source admission remains valid.

## Source assessment

The constructor distinction is supported:

- `candidate_receiver.rs:326` creates the candidate session; `candidate_scheme.rs:2456` initializes default routes and absent definition graphs.
- `candidate_receiver.rs:383` constructs the complete collection-artifact/occurrence `DefinitionUseId` and calls Internal routing. `lib.rs:562` and `:593` retain artifact identity in the key and its equality.
- `lib.rs:18233` routes original target/use terms; `lib.rs:19361` records the admitted fact and Internal receipt. Its assertion and insertion enforce one successful admission per complete use ID.
- `candidate_scheme.rs:4377` requires the stored captured graph before Incoming reconstruction. `:4923` reconstructs FreshUse and publishes a FreshRoute only after IncomingStructured admission.
- Receiving owner, relay definition provider, and operation-provider occurrence remain distinct. `candidate_scheme.rs:425` retains route ownership; `candidate_receiver.rs:461` separately checks operation occurrence/declaration/family and selection.
- The residual at `candidate_receiver.rs:396` uses the original collected endpoints. No proved correspondence to a FreshRoute image is supplied.

Equal IDs, rows, terms, or common provider roots supply none of the missing capture/native-incidence/arrival premises. A second admission violates the observed invariant.

## Proof and checker assessment

Inspected all 11 theorem statements, definitions, proof bodies, and final audit receipts. Final batches 3/4 contain exactly the 11 declarations, with matching ordered BEGIN/END markers. Both fenced stdout blocks reproduce their recorded SHA-256 values. Receipts report exit 0; no checker was rerun.

Complete axiom audit:

- `[propext]`: `admission_exact`, `internal_preserves_fresh`, `unmatched_endpoint_preserved`, `internal_only_no_suppression`, `conditional_fold_exact`.
- `[propext, Quot.sound]`: `single_admission`, `internal_cannot_readmit_incoming`, `internal_alone_no_r43_route`, `native_available_iff`, `suppression_iff`, `suppression_requires_all`.

No proof-hole, project-axiom, or checker-bypass token found in R44 or its R38/R39/R41/R42/R43 source dependency cone.

The empty-inventory premise is explicit. Existing FreshRoutes are preserved by Internal admission. The conditional guard requires the same extracted certificate and R43 binding, actual arrival membership, the supplied exact-entry arrival predicate, concrete permission, and selected native Catch checks. Source-owner/provider authenticity and `arrivalAtEntry` meaning remain source obligations; supplying records or a Boolean predicate closes neither.

## Hashes

All 20 frozen dependency-table pins match.

- Contract: `07cee599c23258ee9266cc8b523f92246ee13df0783555a785e1f4ff281fa29c`
- Source handoff: `34a9f5d2d62284abfd83ea30d0bcd3aa95ea18aa27a8280ef3453da29e54f840`
- Lean: `98674f033a0e16e7a5cccb8df8cb97c29495b326a5896c1cfcdcc82913a4816d`
- Proof handoff: `5294b138e2b56d5c2c5421d7c5abb3d92718ba0c3afb7ad3b9c3b02ff1dffe36`

## Remaining boundary and STOP receipt

Authentic receiving-instance incidence, provider arrival, selected Catch/residual correspondence, parent hygiene closure, and production promotion remain open. The packet selects no routing replacement or Internal adapter.

Reviewer `/root/r40_read2_review` STOPPED. Read-only commands only; no writes, checker/build/test execution, environments, scratch files, or children. The primary placed this frozen review text in the designated handoff under the acknowledged read-only handoff adjustment.
