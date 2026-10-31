# R65 Rust handoff — occurrence-qualified native fact reader

Sprint `EFFECT-PERMISSION-OCCURRENCE-FACTS/20261031-R65`, contract revision 1,
SHA-256 `57f6f8f978aa86922e01998a7a29ead015cd2e67eb0939188982f9294d0bbf08`.
Assignment `/root/r65_rust`, handoff revision 1. Parent gate: unchanged
effect-hygiene obligation under `research/simple-sub-intrusion`; source domain,
lawful histories, scopes, A/B quantifiers, and annotation permission semantics
are unchanged. Baseline HEAD `a89bccbfb7b6123dff3522cc8cb000728f206fae`.

## Runtime and lease

Role requested: implementer, Luna/high. Requested model/effort: Luna/high.
Observed worker ID, effective model, effort, and session launch receipt: UNKNOWN
in available runtime metadata. Descendants: none. Exact write leases used:
`crates/yu-solver/src/candidate_receiver.rs` and this handoff only. No other
paths were written. Assigned resource bound: 1,000 seconds; actual elapsed and
remaining assignment budget are UNKNOWN in available runtime metadata. No
scratch or disposable path was created.

## Authenticated R64 corrections

Starting `candidate_receiver.rs` SHA-256 was the frozen contract value
`ff03bb9cfa1222a61f7c9594f437049e470b7a2fb6d69af00ef74c8625b4a63e`. I
compared the admitted repair to both R64 blocking review findings before editing:

- R64-R1 identified `copy_owned_borrowed_inventory(iterator)` as a type mismatch
  because that helper accepts a slice. At the R65 starting bytes, the provenance
  table uses `collect_owned_borrowed_inventory(store.provenance().iter().enumerate())`
  and maps collector failure to `SearchLimit`, retaining the iterator's ordered
  rows.
- R64-R2 identified `entry_effect: u32` in the `Vec<Term>` seed array as a
  namespace/type error. At the R65 starting bytes, the seed array contains the
  owning `argument_effect: Term` and no `entry_effect` ordinal.

These match the review's exact minimum repairs. They were not build-verified;
R64's review explicitly had no build evidence.

## Outcome and parent application

Added private `InventoryOccurrenceFact` borrowed view and
`InventoryPackage::source_fact_at(occurrence, slot, selected_native_fact)` in
`candidate_receiver.rs`. The lookup:

1. filters the complete retained provenance-derived occurrence rows by exact
   `(HirOccurrenceId, local_slot)` and rejects a second row at that coordinate;
2. verifies the row's original provenance and semantic-fact owner-table indices
   and pointers, exact edge cause coordinate, edge-to-fact `FactId`, and the
   semantic table coordinate encoded by that `FactId`;
3. requires pointer identity with the selected native semantic fact and checks
   its `FactId` and both endpoints; and
4. returns the borrowed occurrence/slot row view without copying or collapsing
   provenance edges.

`InventoryPackage::capture` applies the lookup to its selected Internal fact at
the selected `DefinitionUse` occurrence and local slot 0, returning the existing
private `BoundMismatch` gap if selection is absent, ambiguous, foreign, or does
not identify that exact native fact. Every provenance edge remains stored in
its original ordered `provenance` table and separate `admitted_fact_occurrences`
row, including distinct occurrences sharing a semantic FactId. Existing capture
checks reject semantic facts with no provenance and reject dangling/ambiguous
FactId resolution.

Source-owner correspondence is structural and borrowed: the coordinate comes
from `ProvenanceEdge::cause().occurrence()`, the edge from
`InferenceSession.store.provenance()`, and the semantic fact from the same
session's `store.facts()` inventory. The selected fact comes from the existing
Internal incidence. This is source-to-owner evidence for the private Rust
reader, not a Lean theorem or an authenticated Rust-to-Lean mapping.

No source constraint generation, propagation, inference, routing, subtraction,
producer, or execution path changed. The contribution is confined to the
owner-local candidate inventory capture and validates the selected fact reader.
No native runtime multiplicity or cross-occurrence duplicate is claimed.

## Evidence, checks, and limits

- Frozen direct inputs rechecked after editing: `lib.rs`
  `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`,
  `candidate_context.rs`
  `962af7c44b2e57ba50b7738e82785bd68b517e881ba08ea41c544c9314d60021`,
  R55 `SourceInternalContextR55.lean`
  `7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123`,
  R57 `ProviderNativeContextR57.lean`
  `804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63`, and R64
  `BrandedInventoryOwnerR64.lean`
  `790b1ac0a99f8a1582c442edfb352614e72cac28f13a9158c4e81a396474e86b`.
- Source after hash: `candidate_receiver.rs`
  `af4f4158a79535e26810dd95c0a4d7cbb91d692677d8c1409a2c6faabfb7aaea`.
  Source before hash: `ff03bb9cfa1222a61f7c9594f437049e470b7a2fb6d69af00ef74c8625b4a63e`.
- Manual source/diff inspection only. No build, test, Cargo, formatter, checker,
  Git mutation, cache, target, environment, worktree, or scratch was run or
  created. Compile behavior remains unverified by contract.

## Remaining source/proof gap and mutual TODO

The private reader does not prove that R55's identity-only `routeFact` or R57's
`factRead` agrees with this occurrence-qualified reader. It does not establish
whether the selected native fact has another provenance edge at a different
occurrence, nor does it establish Rust-to-Lean owner/table/TermView
correspondence. No Simple-sub bypass or global FactId uniqueness premise was
introduced.

- Proof lane TODO: use the exact `(selected occurrence, slot 0)` reader
  criterion and selected fact from this source path to prove qualified
  `readAt` clauses, route-input agreement, and same-use root agreement in the
  leased R65 module; retain a distinct-occurrence/shared-FactId witness and do
  not claim it is a native runtime trace.
- Luna source-owner TODO: independently inspect the frozen Rust reader/capture
  and determine whether the actual selected fact is source-qualified into the
  Lean bundle without dropping any edge. Falsifier: duplicate edges at one key
  must reject; distinct keys sharing FactId must remain retained; dangling,
  foreign, owner-mixed, or endpoint-mismatched selection must fail.

Original A/B, native runtime multiplicity, R55/R57 equivalence, authentic full
Rust-to-Lean correspondence, successful outer `Run`, effects, soundness,
principality, termination, full hygiene, and production remain OPEN. No
expectation, diagnostic, source-domain, or inference change was made.

Worker state: **STOPPED / WRITES STOPPED.** No descendant leases remain. This
handoff is frozen after correcting the dependency digest and hashing the final
bytes; Luna owns intake and review state.
