# R64 Rust handoff — authentic Owner and Call carrier

Sprint `EFFECT-PERMISSION-OWNER-CARRIER/20261031-R64`, contract revision 1,
SHA-256 `8a65eee3a7397b40f1522f0426be00d1d51b0b1d01bfb73486dd0c4cda844a38`.
Assignment handoff revision 2 (supersedes this assignment's frozen revision 1).
Baseline supplied by Luna: `9c7dd3d74b56bccce776abb18d597d62f9161ba3`.
Assignment `/root/r64_rust`; requested runtime Luna/high; observed model and
effort UNKNOWN. No descendants.

## Outcome and parent application

Extended the private `InventoryPackage` in `candidate_receiver.rs` with:

- the complete ordered semantic-store `ProvenanceEdge` table;
- one `InventoryAdmittedFact` row per provenance edge, retaining edge index,
  semantic-fact index, exact `HirOccurrenceId` and local slot, and borrowed
  edge/fact. The source occurrence field has type `&HirOccurrenceId`; the
  provenance edge separately retains its exact `ConstraintOccurrenceId` cause;
- the complete TermView closure derived from owner component terms, semantic
  and collected fact endpoints, and R55 function/fact terms. Each row retains a
  package-local term coordinate, the original `Term`, its borrowed `TermView`,
  and indexed children for function, tuple, record and variant constructors;
- one `InventoryOwnerCall` tying the selected source-call index and source/target
  roots to the exact use, relay/answer, Catch/scrutinee, provider, declaration,
  arm and source-range coordinates already owned by the same experiment.

Every allocation is fallible. The package reads the existing owner tables and
does not invoke inference, forwarding, routing, subtraction or execution. Empty
source/native inventories are retained as empty vectors. Provenance occurrences
are not deduplicated by semantic fact identity. A semantic fact with no retained
provenance edge makes capture fail; an empty semantic-fact table with an empty
edge table remains valid. TermView construction has no nonempty assumption.

Source mapping:

- `SourceInternalProjection::component_terms` and `native.facts` are preserved
  as before; component terms, all semantic facts, and all collected facts seed
  the TermView closure. `internal_function_witness` and the selected lambda and
  Internal facts are additional explicit seeds. All constructor children are
  recursively obtained from `session.store.term_view` and mapped back to the
  same package-local coordinate table.
- `session.store.provenance()` is copied in owner order. Each edge's `FactId`
  is checked against exactly one entry in the complete semantic-fact inventory.
  Its cause supplies the retained source occurrence and local slot. Multiple
  edges for one semantic fact remain separate rows with their original indices.
- The call record uses the unique already checked `source_call`, the selected
  `DefinitionUse`, exact permission target owner, and `owner.schema` fields.
  Provider and Catch source ranges, arm ordinal, operation identities, raw and
  canonical endpoint records remain separately available in the package.

This supplies the Rust-side structural inputs for R63's typed Owner and Call;
it does not prove Rust/Lean equality, instantiate R63, or close source/native
correspondence. The parent must prove complete-field equations and every
R55/R62 lookup equation for these same values, then apply R63 without changing
its quantifiers.

## Provenance multiplicity finding

Read-only owner path: `crates/yu-solver/src/lib.rs:18298-18306` selects the
unique routed Internal record and obtains its fact from
`admitted_source_fact(use_record.occurrence, 0)`. That lookup at
`lib.rs:18410-18422` filters provenance by the exact selected occurrence and
slot, rejects a second edge at that same coordinate, then returns the edge's
semantic fact. `lib.rs:3829-3875` records one edge for each consumed source
admission receipt. Since fact admission interns equal endpoint pairs, distinct
occurrence/slot edges can still share a semantic `FactId`; the Internal reader
does not check global FactId uniqueness.

For the selected path, the exact symbolic coordinates are the returned
`DefinitionUseId`/`use_record.occurrence` at slot `0`, and
`internal_route.fact` (looked up in `session.store.facts()` by `FactId::index`).
The private source program admits one `DefinitionUse`, and no duplicate edge at
that exact coordinate is admitted by the reader. Whether that selected FactId
also has another edge at a distinct source occurrence requires observing the
actual constructed session. Numeric occurrence and FactId values are runtime
values and were not obtained here because this packet forbids running the
compiler/tests. Thus no concrete cross-occurrence duplicate is claimed.

If a complete R55 `admittedFacts` list represents every provenance occurrence,
R55's `routeFact` lookup, which is unique by semantic fact (`SourceInternalContextR55.lean:143-144`), will reject a selected FactId with another occurrence. This remains a precise conditional source/proof TODO; no R55/R63 file or source producer was changed. The owner-level carrier preserves enough evidence for the proof lane to establish or falsify that premise.

## Reused evidence, checks, and limits

R63's frozen Rust implementation and review were read. The review explicitly
leaves authentic Rust-carrier interpretation OPEN and warns that arbitrary
mathematical owners can omit facts, views or competitors. R55/R62 definitions
were inspected for the consumed `componentTerm`, `positiveFunctionChild`,
`negativeEntry`, provenance and owner/call coordinates. The exact source-owner
path and store admission/provenance code above were inspected; R63's
unique-by-Fact behavior was not weakened or bypassed.

Before writing, the contract's direct dependencies matched their frozen pins:

- `candidate_receiver.rs` baseline: `3119ed33909f85ddbee5864b8f0e910ee65c69fdf3d056d600b95deab0cbf84a`
- `lib.rs`: `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`
- `candidate_context.rs`: `962af7c44b2e57ba50b7738e82785bd68b517e881ba08ea41c544c9314d60021`
- `term.rs`: `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`
- `RustInventoryRequestR63.lean`: `74381ebd183fa7d26f626fe166f848e1312377fca855cd08beb92d9256edfacc`
- `InternalRootPolicyR62.lean`: `e76e41a853673e75555cc5e603f1f84c456332794980613c554a2d69af8d976e`

Before revision 2 writing, the read-only Rust/Lean dependencies rehashed to
those same pins.
Changed artifact hash: `candidate_receiver.rs` SHA-256
`4d9bef6a954c5863d279ab8dcde9a6f5471e1dc8936526b5d7b83b7409ede067`.
Revision 2 makes the source occurrence field agree with the supplied
`HirOccurrenceId`, while retaining the complete edge's cause identity and slot.
This handoff is the only other written path; its frozen SHA-256 is returned to
Luna with this revision.

Inspection was limited to dependency hashing, source/type/owner-path reads, and
manual review of the leased edits. No build, test, Cargo, formatter, checker,
Git operation, worktree, cache, environment, target, scratch, or build output
was created or run. No disposable scratch path exists. Compile behavior remains
unverified by design.

Original A/B, actual successful outer `Run`, allocator/resource/failure
correspondence, whole-program soundness/effects/principality/termination,
hygiene and production remain OPEN. The package is private, fallible,
observation-only research evidence and is not connected to inference.

Worker state: **STOPPED — WRITES STOPPED.**

## Luna repair revision 3 — 2026-10-31

Parent: frozen R64 independent review, SHA-256
`bb5065a5f90e0e5106749b2ae8df90f42ee4fac4f4154f0438ba928f6d2b9bbd`.
The reviewer identified two concrete type errors in the revision-2 source.
After the reviewer STOPPED, Luna took the same exact source and handoff paths;
the Rust author remained STOPPED. No path or semantic authority was added.

Corrections in `candidate_receiver.rs`:

1. Provenance capture now passes the ordered `Enumerate<Iter<ProvenanceEdge>>`
   to `collect_owned_borrowed_inventory`, the iterator-taking fallible helper,
   mapping its `None` to `CurrentEmissionGap::SearchLimit`. It still retains
   every original edge and owner index.
2. Removed `InternalFunctionWitness.entry_effect: u32` from the `Vec<Term>`
   seed array. The actual `argument_effect: Term` remains included. The
   fallible capacity bound now counts the six Term seeds exactly.

The repair is source-level only. R64 prohibits builds, tests, Cargo, and
formatters, so no compilation or runtime result is claimed. Fresh independent
review of this revision is pending.

The fixed R64 gate remains **OPEN**. The review's R3 authenticated Rust-to-Lean
construction finding and R4 provenance-reader mismatch remain unresolved; no
global FactId uniqueness premise, occurrence dropping, or native-runtime
counterexample is claimed. Structural Lean results remain conditional and do
not authenticate the native owner.

Repair source hash: `ff03bb9cfa1222a61f7c9594f437049e470b7a2fb6d69af00ef74c8625b4a63e`.
