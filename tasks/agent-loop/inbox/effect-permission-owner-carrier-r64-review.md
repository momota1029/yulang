# R64 independent review

**Verdict: BLOCKED. The fixed R64 outcome is not established.** Two concrete Rust type errors block the feature build. The Lean artifact establishes useful structural candidate equations and a finite model discriminator, but does not construct an authenticated interpretation of the actual Rust package.

Review identity: `/root/r64_review`. No author contact, descendants, edits, builds, tests, Cargo, formatter, Lake, or checker reruns. Initial analysis used code and the governing contract before reading author explanations. Later handoff inspection was limited to retained evidence and claim reconciliation.

## Findings

### BLOCKING R64-R1 — iterator passed to a slice-taking helper

Location: `crates/yu-solver/src/candidate_receiver.rs:3022`.

```rust
copy_owned_borrowed_inventory(
    native.session.store.provenance().iter().enumerate()
)?
```

The argument is an `Enumerate<Iter<ProvenanceEdge>>`. The helper at lines 788–790 requires:

```rust
items: &[(usize, &'a T)]
```

These types cannot match. The iterator-taking helper is `collect_owned_borrowed_inventory` at line 772, which returns `Option`.

This blocks compilation with `shadow-apply-candidate`, including though the observer is unused. It violates the contract’s requirement for a valid private, fallible Rust carrier.

Minimum closure: use the iterator-taking collector with the required failure conversion, or an equivalent fallible construction. Retain every ordered provenance edge. Obtain focused feature compilation evidence after the repair under primary authorization.

### BLOCKING R64-R2 — effect-row ordinal inserted into a Term array

Location: `crates/yu-solver/src/candidate_receiver.rs:3077`.

```rust
source.internal_function_witness.entry_effect,
```

`InternalFunctionWitness.entry_effect` is `u32` at line 769. The surrounding array contains `Term` values, including `function`, `argument_effect`, and semantic endpoints. `term_seeds` is already inferred as `Vec<Term>` at line 3067.

This is a type error and a concrete namespace confusion: the row ordinal is not a term handle. The owning `argument_effect: Term` is already included at line 3076.

Minimum closure: remove the ordinal from the Term seed array, or obtain a genuine owning Term through an approved owner operation if another term is required. Do not cast the ordinal into a term identity. Obtain focused feature compilation evidence after repair.

### BLOCKING R64-R3 — authenticated Rust-to-Lean construction remains absent

Locations:

- `BrandedInventoryOwnerR64.lean:77`: `Carrier`.
- Lines 117–148: `name`, `owner`.
- Lines 152–178: `call`, `construct`.
- Lines 181–198: `complete_fields`.
- Lines 344–363: `same_constructed_consumer`.

The mathematical `Carrier` accepts independently supplied typed lists, arbitrary Nat owner tokens, arbitrary raw TermViews, and source-call/schema records. No constructor maps the actual private Rust `InventoryPackage` to those fields. No finite-table encoding, coordinate round trip, or native identity injectivity theorem authenticates that mapping.

`complete_fields` proves equality to the supplied carrier fields. It cannot detect an extant Rust receipt, fact, permission, view, competitor, or provenance occurrence omitted before constructing `Carrier`.

Concrete attacks against the submitted mathematical constructor:

- Removing a live receipt or competing provider from supplied tables does not invalidate `complete_fields`.
- With `semanticFacts = []`, a nonempty `provenance` list contributes no rows through `admittedFacts` or `sourceFacts`. `construct` does not validate this reference join.
- `call` ignores `SourceCall.sourceOwner` and `expressionIndex`; changing either leaves its result unchanged.
- Changing supplied schema Catch/provider coordinates changes the constructed request without checking them against the actual Rust schema.

These are mathematical carrier counterexamples to authenticity checking, not actual Rust package executions. Rust capture contains checks that would exclude some such malformed inputs, but the missing bridge never transfers those checks into Lean.

**OwnerName audit:** `artifact`, `state`, `store`, and `batch` are unencoded Nat fields. There is no authentic finite-table token assignment, decode/encode round trip, scoped injectivity, or four-namespace correspondence. Separate record fields and `Fact.semantic`/`Fact.collected` constructors preserve mathematical distinctions; they do not authenticate native brands.

**Term audit:** Rust `InventoryTermView` retains actual `Term` handles, borrowed views, and package-local child indices. Lean `OwnedTerm` instead accepts arbitrary `T` and `RawView S T`. Its children are structural symbols. There is no theorem relating them to the Rust handles or checked child coordinates. `termCoverage` establishes closure of the supplied mathematical table only.

This violates the fixed outcome and success evidence 2: construct the carrier from the actual package, prove complete-field and consumed-lookup coverage, then apply R63 to those same values.

Minimum closure: construct the finite typed interpretation from the actual borrowed package and prove the exact owner/table/source-call/schema/TermView coordinate correspondence, including all competitors and provenance occurrences. Then establish the relevant constructor/check premises and instantiate R63 with that interpretation. An assumed faithfulness predicate or independently supplied mirror cannot close this finding.

### major R64-R4 — provenance multiplicity exposes an unresolved reader mismatch

Locations:

- Rust `lib.rs:18410–18424`: `admitted_source_fact`.
- R55 `SourceInternalContextR55.lean:143–144`: `routeFact`.
- R57 `ProviderNativeContextR57.lean:192`: `factRead`.
- R57 lines 193–208: `sourceFact`, `rootTask`.
- R64 lines 367–389: the two discriminator theorems.

Rust chooses exactly one provenance edge at `(HirOccurrenceId, local_slot)`, then reads its semantic fact. It does not require global uniqueness of that FactId. Semantic admission interns equal endpoint pairs at `lib.rs:3982–3985`; provenance retains source receipts separately.

R64 preserves every provenance occurrence when constructing mathematical facts. With two occurrences sharing one semantic identity:

- R55 `routeFact` rejects that identity because its identity-only filter has two rows.
- R57 `sourceFact` can select one exact distinct occurrence/slot.
- R57 `factRead` still rejects the shared identity.
- Consequently, success of `sourceFact` does **not** establish `rootTask`, root candidates, arrival readers, or successful outer `Run`.

`two_occurrences_routeFact_rejected` proves the first mathematical rejection. `two_distinct_causes_native_source_read` proves only the occurrence-qualified R57 lookup succeeds under its explicit finite-list hypotheses.

**Neither theorem is an actual native runtime counterexample.** No retained execution establishes that the selected native Internal fact has another provenance occurrence. Its actual multiplicity remains UNKNOWN.

Minimum closure: establish the exact native/source-qualified premise needed by the current formal readers, or repair the owning formal readers and dependent proofs under an appropriate lease. Do not discard occurrences, assume global FactId uniqueness, or narrow supported source behavior to obtain the bridge.

## Positive evidence and limits

The Rust additions address evidence retention at its owner: ordered provenance is borrowed from the store; per-edge occurrences retain fact/edge coordinates; TermView children are recursively read from the same store; call/schema fields come from the same experiment. No changed inference/routing/subtraction operation was found. Capture is observation-only, and its new lookup/allocation failures return private gaps.

The existing receiver tests statically inspected cover signal suppression, same-spelling distinct-operation forwarding, grouped scrutinee edges, and unsupported-envelope controls preserving ordinary candidate inference. They do not exercise the new carrier. No tests were run.

Empty lists are not rejected merely for being empty. The Rust provenance-count loop accepts jointly empty fact/provenance inventories. Lean’s empty-derived-inventories theorem is appropriately conditional. Neither empty-table evidence authenticates an actual native owner.

## Retained Lean evidence audit

I decoded the retained final stdin entirely in memory.

- Successful receipt: `R64-CONSTRUCT-7`, exit 0.
- Command: pinned native Lean `-j1 -M1024 --stdin`.
- Retained input: 285421 bytes.
- Input SHA-256: `7ed1ce8ab471d7d31d76d72bc80c19d97b2ef85225ae9ebf10217ede23aac3e3`.
- Stdout SHA-256: `2ef6bfd2a3c6dd111e7790d0109397069a41685083a39d7d8960849dc9c6054a`.
- Input and stdout hashes independently recomputed and matched.
- The exact R64 module body, excluding its import, is present in the checked stdin.
- All 18 source theorem declarations have retained full type output and corresponding transitive axiom reports.
- All retained direct and transitive source hashes independently matched the current files.
- No proof bypass or hole was found in the decoded input.

Complete axiom census:

| Axioms | Theorems |
|---|---|
| `propext`, `Quot.sound` | `every_provenance_occurrence`, `every_provider_competitor`, `owned_term_views`, `coverage_contains_seeds_and_children`, `same_constructed_consumer`, `two_occurrences_routeFact_rejected`, `two_distinct_causes_native_source_read` |
| `propext` | `complete_fields`, `provenance_multiplicity`, `every_collected_fact`, `every_permission`, `unique_map`, `consumed_lookup_equations`, `owned_lookup_equation`, `raw_consumed_lookup_equations`, `call_coordinates`, `construct_exact`, `empty_derived_inventories` |

No `sorryAx`, project axiom, or `Classical.choice` appears in that census.

The full types preserve the relevant limits: coverage requires `termCoverage = true`; coordinates require successful `call`; parent application retains successful `extract`, outer `Run`, `Checked`, and terminal equality. This is retained checker evidence for the flattened checked input, not a rerun or ordinary project build.

## Frozen hashes

| Artifact | SHA-256 |
|---|---|
| R64 contract | `8a65eee3a7397b40f1522f0426be00d1d51b0b1d01bfb73486dd0c4cda844a38` |
| `candidate_receiver.rs` | `4d9bef6a954c5863d279ab8dcde9a6f5471e1dc8936526b5d7b83b7409ede067` |
| Rust handoff | `976e7c5eb506ece735dcf248b87210dcddef477834d5e254506e7bfc5d2665b4` |
| `BrandedInventoryOwnerR64.lean` | `790b1ac0a99f8a1582c442edfb352614e72cac28f13a9158c4e81a396474e86b` |
| Proof handoff | `863901cf7b14f0eef4331996a9f76e4fb61b4eb9405a40c5163461a0edd0cff0` |

All five matched the assigned frozen hashes.

The current-state snapshot records both authors STOPPED with writes-stopped acknowledgements; both frozen handoffs also report STOPPED / WRITES STOPPED. This review does not independently infer cessation from file contents.

Original A/B, authentic source/native correspondence, outer successful `Run`, resource/failure correspondence, full hygiene, whole-program effects/soundness/principality/termination, and production remain **OPEN**. No semantic approval or gate weakening is granted.

**Reviewer STOPPED / WRITES STOPPED.** No files were written. Report-file SHA is unavailable because the higher-priority read-only constraint prohibits creating that file; Luna owns persistence and hashing of this verbatim report.
