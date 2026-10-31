# R65 independent review — revision 1

Assignment `/root/r65_review`. Contract revision 1, SHA-256 `57f6f8f978aa86922e01998a7a29ead015cd2e67eb0939188982f9294d0bbf08`. Requested compiler_referee Sol/low; effective model, effort and session ID UNKNOWN. No descendants.

**Disposition: BLOCKING Rust defect; bounded Lean claims pass source and retained-evidence review.**

## BLOCKING R65-R1 — returned coordinate borrows the independent lookup argument

Locations: `crates/yu-solver/src/candidate_receiver.rs:568`, `:682`, `:687`, `:713`.

`InventoryOccurrenceFact<'p, 'a>` retains `occurrence: &'a HirOccurrenceId`. The method accepts independent borrows:

```rust
&self,
occurrence: &HirOccurrenceId,
```

and returns:

```rust
Option<InventoryOccurrenceFact<'_, '_>>
```

Method lifetime elision ties the output lifetime placeholders to `&self`. However, line 713 initializes the returned coordinate with the independently borrowed `occurrence` argument:

```rust
Some(InventoryOccurrenceFact { row, occurrence, slot })
```

The signature does not establish that this argument lives as long as the required output borrow. A caller may supply a temporary clone of the key while retaining the package longer. Equality with the owner key does not extend that argument’s lifetime. The method body therefore cannot satisfy its declared return lifetime when `shadow-apply-candidate` is enabled, even though its current caller immediately discards the view.

This violates the contract’s valid borrowed owner-local view requirement. The responsibility belongs to view construction.

**Minimum repair:** retain the authenticated owner coordinate:

```rust
Some(InventoryOccurrenceFact {
    row,
    occurrence: row.occurrence,
    slot,
})
```

This uses the stored borrow already validated against the requested coordinate and avoids enlarging the lookup argument’s lifetime requirement. Fresh review of the exact repair is needed; focused feature compilation remains outstanding under the present no-build contract. This finding is source reasoning, not an observed compiler diagnostic.

## Source and mathematical review

The change addresses the reader’s selection cause: candidates are selected by occurrence/slot before semantic identity resolution. It does not impose global FactId uniqueness.

- Rust lines 3071–3107 retain every provenance edge, including duplicate rows and separate keys sharing a FactId. Failure aborts package construction rather than silently dropping rows.
- Rust lines 688–711 reject a second candidate before checking the selected fact. Owner-table indices and pointers, provenance pointers, cause coordinate, FactId index and selected native pointer/endpoints are checked.
- Rust lines 3241–3247 apply the reader to the selected Internal use at slot 0. Existing Catch collection remains separate.
- Lean `candidates`, `readAt` and `resolve` preserve duplicate multiplicity and reject ambiguity before owner/index/identity resolution. `readSelectedAt` compares the complete FactRow.
- `foreign_key_extension_preserved` retains the fact table and quantifies over every appended foreign-key edge. Neither it nor the shared-FactId results introduces a global uniqueness premise.
- The versioned `internalInputs` captures the selected use coordinate. `qualified_internal_source_facts` derives slot-0 and slot-2 reads from actual R45 acceptance.
- `current` rejects semantic/native store mismatch. Its slot-51 source reader is exactly the old collected Catch reader.
- R47 acceptance still checks root source, cause, task, completion and same source fact through `RootMatches`. `rootQuery` carries the same Internal certificate’s use, fact and raw permission entry. `qualified_root_extract` retains the same full permission witness and concrete-list multiplicity.

No additional major or minor finding was established within this bounded scope.

The retained `OwnerReads`, `Identity`, R45 acceptance and R47 `Matches` premises remain genuine premises. Numeric edge-index authenticity, Rust pointer/token encodings, source-to-Native correspondence and actual runtime multiplicity remain OPEN. The finite Lean witnesses establish mathematical examples only; they are not independent native runtime counterexamples.

## Retained Lean audit

No checker was rerun.

I decoded attempt 9 entirely in memory and independently established:

- Retained stdin SHA-256 matches `3584b948acd4549b3d4be5579b1ebd31bb20953c8ede77880462c3d23210c41f`.
- The delivered R65 module body occurs byte-for-byte in that stdin.
- All 333 recorded definition spans and all 15 inherited/supplementary theorem spans match their current source hashes and occur byte-for-byte in the retained stdin.
- All 25 authored theorem declarations have retained full types and transitive axiom reports.
- Reports use only `propext`, `Classical.choice` and `Quot.sound`. Only `foreign_key_extension_preserved` reports `Classical.choice`.
- Attempt 9 records exit 0 and empty stderr. This is authenticated retained producer evidence, not an independently executed kernel check.
- The pinned project files specify Lean 4.35.0. No actual imported-module or default-project build is established.

## Snapshot authentication

All five requested hashes matched at intake and final reread:

| Input | SHA-256 |
| --- | --- |
| `candidate_receiver.rs` | `af4f4158a79535e26810dd95c0a4d7cbb91d692677d8c1409a2c6faabfb7aaea` |
| Rust handoff | `30e81d63e691ac81e684c71a7a04ed5b1967a562125d4e79190a216d0b9d3310` |
| R65 Lean module | `3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b` |
| Proof handoff | `c93b9e3a9978f6c4b5c802f5e94456b2c18328a8d58f4835bf60a7884ab0ce6e` |
| Sprint contract | `57f6f8f978aa86922e01998a7a29ead015cd2e67eb0939188982f9294d0bbf08` |

Removing only the R65 view, lookup and capture integration in memory reproduces the admitted Rust baseline SHA `ff03bb9cfa1222a61f7c9594f437049e470b7a2fb6d69af00ef74c8625b4a63e`. The R64 collector and Term-seed repairs satisfy the previous review’s source-level minimum corrections; compilation remains unverified.

Frozen `lib.rs`, `candidate_context.rs`, R55, R57 and R64 dependency hashes also match. Relevant existing receipt/provenance tests were read, including `brands_receipts_and_local_failure_are_isolated`; no tests ran.

**Reviewer STOPPED / WRITES STOPPED.** No checker, build, test, Cargo, formatter, Git, scratch, cache, target, worktree or environment operation ran; no authors were contacted. No files were written because the higher-priority reviewer instruction requires read-only operation. Luna owns persistence and hashing of this report at the leased review path.

## R65-R1 repair re-review supplement

Follow-up assignment `/root/r65_review`; reviewer requested no source/build/checker work beyond the exact one-line repair. **PASS — R65-R1 source repair closes the reported lifetime defect.**

Current `candidate_receiver.rs` SHA-256: `a729f7ae68b421073b36e26d687ef7ef69e79f5d5674a7e1884b4058c37431e3`. Reversing the single initialization change in memory reproduces the reviewed snapshot SHA `af4f4158a79535e26810dd95c0a4d7cbb91d692677d8c1409a2c6faabfb7aaea`, authenticating the exact one-line delta.

At `candidate_receiver.rs:713`, `occurrence: row.occurrence` now retains the owner-derived borrow held by the selected inventory row. That borrow can be shortened to the package borrow required by the return type. The independent lookup argument is used only for comparison and no longer escapes.

The retained coordinate already passed exact occurrence/slot selection and provenance-cause validation. The repair preserves those checks and returns the owner coordinate without changing selection or multiplicity behavior.

Compilation remains unverified: no build, test or checker ran. This PASS covers only the exact R65-R1 repair; previously recorded correspondence and production limits remain OPEN.

**Reviewer STOPPED / WRITES STOPPED.** No files were written.
