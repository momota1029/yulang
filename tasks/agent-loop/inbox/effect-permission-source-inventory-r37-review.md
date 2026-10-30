# R37 independent inventory review — PASS

Reviewer: `/root/r37_inventory_review`. Assignment: `EFFECT-PERMISSION-SOURCE-INVENTORY/20261031-R37`. Contract revision 1, SHA-256 `33c4c4f1d60e69c11a1a082cbe10a91728888bcdcbf2e11b8f735aa5d14dc756`.

**Bounded technical verdict: PASS. No blocking, major, or minor compiler-correctness finding remains open in the reviewed scope.**

The reviewer role is read-only. This file is the primary's verbatim-structured receipt of the reviewer's final report; the reviewer wrote no files. Both producers were confirmed STOPPED with writes stopped before review. Actual model/effort and complete dispatch elapsed time are UNKNOWN. No descendants.

## Independent reconstruction and scope

Initial inspection used the contract, actual Rust diff and declarations, HIR owners, R35/R36 definitions, and governing policy before reading R37 producer explanations. The `yulang-lean-proofs` skill was applied using the contract's pinned read-only stdin exception.

The change repairs the cause at the extraction owner. `program.rs:374–387` constructs a complete occurrence-to-index map from the retained vector, checks every occurrence's artifact and registry/source identity, and rejects duplicate keys. `LocalSource::expression` at `local_source.rs:174–177` checks source-root ownership and vector bounds. `program.rs:463–483` applies that lookup to every retained Apply before filtering selected-formal uses; the checked occurrence map must return the same vector cell, with pointer equality. A malformed unrelated callee cannot disappear behind a nonmatching formal or non-Name filter.

The second pass at `program.rs:485–535` follows retained vector order, matches resolved parameter identity, requires exactly one incoming Apply parent, and emits the actual Name/Apply coordinates. Separate direct uses remain separate witnesses; a shared Name with two Apply parents rejects the inventory. Unused formal Names return an empty successful inventory.

Source-root, Lambda/formal, annotation-owner, outer-effects-free Function, R35 result-row, and Observe guards remain. Function argument types stay general. Exact result path and negative polarity select the row; position, concrete vector and symbolic vector are rechecked. Equal spelling/ranges/payloads do not substitute for source identities. No AST/CST transformation or runtime instruction shape is introduced.

## Rust/Lean correspondence

- `SourceUseInventoryR37.lean:42–50` derives the occurrence/index table from the complete cell vector. `occurrence_lookup_sound`, `occurrence_lookup_complete`, and `occurrence_indices_unique` prove lookup and uniqueness facts.
- `rootValid` at lines 74–76 checks duplicate rejection, every source-key lookup, and every Apply edge. `all_apply_edges_owned` and `invalid_unrelated_apply_rejected` cover the full vector.
- `parent_count_occurrence_index` at line 196 equates incoming-edge counts by occurrence and checked vector index.
- `ambiguity_guard_equivalent` at line 484 proves R36's global ≤1 guard equivalent to Rust's count=1 guard on selected direct edges.
- `enumeration_second_pass` at line 307 relates individual-issuer enumeration to edge filtering and assembly using one selected Lambda and permission.
- `enumeration_order` and `enumeration_multiplicity` preserve ascending index order and predicate counts. `issued_index_bounded` derives its bound from an actual issued edge; `inventory_complete_individual` covers every successful individual issuer.
- `empty_success` returns `some []` after valid preparation when no direct use exists. `inventory_applies_to_r36_r35` applies each result to the original R36 issuer and R35 authentication on the same projected source pool. `inventory_sites_owned` establishes retained registry/source agreement.

No generic Rust simulation law is assumed. The finite model explicitly represents the vector, source-key registry, callee owner, indexed edge, and individual issuer. Native root selection, Arc/HashMap internals, allocation implementation, and HIR construction remain correspondence boundaries; this is not a mechanically verified Rust interpreter.

## Allocation and publication

`source_callback_uses` returns `Result<Option<Vec<_>>, TryReserveError>`. Reservations in both maps and the output vector propagate errors. The R37 path also uses fallible row collection, authentication, and payload cloning; the primary repaired both R35 row recollection and authentication paths so fallible reservations propagate through `Err`. The older Option/bool compatibility wrappers retain their earlier behavior for existing callers, but the reviewed inventory path does not call them. Partially constructed local state is discarded on error; no published or recovery state is mutated.

`allocatedInventory` has an explicit allocation-success premise and separates `.error ()` from `.ok none`. It does not establish allocator implementation, timing, error payload identity, or survival of fatal allocation failure. These limits are disclosed and do not establish runtime closure.

## Independent Lean verification

Observed checker: Lean 4.35.0, x86_64-unknown-linux-gnu, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (Release).

Command: `bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024`. The stream comprised complete R34 standalone source followed by R35/R36/R37 with only first import lines removed; it appended `#check @` and `#print axioms` for all 27 R37 theorems.

Input SHA-256: `fa172640ba999ff373c314e249c9559abbaae686dacc8858264b4039c5bddad6`. Exit 0, empty stderr, no diagnostics, elapsed 9.336047s, 90-second timeout. All complete theorem types were inspected. No theorem assumes runtime invocation, Rust simulation, or original parent closure.

| Theorems | Complete transitive axioms |
|---|---|
| `lookup_of_mem_unique`, `occurrence_lookup_complete`, `occurrence_indices_unique`, `parent_count_occurrence_index`, `issued_one_parent`, `ambiguity_guard_equivalent` | `propext`, `Classical.choice`, `Quot.sound` |
| `occurrence_lookup_sound`, `root_validation_exact`, `all_apply_edges_owned`, `invalid_unrelated_apply_rejected`, `source_key_mismatch_rejected`, `prepare_exact`, `inventory_exact`, `enumeration_complete`, `enumeration_second_pass`, `enumeration_order`, `enumeration_multiplicity`, `empty_enumeration`, `empty_success`, `issued_index_bounded`, `inventory_complete_individual`, `inventory_applies_to_r36_r35`, `projected_cell_origin`, `inventory_sites_owned` | `propext`, `Quot.sound` |
| `duplicate_occurrences_rejected`, `allocation_success_correspondence`, `allocation_failure_distinct` | `propext` |

No `sorryAx` or project axiom occurred. Explicit-file scans of R34–R37 found no proof holes, project axioms, native evaluation, unsafe implementation replacement, or checker bypasses. Three audit invocations occurred; two earlier orchestration captures were discarded, and only the final retained audit is evidence. Count all three invocations conservatively; each had a 90-second timeout. No persistent checker remains.

## Frozen identities

| Artifact | SHA-256 |
|---|---|
| `program.rs` | `d648e2f180cbe4690d70ee0813d92759929678eb10b4e0973e7b6f7833da91b4` |
| Rust handoff r1 | `f7189a06126c9cb32d483e267d7b293c194f05cf5afc2f8bd25b66c23a7460fb` |
| `SourceUseInventoryR37.lean` | `4981f8c20dc5d9c932d9f4a843f2245c034daaa015e7fc7b97aa7a343bb7ea30` |
| Proof handoff r1 | `ded40d8ce118b1403528de519d41ea6c59d7e61d514f8c4b86e1033d8e6f0054` |

All nine immutable manifest inputs matched their recorded hashes, including R36 Lean/review, HIR owners, R34/R35, syntax identity and toolchain pin. Rust handoff's source hash is historical; this review targets the final primary-repaired hash above.

## Remaining boundaries and STOP receipt

Rust compilation and execution remain unobserved. No Cargo, tests, build, Lake, formatter, scratch, cache, target, extraction file, copy, worktree, or new environment was used. Neither quarantined runtime consumer was opened or searched. The R36 unauthorized-read incident remains separate history; this review neither erases it nor releases either quarantine.

This PASS covers checked finite source-use extraction and enumeration correspondence. Runtime Name receipt, entry/invocation, permission/Grant consumption, transport/propagation, Catch subtraction/residual provenance, native Step/History, shared source strategy, original Simple-sub A/B, whole-language hygiene, soundness, principality, progress, termination and production promotion remain OPEN.

Reviewer STOPPED. No writes were performed, no descendants were started, and no continuing verification process or path-release claim remains.
