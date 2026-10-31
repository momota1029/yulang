# R70 independent review — BOUNDED PASS, research only

Reviewer `/root/r70_review`; sole reviewer, no descendants. Rust and Lean authors were confirmed STOPPED / WRITES STOPPED before review. No author contact occurred.

**Findings: blocking 0; major 0; minor 0.**

The review-only role prohibited file edits, so the reviewer returned this report inline. The primary persisted it verbatim in substance after receipt.

## Scope and evidence

Reviewed the actual Rust and Lean artifacts before using author handoffs as verification receipts. Governing scope: R70 contract revision 1, original source-preservation claim §§1, 3, 5, authoritative birth-level SCC correction §§2–6, and R69/R68/R67/R66/R65 definitions. Direct identity owners in `term.rs`, solver `lib.rs`, and HIR `module.rs`; observation construction, recursive closure, endpoint interpretation and qualified fact consumers; relevant existing function, variant, record, tuple, rollback and receiving tests were inspected read-only.

No Cargo, build, test, formatter, Lake, Lean process, bundled checker, scratch/cache/environment/worktree creation or source modification occurred. Read-only hashing, in-memory receipt reconstruction and `git diff --check` were used.

## Correctness assessment

The change addresses the representation gap at its owner: `InventoryEndpointObservations` constructs its finite encoding after validating the source tables, at `candidate_receiver.rs:835–963`. It adds no downstream identity assumption.

- **Full Term equality:** `term.rs:110–123` derives equality and hashing over both arena brand and index. The existing observation map rejects duplicate complete keys; `candidate_receiver.rs:1491–1499` checks the equality-backed lookup against its actual source row before conversion. Equal local indices from unequal brands cannot alias. Repeated references to one complete Term reuse its position.
- **Separate ComponentId identity:** `candidate_receiver.rs:1503–1511` inserts the first equal complete ID and uses equality-based position lookup. Solver `lib.rs:392–422` retains occurrence/root variant and kind; HIR equality retains artifact identity. No name, local ordinal or hash becomes the identity.
- **Nested payloads:** `candidate_receiver.rs:1515–1583` exhaustively preserves every TermView case, function child order, variant alternative/payload order and tags, record names/optional flags, tuple order and duplicate children, leaves, live-variable metadata and polarities. Metadata borrows remain tied to the existing source lifetime.
- **Components and namespaces:** `candidate_receiver.rs:1585–1631` preserves component row order, position associations, live kind/ordinal and separate Value/Effect representative vectors. Repeated equal component IDs with inconsistent term or live metadata reject.
- **Errors and restoration:** missing references and mismatches return `BoundMismatch`; reservations and checked token conversions return `SearchLimit`. Construction uses local temporary vectors and immutable source borrows. Failure drops partial encoding without publishing it or mutating inference state. Existing inference, propagation, permission-consumption and execution algorithms are unchanged.

Traced counterexamples included foreign-brand Terms, missing nested references, unequal components sharing local coordinates, repeated inconsistent components, stale/reordered source rows, zero/multiple variant payloads, optional records, duplicate tuple children, and equal numeric Value/Effect ordinals. The checks or preserved representation distinguish these cases within the stated construction premises.

## Lean assessment

`EncodedOwnerObservationsR70.lean:18–71` constructs equality-decided first-occurrence tables and proves membership, uniqueness, order, round trips and token reflection. `term_token_is_source_position:653` connects term tokens to the original unique observation positions.

`SourceView`, `encodeView`, `nested_children_commute:126`, `nested_metadata_and_order:131` and `nested_reference_roundtrip:447` preserve all represented payloads and order. `References:187` checks coverage and repeated-component consistency; `construct:203` runs those checks and R69 validation on generated tables. Successful construction remains an explicit premise.

`sourceTables:254` is generated from the same primitive rows and component tokens. The lookup, component-coordinate, interpretation, raw/canonical endpoint and fact/decode commutation theorems at lines 264–445 compare those same records. `source_children_reflect:575` recovers original child equality using token reflection; `child_token_is_source_coordinate:694` connects nested Rust tokens with R69 child coordinates.

`qualified_read_commutes:480` and `r67_qualified_read_commutes:497` preserve complete competitor lists and qualified lookup. `r66_same_selected_encoded_endpoints:517` applies R69’s construction theorem through R68/R67 to the same original R66 Root, retaining its slot-0 route and slot-2 construction witnesses, fact identity, registered root/use/function endpoints and both interpretation judgments. No independent interpreted inventory or blanket faithfulness law is introduced.

The theorem still requires successful construction, successful decoding, original R66 Root and exact use/lambda coordinates. These premises have not been converted into conclusions.

## Verified hashes and audit receipt

All 13 unchanged input-manifest entries match their pins. The changed receiver matches both frozen author handoffs.

| Artifact | SHA-256 |
| --- | --- |
| R70 contract | `2f04b0fd4447b0f9d3c31c04c22482b62952fe0e6c84c90b423a7ea9a24a132d` |
| R70 input manifest | `92e9f3cb3e9b95577de9b459fb5114b2dc86c5f25dd3a70ce4b939c1643c90f9` |
| Rust receiver | `ef2f163baf66b87fe461525be2c991c4791ff516253e2f7d621d49b2bcb31624` |
| R70 Lean artifact | `8da5cbf20e12efea18a2c0c7582d39494c09b9b5b403201c114cf61930d21c9d` |
| Rust handoff | `9d7cb950fba6838cb0c3721cd6f9ec3a5aa4520686207b63bada0d64c2c8030d` |
| Proof handoff | `8193ac7bdb80bb3535b1dcca67da1e8431e8ca1b51f19d5ea970103c4a245cf9` |

Independently reconstructed the documented final Lean stdin entirely in memory from the retained R68 prefix and exact R69/R70 non-import bodies:

- Dependency prefix: `2dcd466b386c50ef9773b450ce7a4b81b7f85827f6b6ada77cd62e163facec25`.
- Reconstructed stdin: `c42fc4279c4fe1815740e10cc9fd6643b6754c37115b3e7df68793048f159647`.
- Retained complete stdout: `fb34f69e7611ff9a68ba119ff3b2898fae4a86a1b7bf3c8229f3d6be364fbcf1`.

All match the final receipt. All 44 source theorem names have matching retained full types and axiom reports; per-theorem reports match metadata. Reported axiom union is exactly `propext`, `Quot.sound`. The reconstructed closure contains no `sorry`, `admit`, `sorryAx`, `native_decide` or `skipKernelTC`. This authenticates receipt consistency; the reviewer did not independently rerun Lean.

## Remaining boundaries

Rust compilation/runtime, native identity authentication and Rust-to-Lean execution correspondence, actual source-instance construction/decode success, original R66 Root, native resource/failure equivalence, original A/B, whole-language effect hygiene, soundness, principality, termination and production remain **OPEN**.

Verdict permits a bounded research checkpoint only.

**Reviewer STOPPED / WRITES STOPPED. No files written by reviewer; no descendants or running verification processes.**
