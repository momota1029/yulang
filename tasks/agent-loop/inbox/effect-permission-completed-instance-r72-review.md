# R72 independent source review

**Disposition: BLOCKED / fixed success gate not satisfied.** No files were changed by the reviewer; this report was persisted by Luna from the reviewer's final inline report. Review identity `/root/r72_review`, requested role `compiler_referee`, observed model metadata UNKNOWN. No descendants, author contact, Lean execution, build, test, formatter, scratch, cache, environment or Git mutation by reviewer.

## Findings

### BLOCKING — no successful Lean verification of the final artifact

The final retained Lean run exited 1 against pre-repair artifact SHA `07502471be3d1bd6e1caf5414d4292fc38b5f0c8584e282322751a7ba2c8c7b7`. Diagnostics reject `accepted_package_fields` and `accepted_table_fields`; their retained axiom audits contain `sorryAx`. The submitted final artifact is a different SHA, `f06912ddec14c3b0223dbf44e531ea9600f6df8318cbff0139e90a6247149cab`; the two subsequent repairs were never checked. Retained audit classifications for the prior attempt:

| Declarations | Transitive axioms |
|---|---|
| `term_coordinate`, `accepted_order_and_endpoints`, `accepted_owner_and_readbacks`, `foreign_occurrence_rejected` | `propext` |
| `namespace_identity`, `accepted_replay`, `finite_decode_replay`, `accepted_all_return_fields`, `accepted_r66_same_witnesses`, `accepted_competitors` | `propext`, `Quot.sound` |
| `accepted_package_fields` | `propext`, `sorryAx` |
| `accepted_table_fields` | `propext`, `sorryAx`, `Quot.sound` |

These are pre-repair receipts, not verification of the final module. The proof author used all four allowed probes; attempt 1 completion remains UNKNOWN. The final source must remain **CONSTRUCTED / UNCHECKED**, never a Lean proof pass.

Minimum closure: under a separately admitted bounded packet, check the exact final bytes successfully and retain complete theorem types and transitive axiom audits without `sorryAx`.

### MAJOR — Lean accepts duplicated or reordered `componentPositions`

Locations: `CompletedNativeInstanceR72.lean:112–116, 125–133`; `OwnerEndpointObservationsR69.lean:83–88`; `candidate_receiver.rs:923–925, 941–953`.

`buildTables` copies `componentPositions`, but `InputChecks` never checks its exact length and ordered correspondence with `componentRows`. R69 validation checks lookup and per-entry roundtrip only, so duplicate and reordered associations survive.

Concrete finite counterexample traced by inspection: use `T = C = A = Nat`, `owner = store = 0`, constant-Value kind, `terms = [0]`, `views = [.component 0]`, `components = [0]`, one row `componentRows = [(0,0,Value-coordinate 0)]`, matching one `liveComponents` entry, both Value lists `[0]`, empty Effect lists, and empty fact/provenance/interpretation/occurrence/edge lists. Set `componentPositions = [(0,0),(0,0)]` and give resources capacity at least one. Every R72 input check holds; R69 lookup still returns row zero and both entries roundtrip; R71's empty fact/edge loops and R72 output equalities succeed. Thus an extra row is accepted. With two distinct components, reversing `componentPositions` is similarly invisible.

Native validation rejects duplicates by length and reordering by indexed equality. This violates fixed outcomes 2–3 and the malformed/reordered-row rejection requirement.

Minimum closure: require the exact complete ordered-vector equality `componentPositions = componentRows.zipIdx.map (fun row => (row.1.1, row.2))`, or an equivalent check before replay. `Nodup` alone is insufficient.

### MAJOR — Lean projection does not preserve the distinct native owner identity

Rust retains both the `ReceivingResidualExperiment` borrow and completed `source_view`, and checks pointer equality before comparing source tables (`candidate_receiver.rs:752–762, 774–784, 903–917`). Lean's `owner : A` is used as the HIR artifact identity (`CompletedNativeInstanceR72.lean:78–105, 125–133`); there is no separate experiment/source-view identity or corresponding owner comparison.

Two experiment/session owners derived from the same HIR artifact therefore have the same modeled token. A foreign source-view/experiment pairing cannot be represented, so `foreign_occurrence_rejected` proves artifact rejection, not the native foreign-owner check. With empty provenance the artifact condition is vacuous. `ownerFacts`, `ownerProvenance`, and representative readbacks are independent list fields; equality among supplied lists does not bind them to a retained native owner. The handoff correctly calls this frontier OPEN, which means fixed outcomes 1, 3 and 5 are not established.

Minimum closure: preserve and check distinct owner identities at the primitive boundary and provide concrete extraction/correspondence binding each owner readback to that owner. Keep full HIR occurrence identity separate; do not use a blanket faithfulness premise.

## Source correspondence and remaining attacks

Positive source findings: `primitive_projection` borrows the existing completed encoding and rows, validates before return, publishes no partial projection, and moves existing maps rather than rebuilding them. `internal_root_view` propagates projection/reifier errors with `?`, preserving `SearchLimit` versus `BoundMismatch`. Distinct branded Term and ComponentId tables, structural metadata and ordered payloads survive decoding. Facts retain index, identity, lower/upper Terms and four interpreted endpoints. Provenance retains order, original edge index, occurrence and slot. Exact Value/Effect representatives are compared against the session. R71 reconstructs first-appearance occurrence coordinates and complete provenance-based competitor lists. `accepted_r66_same_witnesses` applies R71 to unchanged source/native/request/Root/use/lambda premises and preserves slot-0 and slot-2 witnesses.

Native fields still outside the Lean corruption model include `source_view`/owner pointers, slice pointers, acceleration maps, completed-edge `fact_index`, fact/edge pointers, and duplicated identity/lower/upper edge fields. Rust validates these, but `Edge Nat` contains only edge index, fact, occurrence and slot. No compiled Rust/runtime or allocator equivalence is claimed.

The actual remaining R66 premise is genuine `Root` (`OccurrenceQualifiedConsumerR66.lean:89`): source incidence and owner/identity reads, same artifact, permission-entry equality, and physical emission/admission/current-bound/root checks. Replay does not construct this Root. Original A/B, whole-language effects/soundness/principality/termination, and production remain OPEN.

## Audit and hashes

All immutable dependency pins matched the R72 manifest; receiver differs from baseline as expected. Attempt-4 embedded output hashes match. Compressed attempt-3, attempt-4 and final-unexecuted input hashes match their decoded bytes. No source holes or checker bypasses were found in the inspected replay inputs. Existing receiver tests were read only and do not exercise malformed projection cases.

| Artifact | SHA-256 |
|---|---|
| Rust receiver | `9dfac06c82d62eb2c012f2f8b3a5affa6a85a397429302925463ee05a5cdf282` |
| Rust handoff | `e6284d0dcb146a3e41f1dff9fba0e69a784e0a80b73021c25737fe41b2009a67` |
| Lean module | `f06912ddec14c3b0223dbf44e531ea9600f6df8318cbff0139e90a6247149cab` |
| Proof handoff | `fefef3e32fc2b200b0e78101f0d2de7cccb77c02727dc7aea76f3bd870fbadf1` |

**Reviewer STOPPED / WRITES STOPPED.**
