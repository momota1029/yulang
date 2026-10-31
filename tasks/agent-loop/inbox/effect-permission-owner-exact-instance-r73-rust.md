# R73 Rust source projection — frozen handoff

Sprint ID / contract revision and SHA-256: `EFFECT-PERMISSION-OWNER-EXACT-INSTANCE/20261031-R73`, revision 1, `4a5f60480983ee6303125651d1e9a059e5b6dccef95f6f0b61dec278d06a9c55`.

Assignment ID / handoff revision: `/root/r73_rust`, revision 1.

Parent gate / original theorem and scope locator: unchanged Yulang inference/executor soundness, effects, principality and termination goal; original Simple-sub A/B and genuine R66 `Root` remain unchanged. This packet advances only the finite owner-indexed completed-instance source projection specified by R73.

Baseline / dependencies: baseline `94caa14c4ebd514d91d07a8101f61a55dba55436`; R73 input manifest SHA-256 `85fbdb5983b1c4588904bf9be38fb8d756167f8475f8649bd9f17d0e8f59474e`; all 44 manifest pins matched before writing. The R72 receiver baseline was `9dfac06c82d62eb2c012f2f8b3a5affa6a85a397429302925463ee05a5cdf282`. R72 source review SHA-256 `f5ae8c9fd71a29dc7f1879f6cde5e09b39afae04c94300b47b7c0d052c13cff2`; R72 outcome SHA-256 `a62bad1383bb803e76e60fa290fde7e3119344c3cc921753b576d6e46665733a`.

Role / actual worker ID / session: implementation author `/root/r73_rust`; session `EFFECT-PERMISSION-OWNER-EXACT-INSTANCE/20261031-R73`; launch/resume receipt is held by Luna. No descendants.

Requested model and effort / observed model and effort: `gpt-6-luna` / high requested; observed model and effort UNKNOWN because runtime telemetry was unavailable.

Exact leased paths / authors: only `crates/yu-solver/src/candidate_receiver.rs` and this handoff; author `/root/r73_rust`.

Outcome class: implementation, bounded source-native owner and completed-view correspondence.

End-to-end source behavior achieved: `primitive_projection` now takes the selected `ReceivingResidualExperiment`, checks its reference identity against the owner retained by the successful completed source view before accessing completed tables, then derives every table readback from that selected view. The projection keeps three distinct references: experiment owner, exact completed-source-view value, and the admitted HIR artifact inventory borrowed directly from the owner's `ConstraintStore`. No pointer is converted to an integer.

For every distinct provenance occurrence, the reifier first applies native `store.require_owned`, resolves it with `hir_for_occurrence`, and stores the exact owning module's index into the original `store.hirs` inventory. The projection checks the occurrence's full branded identity against that admitted inventory entry, checks the selected lookup returns the same `Arc<HirModule>` reference, and re-applies `require_owned`. Artifact position does not replace the original `HirOccurrenceId`; multiple experiments may retain separate experiment identities while referring to the same admitted HIR artifact. No global artifact uniqueness assumption was added.

Exact correspondence / field dispositions:

- **Mapped in the checked source projection:** owner and completed-view selection; complete HIR admitted-inventory membership and per-occurrence artifact coordinate; ordered component rows and exact `component_positions[position] == (row.term, position)` equation, which is the source form of `componentRows.zipIdx`; current Value/Effect bounds by exact slice pointer and length; every Value/Effect representative against the current canonical row; complete fact and provenance tables in order; fact identity and lower/upper terms; interpretation endpoints; occurrence and slot rows; and each edge's original index, `fact_index`, edge/fact references, identity and lower/upper fields. `SearchLimit` remains distinct from malformed `BoundMismatch`.
- **Checked by the Rust source but not thereby proven or pointer-modeled in Lean:** source fact/provenance slice pointers and row pointers; exact owner-bound term/component accelerator maps; completed-view and experiment-owner borrow identity; admitted HIR module reference identity. Lean must derive owner readbacks through its selected owner/view, not accept independently supplied ownerFacts, ownerProvenance or representative lists. The Rust projection supplies source evidence for this binding; it is not a proof of the Lean gate.
- **OPEN in the finite Lean corruption model:** physical source-view/slice pointer values and accelerator-map allocation identity; fact/edge pointer equality as pointer equality. The Lean interpretation can check the corresponding selected indices, ordered contents, and endpoint rows, but must not claim to validate raw pointer/map identity. Native runtime/allocator equivalence remains OPEN.

Parent/source/native correspondence: `InventoryPackage` completes `reify_qualified_facts`; only a successful `InventoryCompletedReificationView` reaches `primitive_projection`. Owner/view selection precedes borrowing its tables. R72's complete bounds, representatives, facts, provenance, occurrences, edges and interpretations are read from this retained view, while artifact ownership resolves through the exact `ConstraintStore.hirs` inventory used by `require_owned`. The existing consumer receives the projection only after validation, and its error path continues to preserve `SearchLimit` versus `BoundMismatch`. This is source inspection evidence only; it is not a compiled Rust result, a Lean proof, or native runtime equivalence.

Prior evidence reused / rejected: reused the R72 receiver's successful-return borrowed projection, exact table order, owner-session bounds and representatives, source edge/fact correspondence, and R72 review's concrete duplicated/reversed `componentPositions` and foreign owner/source-view attacks. Rejected treating R72's Lean artifact as a successful proof: its final bytes were unchecked, and its accepted independent readback lists and collapsed artifact/experiment identity remain invalid inputs to the R73 proof lane. R72's 4-probe budget remains spent/UNKNOWN and is not reused.

Artifact / SHA-256: `crates/yu-solver/src/candidate_receiver.rs`, `eb35c73ead829ed439a347d3cb665d52d3aa4b45b242c1155cfd4377a68d6415`. This is the frozen source snapshot for review.

Checks / coverage / resources: verified all 44 pins in the R73 manifest and its manifest SHA; `git diff --check -- crates/yu-solver/src/candidate_receiver.rs` passed. No Cargo, compiler, build, test, formatter, Lake, cache, target, scratch, worktree, environment, dependency, configuration or Git mutation was performed. Rust compilation/runtime, allocator behavior and two-experiment shared-artifact execution were not run. Assignment cap: 1,400 seconds. Actual elapsed active-work telemetry is UNKNOWN; no claim of a full cap charge or of runtime-model observation is made.

Mutual TODO for Lean owner: use distinct experiment-owner, completed-source-view and HIR-artifact identities. Select the owner/view before reading any tables, resolve each occurrence against its admitted owner inventory, then derive facts/provenance/representatives through that selection. Preserve the exact ordered `componentPositions` equation, current bounds/representatives, complete endpoint and provenance rows, same-FactId distinct occurrences, full competitor lists and unchanged genuine R66 `Root`. Reject duplicated/reversed positions, foreign view/experiment pairings with empty provenance, substituted readbacks, and two experiment owners sharing one HIR artifact. Report the raw-pointer, slice-allocation and accelerator-map checks as OPEN Lean/native-runtime obligations; do not infer them from this source projection.

Remaining OPEN: successful pinned Lean check and complete axiom audit; Lean owner-indexed decode/replay; actual genuine R66 `Root` construction; original A/B; Rust compilation/runtime and allocator/resource equivalence; raw pointer/slice/map identity in the Lean corruption model; whole-language effect hygiene, soundness, principality, termination and production. No inference or semantic rule changed. No provisional cutover is claimed.

New paths: this handoff only. Changed leased source: `crates/yu-solver/src/candidate_receiver.rs`. Disposable scratch paths: none.

Worker state / writer cessation: STOPPED / WRITES STOPPED after freezing the two leased outputs. No descendants or remaining processes are claimed active. Runtime telemetry remains UNKNOWN.

Review / integration: frozen for fresh independent review and Luna adjudication; not self-certified, not integrated, and not a proof or production gate closure.
