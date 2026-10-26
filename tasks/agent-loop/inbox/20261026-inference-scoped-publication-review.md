# Independent review: owner-local scoped publication

Date: 2026-10-26. Reviewer: `/root/call_entry_review`, independent of producer
`/root/inference_frontier`. Requested model/effort inherited; separately observed
runtime model/effort metadata was unavailable. This receipt reviews the frozen
finite structural proof packet, not the whole inference implementation.

## Verdict and severity

**CLEAN within the declared scope.** No blocking, major, or minor finding was
identified. The clause-image theorem derives its correspondence from actual
owned clauses, structural dependencies, and explicit stopping/metadata premises.
The solution corollaries use one supplied post-publication valuation throughout.
Neither the code nor the handoff claims that native successful inference
constructs that valuation or establishes the required metadata invariants.

Recommended action: accept this packet as conditional scoped-publication proof
progress. Keep native all-history metadata closure, complete native clause/root
correspondence, and `SourceProblem.InferenceSoundness` open. The counterexamples
exclude proposed metadata shortcuts; they do not demonstrate an accepted source
program is unsound.

## Inspected frozen inputs

Paths below are relative to `/workspace/scratch/f98087c7ac1a/yulang` unless stated
otherwise. The complete target source and complete handoff were inspected.

| Input | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/SimpleSubScopedPublication.lean` | `d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f` |
| `tasks/agent-loop/inbox/20261026-inference-scoped-publication.md` | `8bc2a4306cb32a32b8c3262d59a7f59d2cf60fe980554465c36d1bc9d2e50a79` |
| `notes/theory/lean/YulangClosure/SimpleSubGeneralizationSoundness.lean` | `3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246` |
| `notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean` | `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/2026-10-24-native-level-closure-and-publication.md` | `37aeacff4a6dc310bedcb5a44db4afcf8329b05ed684df19350487c5e8711c13` |

The four Lean source hashes match the isolated project copies. Existing syntax,
contracts, and transport definitions were used as dependencies, not independently
recertified as whole modules in this review. Repository reviewer and Lean-proof
instructions previously read in this session governed the review.

## Semantic checks and exact locations

All line references in this section are in the frozen target module.

1. **Actual structure and owned bounds, lines 29–90.** `vars` covers every frozen
   `Term` constructor, including all four Function ports and cross-kind effect
   variables, compound tails, and tuple/record/variant bodies. `Bound` retains
   kind, owner, side, and body. Positive and negative clauses have their proper
   orientations; renaming changes both owner and complete body under the same
   kind-preserving map. Boundedness covers every variable needed for the
   transport square.
2. **Reachability and stopping, lines 92–127.** Root rows remain reachable even
   when inactive. A step traverses a bound only from its reached, capture-active
   owner through an actual body dependency. `StoppedClosed` is a concrete
   per-bound dependency condition. `reachable_active_image` derives an image
   path for active targets by induction: an active image dependency cannot have
   an inactive image owner under that condition. It does not assume final
   reachability, publication correspondence, or a source typing judgment.
3. **Publication selection and complete base, lines 129–163.** The zero/one
   `guardLevels` encoding reuses the existing transport and does not replace
   native levels or Value birth. `Published.base` retains every supplied owned
   clause. `Published.copy` requires a supplied bound, selected use, reached
   owner, and capture-active owner; its whole clause uses one allocation map.
   The theorem concerns membership and satisfaction, not physical ordering,
   multiplicity, evidence identities, or allocation traces.
4. **Derived clause inclusion, lines 165–232.** The bounded commuting lemmas
   invoke the existing `Generalization.transport_freshen` with the derived
   inactive anchors. In the hard copied-clause case, the proof splits on the
   post-map capture owner. An active owner obtains the needed post reachability
   from the preceding induction. For an inactive owner, `stopped_clause_fixed`
   uses stopping closure on every body variable plus capture-stop implying
   allocation-stop; the entire copied clause equals a retained base clause.
   Thus `publication_clause_image` assumes neither its final inclusion nor a
   final model. Its complete retained-base premise is essential and explicit.
5. **One valuation and arbitrary clients, lines 234–265.** These corollaries
   explicitly assume a valuation satisfying the selected post publication (and
   the same-map renamed clients where applicable). They pull it back through
   one total `Generalization.transport`; there is no per-use or per-clause
   witness selection. This is conditional solution transport, not a theorem
   producing a solution from native successful return. Arbitrary finite clients
   need no boundedness assumption because their renaming uses the same total
   map. Bounded actual-root equations remain available from the frozen
   generalization dependency; native root inventory is not constructed here.
6. **Exact capture/current/non-generic guards, lines 267–365.** Capture uses
   `boundary < level && !nonGeneric`; use allocation additionally requires the
   captured flag and the current metadata guard. `BoundLevelsClosed` and
   `NonGenericClosed` together derive stopping closure. `MetadataTransport`
   requires level nonincrease and preservation of an already-set non-generic
   bit, separately for capture and current-use snapshots. These facts derive
   inactive-image preservation and the specialized theorem's premises. They
   are explicit local metadata hypotheses, not disguised source soundness or
   a proof that all native histories satisfy them.
7. **Counterexample scope, lines 367–423.** The first finite example has numeric
   level closure but violates the non-generic-aware stopping property. The
   second uses the exact class-minimum construction and proves its finite map
   canonical, yet loses the post stopping property. Neither provides a source
   occurrence, qualifying intrusion pair, or accepted native source trace. The
   handoff correctly limits both conclusions.

The governing October 24 note distinguishes the stronger reachable-set and
publication equality obligations in NL6 from solution transport in NL7. This
packet proves forward clause inclusion only. It can therefore avoid reverse
reachability and quotient-class saturation without asserting the stronger
equality result. Its generic algebra permits arbitrary kind-preserving maps;
canonical native allocation and disjointness remain additional obligations, as
the handoff states.

## Native correspondence readback and limits

Readback in `crates/yu-solver/src/candidate_scheme.rs` covered row capture at
1740–1782, owner stopping and Value/effect expansion at 2137–2250, restoration
at 4178–4194, and current allocation/memo decisions at 4234–4275. The captured
`local` test and current-use level/non-generic test agree with the two-stage
guards. The existing canonical image can win before a new eligibility
decision, so canonical first-image coherence remains a real separate premise.
Effect incidence/allowance clauses and reverse upper-owner frontiers are not
all ordinary owner/body bounds and remain outside the new correspondence.

Native input hashes matched the handoff:

| File under `crates/yu-solver/src/` | SHA-256 |
| --- | --- |
| `candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |

This was selective correspondence readback, not a whole-file or all-history
Rust review. The original Scala source was not freshly inspected. Native
all-history metadata closure, all publication clauses and roots, canonical
memo coherence, allocator identity, regular-model existence, successful native
inference, full source constructor/effect/Call coverage, principality, and
termination remain uninspected or unproved by this packet. No other module or
production gate is certified by this receipt.

## Retained checker evidence

The complete 1,286-line `audit-04.log` was read, including actual types and
axiom reports for private/generated declarations. Audit source enumerates
the originating module, rejects project axioms, checks required roots, and
prints/checks each theorem against the allowed axiom policy. Parsing the full
log, including wrapped axiom reports, confirmed 82 unique matching begin/end
and axiom entries: 51 without axioms, 13 with only `propext`, and 18 with
`propext` plus `Quot.sound`. The source has 26 authored theorems (three private);
the remaining 56 audited theorems are generated. No `sorryAx`, project axiom,
or `Classical.choice` occurs in their audited dependency sets.

The retained build and audit receipts both record exit code 0. Build command:
`lake --no-cache build +YulangClosure.SimpleSubScopedPublication`; five jobs,
2.2743514239991782 seconds. Audit command: `lake env lean -j1 -M1024
ScopedPublicationAudit.lean`; 1.2197492499999498 seconds. Both use the recorded
absolute Lake under the pinned Lean 4.35.0 toolchain. `versions.log` records
Lean commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` and Lake
5.0.0-src+eb6cafb. No checker or version command was rerun by this reviewer.

All following paths are under
`/workspace/scratch/f98087c7ac1a/inference-scoped-publication/`:

| Evidence | SHA-256 |
| --- | --- |
| `audit-04.log` | `9262b9a4b2f1b6abc496f439936537c047d852abb676280c0ae72eb640c8c029` |
| `audit-04.json` | `2e1e7d41dd685f4759294efce3b1c1cb1ec5fb4f638ebd3834cdea1ff9468477` |
| `ScopedPublicationAudit.lean` | `a8a9ffb6d8cb9363427957c90080a9cc9de6c145c125bce6331965372c101e53` |
| `check-03.log` | `21cadadea08ec1a27c69f31e17ff1906f7712065003e803caf1dce5ef9bfa6b2` |
| `check-03.json` | `139bdb9d7c0910406d8c1513a4f4bc225fdde2b41e4b7e39079f5cb9d387c029` |
| `versions.log` | `dcbd6028b14fe332f4f1e8b181b54773f82fbffbd929be40c5d93cfa4656dd11` |

## Freeze and write boundary

No source, cache, configuration, Git, or shared coordination state was changed;
no child or checker was launched. The only writes in this two-part assignment
were the separately leased certificate delta receipt and this new scoped
publication review receipt. The target, handoff, and audit hashes were
rechecked before this receipt was written. This receipt is frozen at write
completion; its SHA-256 is reported to the primary. All reviewer writes have
stopped.
