# Centered reachable permutation: correspondence and installation obligation

2026-11-14, astra2-centered-10; integration base `9adf3351c`.

**Status: the requested `GeneralNominalCenteredCanonicalTransport.ReachablePermutationSimulation roles` is still open.** This turn proves the correspondence representation, its initialization on every reachable packet-free state, all non-installation constructor branches, and substantial guard and ledger transport. It does not establish `CanonicalExitLifting` or unconditional `CanonicalLocalOrder`. The previous executor and its eleven unconditional fields are unchanged.

## Representation

`GeneralNominalMetadataEquivalence.Same` retains the entire observation core and changes only the enumeration of `allocated` and `reserved`, preserving membership in both. Models, Known, RootPending, source membership, Linked, Fresh, and both sides of refinement certificates transport. This is stronger than model equivalence: raw observation descriptors and ordinary constraints remain literal.

`GeneralNominalCenteredPermutationRepresentation.RebasedPacket first last packet other` says that the first packet records `first`, its declaration is paired under `DeclarationReorders`, and the other packet is precisely the existing registry/declaration rebase followed by `GeneralNominalPacketMetadata.rebase`. The second operation changes the historical context's allocation/reservation enumeration with the same membership. It retains bounds, source identities, the site and interpretation. `packet_observation` proves its semantic and readback properties, assuming `first.roles = roles`.

`Corresponds first last left right` uses one finite table of packet pairs. Every table entry satisfies `RebasedPacket` and occurs in the respective packet journals. A single coherent partial bijection induced by that table is used by both raw facts and centered plans. The centered relation retains literal source roots, equal raw sites/edges/aliases, equal centered-site membership, and pointwise paired plan ledgers. It transports raw/centered models, plan equations and plan-test membership. It allows permutation of emitted centered sites. Every table entry must be recorded; the definition does not require the converse that every raw packet is in the table. The raw journal separately pairs all packets semantically. Any stronger table-coverage invariant needed by installation must still be established from reachability.

Coherence is essential: separate existential witnesses for each ledger would not identify the packet referenced by a prior input fact with the packet being settled and promoted. `Coherent.left/right`, `fact_members`, and centered `PlanPair.left/right` supply that identity. No equivalence of inputs is substituted for literal packet/plan equality in a promotion rule.

`reachable_packet_free` establishes `Corresponds first last state state` for every state reachable under G′ at `first` with an empty packet journal, for any `last`. The added `packet_free_facts` proof shows that such a trace has no support facts: installation contradicts the empty journal, and the singleton centered site makes a merge contradict its novelty guard. The prior shape theorem supplies the empty plan ledger.

## Checked transport

The exact public declaration inventory is in [`lean/Audit/CenteredReachablePermutation.lean`](../../lean/Audit/CenteredReachablePermutation.lean): 152 declarations from thirteen new modules, including definitions carrying proof data. The main results are:

| Module/namespace | Results |
|---|---|
| `GeneralNominalMetadataEquivalence` | `models`, `known`, `pending`, `sources`, `linked`, `fresh`, `refines_left`, `refines_right`, `extend` |
| `GeneralNominalJournalPermutation.Related` | `models`, `alias`, `generated`, `discharged`, `waiting`, `refresh`, `reobserve`, `view`, `administrative` |
| `GeneralNominalJournalPermutation.Related` (K2 module) | `argument`, `structural`, `edge`, `path`, `cycle`, `recursAt`, `recover`, `sameInputs`, `committed` |
| `GeneralNominalLedgerPermutation.Related` | `slice`, `packet_settled`, `readback`, `trusted`, `pool`, `head_supported`, `available`, `ready`, `settled_head` |
| `GeneralNominalLedgerPermutation.Related` (shared module) | `input_explanation`, `output_certificate`, `shared_trusted` |
| `GeneralNominalCenteredLedgerPermutation.Related` | `models`, `facts_models`, `readback`, `trusted` |
| `GeneralNominalLedgerPermutation.Related` (value module) | `downstream_need`, `proper_waiting`, `value_need`, `grounded`, `supported` |
| `GeneralNominalLedgerPermutation.Related` (administrative module) | `merge_guard`, `merge_alternatives`, `merged_facts`, `merge` |
| `GeneralNominalCenteredLedgerPermutation.Related` (administrative module) | `administrative`, `refresh_certificate`, `refresh`, `merge_action`, `at_transport_or_install` |
| `GeneralNominalReportMetadata` | `inspect`, `many`, `bindings`, `selfChecks`, `finished`, `projectionModels` |
| `GeneralNominalPacketMetadata` | `report`, `children`, `named_schema`, `input_schema`, `inputs`, `outputs`, `holds`, `inherited_report`, `observation` |
| `GeneralNominalCenteredPlanLedgerReordering` | `inputs`, `outputs`, `paired` |
| `GeneralNominalCenteredPermutationRepresentation` | `packet_observation`, `packet_free_refl`, `initialAt`, `initial`, `at_transport_or_install`, `step_transport_or_install`, `packet_free_facts`, `reachable_packet_free` |

The non-installation branches are actual constructors of the unrestricted centered relation:

* Administrative enqueue, raw refresh, equality feedback, and certified reobservation transport. A raw refresh reuses the same target context; reobservation copies the descriptor entries onto the counterpart's metadata. Their certificates and improvement conditions transport.
* Centered refresh also reuses the target context. Its exactness premise is transported using centered model equivalence.
* Centered merge transports site membership, center-based SameInputs, alias novelty, and the raw support guard. Equality of the dependency pool and every support guard gives literally equal `mergeAlternatives` and `mergedFacts`, retaining every alternative.

`View` is transported separately from executable steps. Its arbitrary certified refreshes/reobservations need no Known or point-improvement premise. This establishes `Need` transport before proving value-support transport; the proof does not assume the Step simulation it is intended to support.

All three Trusted inductions are proved. The shared proof preserves the exact readback list and the certificate's substitution. The centered proof transports the legacy branch, centered input/output facts, and center merge explanations. Readback witnesses retain the same observations and terms.

## Guard audit and remaining proof

No order-sensitive guard was found. This is a source audit conclusion, not a full Step-invariance theorem. Visibility is declaration membership; requirements are paired by permutation. The support implementation filters all alternatives rather than choosing a first alternative. The associated-equation lookup reads a list retained literally by `DeclarationReorders`. Source-slot lookup is over a source-injective basis. The previous registry-rebase lemmas handle the emitter's choices by equality of their predicates.

The proved constructor reduction has this exact shape (namespace `GeneralNominalCenteredPermutationRepresentation`):

```lean
step_transport_or_install
  (same : Corresponds first last left right)
  (step : GeneralNominalCenteredSteps.Step first root left next) :
  (∃ other,
    GeneralNominalCenteredSteps.Step last root right other ∧
    Corresponds first last next other) ∨
  ∃ plan support,
    GeneralNominalSaturationState.Generated left.erased.current root
      plan.packet.site.occurrence ∧
    next = GeneralNominalCenteredSteps.install left plan support ∧
    GeneralNominalFeedbackSteps.Installable first left.erased.current plan.packet ∧
    ¬ GeneralNominalFeedbackSteps.Committed left.erased.current plan.packet ∧
    GeneralNominalCenteredSteps.PacketGuard left plan support
```

The second disjunct is an exposed obligation, not an installed counterpart. The following work is undischarged:

1. Build the counterpart plan over the counterpart's current context and prove its complete `Installable`, novelty, and `PacketGuard`. The packet metadata and registry rebase semantics are now available, as are the three trusted-ledger and value-support inductions. They have not been assembled with Prepared/HeadReady, Joint, both local-classifier guards, Safe/AlternativesSafe, and root/candidate cycle exclusions for this newly constructed plan.
2. Extend the finite coherent table at installation and show `Corresponds` for the full installed states, including private-context metadata, raw and centered emissions, and all inserted support facts. Novel commitment and recorded commitment are the intended freshness argument; no table-extension theorem is claimed here.
3. Prove the fixed-target-registry observation clause, literally:
   `∀ left right, Corresponds first last left right → ∀ demand frontier, GeneralNominalCenteredAdministrativeLocal.Local last left demand frontier ↔ GeneralNominalCenteredAdministrativeLocal.Local last right demand frontier`.
4. Supply both directions and assemble `Simulation first last root related`, possibly strengthening `Corresponds` with reachable invariants if required. The concrete inverse correspondence and full installation matching are not established.

The exact remaining global hypothesis is the frozen definition:

```lean
GeneralNominalCenteredCanonicalTransport.ReachablePermutationSimulation roles
```

It quantifies over every checked registry, every G′-reachable state and root with an empty packet journal, and requires a relation initially relating the state to itself together with a full two-way `Simulation registry (canonical registry) root related`. Only its initialization and the constructor reduction above are discharged in this turn. Consequently the existing implications to `CanonicalExitLifting` and `CanonicalLocalOrder` remain conditional on that hypothesis; the composition's existing `evidenceNode` and `generatedChildren` residuals are unchanged.

All new component results have explicit premises. Raw/centered `Related` supplies the stated correspondence, not reachability. Ledger results require its `Coherent`, semantic packet observations, source equality, journal correspondence, exact packet-membership correspondence, and paired facts; centered results additionally require site membership, paired plan equations/tests, and source roots. Value-guard results require `Reorders`. Registry packet/plan rebasing additionally requires the stated role equality; metadata packet rebasing does not require it. `PlanLedgerReordering.paired` requires membership of the chosen packet pair in its supplied relation. Refresh transport consumes a genuine original certificate; action transport consumes a genuine original action. No hidden production or common-model hypothesis has been discharged by these general bridges.

## Validation

All commands were run from `lean/`:

| Exact command | Exit code |
|---|---:|
| `lake build Yulang.GeneralNominalCenteredPermutationRepresentation` | 0 |
| `lake build --wfail` | 0 |
| `lake build Yulang` | 0 |
| `lake env lean Audit/CenteredReachablePermutation.lean` | 0 |

The module target imports all thirteen new modules. All 152 audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`. Intermediate elaboration failures were corrected before these checks.

Separate reviewers examined metadata/administrative/view transport and coherent trusted-ledger/merge transport. The requested prover role is unavailable in this environment; no prover agent ran. The primary constructed these component proofs. The main simulation remains open, with no owner question raised by an order-sensitive guard.
