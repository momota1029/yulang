# Centered permutation simulation and canonical local order

Date: 2026-11-14. Scope: turn astra2-centered-11, based on `ddb3c11b3`.

The unrestricted centered Step now has a concrete reversible permutation simulation. This closes the frozen proposition `GeneralNominalCenteredCanonicalTransport.ReachablePermutationSimulation roles` without a new hypothesis. Consequently the canonical executor has literal CanonicalLocalOrder. Its V5 composition has twelve proved fields and exactly two remaining inputs: `evidenceNode` and `generatedChildren`.

The boundary, executor, Step, language decisions, and V5 statements are unchanged. All proof additions are in fourteen new `GeneralNominalCenteredPermutation…` modules.

## Exact top-level results

All names in this block are in namespace `Yulang.GeneralNominalCenteredPermutationSimulation`. Here `b` denotes `GeneralNominalCenteredAdministrativeLocal.boundary roles`, `e` denotes `GeneralNominalCenteredCanonicalExecutor.executor roles`, and `frontiers` denotes `GeneralNominalCenteredAdministrativeLocal.frontiers roles`.

```lean
reachable_permutation_simulation :
  GeneralNominalCenteredCanonicalTransport.ReachablePermutationSimulation roles

canonical_exit_lifting :
  GeneralNominalCenteredCanonicalExecutor.CanonicalExitLifting roles

canonicalLocalOrder :
  GeneralNominalCenteredCanonicalExecutor.CanonicalLocalOrder roles

bridges
  (evidenceNode : B4SkeletonV5.EvidenceNode b)
  (generatedChildren : B4SkeletonV5.GeneratedChildren b) :
  B4SkeletonV5.B4Bridges b e frontiers

composition
  (evidenceNode : B4SkeletonV5.EvidenceNode b)
  (generatedChildren : B4SkeletonV5.GeneratedChildren b) :
  B4TargetV5.Statement b e
```

The first theorem proves the existing quantifiers verbatim: every checked registry, every G′-reachable state and root with an empty packet journal, and a relation initially relating that state to itself with a full forward/backward Step simulation and fixed-target Local correspondence. It does not assume a simulation, exit lifting, confluence, installation completion, evidence production, or a common terminal choice.

The resulting order field is literal, for every demand and frontier, including unregistered demands:

```lean
∀ r r', b.Checked r → b.Checked r' → b.Reorders r r' →
  ∀ s root, B4TargetV5.Reachable b r root s →
    B4TargetV5.Reachable b r' root s → ∀ d f,
    B4TargetV3.Local b r (e.run r s root).1 d f ↔
      B4TargetV3.Local b r' (e.run r' s root).1 d f
```

## Concrete relation and table growth

The simulation uses the previous turn's finite packet table and `Corresponds`, strengthened by a reachable invariant:

```lean
Related first last left right :=
  GeneralNominalCenteredPermutationRepresentation.Corresponds first last left right ∧
  GeneralNominalCenteredCommitment.RecordedCommitted left ∧
  GeneralNominalCenteredCommitment.RecordedCommitted right
```

Each table entry rebases a historical packet's registry and declaration, then changes only the enumeration of allocated origins and reserved names, retaining their memberships. The paired observation core, source context, raw sites, edges, aliases, centered site membership, plan equations/tests, and legacy/centered trusted ledgers are retained by `Corresponds`.

Recorded commitment is necessary for extending a functional pairing table. An installation's novelty gives absence of its packet from the current journal on each side. Since every old table entry is recorded, the new pair cannot collide with either column of the old table. `Extension.table_coherent` proves this argument; `Extension.installed_related` and `Extension.installed_corresponds` extend the table by exactly the newly installed pair. This does not assume that arbitrary corresponding states are reachable. The stronger relation carries precisely the recorded-commitment property it needs, initializes it from `recorded_reachable`, and preserves it with `recorded_at`.

`Symmetry.rebased_symm` reverses registry/declaration rebasing and restores the original metadata enumeration. `Symmetry.corresponds_symm` reverses the entire table and its ledger pairings. The backward simulation is therefore the same constructor proof with reversed registries, rather than an additional choice or confluence assumption.

## Installation counterpart and guard transport

`Counterparts.counterpart` constructs a plan for every visible hypothetical plan over the current context. It keeps the input center site and raw packet site, uses the declaration paired by `DeclarationReorders`, and rebases the packet onto the counterpart's current context. Its `Match` certificate includes packet observations, input equality, declaration reordering, input/output/equation equivalence, exact located arguments, Prepared/HeadReady equivalence, inspected-length equality, and literal inspection-test equality.

This total hypothetical-plan construction matters for AlternativesSafe. The proof transports every hypothetical plan from the target back to the source; pairing only the plans already in the journal would not establish that universal guard.

| Component | New result and reason |
|---|---|
| Prepared / HeadReady | `Context.prepared`, `Context.head_ready`, and `Applicability.prepared`, `Applicability.head_ready`: report rebasing preserves branch models, located arguments, freshness membership, and materialization. Registry/declaration reordering then uses the existing candidate lemmas. |
| Both local-classifier guards | `Applicability.cycle_local`, `Applicability.feedback_local`, `Installable.cycle_order`, `Installable.feedback_order`: all five primitive observations transport, with literal selected keys and children. |
| ChoiceCompatible / merges | `Installable.choice`, `Installable.merges`, `Installable.feedback_merges`: historical declaration IDs, aliases, models, recovered inputs, and sites correspond. |
| Joint | `Applicability.joint` combined with `GeneralDictionaryJointReordering.joint`: the same model witnesses every branch in the alias class. No separately chosen model is substituted at an alias. |
| Trusted centered heads | `Safety.justified`, `Safety.ready`, `Guards.centered_decision`: paired trusted fact lists retain the same observations and pointwise model equivalence. Installation's context equality removes the current-context override. |
| Legacy/value support | `Guards.decision`, `Guards.choices`, and the existing `Related.supported`: the same dependency witness transports. Inspection reads cover every visible candidate. |
| Actual cycles / Safe | `Safety.cyclic`, `Safety.root_cycle`, `Counterparts.safe`: raw actual-origin recurrence and the centered recorded-test graph both transport. |
| AlternativesSafe / candidate cycle | `Observations.alternatives`, `Observations.candidate`: total counterpart construction handles all hypothetical current-context plans in both directions. |
| Full guards and novelty | `Installable.installable`, `InstallationGuard.packet_guard`, `InstallationGuard.counterpart_enabled`: complete eligibility and PacketGuard transport; model/child-edge correspondence transports commitment and therefore novelty. |

The table uses shortened namespaces `Context`, `Applicability`, etc. for `Yulang.GeneralNominalCenteredPermutationContext`, `Yulang.GeneralNominalCenteredPermutationApplicability`, and the analogous full module namespaces. The new audit file lists all 126 public declarations by their full names.

No guard reads declaration-list order. The existing emitter's choices remain literal because their predicates are extensionally equal; `Emission.child_origin`, `Emission.emitted`, and `Emission.rebased_emitted` prove that equality for metadata and registry rebasing.

## Installed states, other constructors, and observations

`Emission.rebased_private` proves the private contexts have the same observation core and metadata membership. The ordinary constraints are identical after report and declaration-head rebasing. Reservation/allocation enumeration may differ, as permitted by the relation.

Raw emitted sites and child edges are literal; centered emitted sites have the same membership. `Extension.support_alternatives` proves the entire finite support-alternative list is equal using the exact dependency pool and the guard equivalence for every support. Both input and output facts for every alternative are paired in `installed_related`. There is no loss of trusted-ledger information during installation.

Administrative, refresh, and merge constructors use the previous turn's transport. Their actions preserve recorded commitment. Installation now uses the newly constructed counterpart and table extension. The public `Simulation.step_forward`, `Simulation.step_backward`, and `Simulation.simulation` assemble the unrestricted relation with no compatibility restriction.

`Observations.local_iff` proves Local correspondence at one fixed registry with the same role declarations. It covers raw pending/K2/inspection/survivor observations, centered cycles, trusted DecisionGuard, registration, and both merge-closure predicates. `Simulation.observations` instantiates that result at the target registry as required by the frozen Simulation interface. It quantifies over all demands, without a registration or generation premise.

## Remaining fields and hypotheses

The twelve supplied fields are `progress`, `execution`, `halted`, `closure`, `stepModels`, `frontierLocal`, `localIdentity`, `whereAccessible`, `treeExecution`, `canonicalLocalOrder`, `dictionaryRefl`, and `initialReorders`. Existing results supply the previous eleven; this turn closes the order field for the same canonical executor.

The only undischarged inputs to `bridges` and `composition` are exactly:

```lean
B4SkeletonV5.EvidenceNode b
B4SkeletonV5.GeneratedChildren b
```

Expanded, `EvidenceNode b` requires:

```lean
∀ r, b.Checked r → ∀ s root, B4TargetV5.Reachable b r root s → ∀ model,
  b.Models s model → ∀ d key children dictionaries,
  (d = root ∨ b.Generated r s root d) → b.Stable r s d →
  (∀ child, child ∈ children → b.Stable r s child) →
  B4Target.SafeKnown b r s d → B4Target.Unique b r s d key children →
  CommonRoleOutermostResolver.All₂
    (fun child dictionary => b.Evidence r s model child dictionary) children dictionaries →
  b.Evidence r s model d (.node key dictionaries)
```

Expanded, `GeneratedChildren b` requires:

```lean
∀ r, b.Checked r → ∀ s root d key children,
  B4TargetV5.Reachable b r root s →
  (d = root ∨ b.Generated r s root d) → b.Stable r s d →
  B4Target.SafeKnown b r s d → B4Target.Unique b r s d key children →
  ∀ child, child ∈ children → b.Generated r s root child
```

There is no undischarged hypothesis on `reachable_permutation_simulation`, `canonical_exit_lifting`, or `canonicalLocalOrder` beyond their existing definitions' quantified premises. Supporting lemmas explicitly take correspondence, registry reordering, role equality, original eligibility/guard facts, or novelty as appropriate. Table extension additionally takes recorded entries and absence of each new packet. These are all constructed or derived within `step_forward` and the reachable initialization; none is an extra global assumption.

General selected-packet completion, dictionary evidence, and the trigger execution are outside this turn's proof. This is a conditional V5 composition, not a closed B4 Statement instance.

## Validation

All Lean commands below ran from `lean/` on the final proof candidate:

| Exact command | Exit code |
|---|---:|
| `lake build Yulang.GeneralNominalCenteredPermutationSimulation` | 0 |
| `lake build --wfail` | 0 |
| `lake build Yulang` | 0 |
| `lake env lean Audit/CenteredPermutationSimulation.lean` | 0 |

The target module imports all fourteen new modules, and `Yulang.lean` explicitly imports each of them. All 126 public declarations are audited. Their dependencies are confined to `propext`, `Classical.choice`, and `Quot.sound`. Intermediate elaboration failures were corrected before these final checks.

The requested prover role is unavailable in this environment; no prover agent ran. The primary constructed the proof. A complementary read-only guard audit identified the recorded-commitment invariant and found no order-sensitive guard. A separate independent review covers the final proof and its quantifiers.

The fresh independent review passed all fourteen modules, with no correctness or quantifier concern. It independently built `Yulang.GeneralNominalCenteredPermutationSimulation` and checked the three unconditional result types and the two-input composition; both checks exited 0. It confirmed the universal hypothetical-plan transport, both table-column freshness arguments, reverse rebasing, and Local agreement for every demand/frontier. The primary subsequently checked the root imports, new audit, design note, and strict append-only changes to the two permitted existing files. `git diff --check` exited 0. No owner question remains from registry-order dependence.
