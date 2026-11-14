import Yulang.GeneralDictionaryMatGuardWitness199

set_option backward.isDefEq.respectTransparency false

/-! The obstruction's initial state is genuinely nonstable: the complete total
packet can be installed by the actual Mat transition. Thus the previous theorem
cannot be passed off as an EvidenceNode counterexample. -/
namespace Yulang.GeneralDictionaryMatGuardTrace199
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadWFJoinSource hiding start reachable inhabited initial_source
open GeneralDictionaryMatGuardObstruction199
open GeneralNominalCenteredHeadMatStepKernel

theorem positions : GeneralNominalCenteredHeadMatStepCycles.Safe start plan := by
  constructor
  · unfold GeneralNominalCenteredSteps.inspection
    rw [query]
    simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
      GeneralNominalRecursiveInspection.Report.append,GeneralNominalRecursiveInspection.Report.visit,
      Site.observed,rootSite,List.ofFn_succ]
  · intro entry member
    rw [inspection_exact] at member
    cases List.mem_singleton.mp member
    exact scalar_acyclic

theorem alternatives : AlternativesSafe registry start plan.input := by
  intro candidate _ framed
  have frame' : GeneralNominalCenteredHeadOutputs.Frame registry start.core root
      candidate.packet.declaration.id candidate := by
    exact framed
  rw [frame_plan frame']
  exact positions

theorem installable : Installable registry start effect := by
  refine ⟨rfl,rfl,safe,GeneralNominalCenteredHeadMatStepObservations.initial_cache context root,
    total_complete,?_,positions,alternatives,?_⟩
  · intro prior member; cases member
  · obtain ⟨assignment,models⟩ := GeneralNominalCenteredHeadMatStepRows.installed_journal_inhabited
    exact ⟨assignment,(GeneralNominalCenteredHeadMatStepJournal.install_models
      (effect := effect) rfl).mp models⟩

theorem children_nonempty : children ≠ [] := by
  have length : children.length = 1 := by
    change packet.children.length = 1
    unfold GeneralNominalSaturationState.Packet.children GeneralNominalAllocation.children
      GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
    simp only [canonical_declaration]
    simp [GeneralDeclarationDemands.emitAll]
  intro empty
  rw [empty] at length
  cases length

theorem not_committed : ¬ Committed start plan := by
  intro committed
  obtain ⟨child,member⟩ := List.exists_mem_of_ne_nil children children_nonempty
  exact List.not_mem_nil (committed.2 child member)

theorem install_step : (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Step registry root start
    (GeneralNominalCenteredHeadMatStepJournal.install start effect) :=
  ⟨root,.root,.install effect installable not_committed⟩

theorem not_stable : ¬ (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Stable registry start root := by
  intro stable
  exact stable root (.root) _ (.install effect installable not_committed)

/-- The reused fixture has only the parent declaration. Its emitted role-1
child has no source implementation; this also prevents the All₂ premise. -/
theorem child_role (child : Occurrence roles) (member : child ∈ children) : child.demand.role = 1 := by
  obtain ⟨clause,present,signature,rfl⟩ := GeneralNominalPatersonLineage.emitted_clause packet child member
  cases List.mem_singleton.mp present
  rfl

theorem no_child_evidence (assignment : GeneralNominalCommonBridge.Assignment)
    (child : Occurrence roles) (member : child ∈ children)
    (dictionary : CommonRoleOutermostResolver.Dictionary) :
    ¬ (GeneralNominalCenteredHeadMatStepBoundary.boundary roles).Evidence registry start assignment child dictionary := by
  cases dictionary with
  | node key dictionaries =>
    intro evidence
    obtain ⟨kids,instanceRule,_⟩ := GeneralDictionaryRecursiveEvidence.evidence_node_elim
      registry context assignment child key dictionaries evidence
    obtain ⟨decl,visible,_,_,role,_⟩ := instanceRule
    cases List.mem_singleton.mp visible
    have impossible : (0 : Nat) = 1 := role.trans (child_role child member)
    cases impossible

end Yulang.GeneralDictionaryMatGuardTrace199
