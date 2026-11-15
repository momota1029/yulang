import Yulang.GeneralNominalSelectedJournal194
import Yulang.GeneralNominalNonleafStable194

/-! A local recorded-node rule and a concrete reason stable closure alone does
not establish total journal coverage. No change to WF or reuse semantics. -/
namespace Yulang.GeneralNominalRecordedNode194
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}
variable {context : GeneralNominalCandidates.Context} {state : State roles}

/-- Actual ordinary history, one root packet, current Local selection and
same-model child evidence suffice. No whole-tree coverage premise is needed. -/
theorem evidence_node
    (path : B4Target.Steps (GeneralNominalOrdinaryEvidence191.OrdinaryStep registry root)
      (initial context root) state)
    (recorded : ∃ packet ∈ state.core.erased.current.packets, packet.site.occurrence = focus)
    {key : Nat} {children : List (Occurrence roles)}
    (selected : Local registry state focus (.selected key children))
    (model : Assignment) (valid : Models state model) (payloads : List Payload)
    (childEvidence : All₂ ((boundary roles).Evidence registry state model) children payloads) :
    (boundary roles).Evidence registry state model focus (.node key payloads) := by
  obtain ⟨packet,present,same⟩ := recorded
  have source := GeneralNominalOrdinaryJournal194.packet_instance path packet present model valid
  rw [same] at source
  exact GeneralDictionaryRecursiveEvidence.evidence_node registry _ model focus key children payloads
    (GeneralNominalSelectedJournal194.selected_instance selected model source).2.2 childEvidence

open GeneralNominalNonleafPlan193 GeneralNominalNonleafInstallation193 GeneralNominalNonleafAdministrative193
open GeneralNominalExamples (displayRoot displayChild)

theorem child_packet_missing :
    ∀ item ∈ finish.core.erased.current.packets, item.site.occurrence ≠ displayChild := by
  intro item member
  change item ∈ [packet] at member
  have same := List.mem_singleton.mp member
  subst item
  intro equal
  have member : displayChild ∈ packet.children := by
    change displayChild ∈ plan.packet.children
    rw [children_exact]; simp
  have above := GeneralNominalCenteredWhere.packet_child_above packet displayChild member
  rw [equal] at above
  exact Nat.lt_irrefl _ above

theorem child_reached : GeneralDictionaryJournalTree.Reach finish.core.erased.current displayRoot displayChild := by
  apply GeneralDictionaryJournalTree.Reach.child .root
  refine ⟨packet,?_,rfl,?_⟩
  · change packet ∈ [packet]; simp
  · change displayChild ∈ plan.packet.children
    rw [children_exact]; simp

theorem not_covered : ¬ GeneralDictionaryJournalTree.Covered finish.core.erased.current displayRoot :=
  GeneralDictionaryJournalTree.missing_packet _ _ _ child_reached child_packet_missing

/-- Stable with a correct selected dictionary still need not record every reused
child. This is a coverage counterexample, not semantic unsoundness. -/
theorem stable_not_covered :
    (GeneralNominalCenteredHeadWFBoundary.boundary GeneralDeclarationExamples.roles).Stable
      GeneralNominalExamples.registry finish displayRoot ∧
    ¬ GeneralDictionaryJournalTree.Covered finish.core.erased.current displayRoot :=
  ⟨GeneralNominalNonleafStable194.stable,not_covered⟩
end Yulang.GeneralNominalRecordedNode194
