import Yulang.GeneralVersionedProspectiveFootprint314

set_option backward.isDefEq.respectTransparency false
/-! Full same-model installation at every genuinely new numerical owner,
even in a history-bearing, reobserved or merged state. -/
namespace Yulang.GeneralVersionedNewOwnerInstall314
open GeneralNominalCenters GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralVersionedUnseenBinder313 (Unseen)
open GeneralVersionedProspectiveNames314 (Read ReadTag excludes)
open GeneralVersionedFirstComputed313 (Compatible proper_keys)
open GeneralVersionedFirstInternal313 (taut_reads)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedComputedRows313 (OutputCell KeyCoherent classifies addresses_disjoint row_present)
open GeneralVersionedCompoundRows313 (Cell coherent_address address)
open GeneralVersionedRootWrites312 (inner internalRows)
open GeneralVersionedJointWrites312 (protect rhs)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds)
open GeneralNominalCommonBridge (Assignment)
open GeneralFiniteTypedWrites312 (reflexive symmetric transitive)
open CommonNominalFullCarrier (Equivalent)


theorem taut_protected {s : State roles} {e : Effect roles}
    {q : GeneralNominalCenteredHeadMatSchemas.Equation}
    (listed : q ∈ inner e.plan) (taut : GeneralVersionedCompoundRows313.Taut e.plan q) :
    q.target ∈ protect s e (sources s) := by
  have all : q ∈ GeneralVersionedJointWrites312.equations e.plan := by
    rw [GeneralVersionedRootWrites312.separates]
    exact List.mem_append_right _ listed
  have read : q.target ∈ (GeneralVersionedJointWrites312.equations e.plan).flatMap
      (GeneralVersionedJointWrites312.inputNames e.plan) :=
    List.mem_flatMap.mpr ⟨q,all,taut_reads e.plan q taut⟩
  simp [protect,read]

theorem cell_free {s : State roles} {e : Effect roles}
    (actual : Reachable registry root s) (unseen : Unseen s e.plan)
    (frame : Frame compiled s.core focus key e.plan) {q : GeneralNominalCenteredHeadMatSchemas.Equation}
    (cell : Cell e.plan q) :
    q.target ∉ protect s e (sources s) := by
  obtain ⟨clause,_,pos,kind,pat,which,_,_,target,_⟩ := cell
  intro present
  have safe := GeneralVersionedProspectiveFootprint314.all actual frame _ present
  rw [target] at safe
  apply excludes frame.context_eq unseen _ clause.id pos safe
  rcases which with rfl|rfl|rfl <;> simp [ReadTag]

theorem output_free {s : State roles} {e : Effect roles}
    (actual : Reachable registry root s) (unseen : Unseen s e.plan)
    (frame : Frame compiled s.core focus key e.plan) {q : GeneralNominalCenteredHeadMatSchemas.Equation}
    (cell : OutputCell e.plan q) :
    q.target ∉ protect s e (sources s) := by
  obtain ⟨_,_,rule,_,_,_,target,_⟩ := cell
  intro present
  have safe := GeneralVersionedProspectiveFootprint314.all actual frame _ present
  rw [target] at safe
  exact excludes frame.context_eq unseen (by simp [ReadTag]) rule.id 0 safe

theorem table {s : State roles} {e : Effect roles}
    (actual : Reachable registry root s) (unseen : Unseen s e.plan)
    (frame : Frame (Compiled registry) s.core focus key e.plan) (m : Assignment)
    (outputs : Compatible e.plan m) :
    GeneralVersionedRootWrites312.FreeCoherent (internalRows e.plan m) (protect s e (sources s)) ∧
    GeneralFiniteTypedWrites312.Protected (internalRows e.plan m) (protect s e (sources s)) m := by
  constructor
  · intro a aMem b bMem same free
    obtain ⟨one,ho,rfl⟩ := List.mem_map.mp aMem
    obtain ⟨two,ht,rfl⟩ := List.mem_map.mp bMem
    have fromOne := (classifies e.plan _ ho).resolve_left (fun taut => free (taut_protected ho taut))
    have fromTwo := (classifies e.plan _ ht).resolve_left (fun taut => free (same.symm ▸ taut_protected ht taut))
    rcases fromOne with first|first <;> rcases fromTwo with last|last
    · rw [coherent_address first last same]
      exact reflexive _
    · exact False.elim (addresses_disjoint first last same)
    · exact False.elim (addresses_disjoint last first same.symm)
    · exact outputs _ _ first last same
  · intro row present protectedName
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp present
    rcases classifies e.plan q hq with taut|cell|cell
    · exact taut m
    · exact False.elim (cell_free actual unseen frame cell protectedName)
    · exact False.elim (output_free actual unseen frame cell protectedName)


theorem joint {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (unseen : Unseen s e.plan)
    (pick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id children))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (inhabited : ∃ m, Models s m) : ∃ m, Residual s e m := by
  have frame : Frame (Compiled registry) s.core e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan :=
    registryEq ▸ snapshot ▸ e.frame
  have visible := registryEq ▸ e.frame.visible
  have keys := GeneralVersionedCompiledFirstInstall313.key_coherence checked.2 visible
  apply GeneralVersionedSelectedJointWrites312.joint_from_internal checked actual pick registryEq snapshot
    (GeneralNominalVersionedModelSupport237.current s) (GeneralNominalVersionedTraceSiteSupport237.current s)
    (GeneralVersionedProspectiveFootprint314.aggregate_class_free actual frame unseen)
    (GeneralVersionedNewOwnerHead314.head checked actual pick frame unseen inhabited)
  intro m _ _ _ _
  exact table actual unseen frame m (proper_keys e.plan keys m)

theorem installable {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (unseen : Unseen s e.plan)
    (pick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id children))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (inhabited : ∃ m, Models s m) :
    GeneralNominalVersionedMixedKernel234.Installable (Compiled registry) s e :=
  (GeneralNominalVersionedMixedMaterialization237.source_installable_iff checked actual pick registryEq snapshot).mpr
    ⟨GeneralVersionedNewOwnerHead314.choice checked actual pick unseen inhabited,
      joint checked actual unseen pick registryEq snapshot inhabited⟩

theorem node_and_edges {s : State roles} {root focus : Occurrence roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (unseen : ∀ prior ∈ s.plans, prior.packet.site.occurrence.identity ≠ focus.identity)
    (picked : Local registry s focus (.selected key kids))
    (stable : (boundary roles).Stable registry s focus)
    (reached : focus = root ∨ GeneralNominalSaturationState.Generated s.core.erased.current root focus)
    (valid : Models s m)
    (ordered : CommonRoleOutermostResolver.All₂
      (GeneralNominalVersionedEvidence231.Evidence (Compiled registry) s.core m) kids dictionaries) :
    GeneralNominalVersionedEvidence231.Evidence (Compiled registry) s.core m focus (.node key dictionaries) ∧
    ∀ child ∈ kids, GeneralNominalSaturationState.Generated s.core.erased.current root child := by
  obtain ⟨e,g,snapshot,o,k,c⟩ := GeneralNominalVersionedMixedSelectedEffect235.source_effect checked actual picked
  have exactPick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids) := by
    rw [o,k]
    exact picked
  have owner : Unseen s e.plan := by unfold Unseen; rw [o]; exact unseen
  have enabled := installable checked actual owner exactPick g snapshot ⟨m,valid⟩
  have mixed := GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp picked
  exact ⟨GeneralNominalVersionedMixedStableEvidence235.selected_node stable enabled o mixed valid ordered,
    fun _ h => GeneralNominalVersionedMixedStableEvidence235.selected_generated_children stable enabled o mixed reached h⟩

end Yulang.GeneralVersionedNewOwnerInstall314
