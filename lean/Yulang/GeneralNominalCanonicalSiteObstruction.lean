import Yulang.GeneralNominalReadbackCounterexample

/-! The frozen canonical site producer loses nonpoint provenance even when
ordinary constraints prove the two endpoints equivalent. The statement concerns
the current source interfaces, not a new language decision or an infinite trace. -/
namespace Yulang.GeneralNominalCanonicalSiteObstruction

open GeneralNominalDemandMerging GeneralNominalSaturationState
open GeneralSourceDictionaries (Occurrence)
open CommonNominalFullCarrier
open Core.PresenceGeneration (TyTerm)

variable {roles : Roles.RoleDecls}

theorem nonpoint_not_related (models : GeneralNominalCommonBridge.Assignment → Prop)
    (root : Occurrence roles) (index : Fin (roles root.demand.role).arity)
    (different : (root.demand.arguments index).1 ≠ (root.demand.arguments index).2) (other : Site roles) :
    ¬ SameInputs models (pointSite root) other := by
  apply unknown_input_prevents_merge
  apply List.mem_ofFn.mpr
  refine ⟨index,?_⟩
  simp [different]

theorem formed_site_not_related (registry : GeneralDeclarations.Registry) (state : State roles)
    (root : Occurrence roles) (formed : GeneralNominalSourceFormation.SourceFormed registry root state)
    (site : Site roles) (member : site ∈ state.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (different : (site.occurrence.demand.arguments index).1 ≠ (site.occurrence.demand.arguments index).2)
    (other : Site roles) : ¬ SameInputs (Models state) site other := by
  obtain ⟨_,_,_,_,canonical,_⟩ := GeneralNominalSourceFormation.formed_provenance state formed
  have same := canonical site member
  rw [same]
  exact nonpoint_not_related (Models state) site.occurrence index different other

abbrev registry := GeneralNominalReadbackCounterexample.registry
abbrev state := GeneralNominalState.extend GeneralNominalIntervalExamples.source []
  (GeneralNominalAllocation.equations 0 (.var 1))
abbrev context : GeneralNominalCandidates.Context := ⟨state,GeneralNominalExamples.interpretation⟩
abbrev root : Occurrence GeneralDeclarationExamples.roles :=
  ⟨100,⟨0,fun _ => (0,1),[],by intro _ member; cases member⟩⟩
abbrev model := GeneralNominalIntervalExamples.model .int .int

theorem equivalent_endpoints (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state assignment) : Equivalent (assignment 0).1 (assignment 1).1 :=
  (GeneralNominalCaptureMerges.equations_exact assignment 0 (.var 1)).mp
    ((GeneralNominalState.extend_models ..).mp valid).2

theorem state_models : GeneralNominalState.Models state model := by
  apply (GeneralNominalState.extend_models ..).mpr
  exact ⟨GeneralNominalIntervalExamples.source_models .int .int,
    (GeneralNominalCaptureMerges.equations_exact model 0 (.var 1)).mpr ⟨subtype_refl _,subtype_refl _⟩⟩

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root := by
  have ready := GeneralNominalReadbackCounterexample.prepared
  obtain ⟨metadata,_⟩ := ready
  refine ⟨rfl,metadata,?_,?_,?_,rfl⟩
  · constructor
    · intro index
      have member (slot : Fin state.base.slots) : state.base.source slot ∈ GeneralNominalState.sources state :=
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))
      exact ⟨member ⟨0,by decide +kernel⟩,member ⟨1,by decide +kernel⟩⟩
    · intro output member; cases member
  · intro assignment valid index
    exact (equivalent_endpoints assignment valid).1
  · intro identity member
    have bound := GeneralNominalAllocation.member_le_max (GeneralNominalState.sources state) identity member
    exact Nat.le_trans bound (by decide +kernel)

theorem formed : GeneralNominalSourceFormation.SourceFormed registry root (initial context root) :=
  .initial context initial_source

theorem known_inputs : GeneralNominalState.Known state 0 ∧ GeneralNominalState.Known state 1 :=
  ⟨⟨⟨0,by decide +kernel⟩,rfl,Or.inr ⟨GeneralNominalIntervalExamples.descriptor,rfl⟩⟩,
    ⟨⟨1,by decide +kernel⟩,rfl,Or.inr ⟨GeneralNominalIntervalExamples.descriptor,rfl⟩⟩⟩

theorem equal_known_input_still_unmergeable :
    GeneralDeclarations.Checked registry ∧
    GeneralNominalSourceFormation.SourceFormed registry root (initial context root) ∧
    (GeneralNominalState.Known state 0 ∧ GeneralNominalState.Known state 1) ∧
    (∃ assignment, Models (initial context root) assignment) ∧
    (∀ assignment, Models (initial context root) assignment → Equivalent (assignment 0).1 (assignment 1).1) ∧
    ¬ SameInputs (Models (initial context root)) (pointSite root) (pointSite root) := by
  refine ⟨GeneralNominalReadbackCounterexample.checked,formed,known_inputs,
    ⟨model,(initial_models context root model).mpr state_models⟩,?_,?_⟩
  · intro assignment valid
    exact equivalent_endpoints assignment ((initial_models context root assignment).mp valid)
  · exact nonpoint_not_related _ root ⟨0,by decide +kernel⟩ (by decide +kernel) _

end Yulang.GeneralNominalCanonicalSiteObstruction
