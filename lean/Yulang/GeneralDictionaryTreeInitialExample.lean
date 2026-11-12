import Yulang.GeneralNominalTreeExample
import Yulang.GeneralNominalSupportBoundary

/-! The strictly nested binary-tree example is genuine initial-source data,
not merely an arbitrary raw source snapshot. No stable-state claim is made. -/
namespace Yulang.GeneralDictionaryTreeInitialExample
open GeneralNominalTreeExample
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveCandidates GeneralDictionaryRecursiveEvidence

abbrev start := GeneralNominalSupport.initial context root

theorem metadata : Metadata registry context := by
  refine ⟨rfl,?_⟩
  intro name base found
  cases found

theorem linked : GeneralNominalState.Linked state root.demand := by
  constructor
  · intro index
    constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
  · intro output member; cases member

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root where
  roles_agree := rfl
  metadata := metadata
  linked := linked
  intervals := fun _ _ _ => CommonNominalFullCarrier.subtype_refl _
  below_seed := by
    intro source member
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    rcases member with h | h | h | h | h | h | h | h | h | h <;> subst source <;> decide +kernel
  unallocated := rfl

theorem initial_models : GeneralNominalSaturationState.Models start.current model :=
  (GeneralNominalSaturationState.initial_models context root model).mpr state_models

theorem actual_reachable :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start :=
  ⟨start,⟨context,initial_source,rfl⟩,.refl⟩

theorem actual_instance : Instance registry context model root declaration.id [] :=
  GeneralDictionaryTreeLeaf.instance_of_shape context registry root declaration (List.mem_singleton_self _)
    checked shape metadata model state_models

theorem evidence : Evidence registry context model root (.node declaration.id []) :=
  (evidence_leaf_iff registry context model root declaration.id).mpr actual_instance

/-- Initial-source reachability, actual journal satisfiability, and same-model
source Evidence hold simultaneously. Stability is deliberately absent. -/
theorem reachable_inhabited_evidence :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start ∧
    GeneralNominalSaturationState.Models start.current model ∧
    Evidence registry start.current.context model root (.node declaration.id []) :=
  ⟨actual_reachable,initial_models,evidence⟩
end Yulang.GeneralDictionaryTreeInitialExample
