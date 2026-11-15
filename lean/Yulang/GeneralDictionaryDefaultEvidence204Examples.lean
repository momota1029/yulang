import Yulang.GeneralDictionaryDefaultEvidence204
import Yulang.GeneralDictionaryAllocDefaultCounterexample202

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryDefaultEvidence204Examples
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryDefaultEvidence204
open GeneralDictionaryAssociatedProvenance
open GeneralDictionaryAllocDefaultSource202
open GeneralDictionaryAllocDefaultCounterexample202
open CommonNominalFullCarrier

theorem default_output (assignment : GeneralNominalCommonBridge.Assignment) :
    OutputWitness plan assignment ⟨0,1⟩ := by
  refine ⟨.default 0 0 (.var 0),.default _ (by intro equation member; cases member) rfl,⟨.variable 0,rfl⟩,?_⟩
  exact (GeneralNominalCenteredHeadMatEffects.positional_default plan assignment (0 : Fin 1)).mpr
    ⟨subtype_refl _,subtype_refl _⟩

theorem generated_empty : generated registry context root declaration declaration_checked [(1,1)] = {} := by
  unfold generated
  rw [GeneralNominalFiniteAssociatedFacts.terminal_requests context.state registry root declaration declaration_checked _ rfl]
  simp [GeneralNominalMaterialization.rootRequests,GeneralNominalMaterialization.generated]

theorem legacy_branch (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models snapshot assignment) :
    BranchModels registry context root declaration declaration_checked [(1,1)] assignment := by
  refine ⟨(head_model_any assignment valid).1,(head_model_any assignment valid).2,?_⟩
  rw [generated_empty]
  exact GeneralNominalMaterialization.empty_models _ _ _ _ _

/-- The closed cycle202 witness has a genuine default-aware source certificate
in every source model. No selection, stability or hypothetical node rule is used. -/
theorem default_certificate (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models snapshot assignment) :
    Certificate registry start.core assignment root 37 [] plan where
  registry_eq := rfl
  context_eq := rfl
  root_eq := rfl
  key_eq := rfl
  visible := List.mem_singleton_self _
  role_eq := rfl
  located := rfl
  finished := by rw [report_exact]; exact ⟨rfl,rfl,rfl⟩
  generated_ready := by
    change (generated registry context root declaration declaration_checked [(1,1)]).unknown = false
    rw [generated_empty]
  children_eq := children_empty.symm
  metadata := source.metadata
  branch := legacy_branch assignment valid
  center_recorded := List.mem_singleton_self _
  center_holds := point_root_holds _ _ (fun _ => rfl) _
  outputs := by
    intro output member
    cases List.mem_singleton.mp member
    exact default_output assignment

theorem default_leaf : Evidence registry start.core model root (.node 37 []) :=
  evidence_leaf_iff.mpr ⟨plan,default_certificate model source_model⟩

/-- A default leaf coexists with the old refutation: the replacement changes
its explicit-only coverage guard, not the actual source or model. -/
theorem old_rejects_new_accepts :
    ¬ GeneralDictionaryRecursiveEvidence.Evidence registry context model root (.node 37 []) ∧
    Evidence registry start.core model root (.node 37 []) :=
  ⟨no_evidence,default_leaf⟩

end Yulang.GeneralDictionaryDefaultEvidence204Examples
