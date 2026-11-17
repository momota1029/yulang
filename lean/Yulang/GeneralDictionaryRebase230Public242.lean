import Yulang.GeneralDictionaryRebase230Private241
import Yulang.GeneralNominalRebasePublicModel242
import Yulang.GeneralNominalRebaseEscapedMerges242
namespace Yulang.GeneralDictionaryRebase230Public242
open GeneralNominalAllocation
open GeneralDictionaryJournalRefinement228Source (snapshot root)
open GeneralDictionaryOptionalInitial229 (registry declaration)
open GeneralDictionaryOptionalInstall229 (model lo hi)
open GeneralDictionaryRebase230Private241
open GeneralNominalRebaseDefinitions241 (entries Fresh)
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalRebaseEscapedReplace242
open GeneralNominalRebaseEscapedMerges242
open GeneralNominalRebasePublicModel242
open GeneralNominalCommonBridge (Assignment)

def hidden : List Nat := [lo,hi]
abbrev oldEntries := entries snapshot.seed root.identity declaration.id oldBindings declaration.inputNames
abbrev newEntries := entries snapshot.seed root.identity declaration.id newBindings declaration.inputNames

theorem old_fresh : Fresh snapshot.seed root.identity declaration.id oldBindings declaration.inputNames pool := by
 intro name named _
 have eq := named_zero named
 subst name
 exact isolated 0 named (by decide)

theorem old_linked : GeneralNominalAllocationSupport.Endpoints oldBindings pool := by
 intro binding member
 rcases List.mem_cons.mp member with rfl | member
 · exact ⟨by simp [pool],by simp [pool]⟩
 · cases List.mem_singleton.mp member
   exact ⟨by simp [pool],by simp [pool]⟩

theorem multiplicity : ∀ name ∈ declaration.inputNames, (occurrences newBindings name).length ≠ 1 →
 (occurrences oldBindings name).length ≠ 1 := by
 intro name named _
 have eq := named_zero named
 subst name
 decide

theorem targets_hidden : ∀ entry ∈ oldEntries, entry.1 ∈ hidden := by
 intro entry member
 obtain ⟨name,named,_,equal⟩ := (GeneralNominalRebaseDefinitions241.member_iff snapshot.seed root.identity declaration.id oldBindings declaration.inputNames).mp member
 have eq := named_zero named
 subst name
 rcases equal with rfl | rfl
 · change lo ∈ [lo,hi]
   simp
 · change hi ∈ [lo,hi]
   simp

def retained (internal : Assignment) : Prop :=
 GeneralNominalState.Models snapshot internal ∧ PresenceNormalForm.All CommonNominalFullCarrier.model internal publicAtoms

def oldModels (publicModel : Assignment) : Prop :=
 Models hidden (fun internal => Definitions oldEntries internal ∧ retained internal) publicModel

def newModels (publicModel : Assignment) : Prop :=
 Models hidden (fun internal => Definitions newEntries internal ∧ retained (GeneralNominalFiniteEquationRealization236.patch oldEntries internal)) publicModel

theorem public_models_iff (publicModel : Assignment) : oldModels publicModel ↔ newModels publicModel :=
 replacement_models_iff oldEntries newEntries
   (GeneralNominalRebaseDefinitions241.coherent snapshot.seed root.identity declaration.id oldBindings declaration.inputNames) (external_entries _ _ _ _ _ old_fresh old_linked)
   (GeneralNominalRebaseDefinitions241.coherent snapshot.seed root.identity declaration.id newBindings declaration.inputNames) (external_entries _ _ _ _ _ isolated linked)
   (targets_within _ _ _ _ _ _ multiplicity) targets_hidden retained
   (GeneralNominalRebaseRawProjection242.raw_atoms_congruent snapshot publicAtoms) publicModel

theorem old_definitions : Definitions oldEntries model := by
 apply (GeneralNominalRebaseEscapedStore242.definitions_iff oldEntries model).mp
 rw [definition_block_eq snapshot registry root.identity declaration oldBindings]
 exact old_merges

theorem initial_public : oldModels model :=
 ⟨model,⟨fun _ _ => rfl,fun _ => rfl⟩,old_definitions,GeneralDictionaryOptionalInstall229.source_model,old_public⟩

theorem replaced_public : newModels model := (public_models_iff model).mp initial_public

theorem same_public : oldModels model ∧ newModels model := ⟨initial_public,replaced_public⟩
end Yulang.GeneralDictionaryRebase230Public242
