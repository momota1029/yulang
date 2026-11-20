import Yulang.GeneralMixedIndexedDiagnosticHeads305
import Yulang.GeneralMixedDiagnosticSlice304

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedIndexedDiagnosticOutputs305
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedDiagnostic232 (ChosenHead ChosenEffects OutputConflict Feasible AtKey SharingConflict)
open GeneralMixedIndexedFrame305
open GeneralMixedIndexedPlanSemantics305
open GeneralMixedIndexedDiagnosticHeads305 (safe_iff unique_iff)
open GeneralMixedDiagnosticSlice304 (Semantics context_models_forward)
open GeneralNominalVersionedMergedConflict232 (MergedOutputConflict)
open GeneralNominalVersionedMergedConflict232.Old (MergedClass ContextPresent)
open GeneralDeferredLadderOperationalView304 (alias_forward)
variable {roles : Roles.RoleDecls} {a b : State roles}

theorem chosen_head_forward (rel : IndexedView a b) (old : ChosenHead r a root key m) :
    ChosenHead r b root key m := by
  obtain ⟨⟨children,choice⟩,p,f,ready,head⟩ := old
  have same := relocated_same rel f
  exact ⟨⟨children,(unique_iff rel r root key children).mp choice⟩,relocate rel f,
    relocated_frame rel f,ready_forward rel.raw same ready,(head_same same m).mp head⟩

theorem chosen_effect_forward (rel : IndexedView a b) (old : ChosenEffects r a root key m) :
    ChosenEffects r b root key m := by
  obtain ⟨⟨children,choice⟩,p,f,ready,head,output⟩ := old
  have same := relocated_same rel f
  exact ⟨⟨children,(unique_iff rel r root key children).mp choice⟩,relocate rel f,
    relocated_frame rel f,ready_forward rel.raw same ready,(head_same same m).mp head,
    classes_forward rel.raw same m output⟩

theorem output_forward (rel : IndexedView a b) (old : OutputConflict r a root key) :
    OutputConflict r b root key := by
  obtain ⟨⟨m,valid,head⟩,no⟩ := old
  refine ⟨⟨m,(rel.raw.models m).mp valid,chosen_head_forward rel head⟩,?_⟩
  rintro ⟨m,valid,after⟩
  exact no ⟨m,(rel.raw.models m).mpr valid,chosen_effect_forward (reverse rel) after⟩

theorem output_iff (rel : IndexedView a b) (r : Registry) (root : Occurrence roles) (key : Nat) :
    OutputConflict r a root key ↔ OutputConflict r b root key :=
  ⟨output_forward rel,output_forward (reverse rel)⟩

theorem feasible_forward (rel : IndexedView a b) (old : Feasible r a root key) :
    Feasible r b root key := by
  obtain ⟨m,valid,p,f,shared⟩ := old
  exact ⟨m,(rel.raw.models m).mp valid,relocate rel f,relocated_frame rel f,
    (sharing_same (relocated_same rel f) m).mp shared⟩

theorem at_key_forward (rel : IndexedView a b) (old : AtKey r a root key) :
    AtKey r b root key := by
  obtain ⟨⟨m,valid⟩,⟨p,f⟩,no⟩ := old
  exact ⟨⟨m,(rel.raw.models m).mp valid⟩,⟨relocate rel f,relocated_frame rel f⟩,
    fun found => no (feasible_forward (reverse rel) found)⟩

theorem sharing_forward (rel : IndexedView a b) (old : SharingConflict r a root) :
    SharingConflict r b root := by
  obtain ⟨key,cs,unique,safe,failed⟩ := old
  exact ⟨key,cs,(unique_iff rel r root key cs).mp unique,(safe_iff rel r root).mp safe,
    at_key_forward rel failed⟩

theorem sharing_iff (rel : IndexedView a b) (r : Registry) (root : Occurrence roles) :
    SharingConflict r a root ↔ SharingConflict r b root :=
  ⟨sharing_forward rel,sharing_forward (reverse rel)⟩

theorem present_forward (rel : IndexedView a b) (given : ContextPresent a.legacy atoms classes) :
    ContextPresent b.legacy atoms classes := by
  constructor
  · intro atom member
    exact rel.ctx.forward.ordinary atom (given.1 member)
  · intro o member
    obtain ⟨site,listed,like⟩ := given.2 o member
    exact ⟨site,rel.raw.sites ▸ listed,like⟩

theorem merged_class_forward (rel : IndexedView a b) (given : MergedClass a.legacy root) :
    MergedClass b.legacy root := by
  obtain ⟨first,last,listed,distinct,linked⟩ := given
  exact ⟨first,last,rel.raw.aliases ▸ listed,distinct,alias_forward rel.raw linked⟩

theorem merged_forward (rel : IndexedView a b) (slices : Semantics a b)
    (given : MergedOutputConflict a root) : MergedOutputConflict b root := by
  obtain ⟨merged,atoms,classes,present,⟨m,possible⟩,impossible⟩ := given
  refine ⟨merged_class_forward rel merged,atoms,classes,present_forward rel present,
    ⟨m,context_models_forward slices possible⟩,?_⟩
  rintro ⟨m,possible,eq⟩
  have back := context_models_forward slices.symm possible
  exact impossible ⟨m,back,(slices.class_on_history root m back.1).mpr eq⟩

theorem merged_iff (rel : IndexedView a b) (slices : Semantics a b) (root : Occurrence roles) :
    MergedOutputConflict a root ↔ MergedOutputConflict b root :=
  ⟨merged_forward rel slices,merged_forward (reverse rel) slices.symm⟩

end Yulang.GeneralMixedIndexedDiagnosticOutputs305
