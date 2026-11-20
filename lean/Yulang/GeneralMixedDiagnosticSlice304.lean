import Yulang.GeneralDeferredLadderAdministrative304

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedDiagnosticSlice304
open GeneralDeferredLadderResnapshot304 (HeadView)
open GeneralDeferredLadderOperationalView304 (alias_forward)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMergedConflict232 (HistoryModels ClassEquations ContextModels MergedOutputConflict)
open GeneralNominalVersionedMergedConflict232.Old (MergedClass ContextPresent Registered)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceDictionaries (Occurrence)

variable {roles : Roles.RoleDecls} {a b : State roles}

/-- Class equations are observed only on models of the archived history
before imposing arbitrary combinations of live output equations. -/
structure Semantics (a b : State roles) : Prop where
  history : ∀ m, HistoryModels a m ↔ HistoryModels b m
  class_on_history : ∀ o m, HistoryModels a m → (ClassEquations a o m ↔ ClassEquations b o m)

theorem Semantics.symm (ab : Semantics a b) : Semantics b a :=
  ⟨fun m => (ab.history m).symm,
    fun o m hm => (ab.class_on_history o m ((ab.history m).mpr hm)).symm⟩

theorem merged_forward (head : HeadView a b) (given : MergedClass a.legacy focus) :
    MergedClass b.legacy focus := by
  obtain ⟨i,j,listed,distinct,withFirst⟩ := given
  exact ⟨i,j,head.raw.aliases ▸ listed,distinct,alias_forward head.raw withFirst⟩

theorem registered_forward (head : HeadView a b) (given : Registered a.legacy focus) :
    Registered b.legacy focus := by
  obtain ⟨row,listed,eq⟩ := given
  exact ⟨row,head.raw.sites ▸ listed,eq⟩

theorem context_forward (head : HeadView a b) (given : ContextPresent a.legacy atoms classes) :
    ContextPresent b.legacy atoms classes := by
  constructor
  · have subset := given.1
    change atoms ⊆ a.core.erased.current.context.state.ordinary at subset
    rw [head.context] at subset
    exact subset
  · exact fun o member => registered_forward head (given.2 o member)

theorem context_models_forward (sem : Semantics a b) (given : ContextModels a atoms classes m) :
    ContextModels b atoms classes m :=
  ⟨(sem.history m).mp given.1,given.2.1,fun o member =>
    (sem.class_on_history o m given.1).mp (given.2.2 o member)⟩

theorem conflict_forward (head : HeadView a b) (sem : Semantics a b)
    (given : MergedOutputConflict a focus) : MergedOutputConflict b focus := by
  obtain ⟨merged,atoms,classes,present,⟨m,possible⟩,impossible⟩ := given
  refine ⟨merged_forward head merged,atoms,classes,context_forward head present,
    ⟨m,context_models_forward sem possible⟩,?_⟩
  rintro ⟨m,possible,eq⟩
  have back := context_models_forward sem.symm possible
  exact impossible ⟨m,back,(sem.class_on_history focus m back.1).mpr eq⟩

theorem conflict_iff (head : HeadView a b) (sem : Semantics a b) (focus : Occurrence roles) :
    MergedOutputConflict a focus ↔ MergedOutputConflict b focus :=
  ⟨conflict_forward head sem,conflict_forward head.symm sem.symm⟩

end Yulang.GeneralMixedDiagnosticSlice304
