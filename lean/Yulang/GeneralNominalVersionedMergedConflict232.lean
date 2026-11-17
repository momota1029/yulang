import Yulang.GeneralNominalVersionedJournal232
import Yulang.GeneralNominalCenteredHeadAllocMergedConflict
set_option backward.isDefEq.respectTransparency false
/-! The existing feasible-history-slice conflict, extended to every recorded
versioned plan/effect. Legacy-only lifts recover the old predicate exactly. -/
namespace Yulang.GeneralNominalVersionedMergedConflict232
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Alias)
namespace Old
abbrev HistoryModels := @GeneralNominalCenteredHeadAllocMergedConflict.HistoryModels
abbrev ClassEquations := @GeneralNominalCenteredHeadAllocMergedConflict.ClassEquations
abbrev MergedClass := @GeneralNominalCenteredHeadAllocMergedConflict.MergedClass
abbrev Registered := @GeneralNominalCenteredHeadAllocMergedConflict.Registered
abbrev ContextPresent := @GeneralNominalCenteredHeadAllocMergedConflict.ContextPresent
end Old

def HistoryModels (state : State roles) (model : Assignment) : Prop :=
  Old.HistoryModels state.legacy model ∧
    (∀ plan ∈ state.plans, GeneralNominalVersionedPlans231.Holds plan model) ∧
    ∀ effect ∈ state.effects, effect.Holds model

def ClassEquations (state : State roles) (focus : Occurrence roles) (model : Assignment) : Prop :=
  Old.ClassEquations state.legacy focus model ∧
    ∀ effect ∈ state.effects, Alias state.core.erased.current focus.identity effect.plan.packet.site.occurrence.identity →
      effect.Live state.core model

def ContextModels (state : State roles) (atoms : List (PresenceNormalForm.Atom Nat))
    (classes : List (Occurrence roles)) (model : Assignment) : Prop :=
  HistoryModels state model ∧ PresenceNormalForm.All CommonNominalFullCarrier.model model atoms ∧
    ∀ focus ∈ classes, ClassEquations state focus model

def MergedOutputConflict (state : State roles) (focus : Occurrence roles) : Prop :=
  Old.MergedClass state.legacy focus ∧ ∃ atoms classes, Old.ContextPresent state.legacy atoms classes ∧
    (∃ model, ContextModels state atoms classes model) ∧
    ¬ ∃ model, ContextModels state atoms classes model ∧ ClassEquations state focus model

theorem models_history (valid : Models state model) : HistoryModels state model :=
  ⟨GeneralNominalCenteredHeadAllocMergedConflict.models_history valid.1,
    valid.2.1,fun effect member => (valid.2.2 effect member).1⟩

theorem class_of_models (valid : Models state model)
    (equal : GeneralNominalCenteredHeadOutputs.EqualOutputs state.core focus model) :
    ClassEquations state focus model :=
  ⟨⟨equal,fun effect member _ => (valid.1.2.2.2.2.2 effect member).2⟩,
    fun effect member _ => (valid.2.2 effect member).2⟩

theorem history_lift (legacy : Legacy.State roles) (model : Assignment) :
    HistoryModels (lift legacy) model ↔ Old.HistoryModels legacy model := by
  simp [HistoryModels,lift]

theorem class_lift (legacy : Legacy.State roles) (focus : Occurrence roles) (model : Assignment) :
    ClassEquations (lift legacy) focus model ↔ Old.ClassEquations legacy focus model := by
  simp [ClassEquations,lift]

theorem context_lift (legacy : Legacy.State roles) (atoms classes) (model : Assignment) :
    ContextModels (lift legacy) atoms classes model ↔
      GeneralNominalCenteredHeadAllocMergedConflict.ContextModels legacy atoms classes model := by
  simp only [ContextModels,GeneralNominalCenteredHeadAllocMergedConflict.ContextModels,history_lift,class_lift]

theorem conflict_lift (legacy : Legacy.State roles) (focus : Occurrence roles) :
    MergedOutputConflict (lift legacy) focus ↔
      GeneralNominalCenteredHeadAllocMergedConflict.MergedOutputConflict legacy focus := by
  simp only [MergedOutputConflict,GeneralNominalCenteredHeadAllocMergedConflict.MergedOutputConflict,context_lift,class_lift]
  rfl

theorem conflict_inhabited (bad : MergedOutputConflict state focus) : ∃ model, HistoryModels state model := by
  obtain ⟨_,_,_,_,⟨model,valid⟩,_⟩ := bad
  exact ⟨model,valid.1⟩

theorem models_exclude_conflict (valid : Models state model)
    (classes : ∀ focus, Old.Registered state.legacy focus →
      GeneralNominalCenteredHeadOutputs.EqualOutputs state.core focus model)
    (focusEquations : GeneralNominalCenteredHeadOutputs.EqualOutputs state.core focus model) :
    ¬ MergedOutputConflict state focus := by
  rintro ⟨_,atoms,others,present,_,impossible⟩
  apply impossible
  refine ⟨model,⟨models_history valid,?_,?_⟩,class_of_models valid focusEquations⟩
  · exact fun atom member => valid.1.1.2.2 atom (present.1 member)
  · exact fun focus member => class_of_models valid (classes focus (present.2 focus member))

end Yulang.GeneralNominalVersionedMergedConflict232
