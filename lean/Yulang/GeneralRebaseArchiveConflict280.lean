import Yulang.GeneralRebaseCompactMachine280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
namespace Yulang.GeneralRebaseArchiveConflict280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralRebaseArchiveTrust280
open GeneralRebaseArchiveGuards280 (models)
open GeneralNominalVersionedMergedConflict232
open GeneralNominalVersionedDiagnostic232
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls} {s : State roles} {ys : List (Effect roles)}

theorem history (pair : Correspond s.effects ys) (m : Assignment) :
    HistoryModels s m ↔ HistoryModels (changeEffects s ys) m := by
  constructor
  · rintro ⟨raw,plans,done⟩
    refine ⟨raw,plans,?_⟩
    intro eff recorded
    obtain ⟨old,member,rel⟩ := pair.2 eff recorded
    exact (rel.holds m).mp (done old member)
  · rintro ⟨raw,plans,done⟩
    refine ⟨raw,plans,?_⟩
    intro eff recorded
    obtain ⟨new,member,rel⟩ := pair.1 eff recorded
    exact (rel.holds m).mpr (done new member)

theorem class_equations (pair : Correspond s.effects ys) (focus : Occurrence roles) (m : Assignment) :
    ClassEquations s focus m ↔ ClassEquations (changeEffects s ys) focus m := by
  constructor
  · rintro ⟨raw,done⟩
    refine ⟨raw,?_⟩
    intro eff recorded alias
    obtain ⟨old,member,rel⟩ := pair.2 eff recorded
    exact (rel.live s.core m).mp (done old member (rel.plan.symm ▸ alias))
  · rintro ⟨raw,done⟩
    refine ⟨raw,?_⟩
    intro eff recorded alias
    obtain ⟨new,member,rel⟩ := pair.1 eff recorded
    exact (rel.live s.core m).mpr (done new member (rel.plan ▸ alias))

theorem context (pair : Correspond s.effects ys) (atoms classes) (m : Assignment) :
    ContextModels s atoms classes m ↔ ContextModels (changeEffects s ys) atoms classes m := by
  unfold ContextModels
  simp only [history pair,class_equations pair]

theorem merged (pair : Correspond s.effects ys) (focus : Occurrence roles) :
    MergedOutputConflict s focus ↔ MergedOutputConflict (changeEffects s ys) focus := by
  unfold MergedOutputConflict
  simp only [context pair,class_equations pair]
  rfl

theorem output (pair : Correspond s.effects ys) (r : Registry) (focus : Occurrence roles) (key : Nat) :
    OutputConflict r s focus key ↔ OutputConflict r (changeEffects s ys) focus key := by
  unfold OutputConflict
  rw [models pair]
  rfl

theorem feasible (pair : Correspond s.effects ys) (r : Registry) (focus : Occurrence roles) (key : Nat) :
    Feasible r s focus key ↔ Feasible r (changeEffects s ys) focus key := by
  unfold Feasible
  rw [models pair]
  rfl

theorem at_key (pair : Correspond s.effects ys) (r : Registry) (focus : Occurrence roles) (key : Nat) :
    AtKey r s focus key ↔ AtKey r (changeEffects s ys) focus key := by
  unfold AtKey
  rw [models pair,feasible pair]
  rfl

end Yulang.GeneralRebaseArchiveConflict280
