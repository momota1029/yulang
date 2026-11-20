import Yulang.GeneralRebaseRowParentOutput287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 12500000
namespace Yulang.GeneralRebaseRowChildRaw287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentOutput287
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalCenteredHeadMatCompilerSemantics (nominal_congr)

def SourceCheck (m : Assignment) : Prop :=
  Equivalent (m 0).1 (R (m 0).2) ∧ Equivalent (m 1).1 (F (m 0).1)

def OutputCheck (m : Assignment) : Prop :=
  SourceCheck m ∧ Equivalent (m 2).1 (F (F (m 0).1))

theorem inner_checked (m : Assignment) (valid : GeneralNominalState.Models raw m) :
    Equivalent (m 0).1 (R (m 0).2) := by
  obtain ⟨args,fit,equal⟩ := GeneralNominalState.nominal_models raw m valid 0 inner rfl
  change GeneralNominalState.FitsAll raw.base m [.row (0,0)] args at fit
  cases fit with
  | @cons _ v _ rest compatible tail =>
    cases tail
    cases v with
    | inl => cases compatible
    | inr row =>
      have rowEq : row = (m 0).2 := Common.rowLe_antisymm compatible.2 compatible.1
      rw [rowEq] at equal
      exact equal

theorem outer_checked (m : Assignment) (valid : GeneralNominalState.Models raw m) :
    Equivalent (m 1).1 (F (m 0).1) := by
  obtain ⟨args,fit,equal⟩ := GeneralNominalState.nominal_models raw m valid 1 outer rfl
  change GeneralNominalState.FitsAll raw.base m [.type (0,0)] args at fit
  cases fit with
  | @cons _ v _ rest compatible tail =>
    cases tail
    cases v with
    | inr => cases compatible
    | inl type =>
      have lift := nominal_congr 0 (.cons (show Equivalent type (m 0).1 from
        ⟨compatible.2,compatible.1⟩) .nil)
      exact ⟨subtype_trans equal.1 lift.1,subtype_trans lift.2 equal.2⟩

theorem exact_source (m : Assignment) :
    GeneralNominalState.Models raw m ↔ SourceCheck m := by
  constructor
  · intro valid; exact ⟨inner_checked m valid,outer_checked m valid⟩
  · rintro ⟨inside,outside⟩
    refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
    · intro _ member; cases member
    · intro _ _ found; cases found
    · intro _ member; cases member
    · intro slot d found
      change (if slot = (0 : Fin 3) then some inner else if slot = 1 then some outer else none) = some d at found
      split at found
      · rename_i same
        subst slot
        cases Option.some.inj found
        exact ⟨[.inr (m 0).2],.cons ⟨Common.rowLe_refl _,Common.rowLe_refl _⟩ .nil,inside⟩
      · split at found
        · rename_i same
          subst slot
          cases Option.some.inj found
          exact ⟨[.inl (m 0).1],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,outside⟩
        · cases found
    · intro _ member; cases member

theorem before_exact (m : Assignment) :
    GeneralNominalVersionedJournal232.Models before m ↔ SourceCheck m :=
  (GeneralNominalVersionedJournal232.initial_models ctx root m).trans
    ⟨fun valid => (exact_source m).mp valid.1,
      fun checked => ⟨(exact_source m).mpr checked,
        GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _⟩⟩

theorem completion (m : Assignment) : SourceCheck (replaceOutput m) ↔ SourceCheck m := by
  unfold SourceCheck
  rw [completion_types _ 0 (by decide),completion_types _ 1 (by decide),completion_rows]

theorem complete_check (m : Assignment) : OutputCheck (replaceOutput m) ↔ SourceCheck m := by
  unfold OutputCheck
  exact (and_iff_left ((outputs_exact true _).mp (completed_outputs true m))).trans (completion m)

def changeAmbient (m : Assignment) (k : Nat) (r : Common.Row) : Assignment :=
  fun n => ((m n).1,if n = k then r else (m n).2)

theorem all_other_rows_irrelevant (m : Assignment) (k : Nat) (notUsed : k ≠ 0) (r : Common.Row) :
    OutputCheck (changeAmbient m k r) ↔ OutputCheck m := by
  have apart : (0 : Nat) ≠ k := Ne.symm notUsed
  simp [OutputCheck,SourceCheck,changeAmbient,apart]

abbrev fullRow : Common.Row := fun _ => True

theorem different_rows : ¬ Equivalent (R Common.rowEmpty) (R fullRow) := by
  intro same
  have invariant := (nominal_regular_invariant_exact 6 6 _ _).mp same.1
  have row := invariant.2.2 0 (.inr Common.rowEmpty) (.inr fullRow) rfl rfl
  have literal : Common.rowEmpty = fullRow := row
  exact Eq.mp (congrFun literal (0,[])).symm True.intro

theorem ambient_boundary :
    let a := model Common.rowEmpty
    let b := changeAmbient a 0 fullRow
    (∀ n, (a n).1 = (b n).1) ∧
      GeneralNominalVersionedJournal232.Models before a ∧
      ¬ GeneralNominalVersionedJournal232.Models before b := by
  dsimp only
  refine ⟨fun _ => rfl,before_model Common.rowEmpty,?_⟩
  intro invalid
  exact different_rows ((before_exact _).mp invalid).1

end Yulang.GeneralRebaseRowChildRaw287
