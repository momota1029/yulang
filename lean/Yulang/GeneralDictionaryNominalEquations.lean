import Yulang.GeneralNominalCommonBridge
import Yulang.GeneralDictionaryBatchRecording

/-!
# Dictionary equations under arbitrary full nominal assignments

This module interprets the existing Located equation terms in the full nominal
carrier, without requiring assignments to come from Common. Type and row source
maps stay separate. Recorded head and interval obligations remain explicit in
nominal Models; no Common-only certificate is used to discharge them.
-/
namespace Yulang.GeneralDictionaryNominalEquations
open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceNormalForm (Atom All)
open GeneralSourceState (State Demand)
open GeneralSourceDictionaryEquations (InstanceEquations)
open GeneralDictionaryStateEquations (Located Recorded liftType liftRow)
open GeneralNominalCommonBridge (Assignment Models)

/-- The same global equation terms, evaluated in the full nominal carrier. -/
def Holds {demand : Demand roles} (equations : InstanceEquations demand)
    (assignment : Assignment) : Prop :=
  (∀ index, CommonNominalFullCarrier.Subtype (assignment (demand.arguments index).1).1
      ((equations.head index).eval CommonNominalFullCarrier.model assignment) ∧
    CommonNominalFullCarrier.Subtype
      ((equations.head index).eval CommonNominalFullCarrier.model assignment)
      (assignment (demand.arguments index).2).1) ∧
  ∀ index, CommonNominalFullCarrier.Equivalent (assignment (demand.outputs[index]).target).1
    ((equations.output index).eval CommonNominalFullCarrier.model assignment)

theorem liftType_eval (state : State) (term : TyTerm (Fin state.slots))
    (assignment : Assignment) :
    (liftType state term).eval CommonNominalFullCarrier.model assignment =
      term.eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment state assignment) := by
  rw [liftType, TyTerm.eval_subst]
  rfl

theorem liftRow_eval (state : State) (term : RowTerm (Fin state.slots))
    (assignment : Assignment) :
    (liftRow state term).eval CommonNominalFullCarrier.model assignment =
      term.eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment state assignment) := by
  rw [liftRow, RowTerm.eval_subst]
  rfl

/-- Storage implies equations for every nominal model, not only lifted models. -/
theorem recorded_holds (located : Located state demand) (recorded : Recorded located)
    (assignment : Assignment) (model : Models state assignment) :
    Holds located.equations assignment := by
  constructor
  · intro index
    have lower := model.1 _ (recorded.lower index)
    have upper := model.1 _ (recorded.upper index)
    change CommonNominalFullCarrier.Subtype (assignment (demand.arguments index).1).1
        ((liftType state (located.head index)).eval CommonNominalFullCarrier.model assignment) ∧
      CommonNominalFullCarrier.Subtype
        ((liftType state (located.head index)).eval CommonNominalFullCarrier.model assignment)
        (assignment (demand.arguments index).2).1
    rw [liftType_eval, located.arguments]
    exact ⟨lower, upper⟩
  · intro index
    have forward := model.1 _ (recorded.outputForward index)
    have backward := model.1 _ (recorded.outputBackward index)
    change CommonNominalFullCarrier.Equivalent (assignment (demand.outputs[index]).target).1
      ((liftType state (located.output index)).eval CommonNominalFullCarrier.model assignment)
    rw [liftType_eval, located.targets]
    exact ⟨forward, backward⟩

/-- Append retains nominal head and interval obligations as well as ordinary atoms. -/
theorem append_models (state : State) (atoms : List (Atom (Fin state.slots)))
    (assignment : Assignment) :
    Models (GeneralDictionaryEquationRecording.append state atoms) assignment ↔
      Models state assignment ∧
        All CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment state assignment) atoms := by
  change (All CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment state assignment)
    (state.ordinary ++ atoms) ∧ _) ↔ _
  rw [PresenceNormalForm.all_append]
  exact ⟨fun ⟨⟨old, fresh⟩, heads, intervals⟩ => ⟨⟨old, heads, intervals⟩, fresh⟩,
    fun ⟨⟨old, heads, intervals⟩, fresh⟩ => ⟨⟨old, fresh⟩, heads, intervals⟩⟩

private theorem all_flatten (parts : Fin count → List (Atom α))
    (assignment : α → Core.PresenceGeneration.Comp CommonNominalFullCarrier.model) :
    All CommonNominalFullCarrier.model assignment (List.ofFn parts).flatten ↔
      ∀ index, All CommonNominalFullCarrier.model assignment (parts index) := by
  simp only [All, List.mem_flatten, List.mem_ofFn, forall_exists_index, and_imp]
  constructor
  · intro h index atom member; exact h atom (parts index) index rfl member
  · intro h atom part index equal member; subst part; exact h index atom member

/-- Exact correspondence retains repeated output occurrences and both inequalities. -/
theorem atoms_exact (located : Located state demand) (assignment : Assignment) :
    All CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment state assignment)
      (GeneralDictionaryEquationRecording.atoms located) ↔ Holds located.equations assignment := by
  unfold GeneralDictionaryEquationRecording.atoms
  rw [PresenceNormalForm.all_append]
  simp only [all_flatten]
  simp only [Holds, Located.equations, liftType_eval, located.arguments, located.targets]
  simp [All, Atom.Holds, TyTerm.eval, CommonNominalFullCarrier.model,
    GeneralNominalCommonBridge.assignment, CommonNominalFullCarrier.Equivalent]

/-- The final shared nominal model satisfies every dictionary package jointly. -/
theorem batch_models (items : List (GeneralDictionaryBatchRecording.Item roles state))
    (assignment : Assignment) :
    Models (GeneralDictionaryBatchRecording.record items) assignment ↔ Models state assignment ∧
      ∀ item ∈ items, Holds item.located.equations assignment := by
  rw [GeneralDictionaryBatchRecording.record, append_models]
  apply and_congr Iff.rfl
  induction items with
  | nil => simp [GeneralDictionaryBatchRecording.batchAtoms]
  | cons item rest ih =>
      simp only [GeneralDictionaryBatchRecording.batchAtoms, List.flatMap_cons,
        PresenceNormalForm.all_append, atoms_exact, List.mem_cons, forall_eq_or_imp]
      exact and_congr Iff.rfl ih

/-- Batch membership supplies storage; relocation preserves all global terms. -/
theorem batch_member_holds (items : List (GeneralDictionaryBatchRecording.Item roles state))
    (item : GeneralDictionaryBatchRecording.Item roles state) (member : item ∈ items)
    (assignment : Assignment) (model : Models (GeneralDictionaryBatchRecording.record items) assignment) :
    Holds item.located.equations assignment := by
  have holds := recorded_holds (GeneralDictionaryBatchRecording.relocate items item.located)
    (GeneralDictionaryBatchRecording.batch_recorded items item member) assignment model
  rw [GeneralDictionaryBatchRecording.relocate_equations] at holds
  exact holds

end Yulang.GeneralDictionaryNominalEquations
