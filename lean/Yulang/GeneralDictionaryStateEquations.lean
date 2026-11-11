import Yulang.GeneralSourceDictionaryEquations

/-!
# Actual shared-state constraints imply dictionary-head/output equations

Every endpoint and output target is located at a concrete state slot. Ordinary
terms are lifted with separate type and row source maps using existing paired
substitution. Syntactic presence of each required inequality in the actual
ordinary state implies the equations in every one of its models.

This is a dictionary meaning bridge, not a declaration-pattern elaborator,
selected-candidate proof, or complete general-source Evidence implementation.
-/
namespace Yulang.GeneralDictionaryStateEquations
open Core.PresenceGeneration (TyTerm RowTerm CompTerm)
open PresenceNormalForm (Atom)
open GeneralSourceState (State Demand Assignment Models)
open GeneralSourceDictionaryEquations (InstanceEquations Entailed equations_exact)

/-- Type slots and row slots have independent source identities. -/
def sourceSubstitution (state : State) (slot : Fin state.slots) : CompTerm Nat :=
  ⟨.var (state.source slot), .var (state.rowSource slot)⟩

def liftType (state : State) (term : TyTerm (Fin state.slots)) : TyTerm Nat :=
  term.subst (sourceSubstitution state)

def liftRow (state : State) (term : RowTerm (Fin state.slots)) : RowTerm Nat :=
  term.subst (sourceSubstitution state)

theorem liftType_eval (state : State) (term : TyTerm (Fin state.slots))
    (assignment : Assignment) :
    (liftType state term).eval Common.model assignment =
      term.eval Common.model (state.assignment assignment) := by
  rw [liftType, TyTerm.eval_subst]
  rfl

theorem liftRow_eval (state : State) (term : RowTerm (Fin state.slots))
    (assignment : Assignment) :
    (liftRow state term).eval Common.model assignment =
      term.eval Common.model (state.assignment assignment) := by
  rw [liftRow, RowTerm.eval_subst]
  rfl

/-- No endpoint or named output occurrence is identified by its list position
alone. Its source ID is checked against the actual shared snapshot. -/
structure Located (state : State) (demand : Demand roles) where
  lower : Fin (roles demand.role).arity → Fin state.slots
  upper : Fin (roles demand.role).arity → Fin state.slots
  head : Fin (roles demand.role).arity → TyTerm (Fin state.slots)
  target : Fin demand.outputs.length → Fin state.slots
  output : Fin demand.outputs.length → TyTerm (Fin state.slots)
  arguments : ∀ index, demand.arguments index = (state.source (lower index), state.source (upper index))
  targets : ∀ index, (demand.outputs[index]).target = state.source (target index)

def Located.equations (located : Located state demand) : InstanceEquations demand where
  head := fun index => liftType state (located.head index)
  output := fun index => liftType state (located.output index)

/-- A checkable storage condition, not a semantic all-model premise. It need not
hold for an arbitrary State or before candidate propagation has occurred. -/
structure Recorded (located : Located state demand) : Prop where
  lower : ∀ index, Atom.tyLe (.var (located.lower index)) (located.head index) ∈ state.ordinary
  upper : ∀ index, Atom.tyLe (located.head index) (.var (located.upper index)) ∈ state.ordinary
  outputForward : ∀ index, Atom.tyLe (.var (located.target index)) (located.output index) ∈ state.ordinary
  outputBackward : ∀ index, Atom.tyLe (located.output index) (.var (located.target index)) ∈ state.ordinary

/-- Soundness: actual stored inequalities at concrete slots establish every
instantiated head and repeated output equation in an arbitrary shared model. -/
theorem recorded_holds (located : Located state demand) (recorded : Recorded located)
    (assignment : Assignment) (model : Models state assignment) :
    located.equations.Holds assignment := by
  constructor
  · intro index
    have lower := model.1 _ (recorded.lower index)
    have upper := model.1 _ (recorded.upper index)
    change Common.Subtype (assignment (demand.arguments index).1).1
        ((liftType state (located.head index)).eval Common.model assignment) ∧
      Common.Subtype ((liftType state (located.head index)).eval Common.model assignment)
        (assignment (demand.arguments index).2).1
    rw [liftType_eval, located.arguments]
    exact ⟨lower, upper⟩
  · intro index
    have forward := model.1 _ (recorded.outputForward index)
    have backward := model.1 _ (recorded.outputBackward index)
    change Common.Equivalent (assignment (demand.outputs[index]).target).1
      ((liftType state (located.output index)).eval Common.model assignment)
    rw [liftType_eval, located.targets]
    exact ⟨forward, backward⟩

/-- Universal model quantification is discharged by actual ordinary storage,
not by postulating entailment as an input to this theorem. -/
theorem recorded_entails (located : Located state demand) (recorded : Recorded located) :
    Entailed state located.equations := by
  intro assignment model
  exact (equations_exact located.equations assignment).mpr (recorded_holds located recorded assignment model)

/-- No assumption that the two maps are equal is made, even for an arrow that
mentions the same local index in type and effect positions. -/
theorem lifted_arrow_separates_sources (state : State) (input output row : Fin state.slots) :
    liftType state (.arrow (.var input) (.var row) (.var output) (.var row)) =
      .arrow (.var (state.source input)) (.var (state.rowSource row))
        (.var (state.source output)) (.var (state.rowSource row)) := rfl

end Yulang.GeneralDictionaryStateEquations

namespace Yulang.GeneralDictionaryStateEquations
open GeneralSourceState (Refines Demand)
open GeneralSourceDictionaryEquations (InstanceEquations Entailed)

/-- Global source equations remain true after any certified source-preserving
state refinement. The equation terms keep their global type and row identities;
no substitution by fresh local slot numbers is performed. -/
theorem entailed_refines (refinement : Refines before after) (demand : Demand roles)
    (equations : InstanceEquations demand) (entailed : Entailed before equations) :
    Entailed after equations := by
  intro assignment model
  exact entailed assignment (GeneralSourceState.refinement_models refinement assignment model)

end Yulang.GeneralDictionaryStateEquations
