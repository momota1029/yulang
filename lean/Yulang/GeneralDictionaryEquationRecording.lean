import Yulang.GeneralDictionaryPlannedEvidence
import Yulang.CommonRoleStructuralRenaming

/-!
# Exact ordinary recording for source dictionary equations

This finite dictionary transaction removes manual storage-membership premises.
It retains every source slot, observation, interval, and output occurrence.
It is not a language Step or a candidate selector. Located terms still need
faithful declaration instantiation, and a nonempty model set is not automatic.
-/
namespace Yulang.GeneralDictionaryEquationRecording
open GeneralSourceState (State Demand Assignment Models Refines)
open GeneralDictionaryStateEquations
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom All)

def append (state : State) (atoms : List (Atom (Fin state.slots))) : State where
  slots := state.slots
  source := state.source
  source_injective := state.source_injective
  rowSource := state.rowSource
  ordinary := state.ordinary ++ atoms
  kinds := state.kinds
  shapes := state.shapes
  shapes_injective := state.shapes_injective
  heads := state.heads
  intervals := state.intervals
  heads_sound := fun assignment valid => state.heads_sound assignment
    (fun atom member => valid atom (List.mem_append_left _ member))
  intervals_sound := fun assignment valid => state.intervals_sound assignment
    (fun atom member => valid atom (List.mem_append_left _ member))

/-- Exact model law. No new graph fact is asserted by the operation. -/
theorem append_models (state : State) (atoms : List (Atom (Fin state.slots)))
    (assignment : Assignment) :
    Models (append state atoms) assignment ↔
      Models state assignment ∧ All Common.model (state.assignment assignment) atoms := by
  rw [GeneralSourceState.models_ordinary, GeneralSourceState.models_ordinary]
  exact PresenceNormalForm.all_append _ _ _ _

def append_refines (state : State) (atoms : List (Atom (Fin state.slots))) :
    Refines state (append state atoms) where
  embed := id
  source := fun _ => rfl
  rowSource := fun _ => rfl
  ordinary := by
    intro atom member
    change atom.rename id ∈ state.ordinary ++ atoms
    rw [CommonRoleStructuralRenaming.atom_rename_id]
    exact List.mem_append_left atoms member
  known := fun _ known => known
  intervals := fun _ member => member

/-- Every argument and repeated output occurrence retains both inequalities. -/
def atoms (located : Located state demand) : List (Atom (Fin state.slots)) :=
  (List.ofFn fun index =>
    [Atom.tyLe (.var (located.lower index)) (located.head index),
      Atom.tyLe (located.head index) (.var (located.upper index))]).flatten ++
  (List.ofFn fun index =>
    [Atom.tyLe (.var (located.target index)) (located.output index),
      Atom.tyLe (located.output index) (.var (located.target index))]).flatten

private theorem all_flatten (parts : Fin count → List (Atom α))
    (assignment : α → Core.PresenceGeneration.Comp Common.model) :
    All Common.model assignment (List.ofFn parts).flatten ↔
      ∀ index, All Common.model assignment (parts index) := by
  simp only [All, List.mem_flatten, List.mem_ofFn, forall_exists_index, and_imp]
  constructor
  · intro h index atom member; exact h atom (parts index) index rfl member
  · intro h atom part index equal member; subst part; exact h index atom member

/-- Slot atoms and source equations agree, retaining separate row identities. -/
theorem atoms_exact (located : Located state demand) (assignment : Assignment) :
    All Common.model (state.assignment assignment) (atoms located) ↔
      located.equations.Holds assignment := by
  unfold atoms
  rw [PresenceNormalForm.all_append]
  simp only [all_flatten]
  simp only [GeneralSourceDictionaryEquations.InstanceEquations.Holds,
    Located.equations, liftType_eval, located.arguments, located.targets]
  simp [All, Atom.Holds, TyTerm.eval, Common.model, State.assignment, Common.Equivalent]

def record (located : Located state demand) : State := append state (atoms located)

/-- Recording allocates no slots and does not choose an interval centre. -/
def relocation (located : Located state demand) : Located (record located) demand where
  lower := located.lower
  upper := located.upper
  head := located.head
  target := located.target
  output := located.output
  arguments := located.arguments
  targets := located.targets

private theorem mem_flatten (parts : Fin count → List α) (index : Fin count)
    (entry : α) (member : entry ∈ parts index) : entry ∈ (List.ofFn parts).flatten :=
  List.mem_flatten.mpr ⟨parts index, List.mem_ofFn.mpr ⟨index, rfl⟩, member⟩

/-- Actual storage membership is an output theorem, not an input certificate. -/
theorem record_recorded (located : Located state demand) : Recorded (relocation located) := by
  constructor
  · intro index
    change Atom.tyLe (.var (located.lower index)) (located.head index) ∈ state.ordinary ++ atoms located
    apply List.mem_append_right
    apply List.mem_append_left
    exact mem_flatten _ index _ (by simp)
  · intro index
    change Atom.tyLe (located.head index) (.var (located.upper index)) ∈ state.ordinary ++ atoms located
    apply List.mem_append_right
    apply List.mem_append_left
    exact mem_flatten _ index _ (by simp)
  · intro index
    change Atom.tyLe (.var (located.target index)) (located.output index) ∈ state.ordinary ++ atoms located
    apply List.mem_append_right
    apply List.mem_append_right
    exact mem_flatten _ index _ (by simp)
  · intro index
    change Atom.tyLe (located.output index) (.var (located.target index)) ∈ state.ordinary ++ atoms located
    apply List.mem_append_right
    apply List.mem_append_right
    exact mem_flatten _ index _ (by simp)

theorem record_models (located : Located state demand) (assignment : Assignment) :
    Models (record located) assignment ↔
      Models state assignment ∧ located.equations.Holds assignment := by
  rw [record, append_models, atoms_exact]

/-- A common old model satisfying all new obligations is exactly feasibility. -/
theorem record_satisfiable (located : Located state demand) :
    (∃ assignment, Models (record located) assignment) ↔
      ∃ assignment, Models state assignment ∧ located.equations.Holds assignment := by
  simp only [record_models]

theorem record_conservative (located : Located state demand)
    (entailed : ∀ assignment, Models state assignment → located.equations.Holds assignment)
    (assignment : Assignment) :
    Models (record located) assignment ↔ Models state assignment := by
  rw [record_models]
  exact ⟨And.left, fun model => ⟨model, entailed assignment model⟩⟩

theorem relocation_equations (located : Located state demand) :
    (relocation located).equations = located.equations := rfl

end Yulang.GeneralDictionaryEquationRecording
