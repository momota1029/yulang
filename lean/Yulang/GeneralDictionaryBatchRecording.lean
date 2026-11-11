import Yulang.GeneralDictionaryEquationRecording

/-!
# Shared recording of every finite dictionary-node obligation

All nodes use one original slot carrier and one final shared assignment.
No candidate branch is committed by this helper: a caller must first decide
which dictionary obligations belong to its candidate. Models characterize the
joint obligations exactly, so incompatible siblings are not hidden.
-/
namespace Yulang.GeneralDictionaryBatchRecording
open GeneralSourceState (State Demand Assignment Models)
open GeneralDictionaryStateEquations
open GeneralDictionaryEquationRecording (append atoms append_models atoms_exact)
open PresenceNormalForm (Atom All)

structure Item (roles : Roles.RoleDecls) (state : State) where
  demand : Demand roles
  located : Located state demand

def batchAtoms (items : List (Item roles state)) : List (Atom (Fin state.slots)) :=
  items.flatMap fun item => atoms item.located

def record (items : List (Item roles state)) : State := append state (batchAtoms items)

def relocate (items : List (Item roles state)) (located : Located state demand) :
    Located (record items) demand where
  lower := located.lower
  upper := located.upper
  head := located.head
  target := located.target
  output := located.output
  arguments := located.arguments
  targets := located.targets

/-- Every finite package, not one independently chosen model per package. -/
theorem batch_models (items : List (Item roles state)) (assignment : Assignment) :
    Models (record items) assignment ↔ Models state assignment ∧
      ∀ item ∈ items, item.located.equations.Holds assignment := by
  rw [record, append_models]
  apply and_congr Iff.rfl
  induction items with
  | nil => simp [batchAtoms]
  | cons item rest ih =>
      simp only [batchAtoms, List.flatMap_cons, PresenceNormalForm.all_append, atoms_exact,
        List.mem_cons, forall_eq_or_imp]
      exact and_congr Iff.rfl ih

theorem relocate_equations (items : List (Item roles state)) (located : Located state demand) :
    (relocate items located).equations = located.equations := rfl

private theorem atom_present (items : List (Item roles state)) (item : Item roles state)
    (present : item ∈ items) (atom : Atom (Fin state.slots))
    (member : atom ∈ atoms item.located) : atom ∈ (record items).ordinary :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨item, present, member⟩)

/-- Actual batch membership generates all four storage families automatically. -/
theorem batch_recorded (items : List (Item roles state)) (item : Item roles state)
    (present : item ∈ items) : Recorded (relocate items item.located) := by
  have stored := GeneralDictionaryEquationRecording.record_recorded item.located
  constructor
  · intro index
    change Atom.tyLe (.var (item.located.lower index)) (item.located.head index) ∈ (record items).ordinary
    have member := stored.lower index
    change _ ∈ state.ordinary ++ atoms item.located at member
    rcases List.mem_append.mp member with old | fresh
    · exact List.mem_append_left _ old
    · exact atom_present items item present _ fresh
  · intro index
    change Atom.tyLe (item.located.head index) (.var (item.located.upper index)) ∈ (record items).ordinary
    have member := stored.upper index
    change _ ∈ state.ordinary ++ atoms item.located at member
    rcases List.mem_append.mp member with old | fresh
    · exact List.mem_append_left _ old
    · exact atom_present items item present _ fresh
  · intro index
    change Atom.tyLe (.var (item.located.target index)) (item.located.output index) ∈ (record items).ordinary
    have member := stored.outputForward index
    change _ ∈ state.ordinary ++ atoms item.located at member
    rcases List.mem_append.mp member with old | fresh
    · exact List.mem_append_left _ old
    · exact atom_present items item present _ fresh
  · intro index
    change Atom.tyLe (item.located.output index) (.var (item.located.target index)) ∈ (record items).ordinary
    have member := stored.outputBackward index
    change _ ∈ state.ordinary ++ atoms item.located at member
    rcases List.mem_append.mp member with old | fresh
    · exact List.mem_append_left _ old
    · exact atom_present items item present _ fresh

/-- Reordering does not change models; it does not collapse or deduplicate the
source obligations that supply the batch. -/
theorem batch_order_models (first last : List (Item roles state)) (same : first.Perm last)
    (assignment : Assignment) : Models (record first) assignment ↔ Models (record last) assignment := by
  rw [batch_models, batch_models]
  exact and_congr Iff.rfl (by simp only [same.mem_iff])

theorem batch_satisfiable (items : List (Item roles state)) :
    (∃ assignment, Models (record items) assignment) ↔
      ∃ assignment, Models state assignment ∧ ∀ item ∈ items, item.located.equations.Holds assignment := by
  simp only [batch_models]

/-- No false loss of models when every listed obligation is already entailed. -/
theorem batch_conservative (items : List (Item roles state))
    (entailed : ∀ assignment, Models state assignment →
      ∀ item ∈ items, item.located.equations.Holds assignment)
    (assignment : Assignment) : Models (record items) assignment ↔ Models state assignment := by
  rw [batch_models]
  exact ⟨And.left, fun model => ⟨model, entailed assignment model⟩⟩

theorem batch_append_models (first last : List (Item roles state)) (assignment : Assignment) :
    Models (record (first ++ last)) assignment ↔
      Models (record first) assignment ∧ Models (record last) assignment := by
  simp only [batch_models, List.mem_append, or_imp, forall_and]
  exact ⟨fun ⟨model, first, last⟩ => ⟨⟨model, first⟩, ⟨model, last⟩⟩,
    fun ⟨⟨model, first⟩, ⟨_, last⟩⟩ => ⟨model, first, last⟩⟩

end Yulang.GeneralDictionaryBatchRecording
