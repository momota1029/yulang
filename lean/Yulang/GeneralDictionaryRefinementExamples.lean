import Yulang.GeneralDictionaryRefinementEvidence
import Yulang.GeneralDictionaryReadbackExamples

/-!
# Non-vacuous growth and reindexing of dictionary equation evidence

The previous slot zero moves to slot one in a two-slot state. A fresh source
occupies slot zero; existing type and row sources remain distinct and unchanged.
The three-node source dictionary and its repeated output obligations survive.
-/
namespace Yulang.GeneralDictionaryRefinementExamples
open GeneralSourceState
open GeneralDictionaryStateEquations GeneralDictionaryModelEvidence
open GeneralDictionaryRefinementEvidence
open GeneralDictionaryEquationExamples (state demand located assignment recorded)
open GeneralDictionaryReadbackExamples (Package tree stored_tree)
open GeneralSourceDictionaries
open Core.PresenceGeneration (TyTerm)

abbrev grown : State where
  slots := 2
  source := fun slot => slot.val + 9
  source_injective := by
    intro first last same
    apply Fin.ext
    exact Nat.add_right_cancel same
  rowSource := fun slot => slot.val + 19
  ordinary := equationAtoms 1 (.base .int)
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro index; exact Fin.elim0 index
  heads := fun _ => .unresolved
  intervals := [(1, 1)]
  heads_sound := by intro _ _ _ _ impossible; cases impossible
  intervals_sound := by
    intro values _ pair member
    have same := List.mem_singleton.mp member
    subst pair
    exact Common.subtype_refl _

/-- Old source 10 moves from local slot zero to one; fresh source 9 is added. -/
def refinement : Refines state grown where
  embed := fun _ => 1
  source := fun _ => rfl
  rowSource := fun _ => rfl
  ordinary := by
    intro atom member
    simp only [state, equationAtoms, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [grown, equationAtoms,
      PresenceNormalForm.Atom.rename, TyTerm.rename]
  known := by intro _ impossible; exact False.elim (impossible rfl)
  intervals := by
    intro pair member
    have same := List.mem_singleton.mp member
    subst pair
    exact List.mem_singleton_self _

theorem proper_growth_and_reindex :
    state.slots < grown.slots ∧ refinement.embed 0 = 1 ∧
      grown.source 0 = 9 ∧ grown.source (refinement.embed 0) = 10 ∧
      grown.rowSource (refinement.embed 0) = 20 := by
  decide

/-- The enlarged ordinary constraints have an actual satisfying assignment. -/
theorem grown_models : Models grown assignment := by
  apply (models_ordinary grown assignment).mpr
  apply (equationAtoms_exact 1 (.base .int) (grown.assignment assignment)).mpr
  exact Common.equivalent_refl _

theorem transported_recorded : Recorded (transport refinement located) :=
  transport_recorded refinement located recorded

/-- Renaming local arrow variables does not change global type/effect IDs. -/
theorem reindexed_arrow_sources :
    liftType grown
      ((TyTerm.arrow (.var 0) (.var 0) (.var 0) (.var 0) : TyTerm (Fin state.slots)).rename
        refinement.embed) =
      .arrow (.var 10) (.var 20) (.var 10) (.var 20) := rfl

theorem unchanged_three_node_tree :
    Evidence (StoredInstance (liftPackages refinement Package)) tree ∧
      (observations tree).map (fun event => event.1.identity) = [100, 101, 102] :=
  ⟨indexed_transport refinement Package tree stored_tree, rfl⟩

/-- The same three-node dictionary works in every model of the enlarged state. -/
theorem all_refined_models (model : Assignment) (valid : Models grown model) :
    Evidence (ModelInstance (liftPackages refinement Package) model) tree :=
  indexed_transport_all_models refinement Package tree stored_tree model valid

/-- This evidence is not merely universal over an empty refined model set. -/
theorem nonvacuous_refined_tree : Models grown assignment ∧
    Evidence (ModelInstance (liftPackages refinement Package) assignment) tree :=
  ⟨grown_models, all_refined_models assignment grown_models⟩

end Yulang.GeneralDictionaryRefinementExamples
