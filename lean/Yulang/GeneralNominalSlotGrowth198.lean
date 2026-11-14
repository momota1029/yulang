import Yulang.GeneralNominalSlotTransport198
import Yulang.GeneralDictionaryRefinementExamples

/-! Proper growth and reindexing with unchanged source names. A real nominal
refinement inhabits the arbitrary-slot hypotheses; its source model is nonempty. -/
namespace Yulang.GeneralNominalSlotGrowth198
open GeneralNominalState (State)
open GeneralNominalRefinements (Refines)
open GeneralNominalRecursiveInspection
open GeneralNominalSlotObservation198 (bounds)
open GeneralDictionaryEquationExamples (state)
open GeneralDictionaryRefinementExamples (grown)

def blankView (base : GeneralSourceState.State) : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun _ => .deferred .unresolved
  checked := by intro _ _ impossible; cases impossible

abbrev before : State := {GeneralNominalState.embed state (blankView state) GeneralDeclarationExamples.constructors with
  seed := 20, reserved := [9,19]}
abbrev after : State := {GeneralNominalState.embed grown (blankView grown) GeneralDeclarationExamples.constructors with
  seed := 20, reserved := [9,19]}

def refinement : Refines before after where
  base := GeneralDictionaryRefinementExamples.refinement
  heads := by intro _ _ impossible; cases impossible
  nominals := by intro _ _ impossible; cases impossible
  ordinary := by intro _ impossible; cases impossible
  known := by
    rintro source ⟨slot,same,seen | ⟨descriptor,recorded⟩⟩
    · exact False.elim (seen rfl)
    · cases recorded
  reserved := fun _ member => member
  allocated := fun _ member => member
  seed := rfl
  constructors := rfl

theorem proper_growth : before.base.slots < after.base.slots ∧ refinement.base.embed 0 = 1 :=
  ⟨by decide, rfl⟩

theorem supported : ∀ source ∈ GeneralNominalState.sources after,
    source ∈ GeneralNominalState.sources before := by
  intro source member
  simp [GeneralNominalState.sources,List.ofFn_succ] at member ⊢
  rcases member with h | h | h | h | h | h <;> simp_all

theorem inhabited : ∃ model, GeneralNominalState.Models before model ∧ GeneralNominalState.Models after model := by
  refine ⟨GeneralNominalCommonBridge.lift GeneralDictionaryEquationExamples.assignment,?_,?_⟩
  · constructor
    · exact (GeneralNominalCommonBridge.models_exact _ _).mpr
        (GeneralSourceState.refinement_models GeneralDictionaryRefinementExamples.refinement _
          GeneralDictionaryRefinementExamples.grown_models)
    · constructor
      · intro slot descriptor impossible
        cases impossible
      · intro atom member
        cases member
  · constructor
    · exact (GeneralNominalCommonBridge.models_exact _ _).mpr GeneralDictionaryRefinementExamples.grown_models
    · constructor
      · intro slot descriptor impossible
        cases impossible
      · intro atom member
        cases member

/-- The actual inspector moves local bounds zero to one but retains global
capture source 10. No report agreement is a premise. -/
theorem actual_reinspection (origin : Option Origin) :
    inspect after (.variables [7]) (1,1) origin =
      GeneralNominalSlotReport198.report refinement.base.embed
        (inspect before (.variables [7]) (0,0) origin) :=
  GeneralNominalSlotReport198.inspect_report refinement .variables origin

theorem global_bindings (origin : Option Origin) :
    bindings after (inspect after (.variables [7]) (1,1) origin) = [(7,10,10)] := by
  simp [bindings,inspect,after,grown]
end Yulang.GeneralNominalSlotGrowth198
