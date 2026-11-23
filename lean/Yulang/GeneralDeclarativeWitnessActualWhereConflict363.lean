import Yulang.GeneralDeclarativeWitnessWhereAlternatives363

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 80000
set_option maxHeartbeats 100000000
namespace Yulang.GeneralDeclarativeWitnessActualWhereConflict363
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessWhereAlternatives363 (Trial trial actual)
open GeneralDeclarativeWitnessSelectedSourceMeaning363 (Query rootQuery)
open GeneralDeclarativeWitnessOrderedDictionary363 (Evidence dictionary_sound)
open GeneralDeclarativeWitnessNativeInstall360 (Fits interpreted NativeViews)
open GeneralDeclarativeWitnessNonpointPortModel362 (exact exact_model_iff)
open GeneralDeclarativeWitnessCrossOwnerModel362 (stage model fits_current)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Frontier Classify)

def childQuery {contra x} (t : @Trial contra x) : Query := ⟨[10,0],t.root.occurrence⟩

inductive Local {contra : Bool} {x : Ordered contra} (t : Trial x) : Query → Frontier Query → Prop where
  | root : Local t rootQuery (.selected t.root.chosen.impl.id [childQuery t])
  | ambiguous : Local t (childQuery t) .ambiguous

theorem actual_child_ambiguity_propagates {contra} {x : Ordered contra} (t : Trial x) :
    Classify (Local t) rootQuery .ambiguous := by
  refine ⟨.selected t.root.chosen.impl.id [.ambiguous],?_,?_⟩
  · exact .selected .root (.cons (.ambiguous .ambiguous) .nil)
  · exact .selected (.cons .ambiguous .nil) (.ambiguous (by simp) (by simp))

theorem forced_body_cannot_become_selected_dictionary {contra} {x : Ordered contra} (t : Trial x)
    (dict) : ¬Classify (Local t) rootQuery (.selected dict) := by
  let onlyRoot := fun (d : Query) (_ : Nat) (children : List Query) =>
    d = rootQuery ∧ children = [childQuery t]
  have each : ∀ d key children,Local t d (.selected key children) → onlyRoot d key children := by
    intro _ _ _ sealed
    cases sealed with
    | root => exact ⟨rfl,rfl⟩
  intro made
  have rejected := dictionary_sound each made
  cases rejected with
  | node a b =>
    rw [a.2] at b
    cases b with
    | cons impossible _ =>
      cases impossible with
      | node shared _ =>
        have disagree : ([10,0] : List Nat) = [10] := congrArg Query.path shared.1
        cases disagree

def checked {contra x} (t : @Trial contra x) : Bool :=
  actual t && exact t.unselectedBody.world.ordinary (stage contra)

theorem both_applicable_in_the_same_normal_state (contra : Bool) :
    ((run contra).bind fun x => (trial x).map checked).getD false = true := by cases contra <;> decide +kernel

theorem real_ambiguity_is_not_a_model_inconsistency (contra : Bool) :
    ∃ (x : Ordered contra) (t : Trial x), run contra = some x ∧ trial x = some t ∧
      Classify (Local t) rootQuery .ambiguous ∧
      (∀ dict,¬Classify (Local t) rootQuery (.selected dict)) ∧
      ∀ u,Fits t.unselectedBody.world (model contra u) (interpreted t.unselectedBody.world.board (model contra u)) := by
  have witnessed := both_applicable_in_the_same_normal_state contra
  cases made : run contra with
  | none => rw [made] at witnessed; cases witnessed
  | some x =>
    rw [made] at witnessed
    change ((trial x).map checked).getD false = true at witnessed
    cases inspected : trial x with
    | none => rw [inspected] at witnessed; cases witnessed
    | some t =>
      rw [inspected] at witnessed
      have h := Bool.and_eq_true_iff.mp (show checked t = true from witnessed)
      exact ⟨x,t,rfl,inspected,actual_child_ambiguity_propagates t,
        forced_body_cannot_become_selected_dictionary t,
        fun u => ⟨(exact_model_iff h.2 _).mpr (fits_current contra u),fun _ => rfl⟩⟩

end Yulang.GeneralDeclarativeWitnessActualWhereConflict363
