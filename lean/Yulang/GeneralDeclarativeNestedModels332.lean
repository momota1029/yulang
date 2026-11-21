import Yulang.GeneralDeclarativeNestedChild332
import Yulang.CommonNominalFullModel

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralDeclarativeNestedModels332
open GeneralDeclarativeNestedExample332
open GeneralDeclarativeNestedDecl332 (registry root child)
open GeneralDeclarativeNestedFrame332 (stage spans grouped keep namedStage exact_observed rootStage)
open GeneralDeclarativeNestedChild332 (final childGrouped gathered child_gathered dictionary every_model tree)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeEntailment320 (model_append Holds)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent pair record variant nominal exactEmpty)
open GeneralDeclarativeExampleSource320 (int)

abbrev bool : Ty := .base .bool
abbrev innerTail := record 6 int exactEmpty
abbrev outerTail := record 9 bool exactEmpty
abbrev innerType := record 3 (nominal 0 [.inl bool]) (record 3 int innerTail)
abbrev outerType := record 7 (variant 4 (pair int innerType)) (record 7 bool outerTail)

def model : Assignment := fun n =>
  (if n = 0 then outerType else if n = 14 then innerType else if n = 16 then innerTail else
    if n = 6 ∨ n = 17 then outerTail else if n = 11 ∨ n = 15 then bool else int,Common.rowEmpty)

theorem initial : Models state model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ impossible => False.elim (List.not_mem_nil impossible)⟩,?_⟩
  intro row used
  change row ∈ [outerRow,innerRow,scalar] at used
  simp only [List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with h|h|h <;> cases h <;> exact eqv_refl _

theorem names_model : Models namedStage model := by
  apply (model_append _).mpr
  refine ⟨initial,fun row emitted => ?_⟩
  change row ∈ [⟨16,innerResidual⟩,⟨17,outerResidual⟩] at emitted
  rcases List.mem_cons.mp emitted with rfl|rest
  · exact eqv_refl _
  · cases List.mem_singleton.mp rest
    exact eqv_refl _

theorem stage_model : Models stage model :=
  ((exact_observed (fun _ => False)).2.2.2.2 model).mpr names_model

theorem populated : ∃ m, Models final m := by
  obtain ⟨parentModel,parentFit,parentKeep⟩ := (gathered (fun _ => False)).preserve.lifts model stage_model
  have readParent : Models rootStage parentModel := by
    apply (model_append _).mpr
    refine ⟨parentFit,fun row used => ?_⟩
    cases List.mem_singleton.mp used
    change Equivalent (parentModel 6).1 (parentModel 17).1
    rw [parentKeep 6 (by decide +kernel),parentKeep 17 (by decide +kernel)]
    exact eqv_refl _
  obtain ⟨childModel,childFit,childKeep⟩ := child_gathered.preserve.lifts parentModel readParent
  refine ⟨childModel,(model_append _).mpr ⟨childFit,?_⟩⟩
  intro row used
  cases List.mem_singleton.mp used
  change Equivalent (childModel 5).1 (childModel 3).1
  rw [childKeep 5 (by decide +kernel),childKeep 3 (by decide +kernel),
    parentKeep 5 (by decide +kernel),parentKeep 3 (by decide +kernel)]
  exact eqv_refl _

theorem real_nested_dictionary :
    child.arguments = [⟨18,3,19⟩] ∧ child.outputs = [⟨1,5⟩] ∧
      ∃ m, Models final m ∧ Evidence registry interpretation m root dictionary := by
  obtain ⟨m,valid⟩ := populated
  exact ⟨rfl,rfl,m,valid,every_model m valid⟩

end Yulang.GeneralDeclarativeNestedModels332
