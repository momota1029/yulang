import Yulang.GeneralNominalCenteredHeadMatPatternSemantics
import Yulang.GeneralNominalCenteredHeadMatExpressions
/-! Interval evaluation of arbitrary total expressions. Nominal children read
actual mode in every surrounding mode, so they add no endpoint obligation. -/
namespace Yulang.GeneralNominalExpressionIntervals237
open GeneralNominalCenteredHeadMatExpressions GeneralNominalMaterialization
open CommonNominalFullCarrier GeneralCandidateInspection

mutual
 def reads : Expr → List Nat
   | .variable name => [name]
   | .primitive _ arguments => readsMany arguments
   | .nominal _ _ => []
   | .record _ payload tail => reads payload ++ reads tail
   | .variant _ payload => reads payload
   | .join first last => reads first ++ reads last
 def readsMany : List Expr → List Nat
   | [] => []
   | first :: rest => reads first ++ readsMany rest
end

theorem primitive_mono (primitive : Primitive) (related : GeneralNominalMatchedAssembly.Aligned Subtype first last) :
    Subtype (primitiveValue primitive first) (primitiveValue primitive last) := by
  cases primitive with
  | scalar base => cases related <;> exact subtype_refl _
  | emptyRecord => cases related <;> exact subtype_refl _
  | exactEmpty => cases related <;> exact subtype_refl _
  | pair =>
    cases related with
    | nil => exact subtype_refl _
    | cons one rest =>
      cases rest with
      | nil => exact subtype_refl _
      | cons two rest =>
        cases rest with
        | nil => exact (common_pair_iff ..).mpr ⟨one,two⟩
        | cons => exact subtype_refl _

mutual
 theorem value_mono (variables : Mode → Nat → Ty) (first last : Mode) (expression : Expr)
    (bounded : ∀ name ∈ reads expression, Subtype (variables first name) (variables last name)) :
    Subtype (value variables first expression) (value variables last expression) := by
  cases expression with
  | «variable» name => exact bounded name (List.mem_singleton_self _)
  | primitive constructor arguments => exact primitive_mono constructor (values_mono variables first last arguments bounded)
  | nominal => exact subtype_refl _
  | record label payload tail =>
    exact common_record_mono label
      (value_mono variables first last payload (fun n h => bounded n (List.mem_append_left _ h)))
      (value_mono variables first last tail (fun n h => bounded n (List.mem_append_right _ h)))
  | variant tag payload => exact (common_variant_iff ..).mpr (value_mono variables first last payload bounded)
  | join a b =>
    exact common_union_mono
      (value_mono variables first last a (fun n h => bounded n (List.mem_append_left _ h)))
      (value_mono variables first last b (fun n h => bounded n (List.mem_append_right _ h)))
 termination_by sizeOf expression

 theorem values_mono (variables : Mode → Nat → Ty) (first last : Mode) (expressions : List Expr)
    (bounded : ∀ name ∈ readsMany expressions, Subtype (variables first name) (variables last name)) :
    GeneralNominalMatchedAssembly.Aligned Subtype (values variables first expressions) (values variables last expressions) := by
  cases expressions with
  | nil => exact .nil
  | cons expression rest =>
    exact .cons
      (value_mono variables first last expression (fun n h => bounded n (List.mem_append_left _ h)))
      (values_mono variables first last rest (fun n h => bounded n (List.mem_append_right _ h)))
 termination_by sizeOf expressions
end

theorem interval (variables : Mode → Nat → Ty) (expression : Expr)
    (bounded : ∀ name ∈ reads expression,
      Subtype (variables .lower name) (variables .actual name) ∧
      Subtype (variables .actual name) (variables .upper name)) :
    Subtype (value variables .lower expression) (value variables .actual expression) ∧
      Subtype (value variables .actual expression) (value variables .upper expression) :=
  ⟨value_mono variables _ _ expression (fun n h => (bounded n h).1),
    value_mono variables _ _ expression (fun n h => (bounded n h).2)⟩
end Yulang.GeneralNominalExpressionIntervals237
