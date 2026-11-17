import Yulang.GeneralNominalModeCompiler237
import Yulang.GeneralNominalExpressionIntervals237
/-! Endpoint containment depends only on normalized pattern names, not erased
record fields. Invariant nominal applications evaluate both sides in actual mode. -/
namespace Yulang.GeneralNominalModeIntervals237
open GeneralDeclarationPatterns CommonNominalFullCarrier GeneralNominalMaterialization
open GeneralNominalModePattern237 (eval evals)
open GeneralNominalModeCompiler237 (next)
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra application)
open GeneralNominalMatchedAssembly (Aligned)

mutual
 theorem eval_mono (catalogue : Constructors) (interpretation : GeneralNominalInspection.Interpretation)
    (variables : Mode → Nat → Ty) (first last : Mode) (pattern : Pattern)
    (bounded : ∀ name ∈ pattern.variables, Subtype (variables first name) (variables last name)) :
    Subtype (eval (algebra catalogue interpretation) (next interpretation) variables first pattern)
      (eval (algebra catalogue interpretation) (next interpretation) variables last pattern) := by
  cases pattern with
  | var name => exact bounded name (List.mem_singleton_self _)
  | app name arguments =>
    cases found : interpretation.primitives name with
    | none => simp only [eval,next,found,algebra]; exact subtype_refl _
    | some primitive =>
      simp only [eval,next,found,algebra,application]
      exact GeneralNominalExpressionIntervals237.primitive_mono primitive
        (evals_mono catalogue interpretation variables first last arguments bounded)
  | record label payload tail =>
    exact common_record_mono label
      (eval_mono catalogue interpretation variables first last payload (fun n h => bounded n (List.mem_append_left _ h)))
      (eval_mono catalogue interpretation variables first last tail (fun n h => bounded n (List.mem_append_right _ h)))
  | variant tag payload => exact (common_variant_iff ..).mpr (eval_mono catalogue interpretation variables first last payload bounded)
  | join a b =>
    exact common_union_mono
      (eval_mono catalogue interpretation variables first last a (fun n h => bounded n (List.mem_append_left _ h)))
      (eval_mono catalogue interpretation variables first last b (fun n h => bounded n (List.mem_append_right _ h)))
 termination_by sizeOf pattern

 theorem evals_mono (catalogue : Constructors) (interpretation : GeneralNominalInspection.Interpretation)
    (variables : Mode → Nat → Ty) (first last : Mode) (patterns : List Pattern)
    (bounded : ∀ name ∈ variablesArgs patterns, Subtype (variables first name) (variables last name)) :
    Aligned Subtype (evals (algebra catalogue interpretation) (next interpretation) variables first patterns)
      (evals (algebra catalogue interpretation) (next interpretation) variables last patterns) := by
  cases patterns with
  | nil => exact .nil
  | cons pattern rest =>
    exact .cons
      (eval_mono catalogue interpretation variables first last pattern (fun n h => bounded n (List.mem_append_left _ h)))
      (evals_mono catalogue interpretation variables first last rest (fun n h => bounded n (List.mem_append_right _ h)))
 termination_by sizeOf patterns
end

theorem compiled_interval
    (compiled : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation pattern = some expression)
    (bounded : ∀ name ∈ (normalize pattern).variables,
      Subtype (variables .lower name) (variables .actual name) ∧
      Subtype (variables .actual name) (variables .upper name)) :
    Subtype (GeneralNominalCenteredHeadMatExpressions.value variables .lower expression)
      (GeneralNominalCenteredHeadMatExpressions.value variables .actual expression) ∧
    Subtype (GeneralNominalCenteredHeadMatExpressions.value variables .actual expression)
      (GeneralNominalCenteredHeadMatExpressions.value variables .upper expression) := by
  have lower := GeneralNominalModeCompiler237.compiled_normalized (variables := variables) .lower compiled
  have actual := GeneralNominalModeCompiler237.compiled_normalized (variables := variables) .actual compiled
  have upper := GeneralNominalModeCompiler237.compiled_normalized (variables := variables) .upper compiled
  exact ⟨subtype_trans lower.1 (subtype_trans
    (eval_mono catalogue interpretation variables .lower .actual _ (fun n h => (bounded n h).1)) actual.2),
    subtype_trans actual.1 (subtype_trans
    (eval_mono catalogue interpretation variables .actual .upper _ (fun n h => (bounded n h).2)) upper.2)⟩
end Yulang.GeneralNominalModeIntervals237
