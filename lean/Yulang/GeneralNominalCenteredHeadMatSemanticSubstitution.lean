import Yulang.GeneralNominalCenteredHeadMatCompilerSemantics

namespace Yulang.GeneralNominalCenteredHeadMatSemanticSubstitution
open GeneralDeclarationPatterns CommonNominalFullCarrier
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalMatchedAssembly (Aligned)
variable {algebra : Algebra} {first last variables : Nat → Ty}

mutual
  theorem eval_congr (pattern : Pattern)
      (same : ∀ name ∈ pattern.variables, Equivalent (first name) (last name)) :
      Equivalent (eval algebra first pattern) (eval algebra last pattern) := by
    cases pattern with
    | var name => exact same name (List.mem_singleton_self _)
    | app name arguments => exact algebra.congruent name (evals_congr arguments same)
    | record label payload tail =>
        exact record_congr label
          (eval_congr payload (fun name member => same name (List.mem_append_left _ member)))
          (eval_congr tail (fun name member => same name (List.mem_append_right _ member)))
    | variant tag payload => exact variant_congr tag (eval_congr payload same)
    | join left right =>
        exact union_congr
          (eval_congr left (fun name member => same name (List.mem_append_left _ member)))
          (eval_congr right (fun name member => same name (List.mem_append_right _ member)))
    termination_by sizeOf pattern
  theorem evals_congr (patterns : List Pattern)
      (same : ∀ name ∈ variablesArgs patterns, Equivalent (first name) (last name)) :
      Aligned Equivalent (evals algebra first patterns) (evals algebra last patterns) := by
    cases patterns with
    | nil => exact .nil
    | cons head tail =>
        exact .cons
          (eval_congr head (fun name member => same name (List.mem_append_left _ member)))
          (evals_congr tail (fun name member => same name (List.mem_append_right _ member)))
    termination_by sizeOf patterns
end

mutual
  theorem eval_subst (pattern : Pattern) (capture : Nat → Pattern) :
      eval algebra variables (pattern.subst capture) =
        eval algebra (fun name => eval algebra variables (capture name)) pattern := by
    cases pattern with
    | var => rfl
    | app name arguments => exact congrArg (algebra.application name) (evals_subst arguments capture)
    | record label payload tail => simp only [Pattern.subst,eval,eval_subst payload capture,eval_subst tail capture]
    | variant tag payload => exact congrArg (variant tag) (eval_subst payload capture)
    | join first last => simp only [Pattern.subst,eval,eval_subst first capture,eval_subst last capture]
    termination_by sizeOf pattern
  theorem evals_subst (patterns : List Pattern) (capture : Nat → Pattern) :
      evals algebra variables (substArgs capture patterns) =
        evals algebra (fun name => eval algebra variables (capture name)) patterns := by
    cases patterns with
    | nil => rfl
    | cons head tail => simp only [substArgs,evals,eval_subst head capture,evals_subst tail capture]
    termination_by sizeOf patterns
end

mutual
  theorem subst_closed (pattern : Pattern) (capture : Nat → Pattern)
      (closed : ∀ name ∈ pattern.variables, (capture name).variables = []) :
      (pattern.subst capture).variables = [] := by
    cases pattern with
    | var name => exact closed name (List.mem_singleton_self _)
    | app name arguments => exact substs_closed arguments capture closed
    | record label payload tail | join payload tail =>
        exact List.append_eq_nil_iff.mpr
          ⟨subst_closed payload capture (fun name member => closed name (List.mem_append_left _ member)),
            subst_closed tail capture (fun name member => closed name (List.mem_append_right _ member))⟩
    | variant tag payload => exact subst_closed payload capture closed
    termination_by sizeOf pattern
  theorem substs_closed (patterns : List Pattern) (capture : Nat → Pattern)
      (closed : ∀ name ∈ variablesArgs patterns, (capture name).variables = []) :
      variablesArgs (substArgs capture patterns) = [] := by
    cases patterns with
    | nil => rfl
    | cons head tail =>
        exact List.append_eq_nil_iff.mpr
          ⟨subst_closed head capture (fun name member => closed name (List.mem_append_left _ member)),
          substs_closed tail capture (fun name member => closed name (List.mem_append_right _ member))⟩
    termination_by sizeOf patterns
end

theorem normalized_closed (closed : pattern.variables = []) : (normalize pattern).variables = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name member
  have present := GeneralPatternVariableProvenance.normalize_variables pattern member
  rw [closed] at present
  cases present

theorem normalized_subst_meaning (capture : Nat → Pattern)
    (same : ∀ name ∈ pattern.variables, Equivalent (variables name) (eval algebra (fun _ => .bottom) (capture name))) :
    Equivalent (eval algebra variables pattern)
      (eval algebra (fun _ => .bottom) (normalize (pattern.subst capture))) := by
  have instantiated := eval_congr (algebra := algebra) pattern same
  rw [← eval_subst pattern capture] at instantiated
  exact eqv_trans instantiated (normalize_sound _)

end Yulang.GeneralNominalCenteredHeadMatSemanticSubstitution
