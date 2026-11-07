import Yulang.CommonPatternBoundedGeneration
import Yulang.CommonPatternAllocation

/-! One shared source allocator retains each default row constraint under
all local slot lifts. The cap is a free symbolic row, not a parameter filter. -/

namespace Yulang.CommonPatternBoundedAllocation

set_option backward.isDefEq.respectTransparency false

open Core.PresenceGeneration
open CommonPatternEnvironment
open CommonPatternGeneration (renameBindings evalTypes_rename)
open CommonPatternAllocation (Slots ambient assignment close close_exact bindingSlots bindingValues
  bindingSlots_eval bindingValues_complete assignment_ambient)
open CasePatterns (Pattern)
open CommonPatternBoundedGeneration (DefaultTyping)

def constraints (pattern : Pattern Empty Inference.Expr) (cap : RowTerm α) (environment : SchemeEnv α)
    (priorBindings : NamedTerms α) (input : TyTerm α) : Formula (Slots α pattern.names.length) :=
  CommonPatternBoundedGeneration.generatePattern pattern (cap.rename (ambient pattern.names.length)) (environment.rename (ambient pattern.names.length))
    (renameBindings (ambient pattern.names.length) priorBindings)
    (input.rename (ambient pattern.names.length)) (bindingSlots pattern.names)

def generateAllocatedPattern (pattern : Pattern Empty Inference.Expr) (cap : RowTerm α) (environment : SchemeEnv α)
    (priorBindings : NamedTerms α) (input : TyTerm α) : Formula α :=
  close pattern.names.length (constraints pattern cap environment priorBindings input)

theorem constraints_exact (pattern : Pattern Empty Inference.Expr) (cap : RowTerm α)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α)
    (values : Fin pattern.names.length → Comp Common.model) :
    (constraints pattern cap symbolic priorBindings input).Holds Common.model (assignment ρ values) ↔
      CommonAlignedPatternTyping.RawTyping (DefaultTyping semantic (cap.eval Common.model ρ)) (evalTypes ρ priorBindings) pattern
        (input.eval Common.model ρ) (bindingValues pattern.names values) := by
  simpa only [constraints, evalTypes_rename, TyTerm.eval_rename, RowTerm.eval_rename, assignment_ambient,
    bindingSlots_eval] using
      CommonPatternBoundedGeneration.generatePattern_exact pattern (cap.rename (ambient pattern.names.length)) (assignment ρ values)
        (symbolic.rename (ambient pattern.names.length)) semantic
        (outer.rename _ _ (assignment_ambient ρ values))
        (renameBindings (ambient pattern.names.length) priorBindings)
        (input.rename (ambient pattern.names.length)) (bindingSlots pattern.names)

/-- The actual source traversal allocates every output binder jointly, for
arbitrary source patterns, captured environments, subject types, and free
ambient assignments. The independent judgment retains its stated boundaries. -/
theorem generateAllocatedPattern_exact (pattern : Pattern Empty Inference.Expr) (cap : RowTerm α)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α) :
    (generateAllocatedPattern pattern cap symbolic priorBindings input).Holds Common.model ρ ↔
      ∃ bindings, CommonAlignedPatternTyping.RawTyping (DefaultTyping semantic (cap.eval Common.model ρ)) (evalTypes ρ priorBindings)
        pattern (input.eval Common.model ρ) bindings := by
  simp only [generateAllocatedPattern, close_exact,
    constraints_exact pattern cap ρ symbolic semantic outer priorBindings input]
  constructor
  · rintro ⟨values, typed⟩; exact ⟨_, typed⟩
  · rintro ⟨bindings, typed⟩
    obtain ⟨values, same⟩ := bindingValues_complete pattern.names bindings typed.binding_names.symm
    exact ⟨values, by simpa only [same] using typed⟩

/-- Completeness recovers an arbitrarily prescribed independent result list
literally, rather than merely choosing some successful output environment. -/
theorem allocated_bindings_exact (pattern : Pattern Empty Inference.Expr) (cap : RowTerm α)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α) (bindings : NamedTypes) :
    (∃ values : Fin pattern.names.length → Comp Common.model,
      (constraints pattern cap symbolic priorBindings input).Holds Common.model (assignment ρ values) ∧
        bindingValues pattern.names values = bindings) ↔
      CommonAlignedPatternTyping.RawTyping (DefaultTyping semantic (cap.eval Common.model ρ)) (evalTypes ρ priorBindings)
        pattern (input.eval Common.model ρ) bindings := by
  simp only [constraints_exact pattern cap ρ symbolic semantic outer priorBindings input]
  constructor
  · rintro ⟨values, typed, same⟩; exact same ▸ typed
  · intro typed
    obtain ⟨values, same⟩ := bindingValues_complete pattern.names bindings typed.binding_names.symm
    exact ⟨values, same.symm ▸ typed, same⟩

/-- A consumer is inserted inside the same binder scope. In particular a guard
or body cannot accidentally receive an independently chosen output list. -/
def withPattern (pattern : Pattern Empty Inference.Expr) (cap : RowTerm α) (environment : SchemeEnv α)
    (priorBindings : NamedTerms α) (input : TyTerm α)
    (consumer : Formula (Slots α pattern.names.length)) : Formula α :=
  close pattern.names.length (.and (constraints pattern cap environment priorBindings input) consumer)

theorem withPattern_exact (pattern : Pattern Empty Inference.Expr) (cap : RowTerm α)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α)
    (consumer : Formula (Slots α pattern.names.length)) :
    (withPattern pattern cap symbolic priorBindings input consumer).Holds Common.model ρ ↔
      ∃ values : Fin pattern.names.length → Comp Common.model,
        CommonAlignedPatternTyping.RawTyping (DefaultTyping semantic (cap.eval Common.model ρ)) (evalTypes ρ priorBindings)
          pattern (input.eval Common.model ρ) (bindingValues pattern.names values) ∧
        consumer.Holds Common.model (assignment ρ values) := by
  simp only [withPattern, close_exact, Formula.Holds,
    constraints_exact pattern cap ρ symbolic semantic outer priorBindings input]

def generateCheckedPattern (pattern : Pattern Empty Inference.Expr) (cap : RowTerm α) (environment : SchemeEnv α)
    (priorBindings : NamedTerms α) (input : TyTerm α) : Formula α :=
  if PatternBindingChecks.check pattern then
    generateAllocatedPattern pattern cap environment priorBindings input
  else .bot

/-- The actual Q7/name-set check and the aligned independent source rules,
for every original environment, default expression, subject type and ambient
assignment. This remains the structural value/environment fragment of B2. -/
theorem generateCheckedPattern_exact (pattern : Pattern Empty Inference.Expr) (cap : RowTerm α)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α) :
    (generateCheckedPattern pattern cap symbolic priorBindings input).Holds Common.model ρ ↔
      ∃ bindings, CommonAlignedPatternTyping.Typing (DefaultTyping semantic (cap.eval Common.model ρ)) (evalTypes ρ priorBindings)
        pattern (input.eval Common.model ρ) bindings := by
  cases checked : PatternBindingChecks.check pattern with
  | false =>
      have invalid : ¬ PatternBindingChecks.NamesValid pattern := by
        intro h
        have accepted := (PatternBindingChecks.check_exact pattern).mpr h
        rw [checked] at accepted
        cases accepted
      simp only [generateCheckedPattern, checked, Bool.false_eq_true, ↓reduceIte,
        Formula.Holds, CommonAlignedPatternTyping.Typing, invalid, false_and, exists_false]
  | true =>
      have valid := (PatternBindingChecks.check_exact pattern).mp checked
      simp only [generateCheckedPattern, checked, ↓reduceIte,
        generateAllocatedPattern_exact pattern cap ρ symbolic semantic outer,
        CommonAlignedPatternTyping.Typing, valid, true_and]

end Yulang.CommonPatternBoundedAllocation
