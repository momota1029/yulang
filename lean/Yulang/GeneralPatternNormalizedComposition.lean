import Yulang.GeneralNominalOpenCaptureLabels

/-! Composition of normalized source substitutions. Record hiding is
performed at the same source positions after either composition order. -/
namespace Yulang.GeneralPatternNormalizedComposition
open GeneralDeclarationPatterns GeneralPatternNormalForm GeneralPatternRecordSubstitution
open GeneralNominalTemplateSubstitution

mutual
  theorem subst_compose (pattern : Pattern) (first last : Nat → Pattern) :
      (pattern.subst first).subst last = pattern.subst (fun name => (first name).subst last) := by
    cases pattern with
    | var => rfl
    | app key arguments => exact congrArg (Pattern.app key) (args_compose arguments first last)
    | record key payload tail => simp only [Pattern.subst,subst_compose payload first last,subst_compose tail first last]
    | variant key payload => simp only [Pattern.subst,subst_compose payload first last]
    | join left right => simp only [Pattern.subst,subst_compose left first last,subst_compose right first last]
  theorem args_compose (patterns : List Pattern) (first last : Nat → Pattern) :
      substArgs last (substArgs first patterns) = substArgs (fun name => (first name).subst last) patterns := by
    cases patterns with
    | nil => rfl
    | cons head tail => simp only [substArgs,subst_compose head first last,args_compose tail first last]
end

mutual
  theorem normalize_images (pattern : Pattern) (covered : GeneralDeclarationPatterns.covered pattern = true)
      (capture : Nat → Pattern) (images : ∀ name, GeneralDeclarationPatterns.covered (capture name) = true) :
      normalize (pattern.subst (fun name => normalize (capture name))) = normalize (pattern.subst capture) := by
    cases pattern with
    | var name => exact idempotent_covered (capture name) (images name)
    | join => cases covered
    | app key arguments => exact congrArg (Pattern.app key) (normalize_args_images arguments covered capture images)
    | variant key payload => exact congrArg (Pattern.variant key) (normalize_images payload covered capture images)
    | record key payload tail =>
      have parts : GeneralDeclarationPatterns.covered payload = true ∧ GeneralDeclarationPatterns.covered tail = true :=
        (Bool.and_eq_true ..).mp covered
      simp only [Pattern.subst,normalize,normalize_images payload parts.1 capture images,
        normalize_images tail parts.2 capture images]
  theorem normalize_args_images (patterns : List Pattern) (covered : coveredArgs patterns = true)
      (capture : Nat → Pattern) (images : ∀ name, GeneralDeclarationPatterns.covered (capture name) = true) :
      normalizeArgs (substArgs (fun name => normalize (capture name)) patterns) = normalizeArgs (substArgs capture patterns) := by
    cases patterns with
    | nil => rfl
    | cons head tail =>
      have parts : GeneralDeclarationPatterns.covered head = true ∧ coveredArgs tail = true := (Bool.and_eq_true ..).mp covered
      simp only [substArgs,normalizeArgs,normalize_images head parts.1 capture images,
        normalize_args_images tail parts.2 capture images]
end

def compose (first last : Nat → Pattern) (name : Nat) : Pattern := normalize ((first name).subst last)

theorem normalized_compose (pattern : Pattern) (covered : GeneralDeclarationPatterns.covered pattern = true)
    (first last : Nat → Pattern)
    (one : ∀ name, GeneralDeclarationPatterns.covered (first name) = true)
    (two : ∀ name, GeneralDeclarationPatterns.covered (last name) = true) :
    normalize ((normalize (pattern.subst first)).subst last) = normalize (pattern.subst (compose first last)) := by
  rw [← normalize_template (pattern.subst first) (subst_covered pattern covered first one) last,subst_compose]
  exact (normalize_images pattern covered _ (fun name => subst_covered _ (one name) last two)).symm

theorem normalized_args_compose (patterns : List Pattern) (covered : coveredArgs patterns = true)
    (first last : Nat → Pattern)
    (one : ∀ name, GeneralDeclarationPatterns.covered (first name) = true)
    (two : ∀ name, GeneralDeclarationPatterns.covered (last name) = true) :
    normalizeArgs (substArgs last (normalizeArgs (substArgs first patterns))) =
      normalizeArgs (substArgs (compose first last) patterns) := by
  rw [← normalize_templates _ (args_subst_covered patterns covered first one),args_compose]
  exact (normalize_args_images patterns covered _ (fun name => subst_covered _ (one name) last two)).symm

theorem normal_args_idempotent (patterns : List Pattern) (covered : coveredArgs patterns = true) :
    normalizeArgs (normalizeArgs patterns) = normalizeArgs patterns :=
  args_fixed _ (args_normalized patterns covered)

end Yulang.GeneralPatternNormalizedComposition
