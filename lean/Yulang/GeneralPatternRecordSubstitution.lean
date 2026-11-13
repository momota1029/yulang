import Yulang.GeneralPatternGroundSubstitution

/-! Record hiding commutes with counted substitution after normalization.
The template may contain records and variants; captures are unrestricted. -/
namespace Yulang.GeneralPatternRecordSubstitution
open GeneralDeclarationPatterns

theorem hide_commute (first last : Nat) (pattern : Pattern) :
    hide first (hide last pattern) = hide last (hide first pattern) := by
  cases pattern with
  | record label payload tail =>
    by_cases one : first = label <;> by_cases two : last = label <;>
      simp only [hide,one,two,ite_true,ite_false,hide_commute first last tail]
    all_goals simpa only [one,two] using hide_commute first last tail
  | _ => rfl

theorem hide_substitution (label : Nat) (pattern : Pattern) (capture : Nat → Pattern) :
    hide label (normalize (pattern.subst capture)) =
      hide label (normalize ((hide label pattern).subst capture)) := by
  cases pattern with
  | record key payload tail =>
    by_cases same : label = key
    · subst key
      simp only [hide,ite_true,Pattern.subst,normalize,hide_idempotent]
      exact hide_substitution label tail capture
    · simp only [hide,same,ite_false,Pattern.subst,normalize]
      rw [hide_commute label key,hide_commute label key]
      rw [hide_substitution label tail capture]
  | _ => rfl

mutual
  theorem normalize_template (pattern : Pattern) (complete : covered pattern = true)
      (capture : Nat → Pattern) :
      normalize (pattern.subst capture) = normalize ((normalize pattern).subst capture) := by
    cases pattern with
    | var name => rfl
    | join first last => cases complete
    | app key arguments =>
      simp only [Pattern.subst,normalize]
      exact congrArg (Pattern.app key) (normalize_templates arguments complete capture)
    | variant tag payload =>
      simp only [Pattern.subst,normalize]
      exact congrArg (Pattern.variant tag) (normalize_template payload complete capture)
    | record label payload tail =>
      have coveredParts : covered payload = true ∧ covered tail = true := by simpa only [covered,Bool.and_eq_true] using complete
      have left := normalize_template payload coveredParts.1 capture
      have right := normalize_template tail coveredParts.2 capture
      simp only [Pattern.subst,normalize]
      rw [left,right,hide_substitution label (normalize tail) capture]

  theorem normalize_templates (patterns : List Pattern) (complete : coveredArgs patterns = true)
      (capture : Nat → Pattern) :
      normalizeArgs (substArgs capture patterns) = normalizeArgs (substArgs capture (normalizeArgs patterns)) := by
    cases patterns with
    | nil => rfl
    | cons head tail =>
      have coveredParts : covered head = true ∧ coveredArgs tail = true := by simpa only [coveredArgs,Bool.and_eq_true] using complete
      simp only [substArgs,normalizeArgs,normalize_template head coveredParts.1 capture,
        normalize_templates tail coveredParts.2 capture]
end

theorem counted_template (patterns : List Pattern) (complete : coveredArgs patterns = true)
    (capture : Nat → Pattern) :
    counted (substArgs capture patterns) = counted (substArgs capture (normalizeArgs patterns)) :=
  congrArg encodeArgs (normalize_templates patterns complete capture)

theorem mass_template (patterns : List Pattern) (complete : coveredArgs patterns = true)
    (capture : Nat → Pattern) :
    GeneralNominalPatersonLineage.mass (substArgs capture patterns) =
      GeneralNominalPatersonLineage.mass (substArgs capture (normalizeArgs patterns)) :=
  congrArg Roles.argsSize (counted_template patterns complete capture)

end Yulang.GeneralPatternRecordSubstitution
