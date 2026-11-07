import Yulang.CommonRoleLinearClock

/-!
# Exact capture of finite machine terms from semantic Common matches

Pattern variables range over arbitrary Common types. When an injective
pair/variant pattern matches a finite ground machine term, every used variable
is equivalent to a finite captured subtree. The extraction is a real finite
syntax walk, not an arbitrary decoder of Common semantic types.
-/

namespace Yulang.CommonRoleLinearClock

open Common (Ty Equivalent)

private theorem ground_heads {first last : Ground}
    (same : Equivalent first.eval last.eval) :
    CommonRigidHeadInspection.head first.eval = CommonRigidHeadInspection.head last.eval := by
  have h := CommonRigidHeadInspection.rigid_heads
    (source := first.eval) (target := last.eval)
    (by cases first <;> rfl) (by cases last <;> rfl) same.1
  rcases h with impossible | impossible | equality
  · cases first <;> cases impossible
  · cases last <;> cases impossible
  · exact equality

theorem Ground.equivalent_iff (first last : Ground) :
    Equivalent first.eval last.eval ↔ first = last := by
  constructor
  · intro same
    induction first generalizing last with
    | int =>
      cases last with
      | int => rfl
      | pair _ _ | variant _ _ => cases ground_heads same
    | pair left right ihf ihl =>
      cases last with
      | int | variant _ _ => cases ground_heads same
      | pair a b =>
        have children := (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mp same
        rw [ihf a children.1, ihl b children.2]
    | variant tag payload ih =>
      cases last with
      | int | pair _ _ => cases ground_heads same
      | variant other child =>
        have forward := (CommonRigidHeadInspection.variant_iff tag other _ _).mp same.1
        have backward := (CommonRigidHeadInspection.variant_iff other tag _ _).mp same.2
        have tags := forward.1
        subst other
        rw [ih child ⟨forward.2, backward.2⟩]
  · intro same
    subst last
    exact Common.equivalent_refl _

theorem Pattern.eval_congr (pattern : Pattern) (first last : Nat → Ty)
    (agree : ∀ name, 0 < pattern.encode.occurrences name → Equivalent (first name) (last name)) :
    Equivalent (pattern.eval first) (pattern.eval last) := by
  induction pattern with
  | var name => exact agree name (by simp [Pattern.encode, Roles.Term.occurrences])
  | int => exact Common.equivalent_refl _
  | pair first last ihf ihl =>
    apply (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mpr
    constructor
    · apply ihf
      intro name occurs
      apply agree name
      simp only [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences, Nat.add_zero]
      omega
    · apply ihl
      intro name occurs
      apply agree name
      simp only [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences, Nat.add_zero]
      omega
  | variant tag payload ih =>
    apply (CommonCanonicalShapes.variant_equivalent_iff tag _ _).mpr
    apply ih
    intro name occurs
    apply agree name
    simpa [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences] using occurs

/-- Extract the first occurrence in the finite pattern. The choice is made
from occurrence counts, so no semantic equality test is needed. -/
def extract (name : Nat) : Pattern → Ground → Option Ground
  | .var found, value => if name = found then some value else none
  | .pair first last, .pair a b =>
      if 0 < first.encode.occurrences name then extract name first a else extract name last b
  | .variant _ payload, .variant _ child => extract name payload child
  | _, _ => none

private theorem int_not_pair (first last : Ty) :
    ¬ Equivalent (.base .int) (Common.pair first last) := by
  intro same
  have h := CommonRigidHeadInspection.rigid_heads rfl rfl same.1
  simp [CommonRigidHeadInspection.head, Common.pair] at h

private theorem int_not_variant (tag : Nat) (payload : Ty) :
    ¬ Equivalent (.base .int) (Common.variant tag payload) := by
  intro same
  have h := CommonRigidHeadInspection.rigid_heads rfl rfl same.1
  simp [CommonRigidHeadInspection.head, Common.variant] at h

private theorem pair_not_variant (first last payload : Ty) (tag : Nat) :
    ¬ Equivalent (Common.pair first last) (Common.variant tag payload) := by
  intro same
  have h := CommonRigidHeadInspection.rigid_heads rfl rfl same.1
  simp [CommonRigidHeadInspection.head, Common.pair, Common.variant] at h

theorem extract_semantic (pattern : Pattern) (ground : Ground) (assignment : Nat → Ty)
    (same : Equivalent (pattern.eval assignment) ground.eval) (name : Nat)
    (occurs : 0 < pattern.encode.occurrences name) :
    ∃ captured, extract name pattern ground = some captured ∧
      Equivalent (assignment name) captured.eval := by
  induction pattern generalizing ground with
  | var found =>
    have equal : name = found := by
      by_cases equal : name = found
      · exact equal
      · simp [Pattern.encode, Roles.Term.occurrences, equal] at occurs
    subst found
    exact ⟨ground, by simp [extract], same⟩
  | int => simp [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences] at occurs
  | pair first last ihf ihl =>
    cases ground with
    | int => exact False.elim (int_not_pair _ _ (Common.equivalent_symm same))
    | variant tag payload => exact False.elim (pair_not_variant _ _ _ tag same)
    | pair a b =>
      have children := (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mp same
      by_cases before : 0 < first.encode.occurrences name
      · obtain ⟨captured, extracted, agrees⟩ := ihf a children.1 before
        exact ⟨captured, by simp [extract, before, extracted], agrees⟩
      · have after : 0 < last.encode.occurrences name := by
          simp only [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences, Nat.add_zero] at occurs
          omega
        obtain ⟨captured, extracted, agrees⟩ := ihl b children.2 after
        exact ⟨captured, by simp [extract, before, extracted], agrees⟩
  | variant tag payload ih =>
    cases ground with
    | int => exact False.elim (int_not_variant tag _ (Common.equivalent_symm same))
    | pair first last => exact False.elim (pair_not_variant _ _ _ tag (Common.equivalent_symm same))
    | variant other child =>
      have forward := (CommonRigidHeadInspection.variant_iff tag other _ _).mp same.1
      have backward := (CommonRigidHeadInspection.variant_iff other tag _ _).mp same.2
      have childOccurs : 0 < payload.encode.occurrences name := by
        simpa [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences] using occurs
      obtain ⟨captured, extracted, agrees⟩ := ih child ⟨forward.2, backward.2⟩ childOccurs
      exact ⟨captured, extracted, agrees⟩

def matchingAssignment (pattern : Pattern) (ground : Ground) : Nat → Ground :=
  fun name => (extract name pattern ground).getD .int

theorem matchingAssignment_agrees (pattern : Pattern) (ground : Ground) (assignment : Nat → Ty)
    (same : Equivalent (pattern.eval assignment) ground.eval) (name : Nat)
    (occurs : 0 < pattern.encode.occurrences name) :
    Equivalent (assignment name) (matchingAssignment pattern ground name).eval := by
  obtain ⟨captured, extracted, agrees⟩ := extract_semantic pattern ground assignment same name occurs
  simpa [matchingAssignment, extracted] using agrees

theorem matchingAssignment_head (pattern : Pattern) (ground : Ground) (assignment : Nat → Ty)
    (same : Equivalent (pattern.eval assignment) ground.eval) :
    pattern.instantiate (matchingAssignment pattern ground) = ground := by
  apply (Ground.equivalent_iff _ _).mp
  rw [instantiate_eval]
  exact Common.equivalent_trans
    (Common.equivalent_symm (pattern.eval_congr assignment _
      (matchingAssignment_agrees pattern ground assignment same))) same

/-- An arbitrary Common match has a genuine finite ground substitution.
Every linear child has the same interpretation under that finite witness. -/
theorem finite_match_reflection (rule : Rule) (linear : Linear rule)
    (ground : Ground) (assignment : Nat → Ty)
    (same : Equivalent (rule.left.eval assignment) ground.eval) :
    rule.left.instantiate (matchingAssignment rule.left ground) = ground ∧
      Equivalent (rule.right.eval assignment)
        (rule.right.instantiate (matchingAssignment rule.left ground)).eval := by
  constructor
  · exact matchingAssignment_head rule.left ground assignment same
  · rw [instantiate_eval]
    apply rule.right.eval_congr
    intro name occurs
    apply matchingAssignment_agrees rule.left ground assignment same name
    have count := linear name
    omega

end Yulang.CommonRoleLinearClock
