import Yulang.GeneralPatternRecordSubstitution

/-! Count the normalized templates that the emitter actually consumes.
The conservative head count survives captured record tails; the full child
count bounds normalization from above. Captures are unrestricted. -/
namespace Yulang.GeneralPatternConservativeSubstitution
open GeneralDeclarationPatterns

def captureTerms (capture : Nat → Pattern) : Roles.Subst :=
  fun name => (normalize (capture name)).encode

theorem hide_size (label : Nat) (pattern : Pattern) :
    (hide label pattern).encode.size ≤ pattern.encode.size := by
  cases pattern with
  | record key payload tail =>
    have smaller := hide_size label tail
    by_cases same : label = key <;>
      simp only [hide,same,ite_true,ite_false,Pattern.encode,Roles.Term.size,Roles.argsSize] at * <;> omega
  | _ => exact Nat.le_refl _

mutual
  theorem substitution_bounds (pattern : Pattern) (complete : covered pattern = true)
      (capture : Nat → Pattern) :
      ((lower pattern).subst (captureTerms capture)).size ≤ (normalize (pattern.subst capture)).encode.size ∧
      (normalize (pattern.subst capture)).encode.size ≤ (pattern.encode.subst (captureTerms capture)).size := by
    cases pattern with
    | var name => exact ⟨Nat.le_refl _,Nat.le_refl _⟩
    | join first last => cases complete
    | app key arguments =>
      have bound := substitutions_bounds arguments complete capture
      simp only [lower,Pattern.encode,Pattern.subst,normalize,Roles.Term.subst,Roles.Term.size]
      exact ⟨Nat.add_le_add_left bound.1 1,Nat.add_le_add_left bound.2 1⟩
    | variant tag payload =>
      have bound := substitution_bounds payload complete capture
      simpa only [lower,Pattern.encode,Pattern.subst,normalize,Roles.Term.subst,
        Roles.substArgs,Roles.Term.size,Roles.argsSize,Nat.add_zero] using
        And.intro (Nat.add_le_add_left bound.1 1) (Nat.add_le_add_left bound.2 1)
    | record label payload tail =>
      have parts : covered payload = true ∧ covered tail = true := by
        simpa only [covered,Bool.and_eq_true] using complete
      have left := substitution_bounds payload parts.1 capture
      have right := substitution_bounds tail parts.2 capture
      have hidden := hide_size label (normalize (tail.subst capture))
      have positive := (hide label (normalize (tail.subst capture))).encode.size_pos
      simp only [lower,Pattern.encode,Pattern.subst,normalize,Roles.Term.subst,
        Roles.substArgs,Roles.Term.size,Roles.argsSize] at *
      omega

  theorem substitutions_bounds (patterns : List Pattern) (complete : coveredArgs patterns = true)
      (capture : Nat → Pattern) :
      Roles.argsSize (Roles.substArgs (captureTerms capture) (lowerArgs patterns)) ≤
        Roles.argsSize (counted (substArgs capture patterns)) ∧
      Roles.argsSize (counted (substArgs capture patterns)) ≤
        Roles.argsSize (Roles.substArgs (captureTerms capture) (encodeArgs patterns)) := by
    cases patterns with
    | nil => exact ⟨Nat.le_refl _,Nat.le_refl _⟩
    | cons head tail =>
      have parts : covered head = true ∧ coveredArgs tail = true := by
        simpa only [coveredArgs,Bool.and_eq_true] using complete
      have first := substitution_bounds head parts.1 capture
      have rest := substitutions_bounds tail parts.2 capture
      simp only [lowerArgs,encodeArgs,counted,substArgs,normalizeArgs,Roles.substArgs,Roles.argsSize] at *
      omega
end

theorem normalized_descent (head child : List Pattern)
    (complete : CountsCovered head child) (smaller : ConservativeSmaller head child)
    (capture : Nat → Pattern) :
    GeneralNominalPatersonLineage.mass (substArgs capture (normalizeArgs child)) <
      GeneralNominalPatersonLineage.mass (substArgs capture (normalizeArgs head)) := by
  let declaration : Roles.Impl := ⟨0,lowerArgs (normalizeArgs head),[⟨0,counted child⟩],0⟩
  have well : declaration.WellFormed := by
    intro clause member
    cases List.mem_singleton.mp member
    exact (CheckedRoles.checkCondition_exact _ _).mp smaller
  have strict := Roles.size_decreases well (List.mem_singleton_self _) (captureTerms capture)
  have below := (substitutions_bounds (normalizeArgs child) complete.2 capture).2
  have above := (substitutions_bounds (normalizeArgs head) complete.1 capture).1
  change Roles.argsSize (Roles.substArgs (captureTerms capture) (counted child)) <
    Roles.argsSize (Roles.substArgs (captureTerms capture) (lowerArgs (normalizeArgs head))) at strict
  exact Nat.lt_of_le_of_lt below (Nat.lt_of_lt_of_le strict above)

theorem checked_normalized_descent
    (checked : GeneralDeclarations.DeclarationChecked constructors roles declaration)
    (clause : GeneralDeclarations.Clause) (present : clause ∈ declaration.requirements)
    (capture : Nat → Pattern) :
    GeneralNominalPatersonLineage.mass (substArgs capture (normalizeArgs clause.arguments)) <
      GeneralNominalPatersonLineage.mass (substArgs capture (normalizeArgs declaration.head)) :=
  normalized_descent _ _ (checked.countsCovered clause present) (checked.conservative clause present) capture

end Yulang.GeneralPatternConservativeSubstitution
