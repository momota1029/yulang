import Yulang.CommonRoleLinearInterpreterRules
import Yulang.CommonRoleLinearSubcodes

/-! Finite program compilation and exact root-rewrite execution. -/

namespace Yulang.CommonRoleLinearProgram

open CommonRoleComputation (Tree Code Eval)
open CommonRoleLinearClock (Ground Pattern Rule Configuration Linear Step)
open CommonRoleLinearInterpreter (Kont Resume CopyKont State next)
open CommonRoleLinearInterpreterRules
open CommonRoleLinearSubcodes

def rules (code : Code) : List Rule := genericRules ++ (subcodes code).flatMap entryRules

theorem generic_member (code : Code) {rule : Rule} (member : rule ∈ genericRules) :
    rule ∈ rules code := List.mem_append.mpr (Or.inl member)

theorem entry_member {program code : Code} (member : code ∈ subcodes program)
    {rule : Rule} (entry : rule ∈ entryRules code) : rule ∈ rules program :=
  List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨code, member, entry⟩))

theorem rules_linear (code : Code) : ∀ rule ∈ rules code, Linear rule := by
  intro rule member
  rcases List.mem_append.mp member with generic | entry
  · exact generic_linear rule generic
  · obtain ⟨part, _, selected⟩ := List.mem_flatMap.mp entry
    exact entry_linear part rule selected

def compatible : Pattern → Pattern → Bool
  | .var _, _ | _, .var _ => true
  | .int, .int => true
  | .pair a b, .pair c d => compatible a c && compatible b d
  | .variant tag a, .variant other b => decide (tag = other) && compatible a b
  | _, _ => false

theorem compatible_of_equal (first last : Pattern) (σ τ : Nat → Ground)
    (same : first.instantiate σ = last.instantiate τ) : compatible first last = true := by
  induction first generalizing last with
  | var name => rfl
  | int => cases last <;> simp_all [compatible, Pattern.instantiate]
  | pair a b iha ihb =>
      cases last <;> simp_all [compatible, Pattern.instantiate]
  | variant tag payload ih =>
      cases last <;> simp_all [compatible, Pattern.instantiate]

theorem generic_matches_unique {first last : Rule}
    (firstMember : first ∈ genericRules) (lastMember : last ∈ genericRules)
    (σ τ : Nat → Ground) (sameRole : first.source = last.source)
    (same : first.left.instantiate σ = last.left.instantiate τ) : first = last := by
  have checked : genericRules.all (fun a => genericRules.all (fun b =>
      decide (a = b) || !(decide (a.source = b.source) && compatible a.left b.left))) = true := by
    decide +kernel
  have pairCheck := (List.all_eq_true.mp ((List.all_eq_true.mp checked) first firstMember)) last lastMember
  have shape := compatible_of_equal first.left last.left σ τ same
  simpa [sameRole, shape] using pairCheck

theorem generic_source {rule : Rule} (member : rule ∈ genericRules) :
    rule.source ≠ 0 ∧ rule.source ≠ 1 := by
  have checked : genericRules.all (fun r => decide (r.source ≠ 0 ∧ r.source ≠ 1)) = true := by decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp checked) rule member)

theorem entry_source (code : Code) {rule : Rule} (member : rule ∈ entryRules code) : rule.source = 1 := by
  cases code <;> simp only [entryRules, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals rfl

theorem entry_control (code : Code) {rule : Rule} (member : rule ∈ entryRules code)
    (σ : Nat → Ground) : ∃ rest, rule.left.instantiate σ = .pair code.encode rest := by
  cases code <;> simp only [entryRules, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals simp [Pattern.instantiate]

theorem same_code_entry_unique (code : Code) {first last : Rule}
    (firstMember : first ∈ entryRules code) (lastMember : last ∈ entryRules code)
    (σ τ : Nat → Ground) (same : first.left.instantiate σ = last.left.instantiate τ) : first = last := by
  cases code <;> simp only [entryRules, List.mem_cons, List.not_mem_nil, or_false] at firstMember lastMember
  all_goals rcases firstMember with rfl | rfl
  all_goals rcases lastMember with rfl | rfl
  all_goals first | rfl | simp [Pattern.instantiate] at same

theorem entry_matches_unique {code other : Code} {first last : Rule}
    (firstMember : first ∈ entryRules code) (lastMember : last ∈ entryRules other)
    (σ τ : Nat → Ground) (same : first.left.instantiate σ = last.left.instantiate τ) : first = last := by
  obtain ⟨a, ha⟩ := entry_control code firstMember σ
  obtain ⟨b, hb⟩ := entry_control other lastMember τ
  have codes : code.encode = other.encode := Ground.pair.inj (ha.symm.trans (same.trans hb)) |>.1
  have codeSame := code_encode_injective codes
  subst other
  exact same_code_entry_unique code firstMember lastMember σ τ same

/-- No two distinct source rules match one configuration. This is stronger
than having one selected next state and is needed for role nonambiguity. -/
theorem rules_matches_unique (program : Code) {first last : Rule}
    (firstMember : first ∈ rules program) (lastMember : last ∈ rules program)
    (σ τ : Nat → Ground) (sameRole : first.source = last.source)
    (same : first.left.instantiate σ = last.left.instantiate τ) : first = last := by
  rcases List.mem_append.mp firstMember with firstGeneric | firstEntry
  · rcases List.mem_append.mp lastMember with lastGeneric | lastEntry
    · exact generic_matches_unique firstGeneric lastGeneric σ τ sameRole same
    · obtain ⟨code, _, member⟩ := List.mem_flatMap.mp lastEntry
      exact False.elim ((generic_source firstGeneric).2 (sameRole.trans (entry_source code member)))
  · obtain ⟨code, _, member⟩ := List.mem_flatMap.mp firstEntry
    rcases List.mem_append.mp lastMember with lastGeneric | lastEntry
    · exact False.elim ((generic_source lastGeneric).2 (sameRole.symm.trans (entry_source code member)))
    · obtain ⟨other, _, otherMember⟩ := List.mem_flatMap.mp lastEntry
      exact entry_matches_unique member otherMember σ τ same

theorem no_terminal_source (program : Code) {rule : Rule} (member : rule ∈ rules program) :
    rule.source ≠ 0 := by
  rcases List.mem_append.mp member with generic | entry
  · exact (generic_source generic).1
  · obtain ⟨code, _, selected⟩ := List.mem_flatMap.mp entry
    rw [entry_source code selected]
    decide

theorem images_agree (pattern : Pattern) (σ τ : Nat → Ground)
    (same : pattern.instantiate σ = pattern.instantiate τ) (name : Nat)
    (used : 0 < pattern.encode.occurrences name) : σ name = τ name := by
  induction pattern with
  | var other =>
      simp only [Pattern.encode, Roles.Term.occurrences] at used
      have equal : name = other := by split at used <;> omega
      subst other
      exact same
  | int => simp [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences] at used
  | pair first last ihFirst ihLast =>
      have both := Ground.pair.inj same
      by_cases left : 0 < first.encode.occurrences name
      · exact ihFirst both.1 left
      · apply ihLast both.2
        simp only [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences, Nat.add_zero] at used
        omega
  | variant tag payload ih =>
      apply ih (Ground.variant.inj same).2
      simpa [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences] using used

theorem instantiate_congr (pattern : Pattern) (σ τ : Nat → Ground)
    (agree : ∀ name, 0 < pattern.encode.occurrences name → σ name = τ name) :
    pattern.instantiate σ = pattern.instantiate τ := by
  induction pattern with
  | var name => exact agree name (by simp [Pattern.encode, Roles.Term.occurrences])
  | int => rfl
  | pair first last ihFirst ihLast =>
      change Ground.pair (first.instantiate σ) (last.instantiate σ) =
        Ground.pair (first.instantiate τ) (last.instantiate τ)
      congr 1
      · apply ihFirst
        intro name used
        apply agree name
        simp only [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences, Nat.add_zero]
        omega
      · apply ihLast
        intro name used
        apply agree name
        simp only [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences, Nat.add_zero]
        omega
  | variant tag payload ih =>
      apply congrArg (Ground.variant tag)
      apply ih
      intro name used
      apply agree name
      simpa [Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences] using used

theorem linear_step_deterministic {rule : Rule} (linear : Linear rule)
    {source first last : Configuration} (before : rule.Step source first)
    (after : rule.Step source last) : first = last := by
  obtain ⟨σ, _, firstRole, firstHead, firstValue⟩ := before
  obtain ⟨τ, _, lastRole, lastHead, lastValue⟩ := after
  have rightSame : rule.right.instantiate σ = rule.right.instantiate τ := by
    apply instantiate_congr
    intro name used
    apply images_agree rule.left σ τ (firstHead.trans lastHead.symm) name
    have := linear name
    omega
  cases first
  cases last
  simp_all

theorem step_deterministic (program : Code) {source first last : Configuration}
    (before : Step (rules program) source first) (after : Step (rules program) source last) : first = last := by
  obtain ⟨a, ha, sa⟩ := before
  obtain ⟨b, hb, sb⟩ := after
  obtain ⟨σ, roleA, firstRole, headA, bodyA⟩ := sa
  obtain ⟨τ, roleB, lastRole, headB, bodyB⟩ := sb
  have same := rules_matches_unique program ha hb σ τ (roleA.symm.trans roleB) (headA.trans headB.symm)
  subst b
  exact linear_step_deterministic (rules_linear program a ha)
    ⟨σ, roleA, firstRole, headA, bodyA⟩ ⟨τ, roleB, lastRole, headB, bodyB⟩

end Yulang.CommonRoleLinearProgram
