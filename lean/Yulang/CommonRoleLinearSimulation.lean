import Yulang.CommonRoleLinearMatching

/-!
# Exact regular-clock interpretation of compiled linear rewrite rules

Semantic goals below interpret the two actual arguments of `compile`:
the regular clock and the machine data. Head matching uses arbitrary Common
substitutions. Finite matching reflection proves that a matched child is
equivalent to another finite machine configuration at the same regular clock.
-/

namespace Yulang.CommonRoleLinearClock

open Common (Ty Equivalent)

def clock : Ty := CommonRoleRegularObstructions.loop

def wrapTy : Nat → Ty → Ty
  | 0, value => value
  | count + 1, value => Common.variant 7 (wrapTy count value)

theorem wrapPattern_eval (count : Nat) (pattern : Pattern) (assignment : Nat → Ty) :
    (wrapPattern count pattern).eval assignment = wrapTy count (pattern.eval assignment) := by
  induction count <;> simp_all [wrapPattern, Pattern.eval, wrapTy]

theorem clock_unfold : Equivalent clock (Common.variant 7 clock) :=
  CommonRoleRegularObstructions.loop_unfold

theorem wrapped_clock (count : Nat) : Equivalent (wrapTy count clock) clock := by
  induction count with
  | zero => exact Common.equivalent_refl _
  | succ count ih =>
    exact Common.equivalent_trans
      ((CommonCanonicalShapes.variant_equivalent_iff 7 _ _).mpr ih)
      (Common.equivalent_symm clock_unfold)

theorem clock_cancel (count : Nat) (value : Ty)
    (same : Equivalent (wrapTy count value) clock) : Equivalent value clock := by
  induction count with
  | zero => exact same
  | succ count ih =>
    apply ih
    exact (CommonCanonicalShapes.variant_equivalent_iff 7 _ _).mp
      (Common.equivalent_trans same clock_unfold)

def clockAssignment (rule : Rule) (assignment : Nat → Ground) : Nat → Ty :=
  fun name => if name = rule.fresh then clock else (assignment name).eval

theorem clockAssignment_eval (rule : Rule) (pattern : Pattern)
    (bound : pattern.encode.bound ≤ rule.fresh) (assignment : Nat → Ground) :
    Equivalent (pattern.eval (clockAssignment rule assignment)) (pattern.instantiate assignment).eval := by
  rw [instantiate_eval]
  apply pattern.eval_congr
  intro name occurs
  have different : name ≠ rule.fresh := by
    intro same
    subst name
    have absent := pattern.encode.occurrences_above_bound rule.fresh bound
    omega
  simp [clockAssignment, different, Common.equivalent_refl]

structure SemanticGoal where
  role : Nat
  clock : Ty
  value : Ty

def GoalEquivalent (first last : SemanticGoal) : Prop :=
  first.role = last.role ∧ Equivalent first.clock last.clock ∧ Equivalent first.value last.value

theorem GoalEquivalent.refl (goal : SemanticGoal) : GoalEquivalent goal goal :=
  ⟨rfl, Common.equivalent_refl _, Common.equivalent_refl _⟩

theorem GoalEquivalent.symm {first last : SemanticGoal} (same : GoalEquivalent first last) :
    GoalEquivalent last first :=
  ⟨same.1.symm, Common.equivalent_symm same.2.1, Common.equivalent_symm same.2.2⟩

theorem GoalEquivalent.trans {first middle last : SemanticGoal}
    (before : GoalEquivalent first middle) (after : GoalEquivalent middle last) :
    GoalEquivalent first last :=
  ⟨before.1.trans after.1, Common.equivalent_trans before.2.1 after.2.1,
    Common.equivalent_trans before.2.2 after.2.2⟩

def goalOf (configuration : Configuration) : SemanticGoal :=
  ⟨configuration.role, clock, configuration.value.eval⟩

def headGoal (rule : Rule) (assignment : Nat → Ty) : SemanticGoal :=
  ⟨rule.source, (wrapPattern rule.padding (.var rule.fresh)).eval assignment,
    rule.left.eval assignment⟩

def childGoal (rule : Rule) (assignment : Nat → Ty) : SemanticGoal :=
  ⟨rule.target, assignment rule.fresh, rule.right.eval assignment⟩

def HeadMatches (rule : Rule) (goal : SemanticGoal) (assignment : Nat → Ty) : Prop :=
  GoalEquivalent (headGoal rule assignment) goal

def InstanceStep (rule : Rule) (source target : SemanticGoal) : Prop :=
  ∃ assignment : Nat → Ty,
    HeadMatches rule source assignment ∧ GoalEquivalent (childGoal rule assignment) target

/-- These semantic head and child patterns are exactly the ones in the real
compiled `Roles.Impl`, including the source and target role identifiers. -/
theorem compiled_patterns (key : Nat) (rule : Rule) :
    (compile key rule).role = rule.source ∧
    (compile key rule).head =
      [wrapPattern rule.padding (.var rule.fresh), rule.left].map Pattern.encode ∧
    (compile key rule).constraints =
      [⟨rule.target, [Pattern.var rule.fresh, rule.right].map Pattern.encode⟩] :=
  ⟨rfl, rfl, rfl⟩

/-- Arbitrary semantic head matches cannot escape the finite machine states.
The canonical finite capture supplies an actual independent machine step. -/
theorem matched_child_finite (rule : Rule) (linear : Linear rule)
    (source : Configuration) (assignment : Nat → Ty)
    (matched : HeadMatches rule (goalOf source) assignment) :
    ∃ target : Configuration,
      rule.Step source target ∧ GoalEquivalent (childGoal rule assignment) (goalOf target) := by
  obtain ⟨sourceRole, clockMatch, dataMatch⟩ := matched
  have reflected := finite_match_reflection rule linear source.value assignment dataMatch
  let finite := matchingAssignment rule.left source.value
  refine ⟨⟨rule.target, rule.right.instantiate finite⟩, ?_, ?_⟩
  · exact ⟨finite, sourceRole.symm, rfl, reflected.1, rfl⟩
  · refine ⟨rfl, ?_, reflected.2⟩
    apply clock_cancel rule.padding (assignment rule.fresh)
    simpa [headGoal, goalOf, wrapPattern_eval, Pattern.eval] using clockMatch

theorem finite_step_instance (rule : Rule) (source target : Configuration)
    (step : rule.Step source target) : InstanceStep rule (goalOf source) (goalOf target) := by
  obtain ⟨assignment, sourceRole, targetRole, sourceData, targetData⟩ := step
  refine ⟨clockAssignment rule assignment, ?_, ?_⟩
  · refine ⟨sourceRole.symm, ?_, ?_⟩
    · simpa [headGoal, goalOf, wrapPattern_eval, Pattern.eval, clockAssignment] using
        wrapped_clock rule.padding
    · have agrees := clockAssignment_eval rule rule.left (Nat.le_max_left ..) assignment
      simpa [headGoal, goalOf, sourceData] using agrees
  · refine ⟨targetRole.symm, ?_, ?_⟩
    · simp [childGoal, goalOf, clockAssignment, Common.equivalent_refl]
    · have agrees := clockAssignment_eval rule rule.right (Nat.le_max_right ..) assignment
      simpa [childGoal, goalOf, targetData] using agrees

theorem instanceStep_iff (rule : Rule) (linear : Linear rule) (source target : Configuration) :
    InstanceStep rule (goalOf source) (goalOf target) ↔ rule.Step source target := by
  constructor
  · rintro ⟨assignment, matched, child⟩
    obtain ⟨finite, step, agrees⟩ := matched_child_finite rule linear source assignment matched
    have same := GoalEquivalent.trans (GoalEquivalent.symm agrees) child
    have role : finite.role = target.role := same.1
    have value : finite.value = target.value := (Ground.equivalent_iff _ _).mp same.2.2
    have equal : finite = target := by cases finite; cases target; simp_all
    subst finite
    exact step
  · exact finite_step_instance rule source target

end Yulang.CommonRoleLinearClock
