import Yulang.CommonNominalFoundations
import Yulang.CaseValues

/-!
# A boundary for data-independent finite structural cast plans

One fixed recursive structural chain can contain arbitrarily many nominal
leaves. A registry with just `user_id -> int` needs one leaf conversion at
each such position. Every finite keep/chain/product/tag/branch plan has a
uniform finite conversion budget, so no one such plan converts every chain.

This is an obstruction to extending finite, data-independent structural plans
to all regular graphs. It does not show that recursive plans cannot exist, or
that B5's entire cast statement is false under a partial/recursive execution
interpretation. Source reachability of the example is not asserted here.
-/

namespace Yulang.CommonRegularCastObstruction

open CommonNominalCarrier

abbrev Value := CaseValues.Value Empty

def userId (number : Int) : Value := .nominal 7 0 (.record [(0, .literal (.int number))])

def source : Nat → Value
  | 0 => .variant 0 (.literal .unit)
  | count + 1 => .variant 1 (.pair (userId (Int.ofNat count)) (source count))

inductive TargetChain : Value → Prop where
  | nil : TargetChain (.variant 0 (.literal .unit))
  | cons : TargetChain tail → TargetChain (.variant 1 (.pair (.literal (.int number)) tail))

def wrappers : Value → Nat
  | .literal _ => 0
  | .pair first last => wrappers first + wrappers last
  | .record _ => 0
  | .variant _ payload => wrappers payload
  | .nominal _ _ _ => 1
  | .list _ => 0
termination_by value => sizeOf value

@[simp] theorem wrappers_source (count : Nat) : wrappers (source count) = count := by
  induction count with
  | zero => simp [source, wrappers]
  | succ count ih => simp [source, userId, wrappers, ih, Nat.add_comm]

theorem target_has_no_wrappers {value : Value} (typed : TargetChain value) : wrappers value = 0 := by
  induction typed with
  | nil => simp [wrappers]
  | cons _ ih => simp [wrappers, ih]

/-- Finite data plans made from the structural lifting operations. Nominal
arguments are opaque; the one declared conversion is for the whole user_id. -/
inductive Plan where
  | keep
  | unwrap
  | chain : Plan → Plan → Plan
  | pair : Plan → Plan → Plan
  | tag : Nat → Plan → Plan
  | branch : Plan → Plan → Plan

def Plan.budget : Plan → Nat
  | .keep => 0
  | .unwrap => 1
  | .chain first last | .pair first last => first.budget + last.budget
  | .tag _ payload => payload.budget
  | .branch nil cons => max nil.budget cons.budget

/-- Execution counts declared leaf conversions. A plan cannot silently drop
source components or map inside a nominal; both are excluded by this boundary. -/
inductive Runs : Plan → Value → Value → Nat → Prop where
  | keep : Runs .keep value value 0
  | unwrap : Runs .unwrap (userId number) (.literal (.int number)) 1
  | chain : Runs first input middle before → Runs last middle output after →
      Runs (.chain first last) input output (before + after)
  | pair : Runs first a a' before → Runs last b b' after →
      Runs (.pair first last) (.pair a b) (.pair a' b') (before + after)
  | tag : Runs payload value value' count →
      Runs (.tag label payload) (.variant label value) (.variant label value') count
  | branchNil : Runs nil value value' count →
      Runs (.branch nil cons) (.variant 0 value) (.variant 0 value') count
  | branchCons : Runs cons value value' count →
      Runs (.branch nil cons) (.variant 1 value) (.variant 1 value') count

theorem run_budget {plan : Plan} {input output : Value} {count : Nat}
    (run : Runs plan input output count) : count ≤ plan.budget := by
  induction run with
  | keep | unwrap => exact Nat.le_refl _
  | chain _ _ before after | pair _ _ before after =>
      exact Nat.add_le_add before after
  | tag _ ih => exact ih
  | branchNil _ ih => exact Nat.le_trans ih (Nat.le_max_left ..)
  | branchCons _ ih => exact Nat.le_trans ih (Nat.le_max_right ..)

theorem run_wrapper_count {plan : Plan} {input output : Value} {count : Nat}
    (run : Runs plan input output count) : wrappers input = wrappers output + count := by
  induction run with
  | keep => omega
  | unwrap => simp [userId, wrappers]
  | chain _ _ before after => omega
  | pair _ _ before after => simp only [wrappers]; omega
  | tag _ ih | branchNil _ ih | branchCons _ ih => simpa only [wrappers] using ih

/-- Any successful structural conversion of n source leaves uses exactly n
of the registered user_id-to-int conversions. -/
theorem chain_requires_each_conversion {plan : Plan} {output : Value} {count length : Nat}
    (run : Runs plan (source length) output count) (typed : TargetChain output) : count = length := by
  have exactCount := run_wrapper_count run
  rw [wrappers_source, target_has_no_wrappers typed, Nat.zero_add] at exactCount
  exact exactCount.symm

/-- A concrete failing length is computed from the finite plan itself. -/
theorem plan_fails_at_successor_budget (plan : Plan) :
    ¬ ∃ output count, Runs plan (source (plan.budget + 1)) output count ∧ TargetChain output := by
  rintro ⟨output, count, run, typed⟩
  have required := chain_requires_each_conversion run typed
  have bounded := run_budget run
  omega

theorem no_finite_structural_plan_for_all_chains :
    ¬ ∃ plan : Plan, ∀ length : Nat, ∃ output count,
      Runs plan (source length) output count ∧ TargetChain output := by
  rintro ⟨plan, allLengths⟩
  exact plan_fails_at_successor_budget plan (allLengths (plan.budget + 1))

/-- The lower bound is semantic: even allowing a different plan at each length,
there is no data-independent upper bound for this one boundary. -/
theorem no_data_independent_conversion_bound :
    ¬ ∃ bound : Nat, ∀ length : Nat, ∃ plan output count,
      Runs plan (source length) output count ∧ TargetChain output ∧ count ≤ bound := by
  rintro ⟨bound, allLengths⟩
  obtain ⟨plan, output, count, run, typed, bounded⟩ := allLengths (bound + 1)
  have required := chain_requires_each_conversion run typed
  omega

/-- Fixed two-state regular structural type descriptions for both endpoints.
The nominal leaf remains nominal, rather than being a variant encoding. -/
def graphBody (leaf : Ty) : Fin 2 → CommonNominalSyntax.Layer Row (Fin 2 ⊕ CommonNominalSyntax.State Row)
  | ⟨0, _⟩ => .union (.variant 0 (.inr (.node (.base .unit)))) (.variant 1 (.inl 1))
  | ⟨1, _⟩ => .pair (.inr (.node leaf)) (.inl 0)

def chainType (leaf : Ty) : Ty :=
  CommonNominalSyntax.graph Row (CommonNominalSyntax.closeBlock (graphBody leaf) 0)

def sourceType : Ty := chainType (nominal 7 [])
def targetType : Ty := chainType (.base .int)

end Yulang.CommonRegularCastObstruction

namespace Yulang.CommonRegularCastObstruction

def target : Nat → Value
  | 0 => .variant 0 (.literal .unit)
  | count + 1 => .variant 1 (.pair (.literal (.int (Int.ofNat count))) (target count))

def unrolledPlan : Nat → Plan
  | 0 => .keep
  | count + 1 => .branch .keep (.pair .unwrap (unrolledPlan count))

theorem each_length_converts (length : Nat) :
    Runs (unrolledPlan length) (source length) (target length) length := by
  induction length with
  | zero => exact .keep
  | succ count ih =>
      have run : Runs (.branch .keep (.pair .unwrap (unrolledPlan count)))
          (source (count + 1)) (target (count + 1)) (1 + count) :=
        .branchCons (.pair .unwrap ih)
      simpa only [unrolledPlan, Nat.add_comm] using run

theorem each_target_typed (length : Nat) : TargetChain (target length) := by
  induction length with
  | zero => exact .nil
  | succ count ih => exact .cons ih

@[simp] theorem unrolled_budget (length : Nat) : (unrolledPlan length).budget = length := by
  induction length with
  | zero => rfl
  | succ count ih => simp [unrolledPlan, Plan.budget, ih, Nat.add_comm]

end Yulang.CommonRegularCastObstruction
