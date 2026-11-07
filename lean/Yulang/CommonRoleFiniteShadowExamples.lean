import Yulang.CommonRoleFiniteShadowSemantic

/-! One role and one impl suffice to invalidate raw finite-tree descent.
The zero-variable loop is the smallest component-count illustration; the
separate growing example also defeats exact-goal caches. Neither example
alone proves undecidability; the finite program family does. -/

namespace Yulang.CommonRoleFiniteShadowExamples

open CommonRoleInspectedSemantics
open CommonRoleFiniteShadowRegistry (required dataGoal)

def loopHead : Pattern := .record .int (.record .int .empty)
def loopChild : Pattern := required .int
def loopImpl : Roles.Impl := ⟨0, [loopHead.encode], [⟨0, [loopChild.encode]⟩], 0⟩
def loopGoal : Goal := dataGoal 0 .int

theorem loop_sizes : Roles.argsSize loopImpl.head = 5 ∧ Roles.argsSize [loopChild.encode] = 3 := by
  decide +kernel

theorem loop_accepted : CheckedRoles.checkImpl loopImpl = true := by decide +kernel

theorem loop_ready : Ready [loopImpl] loopGoal := finite_ready _ _ rfl

theorem loop_matches (assignment : Nat → Common.Ty) : Matches loopImpl loopGoal assignment := by
  exact ⟨rfl, _, _, rfl, interpret_encode loopHead assignment,
    Common.common_shadowed_head_equivalent 0 (.base .int) (.base .int) Common.emptyRecord⟩

theorem loop_child (assignment : Nat → Description) :
    interpretGoal ⟨0, [loopChild.encode]⟩ assignment = some loopGoal := by
  simp [interpretGoal, loopChild, required, instantiate, loopGoal, dataGoal]

def growingHead : Pattern := .record (.var 0) (.record .int .empty)
def growingChild : Pattern := required (.variant 7 (.var 0))
def growingImpl : Roles.Impl := ⟨0, [growingHead.encode], [⟨0, [growingChild.encode]⟩], 0⟩

def payload : Nat → Description
  | 0 => .int
  | count + 1 => .variant 7 (payload count)

def chain (count : Nat) : Goal := dataGoal 0 (payload count)

theorem growing_sizes : Roles.argsSize growingImpl.head = 5 ∧ Roles.argsSize [growingChild.encode] = 4 := by
  decide +kernel

theorem growing_accepted : CheckedRoles.checkImpl growingImpl = true := by decide +kernel

/-- A proposal probe, not a change to the actual declaration checker. -/
theorem normalized_examples_rejected :
    CheckedRoles.checkImpl
      ⟨0, [(loopHead.visible false).encode], [⟨0, [(loopChild.visible false).encode]⟩], 0⟩ = false ∧
    CheckedRoles.checkImpl
      ⟨0, [(growingHead.visible false).encode], [⟨0, [(growingChild.visible false).encode]⟩], 0⟩ = false := by
  decide +kernel

theorem payload_finite (count : Nat) : (payload count).finite = true := by
  induction count <;> simp_all [payload, Description.finite]

theorem chain_ready (count : Nat) : Ready [growingImpl] (chain count) :=
  finite_ready _ _ (by simpa [chain, dataGoal, Description.finite] using payload_finite count)

theorem growing_step (count : Nat) :
    Matches growingImpl (chain count) (fun _ => (payload count).eval) ∧
    interpretGoal ⟨0, [growingChild.encode]⟩ (fun _ => payload count) = some (chain (count + 1)) := by
  constructor
  · exact ⟨rfl, _, _, rfl, interpret_encode growingHead _,
      Common.common_shadowed_head_equivalent 0 (payload count).eval (.base .int) Common.emptyRecord⟩
  · simp [interpretGoal, growingChild, required, instantiate, chain, dataGoal, payload]

theorem payload_eval (count : Nat) : (payload count).eval = CommonRoleRegularObstructions.growing count := by
  induction count <;> simp_all [payload, Description.eval, CommonRoleRegularObstructions.growing,
    CommonRoleRegularObstructions.wrap]

theorem chain_equivalent_iff (first last : Nat) :
    Common.Equivalent (chain first).argument.eval (chain last).argument.eval ↔ first = last := by
  change Common.Equivalent (Common.required 0 (payload first).eval) (Common.required 0 (payload last).eval) ↔ _
  rw [CommonCanonicalShapes.required_equivalent_iff, payload_eval, payload_eval]
  exact CommonRoleRegularObstructions.growing_equivalent_iff first last

theorem no_natural_descent_measure :
    ¬ ∃ measure : Goal → Nat, ∀ count, measure (chain (count + 1)) < measure (chain count) := by
  rintro ⟨measure, decreases⟩
  have bounded (count : Nat) : measure (chain count) + count ≤ measure (chain 0) := by
    induction count with
    | zero => omega
    | succ count ih => have smaller := decreases count; omega
  have impossible := bounded (measure (chain 0) + 1)
  omega

end Yulang.CommonRoleFiniteShadowExamples
