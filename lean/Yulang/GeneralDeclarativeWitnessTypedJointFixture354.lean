import Yulang.GeneralDeclarativeWitnessTypedJoint354
import Yulang.GeneralDeclarativeWitnessTypedForestModel354
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 40000
set_option maxHeartbeats 36000000
namespace Yulang.GeneralDeclarativeWitnessTypedJointFixture354
open GeneralDeclarativeWitnessTypedForest354 (Input Plan Wire Accepted decode)
open GeneralDeclarativeWitnessTypedForestFixture354 (problem data)
open GeneralDeclarativeWitnessTypedForestModel354 (model model_fits)
open GeneralDeclarativeWitnessTypedJoint354 (compatible leavesRows shared Supported one_valuation)
open GeneralDeclarativeHead320 (State Models)
open CommonRoleOutermostResolver (All₂)

def reconcile : Bool :=
  (data.map (fun (s,w) =>
    ((decode problem s w).map (fun a => compatible (leavesRows a.children))).getD false)).getD false

theorem two_children_in_one_typed_valuation : reconcile = true := by decide +kernel

def alt (plan : Plan) (payload : Nat) : Plan :=
  {plan with authored := plan.authored ++ [⟨44,13,0,payload⟩]}

def extended (different : Bool) : Input :=
  {problem with kids := [alt (GeneralDeclarativeWitnessTypedForestFixture354.plan false) 7,
    alt (GeneralDeclarativeWitnessTypedForestFixture354.plan true) (if different then 8 else 7)]}

def adjust (w : Wire) : Wire :=
  {w with children := w.children.map (fun child =>
    {child with head := {child.head with center := {child.head.center with center := 5}}})}

def extendedRead (different : Bool) : Bool :=
  (data.map (fun (s,w) => (decode (extended different) s (adjust w)).isSome)).getD false

def extendedReconcile (different : Bool) : Bool :=
  (data.map (fun (s,w) =>
    ((decode (extended different) s (adjust w)).map (fun a => compatible (leavesRows a.children))).getD false)).getD false

theorem independent_readers_do_not_assert_shared_rows : extendedRead true = true := by decide +kernel
theorem disagreement_detected_not_language_rejection : extendedReconcile true = false := by decide +kernel
theorem overlapping_identical_author_data_allowed : extendedReconcile false = true := by decide +kernel

theorem actual_shared_model :
    ∃ (s : State) (w : Wire) (a : Accepted problem s w),
      data = some (s,w) ∧ Models s model ∧
      All₂ (Supported s model (shared problem.producer (leavesRows a.children) model))
        a.parent.output.children a.children.dicts := by
  have testOK := two_children_in_one_typed_valuation
  unfold reconcile at testOK
  cases got : data with
  | none => simp [got] at testOK
  | some pair =>
    obtain ⟨s,w⟩ := pair
    cases ok : decode problem s w with
    | none => simp [got,ok] at testOK
    | some a =>
      have comp : compatible (leavesRows a.children) = true := by simpa [got,ok] using testOK
      have fit := model_fits got
      exact ⟨s,w,a,rfl,fit,one_valuation a comp model fit⟩

end Yulang.GeneralDeclarativeWitnessTypedJointFixture354
