import Yulang.GeneralDeclarativeWitnessTypedJointFixture354
import Yulang.CommonRigidHeadInspection
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 40000
set_option maxHeartbeats 36000000
namespace Yulang.GeneralDeclarativeWitnessTypedOverlap354
open GeneralDeclarativeWitnessCovariantOrigin353 (Row HasView Valuation assigned)
open GeneralDeclarativeWitnessTypedJoint354 (leavesRows compatible)
open GeneralDeclarativeWitnessTypedJointFixture354 (extended adjust)
open GeneralDeclarativeWitnessTypedForest354 (Wire Accepted decode)
open GeneralDeclarativeWitnessTypedForestFixture354 (data)
open GeneralDeclarativeWitnessTypedForestModel354 (model model_fits)
open GeneralDeclarativeHead320 (State Models)
open GeneralNominalCommonBridge (Assignment)

theorem common_row_necessary {m : Assignment} {v : Valuation} {x y : Row}
    (root : x.root = y.root) (a : HasView m v x) (b : HasView m v y) :
    x.tag = y.tag ∧ x.box = y.box ∧
    Common.Equivalent (assigned m x.valueName).1 (assigned m y.valueName).1 := by
  obtain ⟨r,here,tag,box,left⟩ := a
  obtain ⟨q,there,last,end_,right⟩ := b
  rw [root] at here
  have eq := Option.some.inj (here.symm.trans there)
  subst q
  exact ⟨tag.symm.trans last,box.symm.trans end_,
    Common.equivalent_trans (Common.equivalent_symm left) right⟩

def conflictLeft : Row := ⟨44,13,0,7⟩
def conflictRight : Row := ⟨44,13,0,8⟩

def conflictObserved : Bool :=
  (data.map (fun (s,w) => ((decode (extended true) s (adjust w)).map (fun a =>
    decide (conflictLeft ∈ leavesRows a.children ∧ conflictRight ∈ leavesRows a.children))).getD false)).getD false

theorem conflict_is_in_real_rows : conflictObserved = true := by decide +kernel

theorem no_common_view_for_the_actual_accepted_pair :
    ∃ (s : State) (w : Wire) (a : Accepted (extended true) s (adjust w)),
      data = some (s,w) ∧ Models s model ∧
      ¬ ∃ v : Valuation, ∀ r ∈ leavesRows a.children, HasView model v r := by
  have seen := conflict_is_in_real_rows
  unfold conflictObserved at seen
  cases got : data with
  | none => simp [got] at seen
  | some pair =>
    obtain ⟨s,w⟩ := pair
    cases ok : decode (extended true) s (adjust w) with
    | none => simp [got,ok] at seen
    | some a =>
      have facts : decide (conflictLeft ∈ leavesRows a.children ∧ conflictRight ∈ leavesRows a.children) = true :=
        by simpa [got,ok] using seen
      obtain ⟨first,last⟩ := of_decide_eq_true facts
      refine ⟨s,w,a,rfl,model_fits got,?_⟩
      rintro ⟨v,defined⟩
      have both := (common_row_necessary (x := conflictLeft) (y := conflictRight) rfl (defined _ first) (defined _ last)).2.2
      change Common.Equivalent (.base .int) (.base .bool) at both
      exact Inference.Base.noConfusion ((CommonRigidHeadInspection.base_iff .int .bool).mp both.1)

end Yulang.GeneralDeclarativeWitnessTypedOverlap354
