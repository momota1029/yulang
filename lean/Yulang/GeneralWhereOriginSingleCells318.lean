import Yulang.GeneralWhereOriginSingleRead318
import Yulang.GeneralWhereOriginDescriptor318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 1000000
namespace Yulang.GeneralWhereOriginSingleCells318
open GeneralWhereOriginSingleSource318
open GeneralWhereOriginSingleRead318 (old_reads new_reads)
open GeneralDictionaryJournalRefinement228Source (roles)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralWhereVersionCase317 (expr)
open GeneralVersionedEndpointAddress315 (atCell footprint fields)
open GeneralNominalVersionedExpressionFrame236 (variableSource)

abbrev loOld := atCell oldPlan .lower otherChild.id 0 expr
abbrev hi := atCell oldPlan .upper otherChild.id 0 expr
noncomputable abbrev loNow := atCell newPlan .lower otherChild.id 0 expr

theorem lower_moves : loOld ≠ loNow := by
  intro eq
  have equal := (fields (p := oldPlan) (q := newPlan) (e := expr) (f := expr) rfl eq).2.2.2.2.2
  change [variableSource oldPlan .lower 0] = [variableSource newPlan .lower 0] at equal
  rw [old_reads.1,new_reads.1] at equal
  have impossible : (4:Nat) = 2 := List.head_eq_of_cons_eq equal
  cases impossible

theorem upper_kept : atCell newPlan .upper otherChild.id 0 expr = hi := by
  unfold hi
  unfold atCell GeneralVersionedEndpointAddress315.key
  have one : footprint oldPlan GeneralVersionedEndpointAddress315.Side.upper.mode expr = [2] := by
    change [variableSource oldPlan .upper 0] = _
    rw [old_reads.2]
  have two : footprint newPlan GeneralVersionedEndpointAddress315.Side.upper.mode expr = [2] := by
    change [variableSource newPlan .upper 0] = _
    rw [new_reads.2]
  rw [one,two] <;> rfl

abbrev sig : otherChild.Signature roles := GeneralLiveCompoundChildSite316.signature
noncomputable abbrev oldChild := GeneralWhereVersionCompiler317.child oldPlan otherChild sig
noncomputable abbrev newChild := GeneralWhereVersionCompiler317.child newPlan otherChild sig

theorem exact_old : oldChild.occurrence.demand.arguments 0 = (loOld,hi) :=
  GeneralWhereOriginDescriptor318.argument (p := oldPlan) sig 0 (pat := .variant 0 (.var 0)) rfl (fun _ eq => by cases eq) (expr := expr) rfl

theorem exact_new :
    newChild.occurrence.demand.arguments 0 = (loNow,hi) := by
  have h := GeneralWhereOriginDescriptor318.argument (p := newPlan) sig 0
    (pat := .variant 0 (.var 0)) rfl (fun _ eq => by cases eq) (expr := expr) rfl
  change newChild.occurrence.demand.arguments 0 =
    (loNow,atCell newPlan .upper otherChild.id 0 expr) at h
  rw [upper_kept] at h
  exact h

theorem same_child_identity : oldChild.occurrence.identity = newChild.occurrence.identity := by
  calc
    _ = (GeneralNominalVersionedFrame231.childSite oldPlan otherChild sig).occurrence.identity :=
      GeneralWhereVersionCompiler317.child_owner oldPlan otherChild sig
    _ = (GeneralNominalVersionedFrame231.childSite newPlan otherChild sig).occurrence.identity := by
      let key := GeneralNominalAllocation.origin GeneralDictionaryJournalRefinement228Source.root.identity
        declaration.id 6 otherChild.id 0
      change GeneralNominalIdentities.source older.context.state.seed key =
        GeneralNominalIdentities.source newer.context.state.seed key
      have same : older.context.state.seed = newer.context.state.seed := rfl
      rw [same]
    _ = _ := (GeneralWhereVersionCompiler317.child_owner newPlan otherChild sig).symm

theorem unique_endpoint :
    oldChild.occurrence.identity = newChild.occurrence.identity ∧
    loOld ≠ loNow ∧
    oldChild.occurrence.demand.arguments 0 = (loOld,hi) ∧
    newChild.occurrence.demand.arguments 0 = (loNow,hi) :=
  ⟨same_child_identity,lower_moves,exact_old,exact_new⟩

end Yulang.GeneralWhereOriginSingleCells318
