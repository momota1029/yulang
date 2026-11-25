import Yulang.GeneralDeclarativeI65I75ProjectedEventReadback426

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
open GeneralDeclarativeI65
open ProjectedCore425
open Checker408 (Problem Result)
open Check408 (Write)
open GeneralDeclarativeWitnessTree349 (eqTree eq_tree eqResult eq_result)
open ExplicitPick419 (eqWrite eq_write419)
open CommonNominalFullCarrier (Ty Equivalent)

/-- Input data only, not a derivation of the desired result. This is a
private-to-this-module replay branch, not a new case on the public
Check421 witness or an assignment of any public wire tag. -/
structure ProjectedRowsWire426 where
  source : RecordEndpoints422.Wire
  required : RequiredRows426

structure ProjectedLeafPacket426 (p : Problem) where
  original : OriginalProjectedLeaf426 p.state.core p.state.b6 p.root
  retained : RequiredRetention426 original.out

def checkableProjectedLeaf426 (p : Problem) (w : ProjectedRowsWire426) :
    Option (ProjectedLeafPacket426 p) := do
  let original ← readProjectedLeafSource426 p w.source
  let stable ← readRequiredRetention426 original.out w.required
  pure ⟨original,stable⟩

def ProjectedLeafPacket426.originalWrite {p : Problem} (a : ProjectedLeafPacket426 p)
    (tag : Nat) : Write := encodeActualOutput425 tag (.projected a.original.out)

def ProjectedLeafPacket426.exactReport {p : Problem} (a : ProjectedLeafPacket426 p)
    (tag : Nat) : Result :=
  ⟨.selected a.original.out.row.id [],.selected a.original.dictionary,[a.originalWrite tag]⟩

def matchesProjectedLeafReport426 {p : Problem} (a : ProjectedLeafPacket426 p)
    (tag : Nat) (r : Result) : Bool :=
  if tag > 8 then
    (eqTree r.tree (a.exactReport tag).tree && eqResult r.verdict (a.exactReport tag).verdict) &&
      (match r.writes with | [out] => eqWrite out (a.originalWrite tag) | _ => false)
  else false

theorem projected_leaf_report_matches_exactly426 {p : Problem} (a : ProjectedLeafPacket426 p)
    (tag : Nat) (r : Result) :
    matchesProjectedLeafReport426 a tag r = true ↔ 8 < tag ∧ r = a.exactReport tag := by
  by_cases free : 8 < tag
  · cases r with
    | mk tree verdict written =>
      cases written with
      | nil => simp [matchesProjectedLeafReport426,free,ProjectedLeafPacket426.exactReport]
      | cons head rest =>
        cases rest with
        | nil => simp [matchesProjectedLeafReport426,free,ProjectedLeafPacket426.exactReport,
            Bool.and_eq_true,eq_tree,eq_result,eq_write419,and_assoc]
        | cons _ _ => simp [matchesProjectedLeafReport426,free,ProjectedLeafPacket426.exactReport]
  · simp [matchesProjectedLeafReport426,free]

def checkProjectedLeafReport426 (p : Problem) (tag : Nat) (r : Result)
    (w : ProjectedRowsWire426) : Bool :=
  ((checkableProjectedLeaf426 p w).map (fun packet => matchesProjectedLeafReport426 packet tag r)).getD false

/-- A checked offered report gives a real original projected leaf
independent of the offered verdict, exact source writes and the
same-model result for *all* fitting models. The theorem is a scoped
branch result, not the fixed/public Classifies or check_sound. -/
theorem checked_projected_leaf_original_report_and_fixed_target426
    {p : Problem} {tag : Nat} {r : Result} {w : ProjectedRowsWire426}
    (yes : checkProjectedLeafReport426 p tag r w = true) :
    ∃ a : ProjectedLeafPacket426 p, checkableProjectedLeaf426 p w = some a ∧
      8 < tag ∧ r = a.exactReport tag ∧
      (∀ m : I72.Model, Fits p.state m →
        EndpointHead423.Meaning a.original.head.endpoints m ∧
        ∃ v : Ty, a.original.out.valueAt m = some (p.root.occurrence,a.original.out.ordinal,
          a.original.outIndex.val,p.root.demand.outputs[a.original.outIndex].target,v) ∧
        Equivalent (m.assignment p.root.demand.outputs[a.original.outIndex].target).1 v) := by
  cases picked : checkableProjectedLeaf426 p w with
  | none => simp [checkProjectedLeafReport426,picked] at yes
  | some a =>
    have actual : matchesProjectedLeafReport426 a tag r = true := by
      simpa [checkProjectedLeafReport426,picked] using yes
    obtain ⟨free,same⟩ := (projected_leaf_report_matches_exactly426 a tag r).mp actual
    refine ⟨a,rfl,free,same,fun m fit => ?_⟩
    obtain ⟨head,all⟩ := one_projected_leaf_keeps_output_at_original_target426 a.original a.retained m fit
    obtain ⟨v,_,evaluates,kept⟩ := all a.original.outIndex
    exact ⟨head,v,evaluates,kept⟩

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
