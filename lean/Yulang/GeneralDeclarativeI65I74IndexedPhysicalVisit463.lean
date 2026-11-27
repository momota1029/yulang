import Yulang.GeneralDeclarativeI65I74ExactStampedEligible462

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PhysicalVisit463
open RecordTraversal455 (RawSnapshot)
open RecordTraversal455.MixedQA (Address ChildAt readChild ReadChild
  every_canonical_child_has_its_actual_field_or_ordinal_wire)
open AuthenticatedHop458 (Policy HopWire AtStep readStep)
open GeneralDeclarativeWitnessCycle350 (Link checksLink link)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeGraphRows321 (shapeOf)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeHead320 (Equation)

structure IndexedOpen (s : RawSnapshot) (p : Policy) (root : Nat) (code : Expr)
    (ordinal : Nat) (addr : Address) (child : Nat) (next : Expr) (used : Bool) : Prop where
  actual : ∃ row shape, s.equations[ordinal]? = some row ∧ GeneralDeclarativeLowerKnown321.Alias s root row.left ∧
    shapeOf row.right = some shape ∧ ChildAt shape code addr child next ∧ p.opens root row addr child used

theorem projection_to_old_raw_hop {s p root code ordinal a c next used}
    (h : IndexedOpen s p root code ordinal a c next used) : AtStep s p root code a c next used := by
  obtain ⟨r,sh,row,alias,shape,chosen,opened⟩ := h.actual
  exact ⟨r,List.mem_of_getElem? row,sh,alias,shape,chosen,opened⟩

theorem every_old_raw_hop_has_an_actual_row_ordinal {s p root code a c next used} :
    AtStep s p root code a c next used ↔ ∃ n, IndexedOpen s p root code n a c next used := by
  constructor
  · rintro ⟨r,seen,sh,owner,form,chosen,opened⟩
    obtain ⟨n,index⟩ := List.mem_iff_getElem?.mp seen
    exact ⟨n,⟨r,sh,index,owner,form,chosen,opened⟩⟩
  · rintro ⟨_,row⟩
    exact projection_to_old_raw_hop row

theorem raw_witness_reads_its_identical_physical_row {s p root code a c next used} {w : HopWire p}
    (wire : readStep s p root code w = some (a,c,next,used)) :
    IndexedOpen s p root code w.row a c next used := by
  cases row : s.equations[w.row]? with
  | none => simp [readStep,row,Option.bind] at wire
  | some r =>
    cases form : shapeOf r.right with
    | none => simp [readStep,row,form,Option.bind] at wire
    | some sh =>
      cases selected : readChild w.child sh code with
      | none => simp [readStep,row,form,selected,Option.bind] at wire
      | some pick =>
        by_cases pass : checksLink s root r.left w.alias = true ∧
            p.checks root r pick.address pick.child w.author = true
        · simp [readStep,row,form,selected,pass.1,pass.2,Option.bind] at wire
          obtain ⟨rfl,rfl,rfl,rfl⟩ := wire
          exact ⟨r,sh,row,link pass.1,form,pick.valid,(p.reflected ..).mp ⟨w.author,rfl,pass.2⟩⟩
        · simp [readStep,row,form,selected,Bool.and_eq_true,pass,Option.bind] at wire

theorem an_exact_physical_row_reifies_at_the_same_index {s p root code ordinal a c next used}
    (h : IndexedOpen s p root code ordinal a c next used) :
    ∃ w : HopWire p, w.row = ordinal ∧ readStep s p root code w = some (a,c,next,used) := by
  obtain ⟨r,sh,row,alias,form,picked,opened⟩ := h.actual
  obtain ⟨wire,good⟩ := WhereSites450.alias_wire_from_actual_derivation450 alias
  obtain ⟨atChild,found⟩ :=
    every_canonical_child_has_its_actual_field_or_ordinal_wire (⟨a,c,next,picked⟩ : ReadChild sh code)
  obtain ⟨token,mark,verify⟩ := (p.reflected ..).mpr opened
  exact ⟨⟨ordinal,wire,atChild,token⟩,rfl,by
    simp [readStep,row,form,found,good,verify,mark,Option.bind]⟩

end Yulang.GeneralDeclarativeI65.I72.PhysicalVisit463
