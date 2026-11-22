import Yulang.GeneralDeclarativeWitnessGrandchild355
import Yulang.GeneralDeclarativeWitnessTypedJoint354
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessGrandchildContinuity355
open GeneralDeclarativeWitnessGrandchild355 (Plan Wire Accepted stage view)
open GeneralDeclarativeWitnessTypedReemit354 (Linked typedView)
open GeneralDeclarativeWitnessTypedChild354 (downstream)
open GeneralDeclarativeWitnessCovariantOrigin353 (Row HasView View Valuation)
open GeneralDeclarativeWitnessTypedJoint354 (compatible shared author_rows)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (Models)

def previousRows {i s w} (a : Linked i s w) : List Row :=
  (downstream i a.writer.output.state a.child a.out.atWrite.typed.row).rows

def nextRows {i s w} {a : Linked i s w} {p code} (r : Accepted a p code) : List Row :=
  (stage a p r.demand r.released.body.indexed.typed.row).rows

def sameRows {i s w} {a : Linked i s w} {p code} (r : Accepted a p code) : List Row :=
  previousRows a ++ nextRows r

/-- Additional certificate of table agreement for the retained shared
projection. It is a check on this proof route, not language admission. -/
def jointly {i s w} {a : Linked i s w} {p code} (r : Accepted a p code) : Bool :=
  compatible (sameRows r)

theorem preserves_visible_rows {i s w} {a : Linked i s w} {p code} (r : Accepted a p code)
    (good : jointly r = true) (m : Assignment) :
    ∃ v : Valuation,
      (∀ row ∈ previousRows a,HasView m v row) ∧
      (∀ row ∈ nextRows r,HasView m v row) := by
  let v := shared i.producer (sameRows r) m
  have covers : ∀ row ∈ sameRows r,HasView m v row := author_rows good m
  exact ⟨v,fun h m => covers h (List.mem_append_left _ m),fun h m => covers h (List.mem_append_right _ m)⟩

open GeneralDeclarativeWitnessCovariantOrigin353 (assigned)
open GeneralDeclarativeWitnessCovariantViews353 (View.head)
open GeneralDeclarativeWitnessCovariantMetadata353 (table)
open CommonDeclaredNominalInspection (DeclaredSubtype)

def realInterval (v : Valuation) (a : GeneralDeclarativeWhere319.Capture) (b : Nat) : Prop :=
  ∃ l c h : View,
    v a.lower = some l ∧ v a.center = some c ∧ v a.upper = some h ∧
    DeclaredSubtype (table b) (View.head l) (View.head c) ∧
    DeclaredSubtype (table b) (View.head c) (View.head h)

theorem one_model_one_typed_table {i s w} {a : Linked i s w} {p code} (r : Accepted a p code)
    (good : jointly r = true) (m : Assignment) (fit : Models s m) :
    ∃ v,
      realInterval v a.receiver.compiled.readFrom.arg w.receiverHead.center.box ∧
      realInterval v r.results.facts.arg code.head.center.box ∧
      (∀ row ∈ previousRows a,HasView m v row) ∧
      (∀ row ∈ nextRows r,HasView m v row) := by
  obtain ⟨v,before,after⟩ := preserves_visible_rows r good m
  have prior := GeneralDeclarativeWitnessReceipt349.same_model a.receiver.verifies m fit
  obtain ⟨l,c,h,ll,cc,hh,_,lc,ch⟩ := GeneralDeclarativeWitnessTypedRangeWriter354.range_in_same_model
    a.receiver m fit v before
  obtain ⟨u,vw,x,ul,vc,xh,_,uv,vx⟩ := GeneralDeclarativeWitnessCovariantInterval353.typed_interval
    r.results.facts m v prior after
  exact ⟨v,⟨l,c,h,ll,cc,hh,lc,ch⟩,⟨u,vw,x,ul,vc,xh,uv,vx⟩,before,after⟩

end Yulang.GeneralDeclarativeWitnessGrandchildContinuity355
