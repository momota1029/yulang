import Yulang.GeneralDeclarativeWitnessCovariantOrigin353
import Yulang.CommonCanonicalShapes

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantViews353
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Wire Anchored View Valuation HasView ModelsAt assigned
  actual_center)
open GeneralDeclarativeWitnessCovariantMetadata353 (table table_key)
open GeneralNominalCommonBridge (Assignment)
open CommonDeclaredNominalInspection (DeclaredSubtype declared_subtype_exact ArgumentsRel ArgumentRel)
open CommonDeclaredNominalVariance (Subtype covariant_box_subtype_exact)
open CommonNominalHeads (Head)

def View.head (v : View) : Head := ⟨v.box,[.value v.payload]⟩

theorem actual_box_order (x y : View) (key : Nat) (first : x.box = key) (last : y.box = key)
    (below : Common.Subtype x.payload y.payload) : DeclaredSubtype (table key) (View.head x) (View.head y) := by
  apply (declared_subtype_exact ..).mpr
  refine ⟨GeneralDeclarativeWitnessCovariant352.covariant,?_,first.trans last.symm,?_⟩
  · change (table key)[x.box]? = some _
    rw [first]
    exact table_key _
  · exact ⟨⟨rfl,rfl,below⟩,trivial⟩

/-- The original indexed producers and actual demand center agree in the
declaration-aware first-order carrier, over one ordinary assignment.
A proxy endpoint is not the observable center. -/
theorem views {p : Problem} {w : Wire} (a : Anchored p w) (m : Assignment) (v : Valuation) (fit : ModelsAt p m v) :
    ∃ first last current : View,
      v a.first.root = some first ∧ v a.last.root = some last ∧ v a.arg.center = some current ∧
      first.tag = a.shape.tag ∧ last.tag = a.shape.tag ∧ current.tag = a.shape.tag ∧
      DeclaredSubtype (table w.box) (View.head first) (View.head current) ∧
      DeclaredSubtype (table w.box) (View.head last) (View.head current) ∧
      Common.Equivalent current.payload (.union first.payload last.payload) := by
  obtain ⟨l,left,lt,lb,lv⟩ := fit.2 a.first (List.mem_iff_getElem?.mpr ⟨_,a.firstAt⟩)
  obtain ⟨r,right,rt,rb,rv⟩ := fit.2 a.last (List.mem_iff_getElem?.mpr ⟨_,a.lastAt⟩)
  obtain ⟨c,center,ct,cb,cv⟩ := actual_center a m v fit
  have equiv : Common.Equivalent c.payload (.union l.payload r.payload) :=
    Common.equivalent_trans cv (CommonCanonicalShapes.union_congr ⟨lv.2,lv.1⟩ ⟨rv.2,rv.1⟩)
  have unionBelow := (Common.common_union_is_join _ _ _).mp equiv.2
  refine ⟨l,r,c,left,right,center,lt.trans a.firstShape.1,rt.trans a.lastShape.1,ct,?_,?_,equiv⟩
  · exact actual_box_order l c w.box (lb.trans (a.firstShape.2.trans a.sameBox)) (cb.trans a.sameBox) unionBelow.1
  · exact actual_box_order r c w.box (rb.trans (a.lastShape.2.trans a.sameBox)) (cb.trans a.sameBox) unionBelow.2

end Yulang.GeneralDeclarativeWitnessCovariantViews353
