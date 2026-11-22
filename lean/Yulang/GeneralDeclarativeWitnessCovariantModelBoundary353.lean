import Yulang.GeneralDeclarativeWitnessCovariantCanonical353
import Yulang.CommonNominalFullModelMap

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantModelBoundary353
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row View HasView Valuation assigned)
open GeneralDeclarativeWitnessCovariantCanonical353 (valuation find_root)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalRegularErasure (layer)
open CommonNominalFullCarrier (Ty Equivalent Subtype nominal nominal_regular_invariant_exact)

theorem fixed_row {p : Problem} {m : Assignment} {v : Valuation}
    (distinct : (p.rows.map Row.root).Nodup) (fit : ∀ r ∈ p.rows, HasView m v r)
    {r : Row} (author : r ∈ p.rows) :
    ∃ seen canonical : View,
      v r.root = some seen ∧ valuation p m r.root = some canonical ∧
      seen.tag = canonical.tag ∧ seen.box = canonical.box ∧
      Common.Equivalent seen.payload canonical.payload := by
  obtain ⟨seen,atRoot,tag,box,body⟩ := fit r author
  exact ⟨seen,⟨r.tag,r.box,(assigned m r.valueName).1⟩,atRoot,
    by simp [valuation,find_root distinct author],tag,box,body⟩

theorem precise_for_common_payload (m : Assignment) (atName : Nat) (t : Common.Ty)
    (authored : (m atName).1 = CommonNominalFullModelMap.value t) :
    (assigned m atName).1 = t := by
  unfold assigned
  rw [authored]
  exact CommonNominalRegularErasure.layer_value t

/-- The old ordinary carrier model is kept intact for all children
and writes. Its projection used for the typed Box view is not a
faithful overlapping nominal carrier. -/
theorem projection_not_faithful :
    layer (nominal 0 []) = layer (nominal 1 []) ∧ ¬ Equivalent (nominal 0 []) (nominal 1 []) := by
  refine ⟨rfl,?_⟩
  intro same
  have bad := ((nominal_regular_invariant_exact 0 1 [] []).mp same.1).1
  cases bad

end Yulang.GeneralDeclarativeWitnessCovariantModelBoundary353
