import Yulang.GeneralDeclarativeOpaqueIntervals328
import Yulang.GeneralDeclarativeRepeatedActual323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaquePrecision328
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeOpaqueIntervals328 (low high left right ready actual)
open GeneralDeclarativeOpaqueNames328 (expose)
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativeOpaqueChannel328 (project)
open GeneralDeclarativeEntailment320 (Entails model_append)
open GeneralDeclarativeCaptureClosure320 (ordinary_models)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralDeclarativeRepeatedActual323 (pair_exact)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open CommonNominalFullCarrier (Subtype Equivalent subtype_trans)

theorem pullback {s : State} {arg : GeneralDeclarativeWhere319.Capture}
    (m) (model : Models (ready s arg.center extra e) m) : Models s m :=
  ((model_append m).mp ((ordinary_models m).mp model).1).1

/-- All resulting ordinary models, not only a constructed extension,
have the actual projections up to equivalence. The values need not
be syntactically identical to any chosen regular representation. -/
theorem precision {s : State} {arg : GeneralDeclarativeWhere319.Capture}
    (bounds : Bounds s arg)
    (lo : Entails s ⟨arg.lower,low e⟩) (hi : Entails s ⟨arg.upper,high e⟩)
    (extra : List Nat) (m) (model : Models (ready s arg.center extra e) m) :
    ∃ a b, project false (m arg.center).1 = some a ∧ project true (m arg.center).1 = some b ∧
      Equivalent (m (left s arg.center extra e).center).1 a ∧
      Equivalent (m (right s arg.center extra e).center).1 b := by
  have old := pullback m model
  have below := lo m old
  have above := hi m old
  have within := bounds_sound bounds m old
  obtain ⟨a,b,l,r,refolded⟩ := GeneralDeclarativeOpaquePair328.reconstruction _ _ _ _ _
    (subtype_trans below.2 within.1) (subtype_trans within.2 above.1)
  have projected := semantic (actual (s := s) arg.center extra e) m model
  have same := (pair_exact ..).mp (eqv_trans (eqv_symm projected) refolded)
  exact ⟨a,b,l,r,same.1,same.2⟩

end Yulang.GeneralDeclarativeOpaquePrecision328
