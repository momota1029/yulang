import Yulang.GeneralDeclarativeDemand320
import Yulang.GeneralNominalCenters

namespace Yulang.GeneralStoppedOrdinarySite335
open GeneralNominalCenters (Site)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)

/-- The endpoints and center come from different raw records. No
normalization, equality or fresh-name generation is performed on
the retained role argument or its requested output targets. -/
def argument (site : Site roles) (index : Fin (roles site.occurrence.demand.role).arity) : Capture :=
  ⟨(site.occurrence.demand.arguments index).1,site.center index,
    (site.occurrence.demand.arguments index).2⟩

def demand (site : Site roles) : Demand :=
  ⟨site.occurrence.demand.role,List.ofFn (argument site),site.occurrence.demand.outputs⟩

def occurrence (site : Site roles) : Nat × Demand :=
  (site.occurrence.identity,demand site)

theorem each_argument (site : Site roles) (index : Fin (roles site.occurrence.demand.role).arity) :
    (demand site).arguments[index.val]? = some (argument site index) := by
  simp [demand,index.isLt]

theorem output_targets (site : Site roles) :
    (demand site).outputs = site.occurrence.demand.outputs := rfl

theorem retained_order (sites : List (Site roles)) :
    (sites.map occurrence).map Prod.fst = sites.map (fun s => s.occurrence.identity) := by
  simp only [List.map_map]
  rfl

end Yulang.GeneralStoppedOrdinarySite335
