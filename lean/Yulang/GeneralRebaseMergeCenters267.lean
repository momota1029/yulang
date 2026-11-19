import Yulang.GeneralRebaseExecutableGenerated267
import Yulang.GeneralNominalCenters

namespace Yulang.GeneralRebaseMergeCenters267
open GeneralNominalCenters (Site SameInputs)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalDemandMerging (Related All₂)
open GeneralNominalRecursiveInspection (Origin)

def centers (site : Site roles) : List Nat := List.ofFn site.center

def same (first last : Site roles) : Bool :=
 (first.occurrence.demand.role == last.occurrence.demand.role) &&
 (centers first == centers last)

theorem same_exact (first last : Site roles) : same first last = true ↔
 first.occurrence.demand.role = last.occurrence.demand.role ∧ centers first = centers last := by
 simp [same]

theorem related_self (models : Assignment → Prop) (names : List Nat) :
 All₂ (Related models) (names.map fun n => some (.source n)) (names.map fun n => some (.source n)) := by
 induction names with
 | nil => exact .nil
 | cons name rest ih =>
   exact .cons ⟨.source name,.source name,rfl,rfl,GeneralNominalCenters.same_name models name⟩ ih

theorem observed (site : Site roles) :
 site.observed.inputs = (centers site).map (fun n => some (.source n)) := by
 simp [GeneralNominalCenters.Site.observed,centers,List.map_ofFn]
 rfl

theorem source_sound (models : Assignment → Prop) (first last : Site roles)
 (equal : same first last = true) : SameInputs models first last := by
 obtain ⟨role,names⟩ := (same_exact ..).mp equal
 refine ⟨role,?_⟩
 rw [observed first,observed last,←names]
 exact related_self models (centers first)

end Yulang.GeneralRebaseMergeCenters267
