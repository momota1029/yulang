import Yulang.GeneralNominalOriginRootAlias181
import Yulang.GeneralNominalCanonicalSiteObstruction

/-! Ordinary equations identify two different source roots. Nominal projection
readback transports without requiring equal origin syntax. This is an observed
source fixture, not a claim of general selected-candidate coverage. -/
namespace Yulang.GeneralNominalOriginAliasExample181
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralNominalOriginAlias181 (mapSource)
open GeneralNominalOriginRootAlias181
open GeneralNominalCanonicalSiteObstruction (state model state_models)

def rename (name : Nat) : Nat := if name = 0 then 1 else name
def origin : Origin := .nominal (.source 0) 0 0

 theorem recorded : RootRecorded state rename origin := by
  apply Or.inr
  constructor <;> simp [state,GeneralNominalState.extend,GeneralNominalAllocation.equations,
    GeneralNominalIntervalExamples.source,GeneralNominalCenteredModelExtension.originSource,origin,rename]

 theorem observations (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state assignment) (value : Ty) :
    Observes assignment origin value ↔ Observes assignment (.nominal (.source 1) 0 0) value := by
  exact recorded_observes_iff state assignment valid rename origin recorded
    (by intro name equal; cases equal) value

 theorem concrete_old : Observes model origin (.base .int) :=
  .nominal (.source 0) ⟨subtype_refl _,subtype_refl _⟩ rfl

 theorem concrete_new : Observes model (.nominal (.source 1) 0 0) (.base .int) :=
  (observations model state_models _).mp concrete_old

 theorem different_syntax : origin ≠ mapSource rename origin := by
  intro same
  cases same

end Yulang.GeneralNominalOriginAliasExample181
