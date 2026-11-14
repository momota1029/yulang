import Yulang.GeneralNominalHeadLedgerFrame182

namespace Yulang.GeneralNominalHeadLedgerSupport182
open GeneralNominalCenters GeneralSourceDictionaries GeneralNominalCenteredHeadOutputs
open GeneralNominalHeadLedgerFrame182
theorem request_target_mem (state : GeneralNominalCenteredSteps.State roles)
    (root : Occurrence roles) (plan : Plan roles)
    (member : output ∈ requests state root) : output.target ∈ outputSources state root plan :=
  List.mem_append_right _ (List.mem_map.mpr ⟨output,member,rfl⟩)

theorem merged_target_mem (state : GeneralNominalCenteredSteps.State roles)
    (one two : Site roles) (plan : Plan roles) (support)
    (empty : one.occurrence.demand.outputs = [])
    (registered : two.observed ∈ state.erased.current.sites)
    (member : output ∈ two.occurrence.demand.outputs) :
    output.target ∈ outputSources (GeneralNominalCenteredSteps.merge state one two support)
      one.occurrence plan :=
  request_target_mem _ _ _ (one_sided_request state one two empty registered member support)

end Yulang.GeneralNominalHeadLedgerSupport182
