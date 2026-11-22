import Yulang.GeneralDeclarativeStoppedDepthProjection341
import Yulang.GeneralRebaseRawWatchFailure284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedFreshCut341
open GeneralDictionaryOutputDepth252 (model F)
open GeneralRebaseDepthScalar285 (refreshed)
open GeneralRebaseDepthHaltSelection285 (after_model)
open GeneralDeclarativeStoppedDepthProjection341 (fresh4 preserve_raw)
open GeneralDeclarativeStoppedDepthWitness341 (compiled extra)
open GeneralNominalVersionedJournalFrame236 (models_iff)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Subtype)

def unbound : Assignment :=
  fun name => if name = 4 then (.bottom,(model name).2) else model name

theorem raw_still_valid : Models refreshed unbound := by
  apply (models_iff refreshed (first := model) (last := unbound) ?_).mp after_model
  intro name used
  have notNew : name ≠ 4 := fun h => fresh4 (h ▸ used)
  simp [unbound,notNew]

theorem copied_edge : PresenceNormalForm.Atom.tyLe
    (.var 2) (.var 4) ∈ compiled.normal.ordinary :=
  List.mem_append_right _ (by decide +kernel)

theorem exact_extension_needed :
    Models refreshed unbound ∧ ¬ GeneralDeclarativeHead320.Models compiled unbound := by
  refine ⟨raw_still_valid,?_⟩
  intro restored
  have bounded := restored.1.1 _ copied_edge
  change Subtype F .bottom at bounded
  exact GeneralRebaseRawWatchFailure284.nominal_not_bottom bounded

end Yulang.GeneralDeclarativeStoppedFreshCut341
