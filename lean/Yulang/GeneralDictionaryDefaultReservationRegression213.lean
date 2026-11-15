import Yulang.GeneralDictionaryDefaultRawSupport213
import Yulang.GeneralDictionaryDefaultHeadGap213

/-! A reservation-only source is in the old support but not the semantic
support. Its assignment can change while the actual raw model survives. -/
namespace Yulang.GeneralDictionaryDefaultReservationRegression213
open GeneralDictionarySemanticCollapseExample
open GeneralDictionaryDefaultHeadGap213

def reserved : GeneralNominalState.State := {source with reserved := [lower]}

 theorem old_support : lower ∈ GeneralNominalState.sources reserved := by
  unfold GeneralNominalState.sources
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))

 theorem new_support : lower ∉ GeneralDictionaryDefaultRawSupport213.sources reserved := by
  change lower ∉ [0,1,2,3] ++ [0,1,2,3] ++ []
  decide +kernel

 theorem before_model : GeneralNominalState.Models reserved model :=
  GeneralDictionarySemanticCollapseExample.source_models

 theorem changed_model : GeneralNominalState.Models reserved modified :=
  GeneralDictionaryDefaultHeadGap213.source_models

 theorem changed_reserved : model lower ≠ modified lower := by
  intro same
  have types := congrArg Prod.fst same
  change CommonNominalSyntax.Layer.base Inference.Base.int = CommonNominalSyntax.Layer.bottom at types
  cases types
end Yulang.GeneralDictionaryDefaultReservationRegression213
