import Yulang.GeneralDictionaryMixedUpperPlan234
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedUpperSemantics234
open GeneralDictionaryMixedUpperPlan234
open GeneralDictionaryVersionedUpperSnapshot233
open GeneralNominalVersionedPlans231

theorem ordinary_eq (model : GeneralNominalCommonBridge.Assignment) :
    Ordinary packet model = Ordinary oldPlan.packet model := by
  unfold Ordinary
  rw [bindings_exact,GeneralDictionaryVersionedPoint233.bindings_exact]
  unfold GeneralNominalPacketSupport.report
  rw [report_exact,GeneralDictionaryOptionalCurrent229.report_exact]
  rfl

end Yulang.GeneralDictionaryMixedUpperSemantics234
