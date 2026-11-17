import Yulang.GeneralNominalVersionedPlans231
import Yulang.GeneralNominalVersionedJournal232
import Yulang.GeneralDictionaryHeadSharing220
set_option backward.isDefEq.respectTransparency false

/-! Actual head-origin sharing is unchanged: use the existing sharing
predicate, not endpoint equality or a weakened duplicate-name condition.
The versioned total head schema implies it through the shared actual binder. -/
namespace Yulang.GeneralNominalVersionedHeadSharing232
open GeneralNominalCenters GeneralNominalOriginTerms
open GeneralNominalCommonBridge (Assignment)

theorem schema_holds (plan : Plan roles) (model : Assignment)
    (held : GeneralNominalVersionedPlans231.SchemaHolds plan plan.headSchema model) :
    GeneralDictionaryHeadSharing220.Holds plan model := by
  apply (GeneralDictionaryHeadSharing220.holds_iff plan model).mpr
  intro first one last two names
  have actualFirst := GeneralNominalHeadSchemaNames186.head_actual plan first one
  have actualLast := GeneralNominalHeadSchemaNames186.head_actual plan last two
  have a : Same model first.origin (.source (GeneralNominalVersionedFrame231.binder plan first.name)) := by
    simpa only [actualFirst,ite_true] using held.2 first one
  have b : Same model last.origin (.source (GeneralNominalVersionedFrame231.binder plan last.name)) := by
    simpa only [actualLast,ite_true] using held.2 last two
  rw [names] at a
  exact same_trans a (same_symm b)

theorem packet_holds (plan : Plan roles) (model : Assignment)
    (held : GeneralNominalVersionedPlans231.Holds plan model) :
    GeneralDictionaryHeadSharing220.Holds plan model :=
  schema_holds plan model held.2.1.2.2.2.2.1

theorem packet_with_sharing_iff (plan : Plan roles) (model : Assignment) :
    (GeneralNominalVersionedPlans231.Holds plan model ∧ GeneralDictionaryHeadSharing220.Holds plan model) ↔
      GeneralNominalVersionedPlans231.Holds plan model :=
  ⟨And.left,fun held => ⟨held,packet_holds plan model held⟩⟩

theorem recorded_plan_holds (valid : GeneralNominalVersionedJournal232.Models state model)
    (present : plan ∈ state.plans) : GeneralDictionaryHeadSharing220.Holds plan model :=
  packet_holds plan model (valid.2.1 plan present)

end Yulang.GeneralNominalVersionedHeadSharing232
