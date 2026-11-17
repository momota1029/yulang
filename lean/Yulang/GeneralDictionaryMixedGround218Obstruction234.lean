import Yulang.GeneralDictionaryMixedGround218Install234
import Yulang.GeneralDictionaryGroundCopy218Obstruction
set_option backward.isDefEq.respectTransparency false
/-! The actual-center obstruction survives the versioned parent semantics.
This is the semantic core of the child rejection, not yet a proof of child
Prepared/SafeKnown or the V8 rejection classification. -/
namespace Yulang.GeneralDictionaryMixedGround218Obstruction234
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install
open GeneralNominalCenters GeneralNominalRecursiveInspection GeneralNominalOriginTerms
open GeneralDictionaryTopLevelSharing217 (firstCenter secondCenter)
open CommonNominalFullCarrier

theorem centers_different (given : GeneralNominalCommonBridge.Assignment)
    (held : GeneralNominalVersionedPlans231.Holds plan given) :
    ¬ Same given (.source (firstCenter childSite)) (.source (secondCenter childSite)) := by
  rw [GeneralDictionaryGroundCopy218Obstruction.child_first,GeneralDictionaryGroundCopy218Obstruction.child_second]
  intro same
  have schema := held.2.1.2.2.2.2.1
  rw [head_schema] at schema
  have left := schema.2 ⟨0,.nominal (.source 6) 5 0,.actual⟩ (List.mem_cons_self)
  have right := schema.2 ⟨1,.nominal (.source 6) 5 1,.actual⟩
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  change Same given (.nominal (.source 6) 5 0) (.source (GeneralNominalVersionedFrame231.binder plan 0)) at left
  change Same given (.nominal (.source 6) 5 1) (.source (GeneralNominalVersionedFrame231.binder plan 1)) at right
  rw [GeneralNominalVersionedFrame231.binder_eq] at left right
  have rootEqual := root_fixed given held.1
  have firstSeen : Observes given (.nominal (.source 6) 5 0) GeneralDictionaryLooseVariant217.first :=
    .nominal (.source 6) rootEqual rfl
  have secondSeen : Observes given (.nominal (.source 6) 5 1) GeneralDictionaryLooseVariant217.second :=
    .nominal (.source 6) rootEqual rfl
  have a := left.2.2 _ _ firstSeen (.source _)
  have b := right.2.2 _ _ secondSeen (.source _)
  have middle := same.2.2 _ _ (.source _) (.source _)
  exact GeneralDictionaryLooseVariant217.unequal
    ⟨subtype_trans a.1 (subtype_trans middle.1 b.2),subtype_trans b.1 (subtype_trans middle.2 a.2)⟩

theorem child_input_infeasible (candidate : Plan roles)
    (input : candidate.input = childSite)
    (queries : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = [.variables [0],.variables [0]])
    (given : GeneralNominalCommonBridge.Assignment)
    (held : GeneralNominalVersionedJournal232.Models GeneralDictionaryMixedGround218Install234.installed given) :
    ¬ GeneralDictionaryHeadSharing220.Holds candidate given := by
  intro shared
  have one : (⟨0,.source (firstCenter candidate.input),.actual⟩ : GeneralNominalMaterialization.Use) ∈ candidate.headSchema.variables := by
    simp [Plan.headSchema,queries,GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
      GeneralNominalMaterialization.Schema.append,firstCenter]
  have two : (⟨0,.source (secondCenter candidate.input),.actual⟩ : GeneralNominalMaterialization.Use) ∈ candidate.headSchema.variables := by
    simp [Plan.headSchema,queries,GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
      GeneralNominalMaterialization.Schema.append,secondCenter]
  have same := (GeneralDictionaryHeadSharing220.holds_iff candidate given).mp shared _ one _ two rfl
  rw [input] at same
  exact centers_different given (held.2.1 plan (List.mem_cons_self ..)) same
end Yulang.GeneralDictionaryMixedGround218Obstruction234
