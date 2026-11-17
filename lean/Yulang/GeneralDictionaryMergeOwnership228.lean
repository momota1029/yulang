import Yulang.GeneralDictionaryFirstResidual227
import Yulang.GeneralDictionaryRelativeProvenance226

namespace Yulang.GeneralDictionaryMergeOwnership228
open GeneralDeclarations GeneralNominalCenters GeneralNominalAllocation
open GeneralDictionaryRelativeProvenance226
variable {roles : Roles.RoleDecls}

/-- Actual raw merge atoms, without cross checks or reservation bookkeeping,
read only current raw base slots and this declaration's aggregate names. -/
theorem merge_sources (plan : Plan roles) :
    GeneralDictionaryReachablePacket226.mergeSources plan ⊆
      baseSources plan.packet.context.state ++ localSources plan := by
  intro name member
  apply ordinary_sources plan
  obtain ⟨atom,present,within⟩ := List.mem_flatMap.mp member
  apply List.mem_flatMap.mpr
  refine ⟨atom,?_,within⟩
  exact List.mem_append_left _ (List.mem_append_right _ present)

/-- A merge identity absent from the raw base must be allocated by this exact
invocation/declaration, at a declared input name and position zero. -/
theorem merge_new_origin (plan : Plan roles) (key : GeneralNominalIdentities.Origin)
    (absent : source plan.packet.context.state plan.packet.registry plan.packet.site.occurrence.identity key ∉
      baseSources plan.packet.context.state)
    (member : source plan.packet.context.state plan.packet.registry plan.packet.site.occurrence.identity key ∈
      GeneralDictionaryReachablePacket226.mergeSources plan) :
    ∃ name ∈ plan.packet.declaration.inputNames,
      key = origin plan.packet.site.occurrence.identity plan.packet.declaration.id 0 name 0 ∨
      key = origin plan.packet.site.occurrence.identity plan.packet.declaration.id 1 name 0 := by
  have localName := (List.mem_append.mp (merge_sources plan member)).resolve_left absent
  obtain ⟨name,declared,within⟩ := List.mem_flatMap.mp localName
  refine ⟨name,declared,?_⟩
  rcases List.mem_cons.mp within with lower | upper
  · exact Or.inl ((source_identity plan.packet.context.state plan.packet.registry plan.packet.site.occurrence.identity _ _).mp lower)
  · exact Or.inr ((source_identity plan.packet.context.state plan.packet.registry plan.packet.site.occurrence.identity _ _).mp (List.mem_singleton.mp upper))
end Yulang.GeneralDictionaryMergeOwnership228
