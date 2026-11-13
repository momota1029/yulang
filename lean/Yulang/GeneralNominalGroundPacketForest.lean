import Yulang.GeneralNominalGroundForests

/-! A finite forest for the original inspector includes both endpoint
sources at missing constructor roots, as certified by actual recovery. -/
namespace Yulang.GeneralNominalGroundPacketForest
open GeneralNominalGroundForests GeneralNominalGroundAccessibility
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalInspectionOrigins GeneralNominalSaturationState
open CommonNominalFullCarrier

def MissingConstructor (packet : Packet roles)
    (index : Fin (roles packet.site.occurrence.demand.role).arity) : Prop :=
  packet.site.inputs[index.val]? = some none ∧ ∃ query,
    (GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration)[index.val]? = some query ∧
      Constructor query

noncomputable def roots (packet : Packet roles)
    (index : Fin (roles packet.site.occurrence.demand.role).arity) : List Origin := by
  classical
  exact (packet.site.inputs[index.val]?).join.toList ++
    if MissingConstructor packet index then
      [.source (packet.site.occurrence.demand.arguments index).1,
       .source (packet.site.occurrence.demand.arguments index).2] else []

theorem retained_member (packet : Packet roles)
    (index : Fin (roles packet.site.occurrence.demand.role).arity)
    (recorded : packet.site.inputs[index.val]? = some (some origin)) : origin ∈ roots packet index := by
  classical
  apply List.mem_append_left
  simp [recorded]

theorem missing_members (packet : Packet roles)
    (index : Fin (roles packet.site.occurrence.demand.role).arity) (missing : MissingConstructor packet index) :
    .source (packet.site.occurrence.demand.arguments index).1 ∈ roots packet index ∧
      .source (packet.site.occurrence.demand.arguments index).2 ∈ roots packet index := by
  classical
  simp [roots,missing]

theorem roots_meaning {model : GeneralNominalCommonBridge.Assignment}
    (state : State roles) (packet : Packet roles)
    (safe : GeneralNominalActualInspectionSteps.Safe state packet)
    (located : GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds)
    (valid : Models state model)
    (index : Fin (roles packet.site.occurrence.demand.role).arity)
    (fitted : GeneralNominalCaptureMerges.Fits model (packet.site.occurrence.demand.arguments index) value)
    (retained : ∀ origin, packet.site.inputs[index.val]? = some (some origin) → At model .actual origin value)
    (member : origin ∈ roots packet index) : At model .actual origin value := by
  classical
  rcases List.mem_append.mp member with old | fallback
  · have recorded : packet.site.inputs[index.val]? = some (some origin) := by
      cases found : packet.site.inputs[index.val]? with
      | none => simp [found] at old
      | some entry => cases entry with
        | none => simp [found] at old
        | some actual => have same : origin = actual := by simpa [found] using old
                         cases same; rfl
    exact retained origin recorded
  · change origin ∈ (if MissingConstructor packet index then _ else []) at fallback
    split at fallback
    · rename_i missing
      obtain ⟨absent,query,queryAt,constructor⟩ := missing
      have equal := safe_missing_root state packet safe located index queryAt constructor absent model valid
      have lower := GeneralNominalStructuralContainment.equal_endpoints_exact model fitted equal
      have upper : Equivalent (model (packet.site.occurrence.demand.arguments index).2).1 value :=
        ⟨subtype_trans equal.2 lower.1,subtype_trans lower.2 equal.1⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at fallback
      rcases fallback with rfl | rfl
      · exact ⟨⟨_,.source _⟩,by intro actual seen; cases seen; exact lower⟩
      · exact ⟨⟨_,.source _⟩,by intro actual seen; cases seen; exact upper⟩
    · cases fallback

theorem packet_forest {model : GeneralNominalCommonBridge.Assignment}
    (state : State roles) (packet : Packet roles)
    (safe : GeneralNominalActualInspectionSteps.Safe state packet)
    (located : GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds)
    (valid : Models state model) (known : Inputs context model packet.site labels) :
    ∃ entries : List Entry, Forest context model entries ∧
      ∀ index : Fin (roles packet.site.occurrence.demand.role).arity, ∀ origin ∈ roots packet index,
        ∃ entry ∈ entries, entry.origin = origin ∧ labels[index.val]? = some entry.pattern := by
  classical
  obtain ⟨length,meanings⟩ := known
  let term := fun index => Classical.choose (meanings index)
  let entries := (List.finRange (roles packet.site.occurrence.demand.role).arity).flatMap fun index =>
    (roots packet index).map fun origin =>
      (⟨origin,labels[index.val]'(by rw [length]; exact index.isLt),term index⟩ : Entry)
  refine ⟨entries,?_,?_⟩
  · intro entry member
    obtain ⟨index,_,present⟩ := List.mem_flatMap.mp member
    obtain ⟨origin,originMem,entryEq⟩ := List.mem_map.mp present
    subst entry
    have meaning := Classical.choose_spec (meanings index)
    exact ⟨meaning.1,roots_meaning state packet safe located valid index meaning.2.1 meaning.2.2 originMem⟩
  · intro index origin member
    refine ⟨⟨origin,labels[index.val]'(by rw [length]; exact index.isLt),term index⟩,?_,rfl,?_⟩
    · exact List.mem_flatMap.mpr ⟨index,List.mem_finRange _,List.mem_map.mpr ⟨origin,member,rfl⟩⟩
    · exact List.getElem?_eq_getElem (by rw [length]; exact index.isLt)

end Yulang.GeneralNominalGroundPacketForest
