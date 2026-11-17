import Yulang.GeneralDictionaryMixedGround218PointInstall235
import Yulang.GeneralDictionaryMixedGround218PointChildren235
import Yulang.GeneralDictionaryMixedGround218PointStable235
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218PointInstalledShape235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (clause childSite)
open GeneralDictionaryGroundCopy218Reinstall (newChild)
open GeneralDictionaryGroundCopy218SaturatedParent (planFor packetFor)
open GeneralDictionaryMixedGround218PointPacket235 (plan packet)
open GeneralDictionaryMixedGround218PointInstall235 (installed)
open GeneralNominalVersionedChildren232

theorem child_eq (allocated reserved ordinary) (valid : clause.Signature roles) :
    GeneralNominalVersionedFrame231.childSite (planFor allocated reserved ordinary) clause valid = newChild := by
  have occurrence : (GeneralNominalVersionedFrame231.childSite (planFor allocated reserved ordinary) clause valid).occurrence = newChild.occurrence := by
    have eq := GeneralDictionaryMixedGround218PointChildren235.children_eq allocated reserved ordinary
    unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit at eq
    simp only [GeneralDictionaryGroundCopy218Install.canonical_declaration] at eq
    change [_] = [_] at eq
    exact (List.cons.inj eq).1
  unfold GeneralNominalVersionedFrame231.childSite GeneralDictionaryGroundCopy218Reinstall.newChild GeneralNominalCenters.Plan.childSite
  congr 1
  funext i
  rw [GeneralNominalVersionedFrame231.emittedCenter_eq]
  unfold GeneralNominalCenters.Plan.emittedCenter
  simp only [GeneralDictionaryGroundCopy218SaturatedParent.binder_same]


theorem emitted_eq (allocated reserved ordinary) : emitted (planFor allocated reserved ordinary) = [newChild] := by
  have length := congrArg List.length (emitted_occurrences (planFor allocated reserved ordinary))
  rw [GeneralDictionaryMixedGround218PointChildren235.children_eq] at length
  simp only [List.length_map,List.length_singleton] at length
  obtain ⟨one,eq⟩ := List.length_eq_one_iff.mp length
  have member : one ∈ emitted (planFor allocated reserved ordinary) := eq ▸ List.mem_singleton_self _
  obtain ⟨c,present,same⟩ := List.mem_map.mp member
  have visible := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr c.property
  have isClause : c.val = clause := List.mem_singleton.mp visible
  have child := child_eq allocated reserved ordinary
    (GeneralDictionaryGroundCopy218Install.declaration_checked.signature.2.2.2 clause (List.mem_singleton_self _))
  have oneEq : one = newChild := by
    rw [←same]
    rcases c with ⟨c,valid⟩
    change c = clause at isClause
    subst c
    exact child
  exact eq.trans (congrArg List.singleton oneEq)

theorem initial_child_eq (valid : clause.Signature roles) :
    GeneralNominalVersionedFrame231.childSite GeneralDictionaryGroundCopy218Install.plan clause valid = childSite := by
  have occurrence := GeneralDictionaryMixedGround218Frame234.children_eq
  rw [GeneralDictionaryGroundCopy218Install.children_exact] at occurrence
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit at occurrence
  simp only [GeneralDictionaryGroundCopy218Install.canonical_declaration] at occurrence
  change [_] = [_] at occurrence
  have occ := (List.cons.inj occurrence).1
  unfold GeneralNominalVersionedFrame231.childSite GeneralDictionaryGroundCopy218Install.childSite GeneralNominalCenters.Plan.childSite
  congr 1
  funext i
  exact GeneralNominalVersionedFrame231.emittedCenter_eq _ _ _ _

theorem initial_emitted : emitted GeneralDictionaryGroundCopy218Install.plan = [childSite] := by
  have length := congrArg List.length (emitted_occurrences GeneralDictionaryGroundCopy218Install.plan)
  rw [GeneralDictionaryMixedGround218Frame234.children_eq,GeneralDictionaryGroundCopy218Install.children_exact] at length
  simp only [List.length_map,List.length_singleton] at length
  obtain ⟨one,eq⟩ := List.length_eq_one_iff.mp length
  have member : one ∈ emitted GeneralDictionaryGroundCopy218Install.plan := eq ▸ List.mem_singleton_self _
  obtain ⟨c,present,same⟩ := List.mem_map.mp member
  have visible := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr c.property
  have isClause : c.val = clause := List.mem_singleton.mp visible
  have oneEq : one = childSite := by
    rw [←same]
    rcases c with ⟨c,valid⟩
    change c = clause at isClause
    subst c
    exact initial_child_eq _
  exact eq.trans (congrArg List.singleton oneEq)


theorem sites : GeneralDictionaryMixedGround218PointStable235.Sites installed := by
  constructor
  · change ([GeneralDictionaryGroundCopy218Install.plan.input] ++ emitted GeneralDictionaryGroundCopy218Install.plan) ++ emitted plan = _
    rw [initial_emitted,emitted_eq]
    rfl
  constructor
  · change ([GeneralNominalDemandMerging.pointSite root] ++ rawSites GeneralDictionaryGroundCopy218Install.plan) ++ rawSites plan = _
    unfold rawSites
    rw [initial_emitted,emitted_eq]
    rfl
  · change edges GeneralDictionaryGroundCopy218Install.plan ++ edges plan = _
    unfold edges
    rw [GeneralDictionaryMixedGround218Frame234.children_eq,GeneralDictionaryGroundCopy218Install.children_exact,
      GeneralDictionaryMixedGround218PointChildren235.children_eq]
    rfl
end Yulang.GeneralDictionaryMixedGround218PointInstalledShape235
