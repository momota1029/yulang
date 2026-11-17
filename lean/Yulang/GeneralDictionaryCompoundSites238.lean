import Yulang.GeneralDictionaryCompoundReplay238
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundSites238
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
open GeneralDictionaryCompoundPoint238
open GeneralDictionaryCompoundObstruction238
open GeneralNominalVersionedChildren232 GeneralNominalCenters
abbrev signature : child.Signature roles := ⟨rfl,by intro _ h; cases h⟩
abbrev childSite := GeneralNominalVersionedFrame231.childSite oldPlan child signature

theorem children : GeneralNominalVersionedFrame231.children oldPlan.packet = [childSite.occurrence] := by
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  rfl

theorem emitted_eq : emitted oldPlan = [childSite] := by
  have length := congrArg List.length (emitted_occurrences oldPlan)
  rw [children] at length
  simp only [List.length_map,List.length_singleton] at length
  obtain ⟨one,eq⟩ := List.length_eq_one_iff.mp length
  have member : one ∈ emitted oldPlan := eq ▸ List.mem_singleton_self _
  obtain ⟨clause,present,same⟩ := List.mem_map.mp member
  have visible := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
  have isClause : clause.val = child := List.mem_singleton.mp visible
  have oneEq : one = childSite := by
    rw [←same]
    rcases clause with ⟨clause,valid⟩
    change clause = child at isClause
    subst clause
    rfl
  exact eq.trans (congrArg List.singleton oneEq)

theorem raw_sites : point.core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,childSite.observed] := by
  change [GeneralNominalDemandMerging.pointSite root] ++ rawSites oldPlan = _
  unfold rawSites
  rw [emitted_eq]
  rfl

theorem centers : point.core.sites = [rootSite snapshot.seed root,childSite] := by
  change [rootSite snapshot.seed root] ++ emitted oldPlan = _
  rw [emitted_eq]
  rfl

theorem child_not_root : childSite.occurrence ≠ root := by
  intro equal
  have ids := congrArg GeneralSourceDictionaries.Occurrence.identity equal
  exact (by decide +kernel : childSite.occurrence.identity ≠ root.identity) ids

theorem root_raw {site : GeneralNominalDemandMerging.Site roles}
    (member : site ∈ point.core.erased.current.sites) (occurrence : site.occurrence = root) :
    site = GeneralNominalDemandMerging.pointSite root := by
  rw [raw_sites] at member
  rcases List.mem_cons.mp member with same | member
  · exact same
  · cases List.mem_singleton.mp member
    exact False.elim (child_not_root occurrence)

theorem root_center {site : Site roles}
    (member : site ∈ point.core.sites) (occurrence : site.occurrence = root) :
    site = rootSite snapshot.seed root := by
  rw [centers] at member
  rcases List.mem_cons.mp member with same | member
  · exact same
  · cases List.mem_singleton.mp member
    exact False.elim (child_not_root occurrence)

end Yulang.GeneralDictionaryCompoundSites238
