import Yulang.GeneralLiveCompoundUpperRefresh316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 20000000
namespace Yulang.GeneralLiveCompoundChildSite316
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry otherChild leaf)
open GeneralLiveCompoundRoot316 (plan)
open GeneralLiveCompoundUpperRefresh316 (upperState)
open GeneralLiveCompoundUpperSnapshot316 (snap context)
open GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedChildren232
open GeneralNominalRecursiveCandidates (arguments report)
open GeneralNominalRecursiveInspection

abbrev signature : otherChild.Signature roles := ⟨rfl,by intro _ h; cases h⟩
abbrev childSite := GeneralNominalVersionedFrame231.childSite plan otherChild signature
abbrev child := childSite.occurrence

theorem children : GeneralNominalVersionedFrame231.children plan.packet = [child] := by
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  rfl

theorem emitted_eq : emitted plan = [childSite] := by
  have length := congrArg List.length (emitted_occurrences plan)
  rw [children] at length
  simp only [List.length_map,List.length_singleton] at length
  obtain ⟨one,eq⟩ := List.length_eq_one_iff.mp length
  have member : one ∈ emitted plan := eq ▸ List.mem_singleton_self _
  obtain ⟨clause,present,same⟩ := List.mem_map.mp member
  have visible := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
  have isClause : clause.val = otherChild := List.mem_singleton.mp visible
  have oneEq : one = childSite := by
    rw [←same]
    rcases clause with ⟨clause,valid⟩
    change clause = otherChild at isClause
    subst clause
    rfl
  exact eq.trans (congrArg List.singleton oneEq)

theorem raw_sites : upperState.core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,childSite.observed] := by
  change [GeneralNominalDemandMerging.pointSite root] ++ rawSites plan = _
  unfold rawSites
  rw [emitted_eq]
  rfl

theorem centers : upperState.core.sites = [rootSite snapshot.seed root,childSite] := by
  change [rootSite snapshot.seed root] ++ emitted plan = _
  rw [emitted_eq]
  rfl

theorem generated : GeneralNominalSaturationState.Generated upperState.core.erased.current root child :=
  .child .root (GeneralNominalVersionedInstall232.installed_child (children ▸ List.mem_singleton_self _))

theorem center_id : childSite.center 0 = GeneralMixedCompoundChildEquality307.mid := by decide +kernel

theorem raw_input : childSite.observed.inputs = [some (.source GeneralMixedCompoundChildEquality307.mid)] := by
  simp [Site.observed,center_id]

theorem located : arguments context (GeneralNominalVersionedCandidates231.inputs child) = some [(5,6)] := by
  decide +kernel

theorem leaf_query : GeneralNominalInspection.queries snap context.interpretation leaf =
    [.node (.variant 0) [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,GeneralNominalInspection.translate,
    GeneralDeclarations.Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,GeneralCandidateInspection.plainNames]

abbrev ref : Origin := .source GeneralMixedCompoundChildEquality307.mid
abbrev projection : Origin := .structural ref (.variant 0) 0

theorem leaf_report : report context leaf [(5,6)] =
    { inspected := [(5,6)], checked := [(5,6),(5,6),(4,2)],
      captures := [⟨0,(4,2),none⟩] } := by
  have sub : inspectMany snap [.variables [0]] [(4,2)] (fun _ => none) 0 =
      {captures := [⟨0,(4,2),none⟩],checked := [(4,2)]} := by
    rw [inspectMany.eq_2,inspectMany.eq_1]
    simp only [inspect.eq_1,Report.append]
    rfl
  unfold report
  rw [leaf_query]
  simp [inspectMany,inspect,Report.visit,Report.append,GeneralMixedCompoundUpperBase307.viewHeads]
  exact ⟨congrArg Report.captures sub,congrArg Report.inspected sub,congrArg Report.checked sub,
    congrArg Report.blocked sub,congrArg Report.conflicts sub,congrArg Report.arity sub,
    congrArg Report.anchors sub,congrArg Report.tests sub⟩

end Yulang.GeneralLiveCompoundChildSite316
