import Yulang.GeneralMixedCompoundPointChild308
import Yulang.GeneralDictionaryCompoundVacuity239

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralMixedCompoundPointSites308
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralDictionaryCompoundSource238 (child)
open GeneralDictionaryCompoundSites238 (childSite signature)
open GeneralMixedCompoundPointFirstPlan308 (plan pointFirst same_plan)
open GeneralMixedCompoundPointViewTrust308 (observed)
open GeneralNominalVersionedChildren232 (emitted rawSites)
open GeneralNominalCenters (rootSite Site)

theorem child_site :
    GeneralNominalVersionedFrame231.childSite plan child signature = childSite := by
  unfold GeneralNominalVersionedFrame231.childSite GeneralNominalVersionedFrame231.clauseChild
    GeneralDictionaryEmissionPlans.occurrence GeneralDeclarationDemands.emit
    GeneralDeclarationDemands.childDemand GeneralNominalVersionedFrame231.frame
    GeneralNominalVersionedFrame231.emittedCenter
  dsimp only
  congr 1
  congr 1
  congr 1
  all_goals
    funext i
    have zero : i = 0 := Fin.ext (by exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (show i.val < 1 from i.isLt)))
    subst i
    rfl

theorem emitted_exact : emitted plan = [childSite] := by
  have length : (emitted plan).length = 1 := GeneralNominalVersionedChildren232.emitted_length plan
  obtain ⟨one,eq⟩ := List.length_eq_one_iff.mp length
  have member : one ∈ emitted plan := eq ▸ List.mem_singleton_self _
  obtain ⟨clause,present,same⟩ := List.mem_map.mp member
  have visible := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
  have isClause : clause.val = child := List.mem_singleton.mp visible
  have oneEq : one = childSite := by
    rw [← same]
    rcases clause with ⟨clause,valid⟩
    change clause = child at isClause
    subst clause
    exact child_site
  exact eq.trans (congrArg List.singleton oneEq)

theorem centers : observed.core.sites = [rootSite snapshot.seed root,childSite] := by
  change [rootSite snapshot.seed root] ++ emitted plan = _
  rw [emitted_exact]; rfl

theorem raw_sites : observed.core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,childSite.observed] := by
  change [GeneralNominalDemandMerging.pointSite root] ++ rawSites plan = _
  unfold rawSites
  rw [emitted_exact]; rfl

theorem request_exact (focus : GeneralSourceDictionaries.Occurrence roles)
    (output : GeneralSourceState.Output)
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests observed.core focus) :
    output = ⟨0,4⟩ := by
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  rw [raw_sites] at present
  rcases List.mem_cons.mp present with same | present
  · subst site; exact List.mem_singleton.mp within
  · cases List.mem_singleton.mp present
    cases within

theorem equal_outputs (m : GeneralNominalCommonBridge.Assignment) (focus : GeneralSourceDictionaries.Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.EqualOutputs observed.core focus m := by
  intro a one b two _
  cases request_exact focus a one
  cases request_exact focus b two
  exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

end Yulang.GeneralMixedCompoundPointSites308
