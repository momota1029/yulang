import Yulang.GeneralDeclarativeWhereStoreAdvance346

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 22000000
namespace Yulang.GeneralDeclarativeWhereCurrent346
open GeneralDictionaryJournalRefinement228Source (roles)
open GeneralWhereOriginSingleSource318 (sourceRegistry oldPlan boundary_checked)
open GeneralWhereOriginSingleCells318 (loNow hi)
open GeneralWherePhysicalOldHead319 (before)
open GeneralWherePhysicalOldInstall319 (installed prior_delta legacy_trace)
open GeneralWherePhysicalPast319 (point loose savedHi)
open GeneralWherePhysicalCurrentRead319 (plan low high address_lo address_hi)
open GeneralWherePhysicalActive319 (ctx active refines)
open GeneralWherePhysicalReobserve319 (updated revision)
open GeneralWherePhysicalFresh319 (lowerSlot upperSlot finalLayout old_lookup_absent lower_id upper_id fresh_sources)
open GeneralWherePhysicalCommit319 (final newChild models)
open GeneralWhereVersionInstall317 (Models install)
open GeneralWhereOriginDelta318 (Delta Cell)
open GeneralWhereOriginTrace318 (Trace rawOf)
open GeneralWhereVersionCompiler317 (schema)
open GeneralDeclarativeWhereStore346 (Store from_trace revise under_revision)
open GeneralDeclarativeWhereReuse346 (SameAuthor)
open GeneralDeclarativeWherePhysical346 (basis derived_ticket exact_batch)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalCommonBridge (Assignment)

theorem stored_before : Store sourceRegistry installed :=
  from_trace (.placed _ _ legacy_trace GeneralWherePhysicalOldInstall319.step prior_delta)

theorem actual_revision : Store sourceRegistry updated :=
  under_revision stored_before revision

noncomputable def actual_delta : Delta (rawOf updated) ctx.state plan where
  refinement := refines
  current := rfl
  cells := [low]
  absent := by
    intro c h
    cases List.mem_singleton.mp h
    change GeneralVersionedEndpointAddress315.atCell plan .lower
      GeneralLiveCompoundRegistry316.otherChild.id 0 GeneralWhereVersionCase317.expr ∉ GeneralNominalState.sources point
    rw [address_lo]
    exact fresh_sources
  fresh_slot := by
    intro c h
    cases List.mem_singleton.mp h
    refine ⟨lowerSlot,?_⟩
    change active.base.source lowerSlot = GeneralVersionedEndpointAddress315.atCell plan .lower
      GeneralLiveCompoundRegistry316.otherChild.id 0 GeneralWhereVersionCase317.expr
    rw [address_lo]
    exact lower_id
  split_slot := by
    intro i _
    refine Fin.addCases (m := 7) (n := 1) (fun previous => ?_) (fun added => ?_) i
    · exact .inl ⟨previous,GeneralWherePhysicalBase319.source_old finalLayout previous⟩
    · have zero : added = 0 := Subsingleton.elim _ _
      subst added
      exact .inr ⟨low,List.mem_cons_self,lower_id.trans address_lo.symm⟩

theorem tracked_final : Store sourceRegistry final := by
  change Store sourceRegistry (install updated ctx plan)
  exact GeneralDeclarativeWhereStoreAdvance346.under_install actual_revision actual_delta GeneralWherePhysicalCommit319.step

theorem old_upper (m : Assignment) (valid : Models updated m) :
    ∃ d : Cell oldPlan, updated.versionedWhere[0]? = some oldPlan ∧
      d.row.target = high.row.target ∧ d.row ∈ (schema oldPlan).equations ∧ SameAuthor high d ∧
      d.row.Holds (variables oldPlan m) m ∧ high.row.Holds (variables plan m) m := by
  have entered : sourceSlot (rawOf updated).base high.row.target = some savedHi := by
    change sourceSlot point.base (GeneralVersionedEndpointAddress315.atCell plan .upper
      GeneralLiveCompoundRegistry316.otherChild.id 0 GeneralWhereVersionCase317.expr) = _
    rw [address_hi]
    exact GeneralWherePhysicalPast319.point_slots.2
  obtain ⟨k,prior,d,stamp,same,row,author,old,current⟩ :=
    GeneralDeclarativeWhereStoreReplay346.replay boundary_checked actual_revision
      GeneralWherePhysicalCurrentFrame319.frame high entered m valid
  change ([oldPlan] : List (GeneralNominalCenters.Plan roles))[k]? = some prior at stamp
  cases k with
  | zero =>
    have e : oldPlan = prior := Option.some.inj stamp
    subst prior
    exact ⟨d,rfl,same,row,author,old,current⟩
  | succ k => simp at stamp

end Yulang.GeneralDeclarativeWhereCurrent346
