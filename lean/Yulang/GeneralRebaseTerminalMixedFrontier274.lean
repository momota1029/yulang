import Yulang.GeneralRebaseTerminalMixedRefresh274

set_option maxRecDepth 23000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralRebaseTerminalMixedFrontier274
open GeneralNominalCandidates (Context)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedJournal232 (Effect)
open GeneralNominalVersionedMixedKernel234 (Stable Step At Installable Committed)
open GeneralNominalState (Known sources)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralDictionaryOptionalInitial229 (registry)
open GeneralRebaseTerminalMixedRefresh274 (raw widthCandidates only_width candidates_tracked candidates_novel)

def WidthRefresh : Prop :=
 ∃ context : Context, ∃ _ : Refresh installed context, ∃ id ∈ widthCandidates, Known context.state id

theorem no_repeat_install (candidate : Effect GeneralDictionaryJournalRefinement228Source.roles)
 (enabled : Installable registry installed candidate) (rooted : candidate.plan.packet.site.occurrence = root) :
 Committed installed candidate.plan := by
 have framed := candidate.frame
 rw [enabled.registry_eq,enabled.snapshot_eq,rooted] at framed
 have same := GeneralDictionaryVersionedSecondStable233.frame_plan framed
 rw [same]
 exact GeneralNominalVersionedCommitted232.replay_committed GeneralDictionaryVersionedPointStage233.point
   GeneralDictionaryVersionedSecondInstall233.effect

theorem only_refresh (after : GeneralNominalVersionedJournal232.State GeneralDictionaryJournalRefinement228Source.roles)
 (step : Step registry root installed after) :
 ∃ ctx : Context, ∃ _ : Refresh installed ctx, after = GeneralNominalVersionedRefresh232.refresh installed ctx ∧
   ∃ id ∈ widthCandidates, Known ctx.state id := by
 obtain ⟨focus,path,action⟩ := step
 have onlyRoot := GeneralDictionaryVersionedSecondStable233.generated_only path
 cases action with
 | administrative action =>
   cases action with
   | enqueue linked absent =>
     exact False.elim (absent _ (GeneralDictionaryVersionedSecondSelected233.raw_sites ▸ List.mem_singleton_self _) onlyRoot.symm)
   | refresh context cert id support was now =>
     exact ⟨context,cert,rfl,id,only_width context cert id support was now,now⟩
   | equate a b one two same novel =>
     exact False.elim (novel (GeneralDictionaryVersionedSecondEquality233.equality_closed a b one two same))
   | reobserve revision _ improves =>
     exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision
       GeneralDictionaryVersionedSecondStable233.point_closed revision improves)
 | refresh whereAt context cert id support was now =>
   exact ⟨context,cert,rfl,id,only_width context cert id support was now,now⟩
 | install effect enabled novel =>
   exact False.elim (novel (no_repeat_install effect enabled onlyRoot))
 | merge a b one two same novel =>
   rw [GeneralDictionaryVersionedSecondSelected233.centers] at one two
   cases List.mem_singleton.mp one
   cases List.mem_singleton.mp two
   exact False.elim (novel (.refl _))

theorem obstruction_of_action (after : GeneralNominalVersionedJournal232.State GeneralDictionaryJournalRefinement228Source.roles)
 (step : Step registry root installed after) : WidthRefresh := by
 obtain ⟨ctx,certificate,_,id,within,known⟩ := only_refresh after step
 exact ⟨ctx,certificate,id,within,known⟩

theorem model_transparent (after : GeneralNominalVersionedJournal232.State GeneralDictionaryJournalRefinement228Source.roles)
 (step : Step registry root installed after) (model : GeneralNominalCommonBridge.Assignment) :
 GeneralNominalVersionedJournal232.Models after model ↔ GeneralNominalVersionedJournal232.Models installed model := by
 obtain ⟨ctx,certificate,rfl,_⟩ := only_refresh after step
 exact GeneralNominalVersionedMixedObservations233.refresh_models certificate

theorem realizes (possible : WidthRefresh) : ∃ after, Step registry root installed after := by
 obtain ⟨ctx,cert,id,owner,seen⟩ := possible
 exact ⟨GeneralNominalVersionedRefresh232.refresh installed ctx,root,.root,
   .refresh root ctx cert id (candidates_tracked id owner) (candidates_novel id owner) seen⟩

theorem exactly (enabled : ∃ after, Step registry root installed after) : WidthRefresh :=
 let ⟨after,step⟩ := enabled
 obstruction_of_action after step

/-- Stronger mixed stability is equivalent to excluding three explicitly
identified private-cache refresh targets. This does not assert they exist. -/
theorem mixed_stable_iff : Stable registry installed root ↔ ¬ WidthRefresh := by
 constructor
 · intro stable possibility
   obtain ⟨next,focus,generated,enabled⟩ := realizes possibility
   exact stable focus generated next enabled
 · intro no focus generated next enabled
   exact no (obstruction_of_action next ⟨focus,generated,enabled⟩)

end Yulang.GeneralRebaseTerminalMixedFrontier274
