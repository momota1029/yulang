import Yulang.GeneralDeferredLadderRelay304

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralDeferredLadderRelayAdvance304
open GeneralDeferredLadderRelay304 (ctx Relay refState refPhase syntheticEffect realEffect advanceState step_exists)
open GeneralDeferredLadderResnapshot304 (HeadView)
open GeneralDeferredLadderOperationalView304 (View)
open GeneralDeferredLadderEarlyInstall303 (emitted current_requests future_requests)
open GeneralDeferredLadderEarlyReplay303 (all_models after_certificate)
open GeneralObservedLadderRoute301 (focus site)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedInstall232 (install)

theorem trans {a b c : State GeneralDeclarationExamples.roles} (ab : HeadView a b) (bc : HeadView b c) :
    HeadView a c :=
  ⟨⟨ab.raw.sites.trans bc.raw.sites,ab.raw.edges.trans bc.raw.edges,
    ab.raw.aliases.trans bc.raw.aliases,fun m => (ab.raw.models m).trans (bc.raw.models m)⟩,
    ab.context.trans bc.context,ab.centers.trans bc.centers⟩

def next_cert {n k cap s} (rel : Relay n k cap s) (hi : k ≤ n) :
    Refresh (refState n (k+1) (by omega)) (ctx (advanceState rel hi)) :=
  after_certificate (refPhase n k cap) hi (ctx s) rel.cert

theorem reference_after {n k cap s} (rel : Relay n k cap s) (hi : k ≤ n) :
    HeadView (refresh (refState n (k+1) (by omega)) (ctx (advanceState rel hi)))
      (install (refresh (refState n k cap) (ctx s)) (syntheticEffect rel hi)) := by
  let p := refPhase n k cap
  refine ⟨⟨?_,?_,rfl,?_⟩,rfl,?_⟩
  · change p.state.core.erased.current.sites ++ GeneralNominalVersionedChildren232.rawSites
      (GeneralDeferredLadderLedger302.stagePlan p hi) =
        p.state.core.erased.current.sites ++ GeneralNominalVersionedChildren232.rawSites (GeneralDeferredLadderRetargetData302.listPlan p (ctx s) rel.cert k hi)
    rw [GeneralNominalVersionedChildren232.rawSites,GeneralNominalVersionedChildren232.rawSites,
      GeneralDeferredLadderStage302.stage_emits p hi,emitted p hi (ctx s) rel.cert]
  · change p.state.core.erased.current.edges ++ GeneralNominalVersionedChildren232.edges
      (GeneralDeferredLadderLedger302.stagePlan p hi) =
        p.state.core.erased.current.edges ++ GeneralNominalVersionedChildren232.edges (syntheticEffect rel hi).plan
    rw [GeneralDeferredLadderAdvance302.edge_single p hi]
    unfold GeneralNominalVersionedChildren232.edges
    change _ = _ ++ (GeneralNominalVersionedFrame231.children
      (GeneralDeferredLadderRetargetData302.listPlan p (ctx s) rel.cert k hi).packet).map _
    rw [GeneralDeferredLadderSafe303.chosen_children p hi (ctx s) rel.cert]
    rfl
  · intro m
    exact (refresh_models (next_cert rel hi)).trans
      ((GeneralDeferredLadderAdvance302.new_models p hi m).trans
        (all_models p hi (ctx s) rel.cert m).symm)
  · change p.state.core.sites ++ GeneralNominalVersionedChildren232.emitted
      (GeneralDeferredLadderLedger302.stagePlan p hi) =
        p.state.core.sites ++ GeneralNominalVersionedChildren232.emitted (GeneralDeferredLadderRetargetData302.listPlan p (ctx s) rel.cert k hi)
    rw [GeneralDeferredLadderStage302.stage_emits p hi,emitted p hi (ctx s) rel.cert]

def advance {n k cap s} (rel : Relay n k cap s) (hi : k ≤ n) :
    Relay n (k+1) (by omega) (advanceState rel hi) := by
  let p := refPhase n k cap
  refine ⟨next_cert rel hi,?_,trans (reference_after rel hi) ?_,?_,?_,rel.noLegacy⟩
  · exact (GeneralNominalVersionedInstallation231.replay_known (realEffect rel hi).plan (n+1)).mpr rel.known
  · exact GeneralDeferredLadderReinstall304.compared_after rel.view (syntheticEffect rel hi) rfl
      p.legacy_empty rel.noLegacy (current_requests p (ctx s)) (future_requests p hi (ctx s) rel.cert)
      (GeneralDeferredLadderRetargetFrames302.list_held p (ctx s) rel.cert k hi)
  · exact GeneralDeferredLadderOperationalView304.after_choices rel.chosen
      (GeneralDeferredLadderEnabled302.effect p hi) (realEffect rel hi) rfl rfl
  · obtain ⟨initial,init,path⟩ := rel.reached
    exact ⟨initial,init,.tail path (step_exists rel hi)⟩

end Yulang.GeneralDeferredLadderRelayAdvance304
