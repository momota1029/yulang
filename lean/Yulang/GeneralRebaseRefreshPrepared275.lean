import Yulang.GeneralRebaseRefreshAcc275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralRebaseRefreshPrepared275
open GeneralNominalCenters (Plan)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry declaration)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedCandidates231 (Prepared HeadModels inputs)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalRecursiveCandidates (arguments)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseRetarget275 (Observed retarget)
open GeneralRebaseRefreshFrame275 (of_frame refinement interpretation moved)
open GeneralNominalVersionedMixedKernel234 (Committed)
open GeneralSourceDictionaries (Occurrence)

theorem candidate_models (p : Plan roles) (m : Assignment) (reg : p.packet.registry = registry)
 (rooted : p.packet.site.occurrence = root) (valid : Holds p m) :
 HeadModels registry p.packet.context root p.packet.declaration p.packet.bounds m := by
 have heads := GeneralNominalVersionedPlans231.head_models valid
 unfold HeadModels
 unfold GeneralNominalVersionedPlans231.HeadModels GeneralNominalVersionedPlans231.privateState
   at heads
 refine ⟨?_,heads.2⟩
 unfold GeneralNominalVersionedCandidates231.privateState
 change GeneralNominalState.Models
   (GeneralNominalState.extend (GeneralNominalVersionedAllocation231.propagate _ _
     (inputs root).identity _ _) [] _) m
 have identity : p.packet.site.occurrence.identity = root.identity := congrArg Occurrence.identity rooted
 have inputID : (inputs root).identity = root.identity := rfl
 simpa only [reg,identity,inputID,GeneralNominalSaturationState.Packet.bindings,GeneralNominalPacketSupport.report] using heads.1

theorem prepared {state : State roles} {ctx : GeneralNominalCandidates.Context}
 {p : Plan roles} (prior : Frame registry state.core root key p)
 (seen : Observed p) (committed : Committed state p)
 (cert : Refresh state ctx) (m : Assignment) (valid : GeneralNominalVersionedJournal232.Models (refresh state ctx) m) :
 Prepared registry ctx root p.packet.declaration := by
 let location := of_frame prior
 let ref := refinement location cert
 have interp := interpretation location cert
 let q := retarget p ref
 have old : Prepared registry p.packet.context root p.packet.declaration := prior.context_eq.symm ▸ prior.prepared
 obtain ⟨metadata,linked,bs,ls,fresh,finished,_⟩ := old
 have bounds : bs = p.packet.bounds := Option.some.inj (ls.symm.trans prior.located)
 subst bs
 have empty : p.packet.declaration.requirements = [] := by rw [location.declaration_eq]
 have packet := GeneralRebaseRetarget275.holds_leaf p ref interp seen empty m valid.1.1
   (committed.1 m ((refresh_models cert).mp valid)).1
 refine ⟨GeneralDictionaryRefinedLocations.metadata _ _ ref interp registry metadata,
   GeneralNominalRefinements.linked ref _ linked,q.packet.bounds,(moved location cert).located,?_,?_,
   m,candidate_models q m prior.registry_eq prior.occurrence_eq packet⟩
 · change GeneralNominalVersionedAllocation231.Fresh ctx.state registry root.identity q.packet.bindings
   rw [show q.packet.bindings = p.packet.bindings from GeneralRebaseRetarget275.packet_bindings p ref interp seen]
   intro key member collision
   apply ref.allocated
   apply fresh key member
   have subset := cert.support _ collision
   rw [ref.seed] at collision
   rw [ref.seed] at subset
   exact prior.context_eq.symm ▸ subset
 · change GeneralNominalRecursiveInspection.Finished (GeneralNominalPacketSupport.report q.packet)
   rw [show GeneralNominalPacketSupport.report q.packet = _ from GeneralRebaseRetarget275.report p ref interp seen]
   exact (GeneralNominalSlotFacts198.finished_report ref.base.embed _).mpr finished

theorem rebuild {state : State roles} {ctx : GeneralNominalCandidates.Context}
 {p : Plan roles} (prior : Frame registry state.core root key p)
 (seen : Observed p) (committed : Committed state p) (cert : Refresh state ctx)
 (m : Assignment) (valid : GeneralNominalVersionedJournal232.Models (refresh state ctx) m) :
 Frame registry (refresh state ctx).core root key (retarget p (refinement (of_frame prior) cert)) :=
 ⟨prior.registry_eq,rfl,prior.occurrence_eq,prior.key_eq,prior.raw_recorded,prior.center_recorded,
   prior.visible,prior.role_eq,(moved (of_frame prior) cert).located,
   prepared (p := p) prior seen committed cert m valid⟩

end Yulang.GeneralRebaseRefreshPrepared275
