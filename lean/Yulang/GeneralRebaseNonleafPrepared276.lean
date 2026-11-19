import Yulang.GeneralRebaseNonleafCommitted276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralRebaseNonleafPrepared276
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedMixedKernel234 (Committed)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedCandidates231 (Prepared HeadModels inputs)
open GeneralRebaseRetarget275 (Observed retarget)
open GeneralRebaseNonleafCommitted276 (refinement interpretation result)

variable {roles : Roles.RoleDecls} {state : State roles} {ctx : GeneralNominalCandidates.Context}
variable {p : Plan roles} {registry : Registry} {root : Occurrence roles} {key : Nat}

theorem heads_of_packet (m : Assignment)
 (reg : p.packet.registry = registry) (rooted : p.packet.site.occurrence = root)
 (valid : GeneralNominalVersionedPlans231.Holds p m) :
 HeadModels registry p.packet.context root p.packet.declaration p.packet.bounds m := by
 rw [←reg,←rooted]
 exact (GeneralNominalVersionedCandidates231.headModels_packet_iff p.packet m).mpr
   (GeneralNominalVersionedPlans231.head_models valid)

theorem located (frame : Frame registry state.core root key p) (cert : Refresh state ctx) :
 GeneralNominalRecursiveCandidates.arguments ctx (inputs root) = some (result frame cert).packet.bounds :=
 GeneralDictionaryRefinedLocations.arguments p.packet.context ctx (refinement frame cert)
   (inputs root) p.packet.bounds frame.located

theorem prepared (frame : Frame registry state.core root key p) (cert : Refresh state ctx)
 (seen : Observed p) (prior : Committed state p) (m : Assignment) (valid : Models (refresh state ctx) m) :
 Prepared registry ctx root p.packet.declaration := by
 let q := result frame cert
 let ref := refinement frame cert
 have interp := interpretation frame cert
 have old : Prepared registry p.packet.context root p.packet.declaration := frame.context_eq.symm ▸ frame.prepared
 obtain ⟨metadata,linked,bounds,resolved,fresh,finished,_⟩ := old
 have same : bounds = p.packet.bounds := Option.some.inj (resolved.symm.trans frame.located)
 subst bounds
 have qualified := (GeneralRebaseNonleafCommitted276.committed frame cert seen prior).1 m valid
 refine ⟨GeneralDictionaryRefinedLocations.metadata _ _ ref interp registry metadata,
   GeneralNominalRefinements.linked ref _ linked,q.packet.bounds,located frame cert,?_,?_,m,?_⟩
 · change GeneralNominalVersionedAllocation231.Fresh ctx.state registry root.identity q.packet.bindings
   rw [show q.packet.bindings = p.packet.bindings from GeneralRebaseRetarget275.packet_bindings p ref interp seen]
   intro k member overlap
   apply ref.allocated
   apply fresh k member
   have support := cert.support _ overlap
   rw [ref.seed] at support
   exact frame.context_eq.symm ▸ support
 · change GeneralNominalRecursiveInspection.Finished (GeneralNominalPacketSupport.report q.packet)
   rw [show GeneralNominalPacketSupport.report q.packet = _ from GeneralRebaseRetarget275.report p ref interp seen]
   exact (GeneralNominalSlotFacts198.finished_report ref.base.embed _).mpr finished
 · exact heads_of_packet (p := q) m frame.registry_eq frame.occurrence_eq qualified.1

theorem frame (old : Frame registry state.core root key p) (cert : Refresh state ctx)
 (seen : Observed p) (prior : Committed state p) (m : Assignment) (valid : Models (refresh state ctx) m) :
 Frame registry (refresh state ctx).core root key (result old cert) :=
 ⟨old.registry_eq,rfl,old.occurrence_eq,old.key_eq,old.raw_recorded,old.center_recorded,
   old.visible,old.role_eq,located old cert,prepared (p := p) old cert seen prior m valid⟩

end Yulang.GeneralRebaseNonleafPrepared276
