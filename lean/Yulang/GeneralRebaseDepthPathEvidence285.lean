import Yulang.GeneralRebaseDepthPathSharp285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28600
set_option maxHeartbeats 12500000
namespace Yulang.GeneralRebaseDepthPathEvidence285
open GeneralDictionaryOutputDepth252 (registry root roles plan declaration model initial)
open GeneralDictionaryOutputDepthInstall252 (installed effect installed_model)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Frame Evidence)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh refresh_requests)
open GeneralNominalVersionedMixedKernel234 (Committed)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthPathAnchor285 (Anchor)
open GeneralRebaseDepthPathKeep285 (Kept replay replay_frame replay_seen)
open GeneralRebaseRetarget275 (Observed retarget)
open GeneralRebaseNonleafCommitted276 (refinement interpretation result)
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralNominalVersionedCandidates231 (Prepared HeadModels inputs)

theorem candidate_models (p : Plan roles) (m : Assignment)
    (reg : p.packet.registry = registry) (focus : p.packet.site.occurrence = root)
    (valid : GeneralNominalVersionedPlans231.Holds p m) :
    HeadModels registry p.packet.context root p.packet.declaration p.packet.bounds m := by
 have holds := GeneralNominalVersionedPlans231.head_models valid
 unfold HeadModels
 unfold GeneralNominalVersionedPlans231.HeadModels GeneralNominalVersionedPlans231.privateState at holds
 refine ⟨?_,holds.2⟩
 unfold GeneralNominalVersionedCandidates231.privateState
 change GeneralNominalState.Models
   (GeneralNominalState.extend (GeneralNominalVersionedAllocation231.propagate _ _ (inputs root).identity _ _) [] _) m
 have identity := congrArg GeneralSourceDictionaries.Occurrence.identity focus
 have inputID : (inputs root).identity = root.identity := rfl
 simpa only [reg,identity,inputID,GeneralNominalSaturationState.Packet.bindings,GeneralNominalPacketSupport.report] using holds.1

theorem prepared {s : State roles} {ctx : GeneralNominalCandidates.Context}
    {p : Plan roles} (frame : Frame registry s.core root 0 p) (observed : Observed p)
    (done : Committed s p) (cert : Refresh s ctx) (m : Assignment) (valid : Models (refresh s ctx) m) :
    Prepared registry ctx root p.packet.declaration := by
 let ref := refinement frame cert
 have interp := interpretation frame cert
 let q := result frame cert
 have old : Prepared registry p.packet.context root p.packet.declaration := frame.context_eq.symm ▸ frame.prepared
 obtain ⟨details,linked,bounds,located,fresh,finished,_⟩ := old
 have exactBounds : bounds = p.packet.bounds := Option.some.inj (located.symm.trans frame.located)
 subst bounds
 have kernel := (GeneralRebaseNonleafCommitted276.committed frame cert observed done).1 m valid
 refine ⟨GeneralDictionaryRefinedLocations.metadata _ _ ref interp registry details,
   GeneralNominalRefinements.linked ref _ linked,q.packet.bounds,?_,?_,?_,
   m,candidate_models q m frame.registry_eq frame.occurrence_eq kernel.1⟩
 · exact GeneralDictionaryRefinedLocations.arguments _ _ ref (inputs root) _ frame.located
 · change GeneralNominalVersionedAllocation231.Fresh ctx.state registry root.identity q.packet.bindings
   rw [show q.packet.bindings = p.packet.bindings from GeneralRebaseRetarget275.packet_bindings p ref interp observed]
   intro key member collision
   apply ref.allocated
   apply fresh key member
   rw [ref.seed] at collision
   have was := cert.support _ collision
   exact frame.context_eq.symm ▸ was
 · change GeneralNominalRecursiveInspection.Finished (GeneralNominalPacketSupport.report (retarget p ref).packet)
   rw [GeneralRebaseRetarget275.report p ref interp observed]
   exact (GeneralNominalSlotFacts198.finished_report ref.base.embed _).mpr finished

theorem after_frame {s : State roles} {ctx : GeneralNominalCandidates.Context}
    {p : Plan roles} (frame : Frame registry s.core root 0 p) (observed : Observed p)
    (done : Committed s p) (cert : Refresh s ctx) (m : Assignment) (valid : Models (refresh s ctx) m) :
    Frame registry (refresh s ctx).core root 0 (result frame cert) :=
  ⟨frame.registry_eq,rfl,frame.occurrence_eq,frame.key_eq,frame.raw_recorded,frame.center_recorded,
    frame.visible,frame.role_eq,GeneralDictionaryRefinedLocations.arguments _ _
      (refinement frame cert) (inputs root) _ frame.located,prepared (p := p) frame observed done cert m valid⟩

def Witness (s : State roles) : Prop :=
  ∃ p : Plan roles, Frame registry s.core root 0 p ∧ Observed p ∧ Committed s p ∧
    Ready s.core root p ∧ GeneralNominalVersionedFrame231.children p.packet = []

theorem witness_start : Witness installed := by
 have ready := GeneralNominalVersionedInstalledEvidence233.ready (effect := effect) (state := initial) rfl GeneralDictionaryOutputDepth252.children_empty
 exact ⟨replay,replay_frame,replay_seen,GeneralNominalVersionedCommitted232.replay_committed initial effect,
   ready,(GeneralNominalVersionedInstallation231.replay_children _).trans GeneralDictionaryOutputDepth252.children_empty⟩

theorem witness_next {s : State roles} (anchor : Anchor s) (known : Witness s)
    (ctx : GeneralNominalCandidates.Context) (cert : Refresh s ctx) : Witness (refresh s ctx) := by
 obtain ⟨p,frame,seen,done,ready,noChildren⟩ := known
 have valid : Models (refresh s ctx) model := (refresh_models cert).mpr (GeneralRebaseDepthPathAnchor285.valid_model anchor.models)
 exact ⟨result frame cert,after_frame frame seen done cert model valid,
   GeneralRebaseNonleafCommitted276.observed frame cert seen,
   GeneralRebaseNonleafCommitted276.committed frame cert seen done,
   GeneralRebaseNonleafCommitted276.ready frame cert ready,
   (GeneralRebaseNonleafRetarget276.children_eq p (refinement frame cert) (interpretation frame cert) seen).trans noChildren⟩

theorem witness_any {s : State roles} {n : Nat} (path : ActualPath installed s n) :
    Anchor s ∧ Kept s ∧ Witness s := by
  induction path with
  | empty => exact ⟨GeneralRebaseDepthPathAnchor285.initial,GeneralRebaseDepthPathKeep285.start,witness_start⟩
  | more _ action ih =>
    have hop := (GeneralRebaseDepthPathRank285.exact ih.1 ih.2.1).mp action
    cases hop with
    | refresh ctx cert _ _ _ _ =>
      exact ⟨GeneralRebaseDepthPathAnchor285.next ih.1 ctx cert,
        GeneralRebaseDepthPathKeep285.advance ih.2.1 ctx cert,witness_next ih.1 ih.2.2 ctx cert⟩

theorem query {s : State roles} {n : Nat} (path : ActualPath installed s n) (m : Assignment) (payload : Payload) :
    Models s m ∧ Evidence registry s.core m root payload ↔
      Models installed m ∧ Evidence registry installed.core m root payload := by
  have cert := witness_any path
  obtain ⟨p,frame,_,done,ready,noChildren⟩ := cert.2.2
  rw [GeneralRebaseDepthPayload285.same_assignment_exact]
  constructor
  · rintro ⟨holds,existsEvidence⟩
    refine ⟨(GeneralRebaseDepthGroundModels285.final_check m).mp ((cert.1.models m).mp holds),?_⟩
    have reconstructed := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr existsEvidence
    cases reconstructed with
    | node evidence children =>
      obtain ⟨q,detail⟩ := evidence
      have eq := GeneralRebaseDepthPathKeep285.same_plan cert.1
        (GeneralRebaseDepthPathKeep285.of_frame detail.frame) (GeneralRebaseDepthPathKeep285.of_frame frame)
      subst q
      rw [detail.children_eq,noChildren] at children
      cases children
      exact congrArg (fun k => CommonRoleOutermostResolver.Dictionary.node k [])
        (detail.frame.key_eq.symm.trans frame.key_eq)
  · rintro ⟨checks,rfl⟩
    have actual := (cert.1.models m).mpr ((GeneralRebaseDepthGroundModels285.final_check m).mpr checks)
    exact ⟨actual,GeneralNominalVersionedEvidence231.evidence_leaf
      ⟨p,GeneralNominalVersionedEvidence231.certificate_of_semantics frame noChildren.symm
        (done.1 m actual).1 ready (frame.occurrence_eq ▸ (done.1 m actual).2)⟩⟩

end Yulang.GeneralRebaseDepthPathEvidence285
