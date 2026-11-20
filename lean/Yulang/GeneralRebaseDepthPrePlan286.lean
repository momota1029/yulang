import Yulang.GeneralRebaseDepthPreAnchor286

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 13000000
namespace Yulang.GeneralRebaseDepthPrePlan286
open GeneralDictionaryOutputDepth252 (registry root roles plan sourceRegistry model P declaration)
open GeneralRebaseDepthPreAnchor286 (Anchor initial)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedPlans231 (Holds Inputs Outputs)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh refresh_requests)
open GeneralRebaseRetarget275 (Observed retarget)
open GeneralRebaseNonleafCommitted276 (refinement interpretation result)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralNominalVersionedCandidates231 (Prepared inputs)
open GeneralRebaseDepthGroundModels285 (InitialTypeCheck FinalTypeCheck source_inputs)

structure Certified (s : State roles) (p : Plan roles) : Prop where
  frame : Frame registry s.core root 0 p
  observed : Observed p
  ready : Ready s.core root p
  inputs : ∀ m, Inputs p m
  outputs : ∀ m, Outputs p m ↔ Outputs plan m
  class_of_output : ∀ m, Outputs plan m → ClassEffects s.core root p m
  leaf : GeneralNominalVersionedFrame231.children p.packet = []

def Kept (s : State roles) : Prop := ∃ p : Plan roles, Certified s p

theorem start : Kept initial :=
  ⟨plan,GeneralDictionaryOutputDepth252.frame,GeneralRebaseDepthCommit285.seen,
    GeneralDictionaryOutputDepthInstall252.ready,GeneralDictionaryOutputInputs258.inputs,fun _ => Iff.rfl,
    GeneralDictionaryOutputCompletion258.classes,GeneralDictionaryOutputDepth252.children_empty⟩

theorem example_check : InitialTypeCheck model :=
  (source_inputs _).mp GeneralDictionaryOutputDepth252.source_model

theorem packet_holds {s : State roles} {p : Plan roles} (a : Anchor s) (v : Certified s p)
    (m : Assignment) (checked : InitialTypeCheck m) (output : Outputs plan m) : Holds p m :=
  ⟨v.frame.context_eq.symm ▸ (a.rawModels m).mpr checked,v.inputs m,(v.outputs m).mpr output⟩

theorem unrelated_output (m : Assignment) :
    (InitialTypeCheck m ∧ Outputs plan m) ↔ FinalTypeCheck m := by
  unfold FinalTypeCheck
  constructor
  · rintro ⟨source,output⟩
    have eq := (GeneralDictionaryOutputCompletion258.outputs_exact m).mp output
    have close := GeneralRebaseDepthGroundModels285.close_ground m source.2.2
    exact ⟨source,⟨CommonNominalFullCarrier.subtype_trans eq.1 close.1,
      CommonNominalFullCarrier.subtype_trans close.2 eq.2⟩⟩
  · rintro ⟨source,output⟩
    have close := GeneralRebaseDepthGroundModels285.close_ground m source.2.2
    exact ⟨source,(GeneralDictionaryOutputCompletion258.outputs_exact m).mpr
      ⟨CommonNominalFullCarrier.subtype_trans output.1 close.2,
        CommonNominalFullCarrier.subtype_trans close.1 output.2⟩⟩

theorem extended_packet {s : State roles} {p : Plan roles} (a : Anchor s) (v : Certified s p)
    (ctx : GeneralNominalCandidates.Context) (cert : Refresh s ctx) :
    Holds (result v.frame cert) model := by
 let ref := refinement v.frame cert
 have interp := interpretation v.frame cert
 apply (GeneralRebaseNonleafRetarget276.holds_iff p ref interp v.observed model).mpr
 refine ⟨((Anchor.rawModels (GeneralRebaseDepthPreAnchor286.advance a ctx cert) model).mpr example_check),v.inputs model,?_⟩
 exact (v.outputs model).mpr GeneralDictionaryOutputDepth252.output_valid

theorem prepares {s : State roles} {p : Plan roles} (a : Anchor s) (v : Certified s p)
    (ctx : GeneralNominalCandidates.Context) (cert : Refresh s ctx) :
    Prepared registry ctx root p.packet.declaration := by
 let ref := refinement v.frame cert
 have interp := interpretation v.frame cert
 let q := result v.frame cert
 have old : Prepared registry p.packet.context root p.packet.declaration := v.frame.context_eq.symm ▸ v.frame.prepared
 obtain ⟨details,linked,bounds,located,fresh,finished,_⟩ := old
 have sameBounds : bounds = p.packet.bounds := Option.some.inj (located.symm.trans v.frame.located)
 subst bounds
 refine ⟨GeneralDictionaryRefinedLocations.metadata _ _ ref interp registry details,
   GeneralNominalRefinements.linked ref _ linked,q.packet.bounds,?_,?_,?_,model,
   GeneralRebaseDepthPathEvidence285.candidate_models q model v.frame.registry_eq v.frame.occurrence_eq
     (extended_packet a v ctx cert)⟩
 · exact GeneralDictionaryRefinedLocations.arguments _ _ ref (inputs root) _ v.frame.located
 · change GeneralNominalVersionedAllocation231.Fresh ctx.state registry root.identity q.packet.bindings
   rw [show q.packet.bindings = p.packet.bindings from GeneralRebaseRetarget275.packet_bindings p ref interp v.observed]
   intro key member collision
   apply ref.allocated
   apply fresh key member
   rw [ref.seed] at collision
   have held := cert.support _ collision
   exact v.frame.context_eq.symm ▸ held
 · change GeneralNominalRecursiveInspection.Finished (GeneralNominalPacketSupport.report (retarget p ref).packet)
   rw [GeneralRebaseRetarget275.report p ref interp v.observed]
   exact (GeneralNominalSlotFacts198.finished_report ref.base.embed _).mpr finished

theorem frame_next {s : State roles} {p : Plan roles} (a : Anchor s) (v : Certified s p)
    (ctx : GeneralNominalCandidates.Context) (cert : Refresh s ctx) :
    Frame registry (refresh s ctx).core root 0 (result v.frame cert) :=
  ⟨v.frame.registry_eq,rfl,v.frame.occurrence_eq,v.frame.key_eq,v.frame.raw_recorded,v.frame.center_recorded,
    v.frame.visible,v.frame.role_eq,GeneralDictionaryRefinedLocations.arguments _ _
      (refinement v.frame cert) (inputs root) _ v.frame.located,prepares a v ctx cert⟩

theorem advance {s : State roles} (a : Anchor s) (old : Kept s)
    (ctx : GeneralNominalCandidates.Context) (cert : Refresh s ctx) : Kept (refresh s ctx) := by
 obtain ⟨p,v⟩ := old
 let ref := refinement v.frame cert
 have interp := interpretation v.frame cert
 refine ⟨result v.frame cert,frame_next a v ctx cert,
   GeneralRebaseNonleafCommitted276.observed v.frame cert v.observed,
   GeneralRebaseNonleafCommitted276.ready v.frame cert v.ready,?_,?_,?_,
   (GeneralRebaseNonleafRetarget276.children_eq p ref interp v.observed).trans v.leaf⟩
 · intro m
   exact (GeneralRebaseNonleafRetarget276.inputs_iff p ref interp v.observed m).mpr (v.inputs m)
 · intro m
   exact (GeneralRebaseNonleafRetarget276.outputs_iff p ref interp v.observed m).trans (v.outputs m)
 · intro m output
   exact GeneralRebaseRetargetEffects275.class_effects p ref interp _ v.observed m
     ((GeneralNominalVersionedFrameTransport232.class_effects_iff
       (before := (refresh s ctx).core) (after := s.core)
       (fun _ => refresh_requests s ctx) (plan := p) (root := root) (model := m)).mpr
       (v.class_of_output m output))

end Yulang.GeneralRebaseDepthPrePlan286
