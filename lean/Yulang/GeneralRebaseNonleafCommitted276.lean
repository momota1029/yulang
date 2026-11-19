import Yulang.GeneralRebaseNonleafRetarget276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 8800000
namespace Yulang.GeneralRebaseNonleafCommitted276
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh refresh_requests)
open GeneralNominalVersionedMixedKernel234 (Committed)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseRetarget275 (Observed retarget)

variable {roles : Roles.RoleDecls} {state : State roles} {ctx : GeneralNominalCandidates.Context}
variable {p : Plan roles} {registry : Registry} {root : Occurrence roles} {key : Nat}

def refinement (frame : Frame registry state.core root key p) (cert : Refresh state ctx) :
 GeneralNominalRefinements.Refines p.packet.context.state ctx.state :=
 frame.context_eq.symm ▸ cert.refines

theorem interpretation (frame : Frame registry state.core root key p) (cert : Refresh state ctx) :
 ctx.interpretation = p.packet.context.interpretation :=
 cert.interpretation.trans (congrArg GeneralNominalCandidates.Context.interpretation frame.context_eq).symm

abbrev result (frame : Frame registry state.core root key p) (cert : Refresh state ctx) : Plan roles :=
 retarget p (refinement frame cert)

theorem observed (frame : Frame registry state.core root key p) (cert : Refresh state ctx) (old : Observed p) :
 Observed (result frame cert) :=
 GeneralRebaseRetarget275.observed p (refinement frame cert) (interpretation frame cert) old

theorem committed (frame : Frame registry state.core root key p) (cert : Refresh state ctx)
 (seen : Observed p) (prior : Committed state p) : Committed (refresh state ctx) (result frame cert) := by
 let ref := refinement frame cert
 have interp := interpretation frame cert
 refine ⟨?_,?_⟩
 · intro m valid
   have recovery := prior.1 m ((refresh_models cert).mp valid)
   refine ⟨(GeneralRebaseNonleafRetarget276.holds_iff p ref interp seen m).mpr
     ⟨valid.1.1,recovery.1.2.1,recovery.1.2.2⟩,?_⟩
   have transfer := (GeneralNominalVersionedFrameTransport232.class_effects_iff
     (before := (refresh state ctx).core) (after := state.core)
     (fun _ => refresh_requests state ctx) (plan := p) (model := m)
     (root := p.packet.site.occurrence)).mpr recovery.2
   exact GeneralRebaseRetargetEffects275.class_effects p ref interp _ seen m transfer
 · intro child member
   have children := GeneralRebaseNonleafRetarget276.children_eq p ref interp seen
   change child ∈ GeneralNominalVersionedFrame231.children (retarget p ref).packet at member
   rw [children] at member
   exact prior.2 child member

theorem ready (frame : Frame registry state.core root key p) (cert : Refresh state ctx)
 (prior : Ready state.core root p) : Ready (refresh state ctx).core root (result frame cert) := by
 have transferred := (GeneralNominalVersionedFrameTransport232.ready_iff
   (before := (refresh state ctx).core) (after := state.core)
   (fun _ => refresh_requests state ctx)).mpr prior
 exact GeneralRebaseRetargetEffects275.ready p (refinement frame cert) (interpretation frame cert) _ transferred

end Yulang.GeneralRebaseNonleafCommitted276
