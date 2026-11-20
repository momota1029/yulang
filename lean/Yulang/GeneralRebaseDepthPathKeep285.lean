import Yulang.GeneralRebaseDepthPathAnchor285
import Yulang.GeneralNominalVersionedInstalledEvidence233

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 12500000
namespace Yulang.GeneralRebaseDepthPathKeep285
open GeneralDictionaryOutputDepth252 (registry root roles declaration plan initial)
open GeneralDictionaryOutputDepthInstall252 (installed effect installed_model)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedKernel234 (Committed Installable Step)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh refresh_requests)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalRecursiveCandidates (arguments)
open GeneralNominalVersionedCandidates231 (inputs)
open GeneralNominalRefinements (Refines)
open GeneralRebaseRetarget275 (Observed retarget)
open GeneralRebaseDepthPathAnchor285 (Anchor)

structure Located (s : State roles) (p : Plan roles) : Prop where
  registry_eq : p.packet.registry = registry
  context_eq : p.packet.context = s.core.erased.current.context
  declaration_eq : p.packet.declaration = declaration
  raw_recorded : p.packet.site ∈ s.core.erased.current.sites
  center_recorded : p.input ∈ s.core.sites
  located : arguments p.packet.context (inputs root) = some p.packet.bounds

theorem of_frame {s : State roles} {p : Plan roles} {key : Nat} (frame : Frame registry s.core root key p) :
    Located s p :=
  ⟨frame.registry_eq,frame.context_eq,List.mem_singleton.mp frame.visible,frame.raw_recorded,
    frame.center_recorded,frame.located⟩

theorem same_plan {s : State roles} (a : Anchor s) {p q : Plan roles}
    (first : Located s p) (last : Located s q) : p = q := by
 rcases p with ⟨⟨r,c,site,d,check,bs⟩,input,eq⟩
 rcases q with ⟨⟨r',c',site',d',check',bs'⟩,input',eq'⟩
 have rg : r = r' := first.registry_eq.trans last.registry_eq.symm
 have ctx : c = c' := first.context_eq.trans last.context_eq.symm
 have decl : d = d' := first.declaration_eq.trans last.declaration_eq.symm
 have sites : site = site' := (List.mem_singleton.mp (a.sites ▸ first.raw_recorded)).trans
   (List.mem_singleton.mp (a.sites ▸ last.raw_recorded)).symm
 have seen : input = input' := (List.mem_singleton.mp (a.centers ▸ first.center_recorded)).trans
   (List.mem_singleton.mp (a.centers ▸ last.center_recorded)).symm
 subst r'; subst c'; subst d'; subst site'; subst input'
 have bounds : bs = bs' := Option.some.inj (first.located.symm.trans last.located)
 subst bs'
 rfl

def Kept (s : State roles) : Prop := ∃ p, Located s p ∧ Observed p ∧ Committed s p

noncomputable abbrev replay := GeneralNominalVersionedInstallation231.replayPlan plan

theorem replay_frame : Frame registry installed.core root 0 replay :=
  GeneralNominalVersionedInstalledEvidence233.frame rfl installed_model

theorem replay_seen : Observed replay := by
  unfold Observed
  simp only [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead]
  change GeneralNominalRefinementTrace197.ObservedMany replay.packet.context.state
    [GeneralNominalInspection.translate replay.packet.context.state.constructors
      replay.packet.context.interpretation (.var 0)] [((2 : Fin 4),(2 : Fin 4))]
  rw [GeneralNominalInspection.translate.eq_1]
  exact .cons .variables .nil

theorem start : Kept installed :=
  ⟨replay,of_frame replay_frame,replay_seen,GeneralNominalVersionedCommitted232.replay_committed initial effect⟩

theorem advance {s : State roles} (given : Kept s) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh s ctx) : Kept (refresh s ctx) := by
 obtain ⟨p,loc,seen,commit⟩ := given
 let ref : Refines p.packet.context.state ctx.state := loc.context_eq.symm ▸ cert.refines
 have interp : ctx.interpretation = p.packet.context.interpretation :=
   cert.interpretation.trans (congrArg GeneralNominalCandidates.Context.interpretation loc.context_eq).symm
 let q := retarget p ref
 refine ⟨q,?_,GeneralRebaseRetarget275.observed p ref interp seen,?_⟩
 · exact ⟨loc.registry_eq,rfl,loc.declaration_eq,loc.raw_recorded,loc.center_recorded,
     GeneralDictionaryRefinedLocations.arguments p.packet.context ctx ref (inputs root) p.packet.bounds loc.located⟩
 · constructor
   · intro m held
     have old := commit.1 m ((refresh_models cert).mp held)
     refine ⟨(GeneralRebaseNonleafRetarget276.holds_iff p ref interp seen m).mpr
       ⟨held.1.1,old.1.2.1,old.1.2.2⟩,?_⟩
     exact GeneralRebaseRetargetEffects275.class_effects p ref interp _ seen m
       ((GeneralNominalVersionedFrameTransport232.class_effects_iff
         (before := (refresh s ctx).core) (after := s.core)
         (fun _ => refresh_requests s ctx) (plan := p) (model := m)
         (root := p.packet.site.occurrence)).mpr old.2)
   · intro child member
     change child ∈ GeneralNominalVersionedFrame231.children (retarget p ref).packet at member
     rw [GeneralRebaseNonleafRetarget276.children_eq p ref interp seen] at member
     exact commit.2 child member

theorem no_install {s : State roles} (a : Anchor s) (kept : Kept s)
    (effect : Effect roles) (enabled : Installable registry s effect)
    (atRoot : effect.plan.packet.site.occurrence = root) : Committed s effect.plan := by
  obtain ⟨p,stored,_,made⟩ := kept
  have frame := effect.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,atRoot] at frame
  rw [same_plan a (of_frame frame) stored]
  exact made

end Yulang.GeneralRebaseDepthPathKeep285
