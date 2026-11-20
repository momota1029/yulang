import Yulang.GeneralRebaseDepthPrePlan286

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 13500000
namespace Yulang.GeneralRebaseDepthPreInstall286
open GeneralDictionaryOutputDepth252 (roles registry root plan declaration)
open GeneralRebaseDepthPreAnchor286 (Anchor)
open GeneralRebaseDepthPrePlan286 (Certified Kept unrelated_output packet_holds)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedKernel234 (Installable Committed)
open GeneralNominalVersionedInstall232 (install InstallationModels)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedPlans231 (Outputs)
open GeneralRebaseDepthGroundModels285 (FinalTypeCheck InitialTypeCheck)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralRebaseDepthPathKeep285 (Located of_frame)

theorem unique_located {s : State roles} (a : Anchor s) {p q : Plan roles}
    (one : Located s p) (two : Located s q) : p = q := by
  rcases p with ⟨⟨r,c,site,d,check,bs⟩,input,eq⟩
  rcases q with ⟨⟨r',c',site',d',check',bs'⟩,input',eq'⟩
  have rg : r = r' := one.registry_eq.trans two.registry_eq.symm
  have ctx : c = c' := one.context_eq.trans two.context_eq.symm
  have decl : d = d' := one.declaration_eq.trans two.declaration_eq.symm
  have atSite : site = site' := (List.mem_singleton.mp (a.sites ▸ one.raw_recorded)).trans
    (List.mem_singleton.mp (a.sites ▸ two.raw_recorded)).symm
  have atCenter : input = input' := (List.mem_singleton.mp (a.centers ▸ one.center_recorded)).trans
    (List.mem_singleton.mp (a.centers ▸ two.center_recorded)).symm
  subst r'; subst c'; subst d'; subst site'; subst input'
  have sameBounds : bs = bs' := Option.some.inj (one.located.symm.trans two.located)
  subst bs'
  rfl

theorem source_frame {s : State roles} {e : Effect roles}
    (enabled : Installable registry s e) (atRoot : e.plan.packet.site.occurrence = root) :
    Frame registry s.core root e.plan.packet.declaration.id e.plan := by
  have raw := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,atRoot] at raw
  exact raw

theorem installed_uses_certified {s : State roles} (a : Anchor s) (kept : Kept s)
    {e : Effect roles} (enabled : Installable registry s e) (atRoot : e.plan.packet.site.occurrence = root) :
    Certified s e.plan := by
  obtain ⟨p,cert⟩ := kept
  have eq := unique_located a (of_frame (source_frame enabled atRoot)) (of_frame cert.frame)
  exact eq.symm ▸ cert

theorem installation_check {s : State roles} (a : Anchor s) {e : Effect roles}
    (v : Certified s e.plan) (snap : e.snapshot = s.core) (atRoot : e.plan.packet.site.occurrence = root)
    (m : Assignment) :
    InstallationModels s e m ↔ FinalTypeCheck m := by
  rw [← unrelated_output m]
  constructor
  · intro valid
    exact ⟨(a.models m).mp valid.1,(v.outputs m).mp valid.2.1.2.2⟩
  · rintro ⟨source,output⟩
    have packet := packet_holds a v m source output
    have classes : GeneralNominalVersionedEffects231.ClassEffects s.core e.plan.packet.site.occurrence e.plan m :=
      atRoot.symm ▸ v.class_of_output m output
    refine ⟨(a.models m).mpr source,packet,?_,?_,?_,?_⟩
    · refine ⟨GeneralNominalVersionedPlans231.head_models packet,?_⟩
      rw [snap]
      exact classes
    · unfold GeneralNominalVersionedJournal232.Effect.Live
      apply (GeneralNominalVersionedFrameTransport232.class_effects_iff
        (fun _ => GeneralNominalVersionedTerminal232.requests_iff v.leaf)).mpr
      exact classes
    · intro prior member
      rw [a.legacy] at member
      cases member
    · intro prior member
      rw [a.effects] at member
      cases member

theorem installed_check {s : State roles} (a : Anchor s) (kept : Kept s)
    {e : Effect roles} (enabled : Installable registry s e) (atRoot : e.plan.packet.site.occurrence = root)
    (m : Assignment) :
    Models (install s e) m ↔ Models GeneralDictionaryOutputDepthInstall252.installed m :=
  (GeneralNominalVersionedInstall232.install_models enabled.snapshot_eq).trans
    ((installation_check a (installed_uses_certified a kept enabled atRoot) enabled.snapshot_eq atRoot m).trans
      (GeneralRebaseDepthGroundModels285.final_check m).symm)

theorem genuinely_novel {s : State roles} (a : Anchor s) {p : Plan roles} (v : Certified s p) :
    ¬ Committed s p := by
  intro committed
  let m := GeneralDictionaryOutputDepthInstall252.smallModel
  have source : InitialTypeCheck m :=
    (GeneralRebaseDepthGroundModels285.source_inputs _).mp GeneralDictionaryOutputDepthInstall252.small_source
  have outputs := (v.outputs m).mp (committed.1 m ((a.models m).mpr source)).1.2.2
  have strict := (unrelated_output m).mp ⟨source,outputs⟩
  exact GeneralRebaseDepthMinimal285.scalar_ne_output strict.2

end Yulang.GeneralRebaseDepthPreInstall286
