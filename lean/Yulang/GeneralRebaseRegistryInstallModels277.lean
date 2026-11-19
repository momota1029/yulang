import Yulang.GeneralRebaseRegistryLocal277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRegistryInstallModels277
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedInstall232 (installCore InstallationModels LegacyLive)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseCompiledRetag277 (retag children_eq holds headModels)
open GeneralRebaseRegistrySurface277 (Surface)
open GeneralRebaseRegistryEvidence277 (frame body_schema body_holds)
variable {roles : Roles.RoleDecls}

theorem ready {core : GeneralNominalCenteredSteps.State roles} {root : Occurrence roles}
    (p : Plan roles) (b : Registry) (ctors) :
    GeneralNominalCenteredHeadMatEffects.Ready core root (retag p b ctors) ↔
      GeneralNominalCenteredHeadMatEffects.Ready core root p := by
  unfold GeneralNominalCenteredHeadMatEffects.Ready
  simp only [body_schema]
  rfl

theorem classes {core : GeneralNominalCenteredSteps.State roles} {root : Occurrence roles}
    (p : Plan roles) (b : Registry) (ctors) (m : Assignment) :
    GeneralNominalVersionedEffects231.ClassEffects core root (retag p b ctors) m ↔
      GeneralNominalVersionedEffects231.ClassEffects core root p m := by
  rw [GeneralNominalVersionedEffects231.class_effects_iff,GeneralNominalVersionedEffects231.class_effects_iff]
  unfold GeneralNominalCenteredHeadMatEffects.ClassEffects
  simp only [body_holds]
  rfl

theorem retagCtors {e : Effect roles} {b : Registry}
    (surface : Surface e.registry b e.snapshot.erased.current.context e.plan.packet.site.occurrence) :
    b.constructors = e.plan.packet.registry.constructors :=
  surface.constructors.symm.trans (congrArg Registry.constructors e.frame.registry_eq).symm

def rebound (e : Effect roles) (b : Registry)
    (surface : Surface e.registry b e.snapshot.erased.current.context e.plan.packet.site.occurrence) :
    Effect roles := by
  let ctors := retagCtors surface
  let p := retag e.plan b ctors
  refine ⟨b,e.snapshot,p,frame surface e.frame,?_,(ready e.plan b ctors).mpr e.ready⟩
  have steady := (GeneralRebaseRegistrySurface277.unique surface).mp e.unique
  change GeneralNominalVersionedCandidates231.Unique b e.snapshot.erased.current.context
    e.plan.packet.site.occurrence e.plan.packet.declaration.id
      (GeneralNominalVersionedFrame231.children (GeneralRebaseCompiledRetag277.retagPacket e.plan.packet b ctors))
  rw [children_eq]
  exact steady

theorem rebound_plan (e : Effect roles) (b : Registry)
    (surface : Surface e.registry b e.snapshot.erased.current.context e.plan.packet.site.occurrence) :
    (rebound e b surface).plan = retag e.plan b (retagCtors surface) := rfl

theorem emitted (p : Plan roles) (b : Registry) (ctors) :
    GeneralNominalVersionedChildren232.emitted (retag p b ctors) =
      GeneralNominalVersionedChildren232.emitted p := by
  unfold GeneralNominalVersionedChildren232.emitted
  apply List.map_congr_left
  intro clause _
  exact GeneralRebaseCompiledRetag277.childSite_eq p b ctors clause.val _

theorem installed_requests (core : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles)
    (p : Plan roles) (b : Registry) (ctors) (output : GeneralSourceState.Output) :
    output ∈ requests (installCore core (retag p b ctors)) root ↔
      output ∈ requests (installCore core p) root := by
  apply GeneralNominalVersionedRefresh232.requests_iff_of_same_lists (before := installCore core (retag p b ctors))
    (after := installCore core p) _ rfl
  change core.erased.current.sites ++ GeneralNominalVersionedChildren232.rawSites (retag p b ctors) =
    core.erased.current.sites ++ GeneralNominalVersionedChildren232.rawSites p
  unfold GeneralNominalVersionedChildren232.rawSites
  rw [emitted]

theorem effect_holds (e : Effect roles) (b : Registry) (m : Assignment)
    (surface : Surface e.registry b e.snapshot.erased.current.context e.plan.packet.site.occurrence) :
    (rebound e b surface).Holds m ↔ e.Holds m := by
  unfold Effect.Holds
  exact and_congr (headModels e.plan.packet b (retagCtors surface) m)
    (classes e.plan b (retagCtors surface) m)

theorem prior_live (prior : Effect roles) (core : GeneralNominalCenteredSteps.State roles)
    (p : Plan roles) (b : Registry) (ctors) (m : Assignment) :
    prior.Live (installCore core (retag p b ctors)) m ↔
      prior.Live (installCore core p) m :=
  GeneralNominalVersionedFrameTransport232.class_effects_iff
    (installed_requests core prior.plan.packet.site.occurrence p b ctors)

theorem legacy_prior_live (prior : GeneralNominalCenteredHeadMatStepJournal.Effect roles)
    (core : GeneralNominalCenteredSteps.State roles)
    (p : Plan roles) (b : Registry) (ctors) (m : Assignment) :
    prior.Live (installCore core (retag p b ctors)) m ↔
      prior.Live (installCore core p) m := by
  unfold GeneralNominalCenteredHeadMatStepJournal.Effect.Live
  rw [← GeneralNominalVersionedEffects231.class_effects_iff,← GeneralNominalVersionedEffects231.class_effects_iff]
  exact GeneralNominalVersionedFrameTransport232.class_effects_iff
    (installed_requests core prior.plan.packet.site.occurrence p b ctors)

theorem new_live (s : State roles) (e : Effect roles) (b : Registry) (m : Assignment)
    (surface : Surface e.registry b e.snapshot.erased.current.context e.plan.packet.site.occurrence) :
    (rebound e b surface).Live (installCore s.core (rebound e b surface).plan) m ↔
      e.Live (installCore s.core e.plan) m := by
  unfold Effect.Live
  exact (classes e.plan b (retagCtors surface) m).trans
    (prior_live e s.core e.plan b (retagCtors surface) m)

theorem installation_equiv (s : State roles) (e : Effect roles) (b : Registry) (m : Assignment)
    (surface : Surface e.registry b e.snapshot.erased.current.context e.plan.packet.site.occurrence) :
    InstallationModels s (rebound e b surface) m ↔ InstallationModels s e m := by
  have H : GeneralNominalVersionedPlans231.Holds (rebound e b surface).plan m ↔
      GeneralNominalVersionedPlans231.Holds e.plan m := holds e.plan b (retagCtors surface) m
  have L : LegacyLive s.legacy (rebound e b surface).plan m ↔ LegacyLive s.legacy e.plan m := by
    unfold LegacyLive
    simp only [rebound_plan,legacy_prior_live]
  have P : (∀ prior ∈ s.effects, prior.Live (installCore s.core (rebound e b surface).plan) m) ↔
      (∀ prior ∈ s.effects, prior.Live (installCore s.core e.plan) m) := by
    simp only [rebound_plan,prior_live]
  unfold InstallationModels
  exact and_congr Iff.rfl (and_congr H (and_congr (effect_holds e b m surface)
    (and_congr (new_live s e b m surface) (and_congr L P))))

theorem installed_models (s : State roles) (e : Effect roles) (b : Registry) (m : Assignment)
    (surface : Surface e.registry b e.snapshot.erased.current.context e.plan.packet.site.occurrence)
    (snapshot : e.snapshot = s.core) :
    Models (GeneralNominalVersionedInstall232.install s (rebound e b surface)) m ↔
      Models (GeneralNominalVersionedInstall232.install s e) m := by
  have same : (rebound e b surface).snapshot = s.core := snapshot
  exact (GeneralNominalVersionedInstall232.install_models same).trans
    ((installation_equiv s e b m surface).trans (GeneralNominalVersionedInstall232.install_models snapshot).symm)

end Yulang.GeneralRebaseRegistryInstallModels277
