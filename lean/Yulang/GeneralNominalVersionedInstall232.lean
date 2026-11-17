import Yulang.GeneralNominalVersionedJournal232
import Yulang.GeneralNominalVersionedChildren232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedInstall232
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedChildren232

def installCore (core : GeneralNominalCenteredSteps.State roles) (plan : Plan roles) :
    GeneralNominalCenteredSteps.State roles :=
  { core with
    erased := { core.erased with current := { core.erased.current with
      context := (GeneralNominalVersionedInstallation231.replayPlan plan).packet.context
      packets := plan.packet :: core.erased.current.packets
      sites := core.erased.current.sites ++ rawSites plan
      edges := core.erased.current.edges ++ edges plan } }
    sites := core.sites ++ emitted plan
    sourceRecorded := fun site member => List.mem_append_left _ (core.sourceRecorded site member) }

def installLegacy (legacy : Legacy.State roles) (plan : Plan roles) : Legacy.State roles :=
  ⟨installCore legacy.core plan,legacy.effects⟩

def install (state : State roles) (effect : Effect roles) : State roles :=
  ⟨installLegacy state.legacy effect.plan,effect.plan :: state.plans,effect :: state.effects⟩

theorem requests_included (core : GeneralNominalCenteredSteps.State roles) (plan : Plan roles) :
    ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests core root,
      output ∈ GeneralNominalCenteredHeadOutputs.requests (installCore core plan) root :=
  GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
    (fun _ h => List.mem_append_left _ h) (fun _ h => h)

def LegacyLive (legacy : Legacy.State roles) (plan : Plan roles) (model : Assignment) : Prop :=
  ∀ effect ∈ legacy.effects, effect.Live (installCore legacy.core plan) model

theorem legacy_install_models
    (context : plan.packet.context = legacy.core.erased.current.context)
    (branch : GeneralNominalVersionedPlans231.Holds plan model) :
    Legacy.Models (installLegacy legacy plan) model ↔ Legacy.Models legacy model ∧ LegacyLive legacy plan model := by
  constructor
  · rintro ⟨_,source,raw,sites,plans,effects⟩
    refine ⟨⟨context ▸ branch.1,source,?_,?_,plans,?_⟩,?_⟩
    · exact fun site member => raw site (List.mem_append_left _ member)
    · exact fun site member => sites site (List.mem_append_left _ member)
    · intro effect member
      have pair := effects effect member
      exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
        (requests_included legacy.core plan) pair.2⟩
    · exact fun effect member => (effects effect member).2
  · rintro ⟨⟨_,source,raw,sites,plans,effects⟩,live⟩
    refine ⟨?_,source,appended_raw_holds raw branch,appended_sites_holds sites branch,plans,?_⟩
    · exact (GeneralNominalVersionedInstallation231.replay_private_models plan model).mpr
        (GeneralNominalVersionedPlans231.head_models branch).1
    · exact fun effect member => ⟨(effects effect member).1,live effect member⟩

def InstallationModels (state : State roles) (effect : Effect roles) (model : Assignment) : Prop :=
  Models state model ∧ GeneralNominalVersionedPlans231.Holds effect.plan model ∧
    effect.Holds model ∧ effect.Live (installCore state.core effect.plan) model ∧
    LegacyLive state.legacy effect.plan model ∧
    ∀ prior ∈ state.effects, prior.Live (installCore state.core effect.plan) model

theorem install_models (snapshot : effect.snapshot = state.core) :
    Models (install state effect) model ↔ InstallationModels state effect model := by
  have context : effect.plan.packet.context = state.core.erased.current.context :=
    effect.frame.context_eq.trans (congrArg (fun core => core.erased.current.context) snapshot)
  constructor
  · rintro ⟨legacy,plans,effects⟩
    have branch := plans effect.plan (List.mem_cons_self ..)
    have old := (legacy_install_models context branch).mp legacy
    have current := effects effect (List.mem_cons_self ..)
    refine ⟨⟨old.1,fun plan member => plans plan (List.mem_cons_of_mem _ member),?_⟩,
      branch,current.1,current.2,old.2,?_⟩
    · intro prior member
      have pair := effects prior (List.mem_cons_of_mem _ member)
      exact ⟨pair.1,live_restrict (requests_included state.core effect.plan) pair.2⟩
    · exact fun prior member => (effects prior (List.mem_cons_of_mem _ member)).2
  · rintro ⟨⟨legacy,plans,effects⟩,branch,recorded,current,legacyLive,live⟩
    refine ⟨(legacy_install_models context branch).mpr ⟨legacy,legacyLive⟩,?_,?_⟩
    · intro plan member
      rcases List.mem_cons.mp member with rfl | member
      · exact branch
      · exact plans plan member
    · intro prior member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨recorded,current⟩
      · exact ⟨(effects prior member).1,live prior member⟩

theorem step_models (snapshot : effect.snapshot = state.core)
    (valid : Models (install state effect) model) : Models state model :=
  ((install_models snapshot).mp valid).1

theorem installed_plan : effect.plan ∈ (install state effect).plans := List.mem_cons_self ..
theorem installed_effect : effect ∈ (install state effect).effects := List.mem_cons_self ..

theorem installed_child (member : child ∈ GeneralNominalVersionedFrame231.children effect.plan.packet) :
    (effect.plan.packet.site.occurrence,child) ∈ (install state effect).core.erased.current.edges :=
  appended_child_edge member

theorem legacy_plans_preserved : (install state effect).core.plans = state.core.plans := rfl
theorem legacy_effects_preserved : (install state effect).legacy.effects = state.legacy.effects := rfl
theorem source_preserved : (install state effect).core.erased.source = state.core.erased.source := rfl

end Yulang.GeneralNominalVersionedInstall232
