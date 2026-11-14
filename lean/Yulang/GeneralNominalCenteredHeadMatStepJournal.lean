import Yulang.GeneralNominalCenteredHeadMatStepPackets

set_option backward.isDefEq.respectTransparency false

/-! A corrected journal interprets every stored plan with total equations.
Legacy packet and support data have no semantic authority here. New raw sites
record the emitted centers directly, without recovering output captures. -/
namespace Yulang.GeneralNominalCenteredHeadMatStepJournal
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatEffects (ClassEffects Ready)
open GeneralNominalCenteredHeadMatStepPackets (Holds)
variable {roles : Roles.RoleDecls}

structure Effect (roles : Roles.RoleDecls) where
  registry : Registry
  snapshot : GeneralNominalCenteredSteps.State roles
  plan : Plan roles
  frame : GeneralNominalCenteredHeadOutputs.Frame registry snapshot plan.packet.site.occurrence plan.packet.declaration.id plan
  unique : GeneralNominalCenteredHeadCandidates.Unique registry snapshot.erased.current.context
    plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children
  ready : Ready snapshot plan.packet.site.occurrence plan

def Effect.Holds (effect : Effect roles) (model : Assignment) : Prop :=
  GeneralNominalCenteredHeadOutputs.HeadEquations effect.plan model ∧
    ClassEffects effect.snapshot effect.plan.packet.site.occurrence effect.plan model

def Effect.Live (effect : Effect roles) (core : GeneralNominalCenteredSteps.State roles) (model : Assignment) : Prop :=
  ClassEffects core effect.plan.packet.site.occurrence effect.plan model

structure State (roles : Roles.RoleDecls) where
  core : GeneralNominalCenteredSteps.State roles
  effects : List (Effect roles) := []

def Models (state : State roles) (model : Assignment) : Prop :=
  GeneralNominalState.Models state.core.erased.current.context.state model ∧
  GeneralNominalState.Models state.core.erased.source.state model ∧
  (∀ site ∈ state.core.erased.current.sites, GeneralNominalSaturationState.SiteHolds site model) ∧
  (∀ site ∈ state.core.sites, site.Holds model) ∧
  (∀ plan ∈ state.core.plans, Holds plan model) ∧
  ∀ effect ∈ state.effects, effect.Holds model ∧ effect.Live state.core model

def initial (context : GeneralNominalCandidates.Context) (root : Occurrence roles) : State roles :=
  ⟨GeneralNominalCenteredSteps.initial context root,[]⟩

theorem initial_models (context : GeneralNominalCandidates.Context) (root : Occurrence roles) (model : Assignment) :
    Models (initial context root) model ↔ GeneralNominalState.Models context.state model ∧
      (rootSite context.state.seed root).Holds model := by
  constructor
  · intro valid
    exact ⟨valid.1,valid.2.2.2.1 _ (List.mem_singleton_self _)⟩
  · rintro ⟨source,centers⟩
    exact ⟨source,source,(by intro site member; cases List.mem_singleton.mp member; exact GeneralNominalSaturationState.point_holds _ _),
      (by intro site member; cases List.mem_singleton.mp member; exact centers),
      (by intro plan member; cases member),(by intro effect member; cases member)⟩

theorem point_initial_models {root : Occurrence roles} (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) :
    Models (initial context root) model ↔ GeneralNominalState.Models context.state model := by
  rw [initial_models]
  exact ⟨And.left,fun source => ⟨source,point_root_holds _ _ point _⟩⟩

def installCore (core : GeneralNominalCenteredSteps.State roles) (plan : Plan roles) : GeneralNominalCenteredSteps.State roles :=
  { core with
    erased := { core.erased with current := { core.erased.current with
      context := plan.packet.privateContext
      packets := plan.packet :: core.erased.current.packets
      sites := core.erased.current.sites ++ plan.emitted.map Site.observed
      edges := core.erased.current.edges ++ plan.packet.children.map (fun child => (plan.packet.site.occurrence,child)) } }
    sites := core.sites ++ plan.emitted
    plans := plan :: core.plans
    sourceRecorded := fun site member => List.mem_append_left _ (core.sourceRecorded site member) }

def install (state : State roles) (effect : Effect roles) : State roles :=
  ⟨installCore state.core effect.plan,effect :: state.effects⟩

def change (state : State roles) (after : GeneralNominalSaturationState.State roles) : State roles :=
  ⟨GeneralNominalCenteredSteps.administrative state.core after,state.effects⟩

def refresh (state : State roles) (context : GeneralNominalCandidates.Context) : State roles :=
  ⟨GeneralNominalCenteredSteps.refresh state.core context,state.effects⟩

def merge (state : State roles) (first last : Site roles) : State roles :=
  change state (GeneralNominalSaturationState.merge state.core.erased.current first.observed last.observed)

variable {state : State roles} {effect : Effect roles} {model : Assignment}

def InstallationModels (state : State roles) (effect : Effect roles) (model : Assignment) : Prop :=
  Models state model ∧ Holds effect.plan model ∧ effect.Holds model ∧
    effect.Live (installCore state.core effect.plan) model ∧
    ∀ prior ∈ state.effects, prior.Live (installCore state.core effect.plan) model

theorem install_models (snapshot : effect.snapshot = state.core) :
    Models (install state effect) model ↔ InstallationModels state effect model := by
  have context : effect.plan.packet.context = state.core.erased.current.context :=
    effect.frame.context_eq.trans (congrArg (fun s => s.erased.current.context) snapshot)
  constructor
  · rintro ⟨_,source,raw,sites,plans,effects⟩
    have branch := plans effect.plan (List.mem_cons_self ..)
    have current := effects effect (List.mem_cons_self ..)
    refine ⟨⟨context ▸ branch.1,source,fun site member => raw site (List.mem_append_left _ member),
      fun site member => sites site (List.mem_append_left _ member),
      fun plan member => plans plan (List.mem_cons_of_mem _ member),?_⟩,branch,current.1,current.2,?_⟩
    · intro prior member
      have pair := effects prior (List.mem_cons_of_mem _ member)
      exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
        (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
          (before := state.core) (after := installCore state.core effect.plan)
          (fun _ h => List.mem_append_left _ h) (fun _ h => h)) pair.2⟩
    · exact fun prior member => (effects prior (List.mem_cons_of_mem _ member)).2
  · rintro ⟨old,branch,recorded,current,live⟩
    refine ⟨GeneralNominalCenteredHeadMatStepPackets.private_models branch,old.2.1,?_,?_,?_,?_⟩
    · intro site member
      rcases List.mem_append.mp member with present | emitted
      · exact old.2.2.1 site present
      · obtain ⟨center,present,rfl⟩ := List.mem_map.mp emitted
        exact observed_holds center model (GeneralNominalCenteredHeadMatStepPackets.emitted_holds branch present)
    · intro site member
      exact (List.mem_append.mp member).elim (old.2.2.2.1 site)
        (GeneralNominalCenteredHeadMatStepPackets.emitted_holds branch)
    · intro plan member
      rcases List.mem_cons.mp member with rfl | present
      · exact branch
      · exact old.2.2.2.2.1 plan present
    · intro prior member
      rcases List.mem_cons.mp member with rfl | present
      · exact ⟨recorded,current⟩
      · exact ⟨(old.2.2.2.2.2 prior present).1,live prior present⟩

theorem installed_inhabited (snapshot : effect.snapshot = state.core)
    (common : ∃ model, InstallationModels state effect model) : ∃ model, Models (install state effect) model := by
  obtain ⟨model,valid⟩ := common
  exact ⟨model,(install_models snapshot).mpr valid⟩

theorem installed_packet : effect.plan.packet ∈ (install state effect).core.erased.current.packets :=
  List.mem_cons_self ..

theorem installed_child (member : child ∈ effect.plan.packet.children) :
    (effect.plan.packet.site.occurrence,child) ∈ (install state effect).core.erased.current.edges :=
  List.mem_append_right _ (List.mem_map.mpr ⟨child,member,rfl⟩)

theorem merge_models : Models (merge state first last) model ↔ Models state model ∧
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalDemandMerging.outputAtoms first.observed last.observed) ∧
    ∀ effect ∈ state.effects, effect.Live (merge state first last).core model := by
  constructor
  · rintro ⟨context,source,raw,sites,plans,effects⟩
    obtain ⟨context,atoms⟩ := (GeneralNominalState.extend_models ..).mp context
    refine ⟨⟨context,source,raw,sites,plans,?_⟩,atoms,fun effect member => (effects effect member).2⟩
    intro effect member
    have pair := effects effect member
    exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
      (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
        (before := state.core) (after := (merge state first last).core)
        (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h)) pair.2⟩
  · rintro ⟨old,atoms,live⟩
    exact ⟨(GeneralNominalState.extend_models ..).mpr ⟨old.1,atoms⟩,old.2.1,old.2.2.1,old.2.2.2.1,
      old.2.2.2.2.1,fun effect member => ⟨(old.2.2.2.2.2 effect member).1,live effect member⟩⟩

theorem live_equal_outputs (valid : Models state model) (recorded : effect ∈ state.effects) :
    GeneralNominalCenteredHeadOutputs.EqualOutputs state.core effect.plan.packet.site.occurrence model :=
  (valid.2.2.2.2.2 effect recorded).2.2

end Yulang.GeneralNominalCenteredHeadMatStepJournal
