import Yulang.GeneralRebaseRegistryInstallStep277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRegistryOneStep277
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedKernel234 (Step At)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedChildren232 (emitted emitted_occurrences edges rawSites)
open GeneralNominalSaturationState (Generated Alias)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralRebaseRegistryInstallStep277 (paired_install)
open GeneralRebaseMixedOwnedTrace277 (Invariant)
open GeneralRebaseRegistryDiagnostics277 (surface_of_covered)
variable {roles : Roles.RoleDecls} {a b : Registry} {s after : State roles} {root : Occurrence roles}

structure SamePorts (a b : State roles) : Prop where
  rawSites : a.core.erased.current.sites = b.core.erased.current.sites
  centers : a.core.sites = b.core.sites
  edges : a.core.erased.current.edges = b.core.erased.current.edges
  aliases : a.core.erased.current.aliases = b.core.erased.current.aliases
  seed : a.core.erased.current.context.state.seed = b.core.erased.current.context.state.seed
  ordinary : a.core.erased.current.context.state.ordinary = b.core.erased.current.context.state.ordinary
  known : ∀ n, GeneralNominalState.Known a.core.erased.current.context.state n ↔
    GeneralNominalState.Known b.core.erased.current.context.state n
  models : ∀ m, Models a m ↔ Models b m

theorem reflexive (s : State roles) : SamePorts s s :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,fun _ => Iff.rfl,fun _ => Iff.rfl⟩

theorem symmetric {a b : State roles} (given : SamePorts a b) : SamePorts b a :=
  ⟨given.rawSites.symm,given.centers.symm,given.edges.symm,given.aliases.symm,given.seed.symm,
    given.ordinary.symm,fun n => (given.known n).symm,fun m => (given.models m).symm⟩

theorem output_requests {a b : State roles} (given : SamePorts a b)
    (focus : Occurrence roles) (request : GeneralSourceState.Output) :
    request ∈ requests a.core focus ↔ request ∈ requests b.core focus :=
  GeneralNominalVersionedRefresh232.requests_iff_of_same_lists given.rawSites given.aliases

theorem alias_forward {a b : State roles} (given : SamePorts a b)
    (old : Alias a.core.erased.current x y) : Alias b.core.erased.current x y := by
  induction old with
  | refl name => exact .refl name
  | edge present => exact .edge (given.aliases ▸ present)
  | symm _ ih => exact .symm ih
  | trans _ _ ih ih' => exact .trans ih ih'

theorem generated_forward {a b : State roles} (given : SamePorts a b)
    (old : Generated a.core.erased.current root focus) : Generated b.core.erased.current root focus := by
  induction old with
  | root => exact .root
  | child _ edge ih => exact .child ih (given.edges ▸ edge)
  | alias _ existing target matching ih =>
    exact .alias ih (given.rawSites ▸ existing) (given.rawSites ▸ target) (alias_forward given matching)

theorem generated {a b : State roles} (given : SamePorts a b) (focus : Occurrence roles) :
    Generated a.core.erased.current root focus ↔ Generated b.core.erased.current root focus :=
  ⟨generated_forward given,generated_forward (symmetric given)⟩

theorem installed_ports (before : State roles) (first last : Effect roles)
    (sameRoot : first.plan.packet.site.occurrence = last.plan.packet.site.occurrence)
    (sameSites : emitted first.plan = emitted last.plan)
    (sameSeed : (install before first).core.erased.current.context.state.seed =
      (install before last).core.erased.current.context.state.seed)
    (sameOrdinary : (install before first).core.erased.current.context.state.ordinary =
      (install before last).core.erased.current.context.state.ordinary)
    (sameKnown : ∀ id, GeneralNominalState.Known (install before first).core.erased.current.context.state id ↔
      GeneralNominalState.Known (install before last).core.erased.current.context.state id)
    (allModels : ∀ m, Models (install before first) m ↔ Models (install before last) m) :
    SamePorts (install before first) (install before last) := by
  have sameKids : GeneralNominalVersionedFrame231.children first.plan.packet =
      GeneralNominalVersionedFrame231.children last.plan.packet := by
    rw [← emitted_occurrences,← emitted_occurrences,sameSites]
  refine ⟨?_,?_,?_,rfl,sameSeed,sameOrdinary,sameKnown,allModels⟩
  · change before.core.erased.current.sites ++ rawSites first.plan =
      before.core.erased.current.sites ++ rawSites last.plan
    unfold rawSites
    rw [sameSites]
  · change before.core.sites ++ emitted first.plan = before.core.sites ++ emitted last.plan
    rw [sameSites]
  · change before.core.erased.current.edges ++ edges first.plan = before.core.erased.current.edges ++ edges last.plan
    unfold edges
    rw [sameRoot,sameKids]

/-- Match a real mixed Step from the *same* state and demand. A single step
may not return literally the same raw journal when a declaration was installed.
Match full models, raw/center sites, actual ordered edges and aliases instead. -/
theorem one_step (safe : Invariant s) (ctors : a.constructors = b.constructors)
    (roster : ∀ focus : Occurrence roles, Generated s.core.erased.current root focus →
      ∀ d : Declaration, d.role = focus.demand.role → (d ∈ a.declarations ↔ d ∈ b.declarations))
    (action : Step a root s after) :
    ∃ other, Step b root s other ∧ SamePorts after other := by
  obtain ⟨focus,reached,op⟩ := action
  cases op with
  | administrative op => exact ⟨_,⟨_,reached,.administrative op⟩,reflexive _⟩
  | refresh site ctx cert id tracked unknown known =>
    exact ⟨_,⟨_,reached,.refresh _ ctx cert id tracked unknown known⟩,reflexive _⟩
  | merge first last one two same novel =>
    exact ⟨_,⟨_,reached,.merge first last one two same novel⟩,reflexive _⟩
  | install effect enabled novel =>
    have surface := surface_of_covered safe.owns ctors (roster _ reached)
    obtain ⟨other,matched,_decl,sameRoot,sameSites,seed,ordinary,known,valid⟩ := paired_install effect enabled surface novel
    exact ⟨_,⟨_,reached,matched⟩,symmetric (installed_ports s other effect sameRoot sameSites seed ordinary known valid)⟩

theorem reached_one_step
    (reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
      sourceReg sourceRoot s)
    (ctors : a.constructors = b.constructors)
    (roster : ∀ focus : Occurrence roles, Generated s.core.erased.current root focus →
      ∀ d : Declaration, d.role = focus.demand.role → (d ∈ a.declarations ↔ d ∈ b.declarations))
    (action : Step a root s after) :
    ∃ other, Step b root s other ∧ SamePorts after other :=
  one_step (GeneralRebaseMixedOwnedTrace277.adapter_reachable reachable) ctors roster action

end Yulang.GeneralRebaseRegistryOneStep277
