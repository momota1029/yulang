import Yulang.GeneralNominalCenteredGraph
import Yulang.GeneralNominalCenteredSupport

/-! An additive centered transition kernel. The legacy journal retains ordinary
constraints and support; the center ledger adds actual-argument equations.
Compatibility with the frozen transition system is stated separately. -/
namespace Yulang.GeneralNominalCenteredSteps
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters
open GeneralNominalRecursiveInspection (Origin)

structure State (roles : Roles.RoleDecls) where
  erased : GeneralNominalSupport.Tracked roles
  sites : List (Site roles)
  plans : List (Plan roles) := []
  sourceSites : List (Site roles)
  sourceRecorded : ∀ site ∈ sourceSites, site ∈ sites

def Models (state : State roles) (model : Assignment) : Prop :=
  GeneralNominalSaturationState.Models state.erased.current model ∧
    (∀ site ∈ state.sites, site.Holds model) ∧ ∀ plan ∈ state.plans, plan.Equations model

def initialAt (context : GeneralNominalCandidates.Context) (site : Site roles) : State roles :=
  ⟨GeneralNominalSupport.initial context site.occurrence,[site],[],[site],fun _ member => member⟩

def initial (context : GeneralNominalCandidates.Context) (root : Occurrence roles) : State roles :=
  initialAt context (rootSite context.state.seed root)

theorem initialAt_models (context : GeneralNominalCandidates.Context) (site : Site roles) (model : Assignment) :
    Models (initialAt context site) model ↔ GeneralNominalState.Models context.state model ∧ site.Holds model := by
  constructor
  · intro valid
    exact ⟨valid.1.1,valid.2.1 _ (List.mem_singleton_self _)⟩
  · rintro ⟨source,centers⟩
    exact ⟨(GeneralNominalSaturationState.initial_models context site.occurrence model).mpr source,
      by intro other member; cases List.mem_singleton.mp member; exact centers,
      by intro plan member; cases member⟩

theorem initial_models (context : GeneralNominalCandidates.Context) (root : Occurrence roles) (model : Assignment) :
    Models (initial context root) model ↔ GeneralNominalState.Models context.state model ∧
      (rootSite context.state.seed root).Holds model := by
  constructor
  · intro valid
    exact ⟨valid.1.1,valid.2.1 _ (List.mem_singleton_self _)⟩
  · rintro ⟨source,centers⟩
    exact ⟨(GeneralNominalSaturationState.initial_models context root model).mpr source,
      by intro site member; cases List.mem_singleton.mp member; exact centers,
      by intro plan member; cases member⟩

theorem point_initial_models (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) (model : Assignment) :
    Models (initial context root) model ↔ GeneralNominalState.Models context.state model := by
  rw [initial_models]
  exact ⟨And.left,fun source => ⟨source,point_root_holds _ root point model⟩⟩

def InitialSource (registry : Registry) (root : Occurrence roles) (state : State roles) : Prop :=
  ∃ context site, GeneralNominalSourceFormation.InitialSource registry context root ∧
    site.occurrence = root ∧ site.PointNames ∧ state = initialAt context site

theorem initial_source (source : GeneralNominalSourceFormation.InitialSource registry context root) :
    InitialSource registry root (initial context root) :=
  ⟨context,rootSite context.state.seed root,source,rfl,point_center _ _,rfl⟩

def Plan.tests (plan : Plan roles) : List (Origin × GeneralNominalRecursiveInspection.Test) :=
  plan.headSchema.tests ++ (GeneralNominalPacketSupport.namedSchema plan.packet).tests ++
    plan.packet.declaration.requirements.attach.flatMap fun clause =>
      (plan.schema (plan.childRequests clause.val
        (plan.packet.checked.signature.2.2.2 clause.val clause.property))).tests

def graph (state : State roles) : GeneralNominalCenteredGraph.Journal :=
  ⟨Models state,state.plans.flatMap Plan.tests⟩

theorem graph_tests_hold (state : State roles) (model : Assignment) (valid : Models state model)
    (entry : Origin × GeneralNominalRecursiveInspection.Test) (member : entry ∈ (graph state).tests) :
    GeneralNominalOriginTerms.Head model entry.1 entry.2 := by
  obtain ⟨plan,recorded,member⟩ := List.mem_flatMap.mp member
  have equations := valid.2.2 plan recorded
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · exact equations.2.2.1.1 entry member
    · exact equations.2.2.2.2.1.1 entry member
  · obtain ⟨clause,_,member⟩ := List.mem_flatMap.mp member
    exact (equations.2.2.2.2.2 clause.val clause.property _).2.1 entry member

def Cyclic (state : State roles) (origin : Origin) : Prop :=
  GeneralNominalActualInspectionSteps.Cyclic state.erased.current origin ∨
    GeneralNominalCenteredGraph.Cyclic (graph state) origin

theorem initial_acyclic (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (old : ∀ identity, ¬ GeneralNominalFeedbackK2.Cycle (GeneralNominalSupport.initial context root).current identity)
    (origin : Origin) : ¬ Cyclic (initial context root) origin := by
  rintro (⟨identity,_,cycle,_⟩ | cycle)
  · exact old identity cycle
  · exact GeneralNominalCenteredGraph.empty_acyclic _ rfl origin cycle

def inspection (plan : Plan roles) : GeneralNominalRecursiveInspection.Report plan.packet.context.state :=
  GeneralNominalRecursiveInspection.inspectMany plan.packet.context.state
    (GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration)
    plan.packet.bounds (fun index => ((plan.input.observed.inputs[index]?).join)) 0

def Safe (state : State roles) (plan : Plan roles) : Prop :=
  (inspection plan).inspected.length = (inspection plan).tests.length ∧
    ∀ entry ∈ (inspection plan).tests, ¬ Cyclic state entry.1

def AlternativesSafe (registry : Registry) (state : State roles) (input : Site roles) : Prop :=
  ∀ plan : Plan roles, plan.input = input → plan.packet.registry = registry →
    plan.packet.context = state.erased.current.context →
    plan.packet.declaration ∈ registry.declarations →
    plan.packet.declaration.role = input.occurrence.demand.role →
    GeneralNominalRecursiveCandidates.HeadReady registry state.erased.current.context input.occurrence plan.packet.declaration →
    GeneralNominalRecursiveCandidates.arguments plan.packet.context input.occurrence = some plan.packet.bounds →
    Safe state plan

def RootCycle (state : State roles) (root : Occurrence roles) : Prop :=
  ∃ site ∈ state.sites, site.occurrence = root ∧ ∃ index, Cyclic state (.source (site.center index))

def CandidateCycle (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∃ plan : Plan roles, plan.input ∈ state.sites ∧ plan.input.occurrence = root ∧
    plan.packet.registry = registry ∧ plan.packet.context = state.erased.current.context ∧
    plan.packet.declaration ∈ registry.declarations ∧ plan.packet.declaration.role = root.demand.role ∧
    GeneralNominalRecursiveCandidates.HeadReady registry plan.packet.context root plan.packet.declaration ∧
    GeneralNominalRecursiveCandidates.arguments plan.packet.context root = some plan.packet.bounds ∧
    ∃ entry ∈ (inspection plan).tests, Cyclic state entry.1

def DecisionGuard (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  GeneralNominalCenteredSupport.DecisionGuard registry state.erased state.sourceSites state.plans root

def PacketGuard (state : State roles) (plan : Plan roles) (support : List (Occurrence roles)) : Prop :=
  plan.input ∈ state.sites ∧
  GeneralNominalValueSupport.PacketGuard state.erased plan.packet support ∧
  GeneralNominalCenteredSupport.DecisionGuard plan.packet.registry
    {state.erased with current := {state.erased.current with context := plan.packet.context}}
    state.sourceSites state.plans plan.packet.site.occurrence ∧
  Safe state plan ∧ AlternativesSafe plan.packet.registry state plan.input ∧
  (¬ RootCycle state plan.packet.site.occurrence ∧ ¬ CandidateCycle plan.packet.registry state plan.packet.site.occurrence) ∧
  ∃ model, Models state model ∧ plan.Holds model

noncomputable def install (state : State roles) (plan : Plan roles) (support : List (Occurrence roles)) : State roles :=
  ⟨GeneralNominalSharedSteps.install state.erased plan.packet support,
    state.sites ++ plan.emitted,plan :: state.plans,state.sourceSites,
    fun site member => List.mem_append_left _ (state.sourceRecorded site member)⟩

def administrative (state : State roles) (after : GeneralNominalSaturationState.State roles) : State roles :=
  {state with erased := {state.erased with current := after}}

noncomputable def merge (state : State roles) (first last : Site roles) (support : List (Occurrence roles)) : State roles :=
  {state with erased := GeneralNominalSharedSteps.merge state.erased first.observed last.observed support}

structure Refresh (before : State roles) (after : GeneralNominalCandidates.Context) where
  refines : GeneralNominalRefinements.Refines before.erased.current.context.state after.state
  interpretation : after.interpretation = before.erased.current.context.interpretation
  exact : ∀ model, Models before model → GeneralNominalState.Models after.state model
  support : ∀ source ∈ GeneralNominalState.sources after.state,
    source ∈ GeneralNominalState.sources before.erased.current.context.state

def refresh (state : State roles) (context : GeneralNominalCandidates.Context) : State roles :=
  administrative state (GeneralNominalSaturationState.regenerate state.erased.current context)

theorem refresh_models (certificate : Refresh state context) (model : Assignment) :
    Models (refresh state context) model ↔ Models state model := by
  constructor
  · intro valid
    exact ⟨⟨GeneralNominalRefinements.models certificate.refines model valid.1.1,valid.1.2⟩,valid.2⟩
  · intro valid
    exact ⟨⟨certificate.exact model valid,valid.1.2⟩,valid.2⟩

inductive At (registry : Registry) (before : State roles) : Occurrence roles → State roles → Prop
  | administrative (focus : Occurrence roles) (after : GeneralNominalSaturationState.State roles) :
      GeneralNominalSharedSteps.Administrative registry before.erased.current focus after →
      At registry before focus (administrative before after)
  | refresh (focus : Occurrence roles) (context : GeneralNominalCandidates.Context) :
      Refresh before context → (source : Nat) →
      source ∈ GeneralNominalState.sources before.erased.current.context.state →
      ¬ GeneralNominalState.Known before.erased.current.context.state source →
      GeneralNominalState.Known context.state source → At registry before focus (refresh before context)
  | install (plan : Plan roles) (support : List (Occurrence roles)) :
      GeneralNominalFeedbackSteps.Installable registry before.erased.current plan.packet →
      ¬ GeneralNominalFeedbackSteps.Committed before.erased.current plan.packet → PacketGuard before plan support →
      At registry before plan.packet.site.occurrence (install before plan support)
  | merge (first last : Site roles) (support : List (Occurrence roles)) :
      first ∈ before.sites → last ∈ before.sites → SameInputs (Models before) first last →
      ¬ GeneralNominalSaturationState.Alias before.erased.current first.occurrence.identity last.occurrence.identity →
      GeneralNominalSupportChoices.MergeGuard before.erased first.observed last.observed support →
      At registry before first.occurrence (merge before first last support)

def Step (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  ∃ focus, GeneralNominalSaturationState.Generated before.erased.current root focus ∧ At registry before focus after

def Stable (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∀ focus, GeneralNominalSaturationState.Generated state.erased.current root focus → ∀ after, ¬ At registry state focus after

theorem install_models (same : plan.packet.context = state.erased.current.context) (model : Assignment) :
    Models (install state plan support) model ↔ Models state model ∧ plan.Holds model := by
  change (GeneralNominalSaturationState.Models (GeneralNominalSharedSteps.install state.erased plan.packet support).current model ∧
    (∀ site ∈ state.sites ++ plan.emitted, site.Holds model) ∧
    ∀ other ∈ plan :: state.plans, other.Equations model) ↔ _
  rw [GeneralNominalSharedSteps.install_models same]
  constructor
  · rintro ⟨⟨old,branch⟩,sites,plans⟩
    exact ⟨⟨old,fun site member => sites site (List.mem_append_left _ member),
      fun other member => plans other (List.mem_cons_of_mem _ member)⟩,
      branch,plans plan (List.mem_cons_self ..)⟩
  · rintro ⟨⟨old,sites,plans⟩,branch,equations⟩
    refine ⟨⟨old,branch⟩,?_,?_⟩
    · intro site member
      rcases List.mem_append.mp member with member | member
      · exact sites site member
      · exact emitted_holds plan model ⟨branch,equations⟩ site member
    · intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact equations
      · exact plans other member

theorem step_models (step : Step registry root before after) (model : Assignment)
    (valid : Models after model) : Models before model := by
  obtain ⟨focus,_,action⟩ := step
  cases action with
  | administrative focus after action =>
      exact ⟨(GeneralNominalSupportSteps.administrative_models action model).mp valid.1,valid.2⟩
  | refresh focus context certificate source member unknown known => exact (refresh_models certificate model).mp valid
  | install plan support enabled novel guard => exact ((install_models enabled.1.2.1 model).mp valid).1
  | merge first last support one two same novel guard =>
      exact ⟨((GeneralNominalSaturationState.merge_models ..).mp valid.1).1,valid.2⟩

theorem installed_centers (state : State roles) (plan : Plan roles) (support : List (Occurrence roles)) :
    ∀ site ∈ state.sites, site ∈ (install state plan support).sites :=
  fun _ member => List.mem_append_left _ member

theorem administrative_centers (state : State roles) (after : GeneralNominalSaturationState.State roles) :
    (administrative state after).sites = state.sites := rfl

theorem merge_centers (state : State roles) (first last : Site roles) (support : List (Occurrence roles)) :
    (merge state first last support).sites = state.sites := rfl

theorem guarded_provenance (_guard : PacketGuard state plan support) : GenerationGuard plan := generation_guard plan

theorem tested_cycle_blocks (member : entry ∈ (inspection plan).tests)
    (cycle : Cyclic state entry.1) : ¬ PacketGuard state plan support :=
  fun guard => guard.2.2.2.1.2 entry member cycle

/-- An exact erasure condition, not a theorem that all centered updates satisfy it. -/
def CompatibleStep (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  Step registry root before after ∧ GeneralNominalActualInspectionSteps.Step registry root before.erased after.erased

theorem compatible_erases (step : CompatibleStep registry root before after) :
    GeneralNominalActualInspectionSteps.Step registry root before.erased after.erased := step.2

/-- Exact remaining raw-journal obligations for an installation erasure.
The erased emitter is already definitionally the frozen shared emitter. -/
structure RawPacketCompatibility (state : State roles) (plan : Plan roles) : Prop where
  decision : GeneralNominalSharedSupport.DecisionGuard plan.packet.registry
    {state.erased with current := {state.erased.current with context := plan.packet.context}} plan.packet.site.occurrence
  generation : GeneralNominalSharedCaptures.GenerationGuard state.erased plan.packet
  input : GeneralNominalSharedCaptures.InputCoherence plan.packet
  positions : GeneralNominalActualInspectionSteps.Safe state.erased.current plan.packet
  alternatives : GeneralNominalActualInspectionSteps.AlternativesSafe plan.packet.registry state.erased.current plan.packet.site

theorem raw_guard (centered : PacketGuard state plan support) (raw : RawPacketCompatibility state plan) :
    GeneralNominalActualInspectionSteps.PacketGuard state.erased plan.packet support :=
  ⟨⟨centered.2.1,raw.decision,raw.generation,raw.input⟩,raw.positions,raw.alternatives⟩

theorem administrative_compatible
    (generated : GeneralNominalSaturationState.Generated state.erased.current root focus)
    (action : GeneralNominalSharedSteps.Administrative registry state.erased.current focus after) :
    CompatibleStep registry root state (administrative state after) :=
  ⟨⟨focus,generated,.administrative focus after action⟩,
    ⟨focus,generated,.administrative focus after action⟩⟩

theorem refresh_compatible
    (generated : GeneralNominalSaturationState.Generated state.erased.current root focus)
    (certificate : Refresh state context)
    (raw : ∀ model, GeneralNominalSaturationState.Models state.erased.current model → GeneralNominalState.Models context.state model)
    (source : Nat) (member : source ∈ GeneralNominalState.sources state.erased.current.context.state)
    (unknown : ¬ GeneralNominalState.Known state.erased.current.context.state source)
    (known : GeneralNominalState.Known context.state source) :
    CompatibleStep registry root state (refresh state context) :=
  ⟨⟨focus,generated,.refresh focus context certificate source member unknown known⟩,
    ⟨focus,generated,.administrative focus _ (.refresh focus context
      ⟨certificate.refines,certificate.interpretation,raw,certificate.support⟩ source member unknown known)⟩⟩

theorem merge_compatible (first last : Site roles) (support : List (Occurrence roles))
    (generated : GeneralNominalSaturationState.Generated state.erased.current root first.occurrence)
    (one : first ∈ state.sites) (two : last ∈ state.sites)
    (same : SameInputs (Models state) first last)
    (rawOne : first.observed ∈ state.erased.current.sites) (rawTwo : last.observed ∈ state.erased.current.sites)
    (rawSame : GeneralNominalFeedbackSites.SameInputs state.erased.current first.observed last.observed)
    (novel : ¬ GeneralNominalSaturationState.Alias state.erased.current first.occurrence.identity last.occurrence.identity)
    (guard : GeneralNominalSupportChoices.MergeGuard state.erased first.observed last.observed support) :
    CompatibleStep registry root state (merge state first last support) :=
  ⟨⟨_,generated,.merge first last support one two same novel guard⟩,
    ⟨_,generated,.merge first.observed last.observed support rawOne rawTwo rawSame novel guard⟩⟩

theorem actual_install_lifts (state : State roles) (plan : Plan roles) (support : List (Occurrence roles))
    (generated : GeneralNominalSaturationState.Generated state.erased.current root plan.packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet)
    (centered : PacketGuard state plan support)
    (old : GeneralNominalActualInspectionSteps.PacketGuard state.erased plan.packet support) :
    CompatibleStep registry root state (install state plan support) :=
  ⟨⟨_,generated,.install plan support enabled novel centered⟩,
    ⟨_,generated,.install plan.packet support enabled novel old⟩⟩

theorem compatible_install (state : State roles) (plan : Plan roles) (support : List (Occurrence roles))
    (generated : GeneralNominalSaturationState.Generated state.erased.current root plan.packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet)
    (centered : PacketGuard state plan support) (raw : RawPacketCompatibility state plan) :
    CompatibleStep registry root state (install state plan support) :=
  actual_install_lifts state plan support generated enabled novel centered (raw_guard centered raw)

theorem compatible_steps_erase (path : B4Target.Steps (CompatibleStep registry root) before after) :
    B4Target.Steps (GeneralNominalActualInspectionSteps.Step registry root) before.erased after.erased := by
  induction path with
  | refl => exact .refl
  | tail path step ih => exact .tail ih step.2

theorem accessible_of_erasure
    (accessible : Acc (fun next current => GeneralNominalActualInspectionSteps.Step registry root current next) state.erased) :
    Acc (fun next current => CompatibleStep registry root current next) state := by
  generalize equal : state.erased = erased at accessible
  induction accessible generalizing state with
  | intro erased below ih =>
      constructor
      intro next step
      exact ih next.erased (equal ▸ step.2) rfl

theorem ground_compatible_accessible (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels) :
    Acc (fun next current => CompatibleStep registry root current next) (initial context root) :=
  accessible_of_erasure (GeneralNominalGroundHeadMatching.ground_point_root_accessible checked source point ground)

/-- Only the existing accessibility result is transported; no new descent
argument is introduced here. -/
theorem compatible_terminal_of_accessible
    (accessible : Acc (fun next current => GeneralNominalActualInspectionSteps.Step registry root current next) state.erased) :
    ∃ final, B4Target.Steps (CompatibleStep registry root) state final ∧
      ∀ next, ¬ CompatibleStep registry root final next :=
  GeneralNominalActualBoundary.terminal_of_accessible (accessible_of_erasure accessible)

theorem terminal_of_accessible
    (accessible : Acc (fun next current => Step registry root current next) state) :
    ∃ final, B4Target.Steps (Step registry root) state final ∧ ∀ next, ¬ Step registry root final next :=
  GeneralNominalActualBoundary.terminal_of_accessible accessible

end Yulang.GeneralNominalCenteredSteps
