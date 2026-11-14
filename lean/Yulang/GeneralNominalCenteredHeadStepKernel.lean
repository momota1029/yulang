import Yulang.GeneralNominalCenteredHeadStepEffects
import Yulang.GeneralNominalCenteredHeadBoundary

set_option backward.isDefEq.respectTransparency false

/-! Head-only installation with recorded class equations. Administrative,
refresh and merge certificates are exactly the existing centered certificates. -/
namespace Yulang.GeneralNominalCenteredHeadStepKernel
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Generated)
variable {roles : Roles.RoleDecls}
variable {state before after : State roles} {plan : Plan roles}

def AlternativesSafe (registry : Registry) (state : State roles) (input : Site roles) : Prop :=
  ∀ plan : Plan roles, plan.input = input → plan.packet.registry = registry →
    plan.packet.context = state.core.erased.current.context →
    plan.packet.declaration ∈ registry.declarations →
    plan.packet.declaration.role = input.occurrence.demand.role →
    GeneralNominalCenteredHeadCandidates.Prepared registry state.core.erased.current.context input.occurrence plan.packet.declaration →
    GeneralNominalRecursiveCandidates.arguments plan.packet.context input.occurrence = some plan.packet.bounds →
    GeneralNominalCenteredSteps.Safe state.core plan

def InstallationModels (state : State roles) (plan : Plan roles) (support : List (Occurrence roles)) (model : Assignment) : Prop :=
  Models state model ∧ plan.Holds model ∧
    OutputEquations state.core plan.packet.site.occurrence plan model ∧
    OutputEquations (GeneralNominalCenteredSteps.install state.core plan support) plan.packet.site.occurrence plan model ∧
    ∀ effect ∈ state.effects, effect.Live (GeneralNominalCenteredSteps.install state.core plan support) model

structure Installable (registry : Registry) (state : State roles) (plan : Plan roles)
    (support : List (Occurrence roles)) : Prop where
  frame : Frame registry state.core plan.packet.site.occurrence plan.packet.declaration.id plan
  unique : GeneralNominalCenteredHeadCandidates.Unique registry state.core.erased.current.context
    plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children
  safe : B4TargetV6.SafeKnown (GeneralNominalCenteredHeadBoundary.boundary roles) registry state.core plan.packet.site.occurrence
  ready : EffectsReady state.core plan.packet.site.occurrence plan
  materialized : (GeneralNominalRecursiveCandidates.generated plan.packet.registry plan.packet.context
    plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bounds).unknown = false
  choice : GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current plan.packet
  valueSupport : GeneralNominalValueSupport.PacketGuard state.core.erased plan.packet support
  positions : GeneralNominalCenteredSteps.Safe state.core plan
  alternatives : AlternativesSafe registry state plan.input
  common : ∃ model, InstallationModels state plan support model

def record (enabled : Installable registry state plan support) : Effect roles :=
  ⟨registry,state.core,plan,enabled.frame,enabled.unique,enabled.ready⟩

noncomputable def install (state : State roles) (plan : Plan roles) (support : List (Occurrence roles))
    (enabled : Installable registry state plan support) : State roles :=
  ⟨GeneralNominalCenteredSteps.install state.core plan support,record enabled :: state.effects⟩

def administrative (state : State roles) (after : GeneralNominalSaturationState.State roles) : State roles :=
  ⟨GeneralNominalCenteredSteps.administrative state.core after,state.effects⟩

def refresh (state : State roles) (context : GeneralNominalCandidates.Context) : State roles :=
  ⟨GeneralNominalCenteredSteps.refresh state.core context,state.effects⟩

noncomputable def merge (state : State roles) (first last : Site roles) (support : List (Occurrence roles)) : State roles :=
  ⟨GeneralNominalCenteredSteps.merge state.core first last support,state.effects⟩

inductive At (registry : Registry) (before : State roles) : Occurrence roles → State roles → Prop
  | administrative (focus : Occurrence roles) (after : GeneralNominalSaturationState.State roles) :
      GeneralNominalSharedSteps.Administrative registry before.core.erased.current focus after →
      At registry before focus (administrative before after)
  | refresh (focus : Occurrence roles) (context : GeneralNominalCandidates.Context) :
      GeneralNominalCenteredSteps.Refresh before.core context → (source : Nat) →
      source ∈ GeneralNominalState.sources before.core.erased.current.context.state →
      ¬ GeneralNominalState.Known before.core.erased.current.context.state source →
      GeneralNominalState.Known context.state source → At registry before focus (refresh before context)
  | install (plan : Plan roles) (support : List (Occurrence roles))
      (enabled : Installable registry before plan support) :
      ¬ GeneralNominalFeedbackSteps.Committed before.core.erased.current plan.packet →
      At registry before plan.packet.site.occurrence (install before plan support enabled)
  | merge (first last : Site roles) (support : List (Occurrence roles)) :
      first ∈ before.core.sites → last ∈ before.core.sites →
      SameInputs (GeneralNominalCenteredSteps.Models before.core) first last →
      ¬ GeneralNominalSaturationState.Alias before.core.erased.current first.occurrence.identity last.occurrence.identity →
      GeneralNominalSupportChoices.MergeGuard before.core.erased first.observed last.observed support →
      At registry before first.occurrence (merge before first last support)

def Step (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  ∃ focus, Generated before.core.erased.current root focus ∧ At registry before focus after

def Stable (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state.core.erased.current root focus → ∀ after, ¬ At registry state focus after

theorem install_extends (enabled : Installable registry state plan support) :
    GeneralNominalFeedbackProgress.Extends state.core.erased.current
      (GeneralNominalCenteredSteps.install state.core plan support).erased.current := by
  have refinement := GeneralNominalRefinements.installed plan.packet.registry plan.packet.context
    plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds
  refine ⟨⟨fun model valid => ((GeneralNominalSharedSteps.install_models (support := support) enabled.frame.context_eq model).mp valid).1,
    fun _ member => List.mem_append_left _ member,fun _ member => List.mem_append_left _ member,
    fun _ member => member,?_⟩,?_⟩
  · intro source known
    apply refinement.known source
    simpa only [enabled.frame.context_eq] using known
  · intro model valid
    rw [← enabled.frame.context_eq]
    exact GeneralNominalRefinements.models refinement model valid

theorem at_extends (action : At registry before focus after) :
    GeneralNominalFeedbackProgress.Extends before.core.erased.current after.core.erased.current := by
  cases action with
  | administrative focus after action =>
      exact GeneralNominalReobservationSteps.at_extends (GeneralNominalSupportSteps.administrative_old action)
  | refresh focus context certificate source member unknown known =>
      exact ⟨⟨fun _ valid => ⟨GeneralNominalRefinements.models certificate.refines _ valid.1,valid.2⟩,
        fun _ member => member,fun _ member => member,fun _ member => member,certificate.refines.known⟩,
        GeneralNominalRefinements.models certificate.refines⟩
  | install plan support enabled novel =>
      exact install_extends enabled
  | merge first last support one two same novel guard =>
      exact ⟨⟨fun model valid => ((GeneralNominalSaturationState.merge_models ..).mp valid).1,
        fun _ member => member,fun _ member => member,fun _ member => List.mem_cons_of_mem _ member,
        fun _ known => known⟩,fun model valid => ((GeneralNominalState.extend_models ..).mp valid).1⟩

theorem install_models (enabled : Installable registry state plan support) (model : Assignment) :
    Models (install state plan support enabled) model ↔ InstallationModels state plan support model := by
  constructor
  · rintro ⟨core,ledger⟩
    have branch := (GeneralNominalCenteredSteps.install_models enabled.frame.context_eq model).mp core
    have current := ledger (record enabled) (List.mem_cons_self ..)
    refine ⟨⟨branch.1,?_⟩,branch.2,current.1.2,current.2,?_⟩
    · intro effect member
      have holds := ledger effect (List.mem_cons_of_mem _ member)
      exact ⟨holds.1,live_restrict effect (install_extends enabled).journal holds.2⟩
    · intro effect member
      exact (ledger effect (List.mem_cons_of_mem _ member)).2
  · rintro ⟨old,branch,outputs,current,live⟩
    refine ⟨(GeneralNominalCenteredSteps.install_models enabled.frame.context_eq model).mpr ⟨old.1,branch⟩,?_⟩
    intro effect member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨⟨head_of_plan branch,outputs⟩,current⟩
    · exact ⟨(old.2 effect member).1,live effect member⟩

theorem refresh_models (certificate : GeneralNominalCenteredSteps.Refresh state.core context) (model : Assignment) :
    Models (refresh state context) model ↔ Models state model := by
  constructor
  · intro valid
    exact ⟨(GeneralNominalCenteredSteps.refresh_models certificate model).mp valid.1,
      fun effect member => ⟨(valid.2 effect member).1,
        output_equations_restrict (requests_subset_of_sites_aliases
          (before := state.core) (after := (refresh state context).core) (fun _ h => h) (fun _ h => h))
          (valid.2 effect member).2⟩⟩
  · intro valid
    exact ⟨(GeneralNominalCenteredSteps.refresh_models certificate model).mpr valid.1,
      fun effect member => ⟨(valid.2 effect member).1,
        output_equations_restrict (requests_subset_of_sites_aliases
          (before := (refresh state context).core) (after := state.core) (fun _ h => h) (fun _ h => h))
          (valid.2 effect member).2⟩⟩

theorem stepModels (step : Step registry root before after) (model : Assignment)
    (valid : Models after model) : Models before model := by
  obtain ⟨focus,_,action⟩ := step
  have growth := (at_extends action).journal
  cases action with
  | install plan support enabled novel => exact ((install_models enabled model).mp valid).1
  | refresh focus context certificate source member unknown known => exact (refresh_models certificate model).mp valid
  | administrative focus after action =>
      exact ⟨⟨(GeneralNominalSupportSteps.administrative_models action model).mp valid.1.1,valid.1.2⟩,
        fun effect member => ⟨(valid.2 effect member).1,live_restrict effect growth (valid.2 effect member).2⟩⟩
  | merge first last support one two same novel guard =>
      exact ⟨⟨((GeneralNominalSaturationState.merge_models ..).mp valid.1.1).1,valid.1.2⟩,
        fun effect member => ⟨(valid.2 effect member).1,live_restrict effect growth (valid.2 effect member).2⟩⟩

theorem steps_models (path : B4Target.Steps (Step registry root) before after) :
    ∀ model, Models after model → Models before model := by
  induction path with
  | refl => exact fun _ valid => valid
  | tail _ step ih => exact fun model valid => ih model (stepModels step model valid)

theorem closure (halted : ∀ after, ¬ Step registry root state after) :
    Stable registry state root ∧ ∀ child, Generated state.core.erased.current root child → Stable registry state child := by
  have stable : Stable registry state root := fun focus generated after action => halted after ⟨focus,generated,action⟩
  exact ⟨stable,fun child reached focus path => stable focus (GeneralNominalSaturationState.generated_trans reached path)⟩

theorem installed_inhabited (enabled : Installable registry state plan support) :
    ∃ model, Models (install state plan support enabled) model := by
  obtain ⟨model,valid⟩ := enabled.common
  exact ⟨model,(install_models enabled model).mpr valid⟩

end Yulang.GeneralNominalCenteredHeadStepKernel
