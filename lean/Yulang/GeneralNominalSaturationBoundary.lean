import Yulang.GeneralNominalSaturationProgress

/-! A partial field package through the frozen context projection. It does not
construct SourceBoundary: source formation, joint merged-demand applicability,
non-point provenance, journal feedback and termination remain open. The closure
result concerns the certified updates defined here, not full source saturation.
Evidence remains owned by its separate development. -/
namespace Yulang.GeneralNominalSaturationBoundary

open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalSaturationSteps

def vocabulary (roles : Roles.RoleDecls) : B4Target.Vocabulary where
  Registry := Registry
  State := State roles
  Demand := Occurrence roles
  Model := GeneralNominalCommonBridge.Assignment

def localFields (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Fields (vocabulary roles) where
  Checked := fun registry => registry.roles = roles ∧ Checked registry
  Models := Models
  RootPending := fun _ state root => GeneralNominalState.RootPending state.context.state root.demand
  RootK2 := fun _ state root => GeneralNominalMixedRecurrence.RootK2 state.context.state root.demand
  CandidateK2 := fun registry state => GeneralNominalRecursiveCandidates.CandidateK2 registry state.context
  InspectionPending := fun registry state => GeneralNominalRecursiveCandidates.InspectionPending registry state.context
  Survivor := fun registry state => GeneralNominalRecursiveCandidates.Survivor registry state.context
  Reorders := GeneralRegistryReordering.Reorders
  DictionaryEquivalent := GeneralDictionaryPayloadOrder.Equivalent

/-- The three transition signatures, separated from a completed source boundary. -/
structure Transitions (roles : Roles.RoleDecls) where
  Step : Registry → Occurrence roles → State roles → State roles → Prop
  Stable : Registry → State roles → Occurrence roles → Prop
  Generated : Registry → State roles → Occurrence roles → Occurrence roles → Prop

def transitions (roles : Roles.RoleDecls) : Transitions roles where
  Step := Step
  Stable := Stable
  Generated := fun _ state => Generated state

theorem stepModels (roles : Roles.RoleDecls) :
    ∀ registry, (localFields roles).Checked registry → ∀ root before after,
      (transitions roles).Step registry root before after →
      ∀ model, (localFields roles).Models after model → (localFields roles).Models before model := by
  intro registry _ root before after update model valid
  exact step_models update model valid

theorem closure (roles : Roles.RoleDecls) :
    ∀ registry, (localFields roles).Checked registry → ∀ state root,
      (∀ after, ¬ (transitions roles).Step registry root state after) →
      (transitions roles).Stable registry state root ∧
        ∀ child, (transitions roles).Generated registry state root child →
          (transitions roles).Stable registry state child := by
  intro registry _ state root halted
  exact halted_closure halted

theorem survivor_interface (roles : Roles.RoleDecls)
    (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles)) :
    (localFields roles).Survivor registry state root key children ↔
      GeneralNominalRecursiveCandidates.Survivor registry state.context root key children := Iff.rfl

theorem source_models (roles : Roles.RoleDecls) (state : State roles)
    (model : GeneralNominalCommonBridge.Assignment) (valid : (localFields roles).Models state model) :
    GeneralNominalState.Models state.context.state model := valid.1

theorem progress_of_basis (roles : Roles.RoleDecls)
    (registry : Registry) (root : Occurrence roles) (state : State roles)
    (basis : GeneralNominalSaturationProgress.FiniteBasis registry root state) :
    Acc (fun next current => (transitions roles).Step registry root current next) state :=
  GeneralNominalSaturationProgress.accessible_of_finite_basis basis

end Yulang.GeneralNominalSaturationBoundary
