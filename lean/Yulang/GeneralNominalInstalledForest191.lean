import Yulang.GeneralNominalTerminalForest191

/-! Finite arbitrary-depth installed dictionary forests on the actual WF kernel.
Build is an execution certificate with real Installable and novelty premises,
not a solver, a classifier, or an assumption of dictionary Evidence. -/
namespace Yulang.GeneralNominalInstalledForest191
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
open GeneralNominalOrdinaryEvidence191
open GeneralNominalTerminalForest191 (path_trans)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

/-- Parent-first actual installs, then exact ordered children, then siblings.
Every transition is source-kernel certified. Existence is deliberately not
asserted for arbitrary selections, stable states, or V6 classifications. -/
inductive Build (registry : Registry) (root : Occurrence roles) :
    State roles → List (Occurrence roles) → List Payload → State roles → Prop
  | nil (state) : Build registry root state [] [] state
  | cons {before middle after : State roles} (plan : Plan roles) (support : List (Occurrence roles))
      (enabled : Installable registry before plan support)
      (reached : GeneralNominalSaturationState.Generated before.core.erased.current root plan.packet.site.occurrence)
      (novel : ¬ GeneralNominalFeedbackSteps.Committed before.core.erased.current plan.packet)
      {childPayloads : List Payload} {demands : List (Occurrence roles)} {payloads : List Payload}
      (children : Build registry root (install before plan support enabled) plan.packet.children childPayloads middle)
      (siblings : Build registry root middle demands payloads after) :
      Build registry root before (plan.packet.site.occurrence :: demands)
        (.node plan.packet.declaration.id childPayloads :: payloads) after

variable {before after : State roles} {demands : List (Occurrence roles)} {payloads : List Payload}

theorem ordinary_trace (build : Build registry root before demands payloads after) :
    B4Target.Steps (OrdinaryStep registry root) before after := by
  induction build with
  | nil => exact .refl
  | cons plan support enabled reached novel children siblings childIH siblingIH =>
    exact path_trans (path_trans (.tail .refl (install_step enabled reached novel)) childIH) siblingIH

theorem execution (build : Build registry root before demands payloads after) :
    B4Target.Steps ((boundary roles).Step registry root) before after :=
  trace_steps (ordinary_trace build)

/-- All nodes of the finite recursive forest are evaluated in the final model.
Child proofs are not caller-supplied Evidence: recursion derives them from the
actual child installation certificates and transports through later siblings. -/
theorem evidence (build : Build registry root before demands payloads after)
    (model : Assignment) (valid : Models after model) :
    All₂ ((boundary roles).Evidence registry after model) demands payloads := by
  induction build with
  | nil => exact .nil
  | cons plan support enabled reached novel children siblings childIH siblingIH =>
    have middleValid := trace_models (ordinary_trace siblings) model valid
    have parent := installed_trace_evidence enabled (ordinary_trace children) model middleValid _
      (childIH middleValid)
    exact .cons ((evidence_iff (ordinary_trace siblings) model valid _ _).mpr parent) (siblingIH valid)

theorem inhabited (build : Build registry root before demands payloads after)
    (initial : ∃ model, Models before model) : ∃ model, Models after model := by
  induction build with
  | nil => exact initial
  | cons plan support enabled reached novel children siblings childIH siblingIH =>
    exact siblingIH (childIH (installed_inhabited enabled))

/-- A nonempty build itself supplies final inhabitation, because its first
real enabled installation contains the common-model witness. -/
theorem nonempty_inhabited {demand : Occurrence roles} {payload : Payload}
    (build : Build registry root before (demand :: demands) (payload :: payloads) after) :
    ∃ model, Models after model := by
  cases build with
  | cons plan support enabled reached novel children siblings =>
    exact inhabited siblings (inhabited children (installed_inhabited enabled))

/-- Conditional soundness of a certified installed tree, not V6 EvidenceNode. -/
theorem tree_sound (demand : Occurrence roles) (payload : Payload)
    (build : Build registry root before [demand] [payload] after) :
    B4Target.Steps ((boundary roles).Step registry root) before after ∧
    (∃ model, Models after model) ∧
    ∀ model, Models after model → (boundary roles).Evidence registry after model demand payload := by
  refine ⟨execution build,nonempty_inhabited build,?_⟩
  intro model valid
  have all := evidence build model valid
  cases all with
  | cons first _ => exact first

/-- Source-connected conditional result: the certificate is a real reachable
execution from this actual WF Initial, with no loss of final models. -/
theorem source_tree_sound (payload : Payload)
    (initial : (boundary roles).Initial registry root before)
    (build : Build registry root before [root] [payload] after) :
    B4TargetV6.Reachable (boundary roles) registry root after ∧
    (∃ model, Models after model) ∧
    ∀ model, Models after model → Models before model ∧
      (boundary roles).Evidence registry after model root payload := by
  have result := tree_sound root payload build
  exact ⟨⟨before,initial,result.1⟩,result.2.1,fun model valid =>
    ⟨steps_models result.1 model valid,result.2.2 model valid⟩⟩

end Yulang.GeneralNominalInstalledForest191
