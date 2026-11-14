import Yulang.GeneralNominalOrdinaryEvidence191

/-! An explicit certificate for a finite sequence of real terminal installs.
This is a restricted execution witness, not a replacement language semantics.
The resulting ordered child dictionaries are proved in one final model/context. -/
namespace Yulang.GeneralNominalTerminalForest191
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
open GeneralNominalOrdinaryEvidence191
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

inductive Schedule (registry : Registry) (root : Occurrence roles) :
    State roles → List (Occurrence roles) → List Payload → State roles → Prop
  | nil (state) : Schedule registry root state [] [] state
  | cons {before after : State roles} (plan : Plan roles) (support : List (Occurrence roles))
      (enabled : Installable registry before plan support)
      (terminal : plan.packet.children = [])
      (reached : GeneralNominalSaturationState.Generated before.core.erased.current root plan.packet.site.occurrence)
      (novel : ¬ GeneralNominalFeedbackSteps.Committed before.core.erased.current plan.packet)
      {demands : List (Occurrence roles)} {payloads : List Payload}
      (rest : Schedule registry root (install before plan support enabled) demands payloads after) :
      Schedule registry root before (plan.packet.site.occurrence :: demands)
        (.node plan.packet.declaration.id [] :: payloads) after

variable {before after : State roles} {demands : List (Occurrence roles)} {payloads : List Payload}

theorem path_trans {middle : State roles}
    (first : B4Target.Steps (OrdinaryStep registry root) before middle)
    (last : B4Target.Steps (OrdinaryStep registry root) middle after) :
    B4Target.Steps (OrdinaryStep registry root) before after := by
  induction last with
  | refl => exact first
  | tail _ step ih => exact .tail ih step

theorem ordinary_trace (schedule : Schedule registry root before demands payloads after) :
    B4Target.Steps (OrdinaryStep registry root) before after := by
  induction schedule with
  | nil => exact .refl
  | cons plan support enabled terminal reached novel rest ih =>
    exact path_trans (.tail .refl (install_step enabled reached novel)) ih

theorem execution (schedule : Schedule registry root before demands payloads after) :
    B4Target.Steps ((boundary roles).Step registry root) before after :=
  trace_steps (ordinary_trace schedule)

/-- Later sibling installations may constrain the assignment; every earlier
child is evaluated in this very final assignment, never its old witness. -/
theorem children_evidence (schedule : Schedule registry root before demands payloads after)
    (model : Assignment) (valid : Models after model) :
    All₂ ((boundary roles).Evidence registry after model) demands payloads := by
  induction schedule with
  | nil => exact .nil
  | cons plan support enabled terminal reached novel rest ih =>
    exact .cons (installed_trace_terminal enabled (ordinary_trace rest) terminal model valid) (ih valid)

theorem inhabited (schedule : Schedule registry root before demands payloads after)
    (initial : ∃ model, Models before model) : ∃ model, Models after model := by
  induction schedule with
  | nil => exact initial
  | cons plan support enabled terminal reached novel rest ih =>
    exact ih (installed_inhabited enabled)

/-- Arbitrary finite width, not merely an assumed list of child Evidence.
The required child installation schedule remains an explicit operational premise. -/
theorem parent_evidence {parent : Plan roles} {support : List (Occurrence roles)}
    (enabled : Installable registry before parent support)
    (schedule : Schedule registry root (install before parent support enabled)
      parent.packet.children payloads after)
    (model : Assignment) (valid : Models after model) :
    (boundary roles).Evidence registry after model parent.packet.site.occurrence
      (.node parent.packet.declaration.id payloads) :=
  installed_trace_evidence enabled (ordinary_trace schedule) model valid payloads
    (children_evidence schedule model valid)

theorem parent_inhabited {parent : Plan roles} {support : List (Occurrence roles)}
    (enabled : Installable registry before parent support)
    (schedule : Schedule registry root (install before parent support enabled)
      parent.packet.children payloads after) :
    (∃ model, Models after model) ∧ ∀ model, Models after model →
      (boundary roles).Evidence registry after model parent.packet.site.occurrence
        (.node parent.packet.declaration.id payloads) :=
  ⟨inhabited schedule (installed_inhabited enabled),parent_evidence enabled schedule⟩

end Yulang.GeneralNominalTerminalForest191
