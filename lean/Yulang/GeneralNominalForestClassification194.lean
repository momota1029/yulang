import Yulang.GeneralNominalReusableForest192

/-! A precise conditional classification bridge. Finite executable evidence
forests do not alone establish final classification: local selections must survive
all later ordinary transitions. The transport property below is an explicit,
unproved premise, not a claimed property of the full WF boundary. -/
namespace Yulang.GeneralNominalForestClassification194
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
open GeneralNominalOrdinaryEvidence191 GeneralNominalReusableForest192
open GeneralNominalTerminalForest191 (path_trans)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

/-- Contract required in addition to a finite installation/reuse certificate.
It quantifies actual enabled nodes and ordinary traces, not recursive Evidence or
Classify conclusions. No theorem in this module asserts this contract globally. -/
def SelectionsPersist (registry : Registry) (root : Occurrence roles) : Prop :=
  ∀ (before final : State roles) (plan : Plan roles) (support : List (Occurrence roles)),
    Installable registry before plan support →
    GeneralNominalSaturationState.Generated before.core.erased.current root plan.packet.site.occurrence →
    B4Target.Steps (OrdinaryStep registry root) before final →
    GeneralNominalCenteredHeadWFBoundary.Local registry final plan.packet.site.occurrence
      (.selected plan.packet.declaration.id plan.packet.children)

/-- Recursive classifications are assembled at one common final state, including
all effects of later siblings. This theorem assumes the named local-selection
transport contract; it does not prove that contract or the general EvidenceNode. -/
theorem classify_after (preserve : SelectionsPersist registry root)
    {before after final : State roles} {demands : List (Occurrence roles)} {payloads : List Payload}
    (build : Build registry root before demands payloads after)
    (suffix : B4Target.Steps (OrdinaryStep registry root) after final) :
    All₂ (fun demand payload => B4TargetV6.Classify (boundary roles) registry final demand (.selected payload)) demands payloads := by
  induction build with
  | nil => exact .nil
  | cons plan support enabled reached novel children siblings childIH siblingIH =>
    have parentPath := path_trans (path_trans
      (path_trans (.tail .refl (install_step enabled reached novel)) (ordinary_trace children))
      (ordinary_trace siblings)) suffix
    have localRule := preserve _ _ plan support enabled reached parentPath
    cases localRule with
    | selected safe unique clear =>
      exact .cons (.selected safe unique clear
        (childIH (path_trans (ordinary_trace siblings) suffix))) (siblingIH suffix)
  | reuse plan support enabled reached committed children siblings childIH siblingIH =>
    have parentPath := path_trans (path_trans (ordinary_trace children) (ordinary_trace siblings)) suffix
    have localRule := preserve _ _ plan support enabled reached parentPath
    cases localRule with
    | selected safe unique clear =>
      exact .cons (.selected safe unique clear
        (childIH (path_trans (ordinary_trace siblings) suffix))) (siblingIH suffix)

theorem classify (preserve : SelectionsPersist registry root)
    {before after : State roles} {demands : List (Occurrence roles)} {payloads : List Payload}
    (build : Build registry root before demands payloads after) :
    All₂ (fun demand payload => B4TargetV6.Classify (boundary roles) registry after demand (.selected payload)) demands payloads :=
  classify_after preserve build .refl

/-- A certified single source tree has classification and universal same-final-
model evidence, conditional on the exact transport contract above. Stability is
not included: this statement does not rule out further enabled transitions. -/
theorem source_classification_sound (preserve : SelectionsPersist registry root)
    {before after : State roles} (payload : Payload)
    (initial : (boundary roles).Initial registry root before)
    (build : Build registry root before [root] [payload] after) :
    B4TargetV6.Reachable (boundary roles) registry root after ∧
    B4TargetV6.Classify (boundary roles) registry after root (.selected payload) ∧
    (∃ model, Models after model) ∧
    ∀ model, Models after model → Models before model ∧
      (boundary roles).Evidence registry after model root payload := by
  have semantic := source_tree_sound payload initial build
  have classifications := classify preserve build
  cases classifications with
  | cons first rest => exact ⟨semantic.1,first,semantic.2⟩
end Yulang.GeneralNominalForestClassification194
