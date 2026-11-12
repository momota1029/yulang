import Yulang.GeneralDictionaryInitialSource
import Yulang.B4TargetV5

/-! I-25 concrete V5 boundary. The full unchanged feedback relation is used;
Reachable is exactly SourceFormed, not an additional semantic invariant. -/
namespace Yulang.GeneralDictionaryReachableBoundary
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open B4TargetV5
variable {roles : Roles.RoleDecls}

def boundary (roles : Roles.RoleDecls) : SourceBoundary (GeneralNominalFeedbackBoundary.vocabulary roles) where
  toSourceBoundary := GeneralDictionaryFeedbackEvidence.boundary roles
  Initial := GeneralDictionaryInitialSource.Initial

theorem reachable_iff_sourceFormed (registry : Registry) (root : Occurrence roles) (state : State roles) :
    Reachable (boundary roles) registry root state ↔
      GeneralNominalFeedbackSteps.SourceFormed registry root state :=
  (GeneralDictionaryInitialSource.formed_iff_initial_trace registry root state).symm

theorem initialReorders (registry other : Registry)
    (_checked : (boundary roles).Checked registry) (_checkedOther : (boundary roles).Checked other)
    (order : (boundary roles).Reorders registry other) (state : State roles) (root : Occurrence roles)
    (given : (boundary roles).Initial registry root state) : (boundary roles).Initial other root state :=
  GeneralDictionaryInitialSource.initial_reorders registry other order root state given

noncomputable abbrev frontiers (roles : Roles.RoleDecls) :=
  GeneralNominalFeedbackBoundary.frontiers roles (GeneralDictionaryFeedbackEvidence.evidence roles)

theorem closure (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (_reachable : Reachable (boundary roles) registry root state)
    (halted : ∀ after, ¬ (boundary roles).Step registry root state after) :
    (boundary roles).Stable registry state root ∧
      ∀ child, (boundary roles).Generated registry state root child → (boundary roles).Stable registry state child :=
  GeneralNominalFeedbackBoundary.closure roles (GeneralDictionaryFeedbackEvidence.evidence roles)
    registry checked state root halted

theorem stepModels (registry : Registry) (checked : (boundary roles).Checked registry)
    (root : Occurrence roles) (before after : State roles)
    (_reachable : Reachable (boundary roles) registry root before)
    (step : (boundary roles).Step registry root before after) :
    ∀ model, (boundary roles).Models after model → (boundary roles).Models before model :=
  GeneralNominalFeedbackBoundary.stepModels roles (GeneralDictionaryFeedbackEvidence.evidence roles)
    registry checked root before after step

theorem frontierLocal (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (_reachable : Reachable (boundary roles) registry root state)
    (d : Occurrence roles) (f : CommonRoleOutermostResolver.Frontier (Occurrence roles)) :
    (frontiers roles registry state).frontier d = f ↔ B4TargetV3.Local (boundary roles).toSourceBoundary registry state d f :=
  GeneralNominalFeedbackBoundary.frontierLocal roles (GeneralDictionaryFeedbackEvidence.evidence roles)
    registry checked state d f

theorem localIdentity (registry : Registry) (state : State roles) (root : Occurrence roles)
    (_reachable : Reachable (boundary roles) registry root state) :
    (frontiers roles registry state).Local = B4TargetV3.Local (boundary roles).toSourceBoundary registry state := rfl

theorem dictionaryRefl (dictionary : CommonRoleOutermostResolver.Dictionary) :
    (boundary roles).DictionaryEquivalent dictionary dictionary :=
  GeneralDictionaryPayloadOrder.equivalent_refl dictionary
end Yulang.GeneralDictionaryReachableBoundary
