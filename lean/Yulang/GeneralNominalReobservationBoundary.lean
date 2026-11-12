import Yulang.GeneralNominalReobservationSteps
import Yulang.GeneralDictionaryReachableBoundary

/-! V5 boundary for the additive point-reobservation repair. This packages the
actual extended Step and Stable, retaining the source classifier and dictionary
judgments. It is not a completed maximal-observation consumer. -/
namespace Yulang.GeneralNominalReobservationBoundary

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open CommonRoleOutermostResolver (Frontier)
open B4TargetV5

abbrev vocabulary := GeneralNominalFeedbackBoundary.vocabulary

def remaining (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Remaining (vocabulary roles) where
  Step := GeneralNominalReobservationSteps.Step
  Stable := GeneralNominalReobservationSteps.Stable
  Generated := fun _ state => Generated state
  Evidence := GeneralDictionaryFeedbackEvidence.evidence roles

def sourceBoundary (roles : Roles.RoleDecls) : B4Target.SourceBoundary (vocabulary roles) :=
  GeneralNominalLocalBoundary.complete (GeneralNominalFeedbackK2.fields roles) (remaining roles)

def boundary (roles : Roles.RoleDecls) : SourceBoundary (vocabulary roles) where
  toSourceBoundary := sourceBoundary roles
  Initial := GeneralDictionaryInitialSource.Initial

theorem local_iff_old (roles : Roles.RoleDecls) (registry : Registry) (state : State roles)
    (root : Occurrence roles) (frontier : Frontier (Occurrence roles)) :
    B4TargetV3.Local (boundary roles).toSourceBoundary registry state root frontier ↔
      B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) registry state root frontier :=
  (GeneralNominalLocalBoundary.local_extension (remaining roles) frontier).symm.trans
    (GeneralNominalFeedbackBoundary.local_correspondence roles
      (GeneralDictionaryFeedbackEvidence.evidence roles) registry state root frontier).symm

noncomputable def frontiers (roles : Roles.RoleDecls) : B4SkeletonV3.Frontiers (vocabulary roles) :=
  fun registry state =>
    { frontier := (GeneralDictionaryReachableBoundary.frontiers roles registry state).frontier
      Local := B4TargetV3.Local (boundary roles).toSourceBoundary registry state }

variable {roles : Roles.RoleDecls}

theorem closure (registry : Registry) (_checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (_reachable : Reachable (boundary roles) registry root state)
    (halted : ∀ after, ¬ (boundary roles).Step registry root state after) :
    (boundary roles).Stable registry state root ∧
      ∀ child, (boundary roles).Generated registry state root child → (boundary roles).Stable registry state child :=
  GeneralNominalReobservationSteps.closure halted

theorem stepModels (registry : Registry) (_checked : (boundary roles).Checked registry)
    (root : Occurrence roles) (before after : State roles)
    (_reachable : Reachable (boundary roles) registry root before)
    (step : (boundary roles).Step registry root before after) :
    ∀ model, (boundary roles).Models after model → (boundary roles).Models before model :=
  GeneralNominalReobservationSteps.stepModels step

theorem frontierLocal (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (_reachable : Reachable (boundary roles) registry root state)
    (d : Occurrence roles) (f : Frontier (Occurrence roles)) :
    (frontiers roles registry state).frontier d = f ↔
      B4TargetV3.Local (boundary roles).toSourceBoundary registry state d f :=
  (GeneralNominalFeedbackBoundary.frontierLocal roles (GeneralDictionaryFeedbackEvidence.evidence roles)
    registry checked state d f).trans (local_iff_old roles registry state d f).symm

theorem localIdentity (registry : Registry) (state : State roles) (root : Occurrence roles)
    (_reachable : Reachable (boundary roles) registry root state) :
    (frontiers roles registry state).Local = B4TargetV3.Local (boundary roles).toSourceBoundary registry state := rfl

theorem dictionaryRefl (dictionary : CommonRoleOutermostResolver.Dictionary) :
    (boundary roles).DictionaryEquivalent dictionary dictionary :=
  GeneralDictionaryPayloadOrder.equivalent_refl dictionary

theorem initialReorders (registry other : Registry)
    (_checked : (boundary roles).Checked registry) (_checkedOther : (boundary roles).Checked other)
    (order : (boundary roles).Reorders registry other) (state : State roles) (root : Occurrence roles)
    (given : (boundary roles).Initial registry root state) : (boundary roles).Initial other root state :=
  GeneralDictionaryInitialSource.initial_reorders registry other order root state given

theorem old_reachable (registry : Registry) (state : State roles) (root : Occurrence roles)
    (reachable : Reachable (GeneralDictionaryReachableBoundary.boundary roles) registry root state) :
    Reachable (boundary roles) registry root state := by
  obtain ⟨initial,formed,path⟩ := reachable
  refine ⟨initial,formed,?_⟩
  induction path with
  | refl => exact .refl
  | tail _ update ih => exact .tail ih (GeneralNominalReobservationSteps.old_step update)

end Yulang.GeneralNominalReobservationBoundary
