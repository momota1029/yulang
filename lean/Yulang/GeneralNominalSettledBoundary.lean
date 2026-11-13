import Yulang.GeneralNominalSettledBudget
import Yulang.GeneralNominalValueBoundary

/-! Decision 7 at the initial-state B4 boundary. Lack of a settled explanation
is inspection pending. Ordinary constraints and K2 retain their full journal.
The progress theorem has the explicit source-budget hypothesis. -/
namespace Yulang.GeneralNominalSettledBoundary
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open CommonRoleOutermostResolver (Frontier)
open B4TargetV5

abbrev vocabulary := GeneralNominalValueBoundary.vocabulary

def fields (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Fields (vocabulary roles) :=
  { GeneralNominalValueBoundary.fields roles with
    InspectionPending := fun registry state root =>
      (GeneralNominalValueBoundary.fields roles).InspectionPending registry state root ∨
      GeneralNominalSettledSteps.SupportPending registry state root }

def remaining (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Remaining (vocabulary roles) :=
  { GeneralNominalValueBoundary.remaining roles with
    Step := GeneralNominalSettledSteps.Step
    Stable := GeneralNominalSettledSteps.Stable }

def boundary (roles : Roles.RoleDecls) : SourceBoundary (vocabulary roles) where
  toSourceBoundary := GeneralNominalLocalBoundary.complete (fields roles) (remaining roles)
  Initial := (GeneralNominalValueBoundary.boundary roles).Initial

abbrev Local (registry : Registry) (state : Tracked roles) :=
  GeneralNominalLocalBoundary.Local (fields roles) registry state

theorem local_correspondence (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (frontier : Frontier (Occurrence roles)) :
    B4TargetV3.Local (boundary roles).toSourceBoundary registry state root frontier ↔ Local registry state root frontier :=
  (GeneralNominalLocalBoundary.local_extension (remaining roles) frontier).symm

theorem support_pending (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (ready : ¬ GeneralNominalState.RootPending state.current.context.state root.demand)
    (blocked : GeneralNominalSettledSteps.SupportPending registry state root)
    (noRoot : ¬ GeneralNominalFeedbackK2.RootK2 state.current root)
    (noCandidate : ¬ GeneralNominalFeedbackK2.CandidateK2 registry state.current root) :
    Local registry state root .pending := .inspectionPending ready (Or.inr blocked) noRoot noCandidate

theorem rootK2_priority (cycle : GeneralNominalFeedbackK2.RootK2 state.current root) :
    Local registry state root .rejected :=
  .rejected ⟨GeneralNominalFeedbackK2.root_ready cycle,Or.inl cycle⟩

theorem candidateK2_priority (cycle : GeneralNominalFeedbackK2.CandidateK2 registry state.current root) :
    Local registry state root .rejected :=
  .rejected ⟨GeneralNominalFeedbackK2.candidate_ready cycle,Or.inr (Or.inl cycle)⟩

theorem reachable_formed (reachable : Reachable (boundary roles) registry root state) :
    GeneralNominalSettledSteps.SourceFormed registry root state := by
  obtain ⟨start,⟨context,source,rfl⟩,path⟩ := reachable
  induction path with
  | refl => exact .initial context source
  | tail _ update ih => exact .update ih update

theorem boundary_progress (budget : GeneralNominalSettledBudget.SourceBudget roles)
    (checked : (boundary roles).Checked registry)
    (reachable : Reachable (boundary roles) registry root state) :
    Acc (fun next current => (boundary roles).Step registry root current next) state := by
  obtain ⟨start,⟨context,source,rfl⟩,path⟩ := reachable
  have initial := GeneralNominalSettledBudget.checked_initial_accessible budget checked.2 source
  induction path with
  | refl => exact initial
  | tail _ step ih => exact ih.inv step

theorem closure (halted : ∀ after, ¬ (boundary roles).Step registry root state after) :
    (boundary roles).Stable registry state root ∧
      ∀ child, (boundary roles).Generated registry state root child → (boundary roles).Stable registry state child :=
  GeneralNominalSettledSteps.closure halted

theorem stepModels (step : (boundary roles).Step registry root before after) :
    ∀ model, (boundary roles).Models after model → (boundary roles).Models before model :=
  GeneralNominalSettledSteps.stepModels step

end Yulang.GeneralNominalSettledBoundary
