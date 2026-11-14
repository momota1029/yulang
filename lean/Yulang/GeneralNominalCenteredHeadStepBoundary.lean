import Yulang.GeneralNominalCenteredHeadStepKernel

/-! The V6 boundary for the successor relation. Conflict uses the extended
model journal; head, pending and K2 observations keep their existing inputs. -/
namespace Yulang.GeneralNominalCenteredHeadStepBoundary
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open CommonRoleOutermostResolver
variable {roles : Roles.RoleDecls}

def vocabulary (roles : Roles.RoleDecls) : B4Target.Vocabulary where
  Registry := Registry
  State := State roles
  Demand := Occurrence roles
  Model := GeneralNominalCommonBridge.Assignment

def fields (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Fields (vocabulary roles) where
  Checked := (GeneralNominalCenteredHeadBoundary.fields roles).Checked
  Models := Models
  RootPending := fun registry state => (GeneralNominalCenteredHeadBoundary.fields roles).RootPending registry state.core
  RootK2 := fun registry state => (GeneralNominalCenteredHeadBoundary.fields roles).RootK2 registry state.core
  CandidateK2 := fun registry state => (GeneralNominalCenteredHeadBoundary.fields roles).CandidateK2 registry state.core
  InspectionPending := fun registry state => (GeneralNominalCenteredHeadBoundary.fields roles).InspectionPending registry state.core
  Survivor := fun registry state => (GeneralNominalCenteredHeadBoundary.fields roles).Survivor registry state.core
  Reorders := (GeneralNominalCenteredHeadBoundary.fields roles).Reorders
  DictionaryEquivalent := (GeneralNominalCenteredHeadBoundary.fields roles).DictionaryEquivalent

def remaining (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Remaining (vocabulary roles) where
  Step := Step
  Stable := Stable
  Generated := fun _ state => GeneralNominalSaturationState.Generated state.core.erased.current
  Evidence := fun registry state => GeneralDictionaryFeedbackEvidence.evidence roles registry state.core.erased.current

def Initial (registry : Registry) (root : Occurrence roles) (state : State roles) : Prop :=
  ∃ context labels, GeneralNominalSourceFormation.InitialSource registry context root ∧
    (∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) ∧
    GeneralNominalGroundAccessibility.GroundRoots context root labels ∧ state = initial context root

def OutputConflict (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat) : Prop :=
  (∃ model, Models state model ∧ GeneralNominalCenteredHeadOutputs.ChosenHead registry state.core root key model) ∧
    ¬ ∃ model, Models state model ∧ GeneralNominalCenteredHeadOutputs.ChosenClassEffects registry state.core root key model

def boundary (roles : Roles.RoleDecls) : B4TargetV6.SourceBoundary (vocabulary roles) where
  toV5 := { toSourceBoundary := GeneralNominalLocalBoundary.complete (fields roles) (remaining roles)
            Initial := Initial }
  OutputConflict := OutputConflict

abbrev Local (registry : Registry) (state : State roles) := B4TargetV6.Local (boundary roles) registry state

theorem local_total (registry : Registry) (checked : Checked registry) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, Local registry state root frontier :=
  B4TargetV6.local_total (fun _ _ _ one two => GeneralNominalCenteredHeadCandidates.survivor_children_functional checked one two)

theorem local_functional (one : Local registry state root first) (two : Local registry state root last) : first = last :=
  B4TargetV6.local_functional one two

theorem installable_effects (enabled : Installable registry state plan support) :
    ∃ model, Models state model ∧ GeneralNominalCenteredHeadOutputs.ChosenClassEffects registry state.core
      plan.packet.site.occurrence plan.packet.declaration.id model := by
  obtain ⟨model,valid,branch,outputs,_⟩ := enabled.common
  exact ⟨model,valid,⟨_,enabled.unique⟩,plan,enabled.frame,enabled.ready,head_of_plan branch,outputs⟩

theorem installable_selected (enabled : Installable registry state plan support) :
    Local registry state plan.packet.site.occurrence (.selected plan.packet.declaration.id plan.packet.children) :=
  .selected enabled.safe enabled.unique (fun conflict => conflict.2 (installable_effects enabled))

theorem conflict_no_install
    (conflict : OutputConflict registry state plan.packet.site.occurrence plan.packet.declaration.id) :
    ¬ Installable registry state plan support := fun enabled => conflict.2 (installable_effects enabled)

theorem ambiguous_no_install
    (one : GeneralNominalCenteredHeadCandidates.Survivor registry state.core.erased.current.context plan.packet.site.occurrence a xs)
    (two : GeneralNominalCenteredHeadCandidates.Survivor registry state.core.erased.current.context plan.packet.site.occurrence b ys)
    (different : a ≠ b) : ¬ Installable registry state plan support :=
  fun enabled => GeneralNominalCenteredHeadCandidates.unique_excludes_two enabled.unique one two different

theorem output_conflict_rejected (safe : B4TargetV6.SafeKnown (boundary roles) registry state root)
    (conflict : OutputConflict registry state root key) : Local registry state root .rejected := by
  obtain ⟨_,_,⟨children,unique⟩,_⟩ := conflict.1
  exact B4TargetV6.output_conflict_rejected safe unique conflict

theorem conflict_inhabited (conflict : OutputConflict registry state root key) : ∃ model, Models state model := by
  obtain ⟨model,valid,_⟩ := conflict.1
  exact ⟨model,valid⟩

theorem selected_ready (selected : Local registry state root (.selected key children)) :
    GeneralNominalCenteredAdministrativeLocal.AdministrativeReady state.core root := by
  apply Classical.byContradiction
  intro missing
  cases selected with
  | selected safe _ _ => exact safe.2.2.2 (Or.inr (Or.inr (Or.inr missing)))

theorem boundary_stepModels (registry : Registry) (_checked : (boundary roles).Checked registry)
    (root : Occurrence roles) (before after : State roles)
    (_reachable : B4TargetV6.Reachable (boundary roles) registry root before)
    (step : (boundary roles).Step registry root before after) :
    ∀ model, (boundary roles).Models after model → (boundary roles).Models before model := stepModels step

theorem boundary_closure (registry : Registry) (_checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (_reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (halted : ∀ after, ¬ (boundary roles).Step registry root state after) :
    (boundary roles).Stable registry state root ∧
      ∀ child, (boundary roles).Generated registry state root child → (boundary roles).Stable registry state child := closure halted

end Yulang.GeneralNominalCenteredHeadStepBoundary
