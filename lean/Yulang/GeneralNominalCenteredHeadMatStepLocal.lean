import Yulang.GeneralNominalCenteredHeadMatStepCycles

namespace Yulang.GeneralNominalCenteredHeadMatStepLocal
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal (State Models)
variable {roles : Roles.RoleDecls}

def AdministrativeReady (state : State roles) (root : Occurrence roles) : Prop :=
  (∃ site ∈ state.core.sites, site.occurrence = root) ∧
    ∀ first ∈ state.core.sites, first.occurrence = root → ∀ last ∈ state.core.sites,
      SameInputs (Models state) first last →
      GeneralNominalSaturationState.Alias state.core.erased.current first.occurrence.identity last.occurrence.identity

def vocabulary (roles : Roles.RoleDecls) : B4Target.Vocabulary where
  Registry := Registry
  State := State roles
  Demand := Occurrence roles
  Model := GeneralNominalCommonBridge.Assignment

def fields (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Fields (vocabulary roles) where
  Checked := fun registry => registry.roles = roles ∧ Checked registry
  Models := Models
  RootPending := fun _ state root => GeneralNominalState.RootPending state.core.erased.current.context.state
    (GeneralNominalCenteredHeadCandidates.inputs root).demand
  RootK2 := fun _ state root => GeneralNominalCycleK2.RootK2 state.core.erased.current.context.state
    (GeneralNominalCenteredHeadCandidates.inputs root).demand ∨ GeneralNominalCenteredHeadMatStepCycles.RootCycle state root
  CandidateK2 := fun registry state root => GeneralNominalCycleK2.CandidateK2 registry state.core.erased.current.context
    (GeneralNominalCenteredHeadCandidates.inputs root) ∨ GeneralNominalCenteredHeadMatStepCycles.CandidateCycle registry state root
  InspectionPending := fun registry state root =>
    GeneralNominalCenteredHeadCandidates.InspectionPending registry state.core.erased.current.context root ∨
      ¬ AdministrativeReady state root
  Survivor := fun registry state root => GeneralNominalCenteredHeadCandidates.Survivor registry state.core.erased.current.context root
  Reorders := GeneralRegistryReordering.Reorders
  DictionaryEquivalent := Eq

def ChosenHead (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat)
    (model : GeneralNominalCommonBridge.Assignment) : Prop :=
  (∃ children, GeneralNominalCenteredHeadCandidates.Unique registry state.core.erased.current.context root key children) ∧
    ∃ plan, GeneralNominalCenteredHeadOutputs.Frame registry state.core root key plan ∧
      GeneralNominalCenteredHeadMatEffects.Ready state.core root plan ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations plan model

def ChosenEffects (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat)
    (model : GeneralNominalCommonBridge.Assignment) : Prop :=
  (∃ children, GeneralNominalCenteredHeadCandidates.Unique registry state.core.erased.current.context root key children) ∧
    ∃ plan, GeneralNominalCenteredHeadOutputs.Frame registry state.core root key plan ∧
      GeneralNominalCenteredHeadMatEffects.Ready state.core root plan ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations plan model ∧
      GeneralNominalCenteredHeadMatEffects.ClassEffects state.core root plan model

def OutputConflict (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat) : Prop :=
  (∃ model, Models state model ∧ ChosenHead registry state root key model) ∧
    ¬ ∃ model, Models state model ∧ ChosenEffects registry state root key model

def diagnosticBoundary (roles : Roles.RoleDecls) : B4TargetV6.SourceBoundary (vocabulary roles) where
  toV5 := {
    toSourceBoundary := GeneralNominalLocalBoundary.complete (fields roles) {
      Step := fun _ _ _ _ => False
      Stable := fun _ _ _ => True
      Generated := fun _ state => GeneralNominalSaturationState.Generated state.core.erased.current
      Evidence := fun registry state => GeneralDictionaryFeedbackEvidence.evidence roles registry state.core.erased.current }
    Initial := fun _ _ _ => False }
  OutputConflict := OutputConflict

abbrev Local (registry : Registry) (state : State roles) := B4TargetV6.Local (diagnosticBoundary roles) registry state

theorem local_total (checked : Checked registry) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, Local registry state root frontier :=
  B4TargetV6.local_total (fun _ _ _ one two => GeneralNominalCenteredHeadCandidates.survivor_children_functional checked one two)

theorem local_functional (one : Local registry state root first) (two : Local registry state root last) : first = last :=
  B4TargetV6.local_functional one two

theorem selected_ready (selected : Local registry state root (.selected key children)) : AdministrativeReady state root := by
  classical
  cases selected with
  | selected safe _ _ => exact Classical.byContradiction (fun missing => safe.2.2.2 (Or.inr missing))

end Yulang.GeneralNominalCenteredHeadMatStepLocal
