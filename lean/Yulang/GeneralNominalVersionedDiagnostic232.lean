import Yulang.GeneralNominalVersionedCycles232
import Yulang.GeneralNominalVersionedHeadSharing232
import Yulang.GeneralNominalVersionedMergedConflict232
import Yulang.B4TargetV8
set_option backward.isDefEq.respectTransparency false
/-! Version-coherent V8 diagnostic fields. This LOCAL boundary deliberately
has no initial states or operational steps; it is not the completed successor
boundary and no operational/termination/EvidenceNode theorem is claimed. -/
namespace Yulang.GeneralNominalVersionedDiagnostic232
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver

def AdministrativeReady (state : State roles) (root : Occurrence roles) : Prop :=
  (∃ site ∈ state.core.sites, site.occurrence = root) ∧
    ∀ first ∈ state.core.sites, first.occurrence = root → ∀ last ∈ state.core.sites,
      SameInputs (Models state) first last →
      GeneralNominalSaturationState.Alias state.core.erased.current first.occurrence.identity last.occurrence.identity

def vocabulary (roles : Roles.RoleDecls) : B4Target.Vocabulary where
  Registry := Registry
  State := State roles
  Demand := Occurrence roles
  Model := Assignment

def fields (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Fields (vocabulary roles) where
  Checked := fun registry => registry.roles = roles ∧ Checked registry
  Models := Models
  RootPending := fun _ state root => GeneralNominalState.RootPending state.core.erased.current.context.state
    (GeneralNominalVersionedCandidates231.inputs root).demand
  RootK2 := fun _ state root => GeneralNominalCycleK2.RootK2 state.core.erased.current.context.state
    (GeneralNominalVersionedCandidates231.inputs root).demand ∨ GeneralNominalVersionedCycles232.RootCycle state root
  CandidateK2 := fun registry state root =>
    GeneralNominalVersionedCycles232.RawCandidateK2 registry state.core.erased.current.context
      (GeneralNominalVersionedCandidates231.inputs root) ∨
    GeneralNominalVersionedCycles232.CandidateCycle registry state root
  InspectionPending := fun registry state root =>
    GeneralNominalVersionedCandidates231.InspectionPending registry state.core.erased.current.context root ∨
      ¬ AdministrativeReady state root
  Survivor := fun registry state root => GeneralNominalVersionedCandidates231.Survivor registry state.core.erased.current.context root
  Reorders := GeneralRegistryReordering.Reorders
  DictionaryEquivalent := Eq

def HeadEquations (plan : Plan roles) (model : Assignment) : Prop :=
  plan.input.Holds model ∧
    (∀ name ∈ plan.packet.declaration.inputNames,
      GeneralNominalCaptureMerges.Fits model ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name)
        (model (GeneralNominalVersionedFrame231.binder plan name)).1) ∧
    GeneralNominalVersionedPlans231.SchemaHolds plan plan.headSchema model

theorem head_equations (valid : GeneralNominalVersionedPlans231.Holds plan model) : HeadEquations plan model :=
  ⟨valid.2.1.2.2.1,fun name member => valid.2.1.2.2.2.1 name (Or.inl member),valid.2.1.2.2.2.2.1⟩

def ChosenHead (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat) (model : Assignment) : Prop :=
  (∃ children, GeneralNominalVersionedCandidates231.Unique registry state.core.erased.current.context root key children) ∧
    ∃ plan, GeneralNominalVersionedEvidence231.Frame registry state.core root key plan ∧
      GeneralNominalCenteredHeadMatEffects.Ready state.core root plan ∧ HeadEquations plan model

def ChosenEffects (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat) (model : Assignment) : Prop :=
  (∃ children, GeneralNominalVersionedCandidates231.Unique registry state.core.erased.current.context root key children) ∧
    ∃ plan, GeneralNominalVersionedEvidence231.Frame registry state.core root key plan ∧
      GeneralNominalCenteredHeadMatEffects.Ready state.core root plan ∧ HeadEquations plan model ∧
      GeneralNominalVersionedEffects231.ClassEffects state.core root plan model

def OutputConflict (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat) : Prop :=
  (∃ model, Models state model ∧ ChosenHead registry state root key model) ∧
    ¬ ∃ model, Models state model ∧ ChosenEffects registry state root key model

def v6 (roles : Roles.RoleDecls) : B4TargetV6.SourceBoundary (vocabulary roles) where
  toV5 := {
    toSourceBoundary := GeneralNominalLocalBoundary.complete (fields roles) {
      Step := fun _ _ _ _ => False
      Stable := fun _ _ _ => True
      Generated := fun _ state => GeneralNominalSaturationState.Generated state.core.erased.current
      Evidence := fun registry state => GeneralNominalVersionedEvidence231.Evidence registry state.core }
    Initial := fun _ _ _ => False }
  OutputConflict := OutputConflict

def v7 (roles : Roles.RoleDecls) : B4TargetV7.SourceBoundary (vocabulary roles) where
  toV6 := v6 roles
  MergedOutputConflict := fun _ => GeneralNominalVersionedMergedConflict232.MergedOutputConflict

def Feasible (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat) : Prop :=
  ∃ model, Models state model ∧ ∃ plan, GeneralNominalVersionedEvidence231.Frame registry state.core root key plan ∧
    GeneralDictionaryHeadSharing220.Holds plan model

def AtKey (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat) : Prop :=
  (∃ model, Models state model) ∧ (∃ plan, GeneralNominalVersionedEvidence231.Frame registry state.core root key plan) ∧
    ¬ Feasible registry state root key

def SharingConflict (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∃ key children, B4TargetV7.Unique (v7 roles) registry state root key children ∧
    B4TargetV7.SafeKnown (v7 roles) registry state root ∧ AtKey registry state root key

def boundary (roles : Roles.RoleDecls) : B4TargetV8.SourceBoundary (vocabulary roles) where
  toV7 := v7 roles
  SharingConflict := SharingConflict

abbrev Local (registry : Registry) (state : State roles) := B4TargetV8.Local (boundary roles) registry state

theorem local_total (checked : Checked registry) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, Local registry state root frontier :=
  B4TargetV8.local_total (fun _ _ _ one two =>
    GeneralNominalVersionedCandidates231.survivor_children_functional checked one two)

theorem local_functional (one : Local registry state root first) (two : Local registry state root last) : first = last :=
  B4TargetV8.local_functional one two

end Yulang.GeneralNominalVersionedDiagnostic232
