import Yulang.B4TargetV6
import Yulang.GeneralNominalCenteredHeadOutputs

/-! Head-only local classification with class-wide post-choice output errors.
The transition, initial-state, model, and generation relations stay unchanged. -/
namespace Yulang.GeneralNominalCenteredHeadBoundary
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredHeadCandidates (inputs)
open GeneralNominalCenteredBoundary (vocabulary)
open CommonRoleOutermostResolver
variable {roles : Roles.RoleDecls}

def CandidateCycle (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∃ plan : Plan roles, plan.input ∈ state.sites ∧ plan.input.occurrence = root ∧
    plan.packet.registry = registry ∧ plan.packet.context = state.erased.current.context ∧
    plan.packet.declaration ∈ registry.declarations ∧ plan.packet.declaration.role = root.demand.role ∧
    GeneralNominalCenteredHeadCandidates.Prepared registry plan.packet.context root plan.packet.declaration ∧
    GeneralNominalRecursiveCandidates.arguments plan.packet.context (inputs root) = some plan.packet.bounds ∧
    ∃ entry ∈ (inspection plan).tests, Cyclic state entry.1

def InspectionPending (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  GeneralNominalCenteredHeadCandidates.InspectionPending registry state.erased.current.context root ∨
  (¬ GeneralNominalState.RootPending state.erased.current.context.state (inputs root).demand ∧
    ((GeneralNominalMixedRecurrence.RootK2 state.erased.current.context.state (inputs root).demand ∧
      ¬ GeneralNominalCycleK2.RootK2 state.erased.current.context.state (inputs root).demand) ∨
    (GeneralNominalRecursiveCandidates.CandidateK2 registry state.erased.current.context (inputs root) ∧
      ¬ GeneralNominalCycleK2.CandidateK2 registry state.erased.current.context (inputs root)))) ∨
  ¬ DecisionGuard registry state root ∨
  ¬ GeneralNominalCenteredAdministrativeLocal.AdministrativeReady state root

def fields (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Fields (vocabulary roles) :=
  { GeneralNominalCenteredAdministrativeLocal.fields roles with
    RootPending := fun _ state root => GeneralNominalState.RootPending state.erased.current.context.state (inputs root).demand
    RootK2 := fun _ state root => GeneralNominalFeedbackK2.RootK2 state.erased.current (inputs root) ∨ RootCycle state root
    CandidateK2 := fun registry state root =>
      GeneralNominalFeedbackK2.CandidateK2 registry state.erased.current (inputs root) ∨ CandidateCycle registry state root
    InspectionPending := InspectionPending
    Survivor := fun registry state => GeneralNominalCenteredHeadCandidates.Survivor registry state.erased.current.context }

def boundary (roles : Roles.RoleDecls) : B4TargetV6.SourceBoundary (vocabulary roles) where
  toV5 :=
    { toSourceBoundary := GeneralNominalLocalBoundary.complete (fields roles) (GeneralNominalCenteredBoundary.remaining roles)
      Initial := (GeneralNominalCenteredAdministrativeLocal.boundary roles).Initial }
  OutputConflict := GeneralNominalCenteredHeadOutputs.OutputConflict

abbrev Local (registry : Registry) (state : State roles) := B4TargetV6.Local (boundary roles) registry state

theorem reachable_iff : B4TargetV6.Reachable (boundary roles) registry root state ↔
    B4TargetV5.Reachable (GeneralNominalCenteredAdministrativeLocal.boundary roles) registry root state := Iff.rfl

theorem local_functional (one : Local registry state root first) (two : Local registry state root last) : first = last :=
  B4TargetV6.local_functional one two

theorem local_total (registry : Registry) (checked : Checked registry) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, Local registry state root frontier :=
  B4TargetV6.local_total (fun _ _ _ one two => GeneralNominalCenteredHeadCandidates.survivor_children_functional checked one two)

theorem selected_head (selected : Local registry state root (.selected key children)) :
    GeneralNominalCenteredHeadCandidates.Survivor registry state.erased.current.context root key children := by
  cases selected with | selected _ unique _ => exact unique.1

theorem selected_no_output_conflict (selected : Local registry state root (.selected key children)) :
    ¬ GeneralNominalCenteredHeadOutputs.OutputConflict registry state root key := B4TargetV6.selected_clear selected

theorem selected_has_effects (selected : Local registry state root (.selected key children))
    (baseline : ∃ model, Models state model ∧
      GeneralNominalCenteredHeadOutputs.ChosenHead registry state root key model) :
    ∃ model, Models state model ∧ GeneralNominalCenteredHeadOutputs.ChosenClassEffects registry state root key model :=
  (GeneralNominalCenteredHeadOutputs.no_conflict_iff_effects baseline).mp (selected_no_output_conflict selected)

theorem output_conflict_rejected
    (safe : B4TargetV6.SafeKnown (boundary roles) registry state root)
    (conflict : GeneralNominalCenteredHeadOutputs.OutputConflict registry state root key) : Local registry state root .rejected := by
  obtain ⟨children,unique⟩ := GeneralNominalCenteredHeadOutputs.conflict_unique conflict
  exact B4TargetV6.output_conflict_rejected safe unique conflict

theorem ambiguous_only (safe : B4TargetV6.SafeKnown (boundary roles) registry state root)
    (one : GeneralNominalCenteredHeadCandidates.Survivor registry state.erased.current.context root a xs)
    (two : GeneralNominalCenteredHeadCandidates.Survivor registry state.erased.current.context root b ys)
    (different : a ≠ b) (frontier) : Local registry state root frontier ↔ frontier = .ambiguous :=
  B4TargetV6.ambiguous_only safe one two different frontier

noncomputable def frontiers (roles : Roles.RoleDecls) : Registry → State roles → Protocol (Occurrence roles) := by
  classical
  exact fun registry state =>
    { frontier := fun root => if checked : Checked registry then Classical.choose (local_total registry checked state root) else .pending
      Local := Local registry state }

theorem frontierLocal (checked : (boundary roles).Checked registry) (state : State roles)
    (root : Occurrence roles) (frontier) :
    (frontiers roles registry state).frontier root = frontier ↔ Local registry state root frontier := by
  classical
  have valid := Classical.choose_spec (local_total registry checked.2 state root)
  change (if checked : Checked registry then Classical.choose (local_total registry checked state root) else .pending) = frontier ↔ _
  rw [dite_eq_left checked.2]
  exact ⟨fun same => same ▸ valid,fun chosen => local_functional valid chosen⟩

theorem localIdentity (registry : Registry) (state : State roles) :
    (frontiers roles registry state).Local = B4TargetV6.Local (boundary roles) registry state := rfl

end Yulang.GeneralNominalCenteredHeadBoundary
