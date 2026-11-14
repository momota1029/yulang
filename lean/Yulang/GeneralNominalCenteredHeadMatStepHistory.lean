import Yulang.GeneralNominalCenteredHeadMatStepPreservation

set_option backward.isDefEq.respectTransparency false

/-! An overapproximation of journal construction, used only for metadata
invariants. Installation has its head frame but no operational support or K2
guard here. This relation is not the successor boundary's Step. -/
namespace Yulang.GeneralNominalCenteredHeadMatStepHistory
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
variable {roles : Roles.RoleDecls}

inductive Built (registry : Registry) (context : GeneralNominalCandidates.Context) (root : Occurrence roles) : State roles → Prop
  | initial : Built registry context root (initial context root)
  | install {state : State roles} : Built registry context root state → (effect : Effect roles) →
      effect.snapshot = state.core → effect.registry = registry → Built registry context root (install state effect)
  | merge {state : State roles} : Built registry context root state → first ∈ state.core.sites → last ∈ state.core.sites →
      first.occurrence.demand.role = last.occurrence.demand.role → Built registry context root (merge state first last)
  | context {state : State roles} : Built registry context root state → (after : GeneralNominalCandidates.Context) →
      after.state.seed = state.core.erased.current.context.state.seed →
      after.interpretation = state.core.erased.current.context.interpretation →
      Built registry context root (refresh state after)

variable {state : State roles}

theorem recorded (built : Built registry context root state) :
    GeneralNominalCenteredHeadMatStepCoverage.Recorded state := by
  induction built with
  | initial => exact GeneralNominalCenteredHeadMatStepCoverage.initial_recorded _ _
  | install _ _ _ _ ih => exact GeneralNominalCenteredHeadMatStepCoverage.install_recorded ih
  | merge _ _ _ _ ih => exact GeneralNominalCenteredHeadMatStepCoverage.merge_recorded ih
  | context _ _ _ _ ih => exact GeneralNominalCenteredHeadMatStepCoverage.refresh_recorded ih

theorem snapshots_recorded (built : Built registry context root state) (member : effect ∈ state.effects) :
    GeneralNominalCenteredHeadMatStepCoverage.Recorded (⟨effect.snapshot,[]⟩ : State roles) := by
  induction built with
  | initial => cases member
  | install prior installed snapshot _ ih =>
      rcases List.mem_cons.mp member with rfl | member
      · have priorRecorded := recorded prior
        rw [snapshot]
        exact ⟨priorRecorded.rawCenter,priorRecorded.packetPlan,by intro effect member; cases member⟩
      · exact ih member
  | merge _ _ _ _ ih => exact ih member
  | context _ _ _ _ ih => exact ih member

theorem class_readback_covers_requests (built : Built registry context root state)
    (member : effect ∈ state.effects)
    (readback : GeneralNominalCenteredHeadMatStepSupport.ClassReadback state facts effect)
    (request : output ∈ GeneralNominalCenteredHeadOutputs.requests effect.snapshot effect.plan.input.occurrence) :
    ∃ center ∈ effect.snapshot.sites, output ∈ center.occurrence.demand.outputs ∧
      SameInputs (GeneralNominalCenteredHeadMatStepSupport.Models state facts) effect.plan.input center :=
  GeneralNominalCenteredHeadMatStepCoverage.class_readback_covers_requests
    (snapshots_recorded built member) readback request

theorem roles_invariant (checked : Checked registry) (built : Built registry context root state) :
    GeneralNominalCenteredHeadMatStepRoles.Invariant registry context.state.seed root state.core := by
  induction built with
  | initial => exact GeneralNominalCenteredHeadMatStepRoles.initial _ _
  | install _ effect snapshot registryEq ih =>
      apply GeneralNominalCenteredHeadMatStepRoles.install ih
      exact snapshot ▸ registryEq ▸ effect.frame
  | merge _ first last same ih => exact GeneralNominalCenteredHeadMatStepRoles.merge checked ih first last same
  | context _ after seed _ ih => exact ⟨ih.raw,ih.centers,ih.aliases,seed.trans ih.seed_eq⟩

theorem interpretation (built : Built registry context root state) :
    state.core.erased.current.context.interpretation = context.interpretation := by
  induction built with
  | initial => rfl
  | install _ effect snapshot _ ih =>
      have same := effect.frame.context_eq.trans (congrArg (fun state => state.erased.current.context) snapshot)
      exact (congrArg GeneralNominalCandidates.Context.interpretation same).trans ih
  | merge _ _ _ _ ih => exact ih
  | context _ _ _ same ih => exact same.trans ih

theorem frozen_refresh (built : Built registry context root state)
    (certificate : GeneralNominalCenteredSteps.Refresh state.core after) :
    Built registry context root (refresh state after) :=
  .context built after certificate.refines.seed certificate.interpretation

theorem requests_declared (checked : Checked registry) (built : Built registry context root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan) :
    GeneralNominalCenteredHeadDefaultSchemas.RequestsDeclared state.core focus plan :=
  GeneralNominalCenteredHeadMatStepRoles.requests_declared checked (roles_invariant checked built) frame

theorem ready (checked : Checked registry) (agree : registry.roles = roles)
    (covered : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (built : Built registry context root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan) :
    GeneralNominalCenteredHeadMatEffects.Ready state.core focus plan := by
  apply GeneralNominalCenteredHeadMatStepCoverage.ready checked agree (roles_invariant checked built) _ frame
  rw [interpretation built]
  exact covered

theorem emitted_complete
    (covered : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (built : Built registry context root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan) :
    (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).unknown = false := by
  apply GeneralNominalCenteredHeadMatStepCoverage.emitted_complete _ frame
  rw [interpretation built]
  exact covered

end Yulang.GeneralNominalCenteredHeadMatStepHistory
