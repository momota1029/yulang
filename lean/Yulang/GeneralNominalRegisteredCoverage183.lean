import Yulang.GeneralNominalCompleteNames183
import Yulang.GeneralNominalQueryProvenance183
import Yulang.GeneralNominalGroundProvenance182

/-! Finished registrations cover every declared input and every Needed binder.
One historical origin is selected before all centered assignments. Terminal
heads require no child or covered-head premise. Candidate origin agreement
and the unrestricted EvidenceNode are not supplied by these witnesses. -/
namespace Yulang.GeneralNominalRegisteredCoverage183
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredSteps GeneralNominalRecursiveInspection
open GeneralNominalQueryProvenance183 (headInspection registered_finished)
open GeneralNominalSupportProvenance182 (ActualBinder actual_same)
open GeneralNominalCenteredGroundBoundary (groundBoundary)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem registered_input_actual
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (named : name ∈ plan.packet.declaration.inputNames) :
    ∃ origin, ActualBinder state (plan.binder name) origin := by
  obtain ⟨captured,present,equal⟩ := GeneralNominalCompleteNames183.declaration_input_capture
    plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration
    plan.packet.bounds _ 0 (registered_finished path plan registered) name named
  obtain ⟨origin,_,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 captured present
  exact ⟨origin,plan,registered,plan.headSchema,.head,
    ⟨captured.name,origin,.actual⟩,used,rfl,congrArg plan.binder equal,rfl⟩

theorem registered_capture_actual
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    ∃ origin, ActualBinder state (plan.binder name) origin := by
  apply registered_input_actual path plan registered name
  rcases needed with named | ⟨clause,member,used⟩
  · exact named
  · exact plan.packet.checked.scope.1 clause member name used

theorem ground_capture_actual
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    ∃ origin, ActualBinder state (plan.binder name) origin := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact registered_capture_actual path plan registered name needed

theorem uniform_ground_capture_readback
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    ∃ origin, ActualBinder state (plan.binder name) origin ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model origin (.source (plan.binder name)) := by
  obtain ⟨origin,witness⟩ := ground_capture_actual reachable plan registered name needed
  exact ⟨origin,witness,fun _ valid => actual_same valid witness⟩

theorem uniform_ground_site_readback
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (site : Site roles) (member : site ∈ state.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh state.erased.current.context.state.seed
      invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state (site.center index) origin ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model origin (.source (site.center index)) := by
  obtain ⟨plan,registered,name,needed,equal⟩ :=
    GeneralNominalGroundProvenance182.site_needed reachable site member index center
  rw [← equal]
  exact uniform_ground_capture_readback reachable plan registered name (Or.inr needed)

end Yulang.GeneralNominalRegisteredCoverage183
