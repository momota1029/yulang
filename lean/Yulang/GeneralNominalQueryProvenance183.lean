import Yulang.GeneralNominalCaptureCoverage183
import Yulang.GeneralNominalSupportProvenance182
import Yulang.GeneralNominalCenteredCaptureSchema
import Yulang.GeneralNominalGroundHeadMatching
import Yulang.GeneralNominalCenteredGroundBoundary

/-! Actual installation produces readback witnesses for translated-query names.
The declaration inputNames-to-query-name bridge is not assumed or established
here. No unrestricted EvidenceNode is claimed. -/
namespace Yulang.GeneralNominalQueryProvenance183
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredSteps GeneralNominalRecursiveInspection
open GeneralNominalInspectionAlignment
open GeneralNominalSupportProvenance182 (ActualBinder actual_same)
open GeneralNominalCenteredGroundBoundary (groundBoundary)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

def headInspection (plan : Plan roles) : Report plan.packet.context.state :=
  inspectMany plan.packet.context.state
    (GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration)
    plan.packet.bounds
    (fun index => some (.source ((List.ofFn plan.input.center)[index]?.getD 0))) 0

def queryNames (plan : Plan roles) : List Nat :=
  GeneralNominalCaptureNames.manyNames
    (GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration)

theorem installable_finished (plan : Plan roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet) :
    Finished (headInspection plan) := by
  obtain ⟨_,_,_,_,_,located,prepared,_,_,_,_,_⟩ := enabled.1
  exact finished_origins plan.packet.context.state _ plan.packet.bounds _ _ 0 0
    (GeneralNominalGroundHeadMatching.prepared_finished plan.packet prepared located)

theorem registered_finished
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.plans, Finished (headInspection plan) := by
  induction path with
  | refl => intro plan member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative focus next action => exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel guard =>
      intro old member
      rcases List.mem_cons.mp member with rfl | retained
      · exact installable_finished old enabled
      · exact ih old retained

theorem registered_query_actual
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (named : name ∈ queryNames plan) :
    ∃ origin, ActualBinder state (plan.binder name) origin := by
  obtain ⟨captured,present,equal⟩ := GeneralNominalCaptureCoverage183.many_covers
    plan.packet.context.state _ plan.packet.bounds _ 0 (registered_finished path plan registered) name named
  obtain ⟨origin,_,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 captured present
  refine ⟨origin,plan,registered,plan.headSchema,.head,
    ⟨captured.name,origin,.actual⟩,used,rfl,?_,rfl⟩
  exact congrArg plan.binder equal

theorem ground_query_actual
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (named : name ∈ queryNames plan) :
    ∃ origin, ActualBinder state (plan.binder name) origin := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact registered_query_actual path plan registered name named

theorem uniform_ground_query_readback
    (reachable : B4TargetV5.Reachable (groundBoundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.plans) (name : Nat)
    (named : name ∈ queryNames plan) :
    ∃ origin, ActualBinder state (plan.binder name) origin ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model origin (.source (plan.binder name)) := by
  obtain ⟨origin,witness⟩ := ground_query_actual reachable plan registered name named
  exact ⟨origin,witness,fun _ valid => actual_same valid witness⟩

end Yulang.GeneralNominalQueryProvenance183
