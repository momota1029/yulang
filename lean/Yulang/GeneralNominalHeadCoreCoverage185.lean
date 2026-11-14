import Yulang.GeneralNominalCompleteNames183
import Yulang.GeneralNominalQueryProvenance183
import Yulang.GeneralNominalHeadSiteOrigin185
import Yulang.GeneralNominalHeadPacketSupport185

/-! Finished registrations cover every declared input and every Needed binder.
One historical origin is selected before all centered assignments. Terminal
heads require no child or covered-head premise. Candidate origin agreement
and the unrestricted EvidenceNode are not supplied by these witnesses. -/
namespace Yulang.GeneralNominalHeadCoreCoverage185
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel GeneralNominalRecursiveInspection
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalSupportProvenance182 (ActualBinder actual_same)
open GeneralNominalCenteredHeadWFBoundary (boundary)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem registered_finished
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ plan ∈ state.core.plans, Finished (headInspection plan) := by
  induction path with
  | refl => intro plan member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,_,action⟩ := step
    cases action with
    | administrative | refresh | merge => exact ih
    | install plan support enabled novel =>
      intro previous member
      rcases List.mem_cons.mp member with rfl | old
      · have prepared := enabled.frame.prepared
        rw [← enabled.frame.context_eq] at prepared
        obtain ⟨_,_,_,bounds,found,finished,_⟩ := prepared
        have equal : bounds = previous.packet.bounds := Option.some.inj (found.symm.trans enabled.frame.located)
        subst bounds
        exact GeneralNominalInspectionAlignment.finished_origins previous.packet.context.state _ previous.packet.bounds _ _ 0 0 finished
      · exact ih previous old

theorem site_needed (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (site : Site roles) (member : site ∈ state.core.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh state.core.erased.current.context.state.seed invocation declaration 8 owner position) :
    ∃ plan ∈ state.core.plans, ∃ name, GeneralNominalSharedCaptures.Needed plan.packet name ∧ plan.binder name = site.center index := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  rw [(GeneralNominalCenteredHeadStepTrace.configuration_trace path).1] at center
  exact GeneralNominalHeadSiteOrigin185.purpose_eight_site_needed source path site member index center

theorem registered_input_actual
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) (name : Nat)
    (named : name ∈ plan.packet.declaration.inputNames) :
    ∃ origin, ActualBinder state.core (plan.binder name) origin := by
  obtain ⟨captured,present,equal⟩ := GeneralNominalCompleteNames183.declaration_input_capture
    plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration
    plan.packet.bounds _ 0 (registered_finished path plan registered) name named
  obtain ⟨origin,_,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 captured present
  exact ⟨origin,plan,registered,plan.headSchema,.head,
    ⟨captured.name,origin,.actual⟩,used,rfl,congrArg plan.binder equal,rfl⟩

theorem registered_capture_actual
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    ∃ origin, ActualBinder state.core (plan.binder name) origin := by
  apply registered_input_actual path plan registered name
  rcases needed with named | ⟨clause,member,used⟩
  · exact named
  · exact plan.packet.checked.scope.1 clause member name used

theorem wf_capture_actual
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    ∃ origin, ActualBinder state.core (plan.binder name) origin := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := GeneralNominalCenteredHeadWFBoundary.reachable_old reachable
  exact registered_capture_actual path plan registered name needed

theorem uniform_wf_capture_readback
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (plan : Plan roles) (registered : plan ∈ state.core.plans) (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    ∃ origin, ActualBinder state.core (plan.binder name) origin ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model origin (.source (plan.binder name)) := by
  obtain ⟨origin,witness⟩ := wf_capture_actual reachable plan registered name needed
  exact ⟨origin,witness,fun _ valid => actual_same valid.1 witness⟩

theorem uniform_wf_site_readback
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (site : Site roles) (member : site ∈ state.core.sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (center : site.center index = fresh state.core.erased.current.context.state.seed
      invocation declaration 8 owner position) :
    ∃ origin, ActualBinder state.core (site.center index) origin ∧
      ∀ model, Models state model → GeneralNominalOriginTerms.Same model origin (.source (site.center index)) := by
  obtain ⟨plan,registered,name,needed,equal⟩ :=
    site_needed reachable site member index center
  rw [← equal]
  exact uniform_wf_capture_readback reachable plan registered name (Or.inr needed)

end Yulang.GeneralNominalHeadCoreCoverage185
