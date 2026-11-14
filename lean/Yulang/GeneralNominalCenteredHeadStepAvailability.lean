import Yulang.GeneralNominalCenteredHeadStepBoundary
import Yulang.GeneralNominalCenteredInspection
import Yulang.GeneralNominalCenteredCompletionParts

set_option backward.isDefEq.respectTransparency false

/-! Selection supplies the inspection guards. A positive chosen-head baseline
supplies a common assignment for the current class effects. Extending that
assignment to the emitted packet and the live ledger remains explicit. -/
namespace Yulang.GeneralNominalCenteredHeadStepAvailability
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadStepBoundary
open GeneralNominalCenteredHeadOutputs (Frame EffectsReady HeadEquations OutputEquations)
variable {roles : Roles.RoleDecls}
variable {registry : Registry} {state : State roles} {root : Occurrence roles}

theorem selected_guards (selected : Local registry state root (.selected key children)) :
    GeneralNominalCenteredSteps.DecisionGuard registry state.core root ∧
      ¬ GeneralNominalCenteredSteps.RootCycle state.core root ∧
      ¬ GeneralNominalCenteredHeadBoundary.CandidateCycle registry state.core root := by
  cases selected with
  | selected safe _ _ =>
      exact ⟨Classical.byContradiction (fun missing => safe.2.2.2 (Or.inr (Or.inr (Or.inl missing)))),
        fun cycle => safe.2.1 (Or.inr cycle),fun cycle => safe.2.2.1 (Or.inr cycle)⟩

theorem selected_safe (selected : Local registry state root (.selected key children))
    (plan : Plan roles) (recorded : plan.input ∈ state.core.sites) (input : plan.input.occurrence = root)
    (registryEq : plan.packet.registry = registry) (contextEq : plan.packet.context = state.core.erased.current.context)
    (visible : plan.packet.declaration ∈ registry.declarations)
    (role : plan.packet.declaration.role = root.demand.role)
    (prepared : GeneralNominalCenteredHeadCandidates.Prepared registry plan.packet.context root plan.packet.declaration)
    (located : GeneralNominalRecursiveCandidates.arguments plan.packet.context root = some plan.packet.bounds) :
    GeneralNominalCenteredSteps.Safe state.core plan := by
  refine ⟨GeneralNominalCenteredInspection.plan_complete plan (input ▸ located),?_⟩
  intro entry member cycle
  exact (selected_guards selected).2.2
    ⟨plan,recorded,input,registryEq,contextEq,visible,role,prepared,located,entry,member,cycle⟩

theorem selected_alternatives (selected : Local registry state root (.selected key children))
    (input : Site roles) (recorded : input ∈ state.core.sites) (same : input.occurrence = root) :
    AlternativesSafe registry state input := by
  intro plan inputEq registryEq contextEq visible role prepared located
  apply selected_safe selected plan (inputEq ▸ recorded) (inputEq ▸ same) registryEq contextEq visible
  · simpa only [same] using role
  · simpa only [same,contextEq] using prepared
  · simpa only [same] using located

theorem frame_value_iff (frame : Frame registry state.core root key plan) (support) :
    GeneralNominalValueSupport.PacketGuard state.core.erased plan.packet support ↔
      GeneralNominalValueSupport.DecisionGuard registry state.core.erased root support := by
  rcases plan with ⟨⟨preg,pctx,site,declaration,checked,bounds⟩,input,inputEq⟩
  have reg : preg = registry := frame.registry_eq
  have ctx : pctx = state.core.erased.current.context := frame.context_eq
  have occurrence : site.occurrence = root := frame.occurrence_eq
  subst preg; subst pctx
  constructor
  · rintro ⟨guard,grounded⟩
    exact ⟨occurrence ▸ guard.2,grounded⟩
  · rintro ⟨decision,grounded⟩
    refine ⟨⟨⟨?_,?_,?_⟩,?_⟩,grounded⟩
    · exact occurrence.symm ▸ decision.1
    · exact occurrence.symm ▸ decision.2.1
    · exact decision.2.2 declaration frame.visible frame.role_eq bounds frame.located
    · exact occurrence.symm ▸ decision

theorem selected_initial_value
    (selected : Local registry (initial context root) root (.selected key children))
    (frame : Frame registry (initial context root).core root key plan) :
    GeneralNominalValueSupport.PacketGuard (initial context root).core.erased plan.packet [] :=
  (frame_value_iff frame []).mpr
    (GeneralNominalCenteredCompletionParts.initial_decision (selected_guards selected).1)

theorem selected_has_effects (selected : Local registry state root (.selected key children))
    (baseline : ∃ model, Models state model ∧
      GeneralNominalCenteredHeadOutputs.ChosenHead registry state.core root key model) :
    ∃ model, Models state model ∧
      GeneralNominalCenteredHeadOutputs.ChosenClassEffects registry state.core root key model := by
  classical
  apply Classical.byContradiction
  exact fun absent => B4TargetV6.selected_clear selected ⟨baseline,absent⟩

theorem selected_frame (selected : Local registry state root (.selected key children))
    (baseline : ∃ model, Models state model ∧
      GeneralNominalCenteredHeadOutputs.ChosenHead registry state.core root key model) :
    ∃ plan model, Frame registry state.core root key plan ∧ EffectsReady state.core root plan ∧
      Models state model ∧ HeadEquations plan model ∧ OutputEquations state.core root plan model := by
  obtain ⟨model,valid,_,plan,frame,ready,head,outputs⟩ := selected_has_effects selected baseline
  exact ⟨plan,model,frame,ready,valid,head,outputs⟩

theorem frame_survivor (frame : Frame registry state.core root key plan)
    (known : ¬ GeneralNominalState.RootPending state.core.erased.current.context.state
      (GeneralNominalCenteredHeadCandidates.inputs root).demand) :
    GeneralNominalCenteredHeadCandidates.Survivor registry state.core.erased.current.context root key plan.packet.children := by
  rcases plan with ⟨⟨preg,pctx,site,declaration,checked,bounds⟩,input,inputEq⟩
  have reg : preg = registry := frame.registry_eq
  have ctx : pctx = state.core.erased.current.context := frame.context_eq
  have occurrence : site.occurrence = root := frame.occurrence_eq
  subst preg; subst pctx
  refine ⟨known,declaration,frame.visible,checked,frame.key_eq,frame.role_eq,
    bounds,frame.located,frame.prepared,?_⟩
  change GeneralNominalAllocation.children _ registry site.occurrence declaration checked _ = _
  rw [occurrence]
  rfl

/-- Selection discharges uniqueness, inspection safety and administrative
closure. Materialization, choice compatibility, value support and a common
extension model remain explicit. -/
def Extension (registry : Registry) (state : State roles) (plan : Plan roles) : Prop :=
  (GeneralNominalRecursiveCandidates.generated plan.packet.registry plan.packet.context
    plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bounds).unknown = false ∧
  GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current plan.packet ∧
  ∃ support, GeneralNominalValueSupport.DecisionGuard registry state.core.erased plan.packet.site.occurrence support ∧
    ∃ model, InstallationModels state plan support model

theorem selected_installable_iff
    (selected : Local registry state plan.packet.site.occurrence (.selected plan.packet.declaration.id children))
    (frame : Frame registry state.core plan.packet.site.occurrence plan.packet.declaration.id plan)
    (ready : EffectsReady state.core plan.packet.site.occurrence plan) :
    (∃ support, Installable registry state plan support) ↔ Extension registry state plan := by
  constructor
  · rintro ⟨support,enabled⟩
    exact ⟨enabled.materialized,enabled.choice,support,(frame_value_iff frame support).mp enabled.valueSupport,enabled.common⟩
  · rintro ⟨materialized,choice,support,values,common⟩
    have guards := selected_guards selected
    have alternatives := selected_alternatives selected plan.input frame.center_recorded plan.input_exact
    have positions := selected_safe selected plan frame.center_recorded plan.input_exact frame.registry_eq frame.context_eq
      frame.visible frame.role_eq (frame.context_eq ▸ frame.prepared) frame.located
    cases selected with
    | selected safe unique clear =>
        have kids := (unique.2 _ _ (frame_survivor frame safe.1)).2
        exact ⟨support,frame,(kids.symm ▸ unique),safe,ready,materialized,choice,
          (frame_value_iff frame support).mpr values,positions,alternatives,common⟩

theorem enabled_or_committed (enabled : Installable registry state plan support)
    (generated : GeneralNominalSaturationState.Generated state.core.erased.current root plan.packet.site.occurrence) :
    GeneralNominalFeedbackSteps.Committed state.core.erased.current plan.packet ∨
      ∃ after, Step registry root state after := by
  classical
  by_cases committed : GeneralNominalFeedbackSteps.Committed state.core.erased.current plan.packet
  · exact Or.inl committed
  · exact Or.inr ⟨install state plan support enabled,plan.packet.site.occurrence,generated,
      .install plan support enabled committed⟩

end Yulang.GeneralNominalCenteredHeadStepAvailability
