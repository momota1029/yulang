import Yulang.GeneralNominalCenteredHeadMatStepMonotonicity
import Yulang.GeneralNominalCenteredHeadMatStepExecutor

/-! A finite semantic delta cover suffices for the unrestricted successor Step.
All administrative constructors use the same missing-fact measure. The cover's
producer is separate from the measure and must use total packet equations. -/
namespace Yulang.GeneralNominalCenteredHeadMatStepFiniteProgress
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralNominalCenteredHeadMatStepKernel
open GeneralNominalSaturationState (Generated)
open GeneralNominalSharedBudget (Signature)
open GeneralNominalCenteredAccessibility (Fact facts signature_mem known_mem equal_mem point_mem alias_mem)
variable {roles : Roles.RoleDecls} {state before after : State roles}

def Represents (signature : Signature roles) (plan : Plan roles) : Prop :=
  signature.parent = plan.packet.site.occurrence ∧ signature.children = plan.packet.children ∧
    ∀ model, signature.delta model ↔
      GeneralNominalCenteredHeadMatStepPackets.Inputs plan model ∧ GeneralNominalCenteredHeadMatStepPackets.Outputs plan model

def Holds (state : State roles) : Fact roles → Prop
  | .signature signature =>
    (∀ model, Models state model → signature.delta model) ∧
      ∀ child ∈ signature.children, (signature.parent,child) ∈ state.core.erased.current.edges
  | .known identity => GeneralNominalState.Known state.core.erased.current.context.state identity
  | .equal first last => GeneralNominalFeedbackSteps.RawEqual state.core.erased.current first last
  | .alias first last => GeneralNominalSaturationState.Alias state.core.erased.current first last
  | .point identity => GeneralNominalReobservationOrder.Point state.core.erased.current identity

theorem monotone (step : Step registry root before after) (fact : Fact roles) : Holds before fact → Holds after fact := by
  cases fact with
  | signature signature =>
    intro given
    exact ⟨fun model valid => given.1 model (stepModels step valid),
      fun child member => GeneralNominalCenteredHeadMatStepMonotonicity.edges step.choose_spec.2 (given.2 child member)⟩
  | known => exact GeneralNominalCenteredHeadMatStepMonotonicity.known step.choose_spec.2 _
  | equal => exact fun given model valid => given model (GeneralNominalCenteredHeadMatStepMonotonicity.raw_models step.choose_spec.2 valid)
  | alias => exact GeneralNominalCenteredHeadMatStepTrustedGrowth.aliases (GeneralNominalCenteredHeadMatStepTrustedGrowth.step step)
  | point => exact GeneralNominalCenteredHeadMatStepMonotonicity.point step.choose_spec.2

structure FiniteCover (registry : Registry) (root : Occurrence roles) (start : State roles) where
  signatures : List (Signature roles)
  sources : List Nat
  occurrences : List (Occurrence roles)
  installs : ∀ state, B4Target.Steps (Step registry root) start state → ∀ effect,
    Generated state.core.erased.current root effect.plan.packet.site.occurrence →
    Installable registry state effect → ¬ Committed state effect.plan →
    ∃ signature ∈ signatures, Represents signature effect.plan
  source_mem : ∀ state, B4Target.Steps (Step registry root) start state →
    GeneralNominalState.sources state.core.erased.current.context.state ⊆ sources
  slot_mem : ∀ state, B4Target.Steps (Step registry root) start state →
    ∀ slot, state.core.erased.current.context.state.base.source slot ∈ sources
  center_mem : ∀ state, B4Target.Steps (Step registry root) start state →
    ∀ site ∈ state.core.sites, site.occurrence ∈ occurrences

theorem novel_signature (enabled : Installable registry state effect)
    (novel : ¬ Committed state effect.plan) (represents : Represents signature effect.plan) :
    ¬ Holds state (.signature signature) := by
  intro held
  apply novel
  refine ⟨?_,?_⟩
  · intro model valid
    have context := effect.frame.context_eq.trans
      (congrArg (fun state => state.erased.current.context) enabled.snapshot_eq)
    exact ⟨context.symm ▸ valid.1,(represents.2.2 model).mp (held.1 model valid)⟩
  · intro child member
    simpa only [represents.1] using held.2 child (represents.2.1.symm ▸ member)

theorem installed_signature (snapshot : effect.snapshot = state.core)
    (represents : Represents signature effect.plan) : Holds (install state effect) (.signature signature) := by
  have done := installed_committed snapshot
  refine ⟨?_,?_⟩
  · intro model valid
    exact (represents.2.2 model).mpr (done.1 model valid).2
  · intro child member
    rw [represents.1]
    exact done.2 child (represents.2.1 ▸ member)

theorem fresh_fact (cover : FiniteCover registry root (initial context root))
    (path : B4Target.Steps (Step registry root) (initial context root) before)
    (step : Step registry root before after) :
    ∃ fact ∈ facts cover.signatures cover.sources cover.occurrences, ¬ Holds before fact ∧ Holds after fact := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | install effect enabled novel =>
    obtain ⟨signature,member,represented⟩ := cover.installs before path effect generated enabled novel
    exact ⟨.signature signature,signature_mem member,novel_signature enabled novel represented,
      installed_signature enabled.snapshot_eq represented⟩
  | refresh focus context certificate identity member unknown known =>
    exact ⟨.known identity,known_mem (cover.source_mem before path member),unknown,known⟩
  | merge first last one two same novel =>
    exact ⟨.alias first.occurrence.identity last.occurrence.identity,
      alias_mem (cover.center_mem before path first one) (cover.center_mem before path last two),novel,
      GeneralNominalCycleSteps.merged_inputs before.core.erased.current first.observed last.observed⟩
  | administrative action =>
    cases action with
    | enqueue linked absent =>
      obtain ⟨site,member,same⟩ := GeneralNominalCenteredHeadMatStepTrace.generated_registered
        (GeneralNominalCenteredHeadMatStepTrace.registered_trace path) generated
      exact False.elim (absent site member same)
    | refresh context certificate identity member unknown known =>
      exact ⟨.known identity,known_mem (cover.source_mem before path member),unknown,known⟩
    | equate first last one two equal novel =>
      exact ⟨.equal first last,equal_mem (cover.source_mem before path one) (cover.source_mem before path two),novel,
        GeneralNominalFeedbackSteps.equate_feedback before.core.erased.current first last⟩
    | reobserve revision certificate improved =>
      obtain ⟨slot,old,now⟩ := improved.2
      refine ⟨.point (before.core.erased.current.context.state.base.source slot),
        point_mem (cover.slot_mem before path slot),?_,slot,rfl,now⟩
      rintro ⟨other,same,point⟩
      have equal := before.core.erased.current.context.state.base.source_injective same
      exact old (equal ▸ point)

theorem accessible_of_cover (cover : FiniteCover registry root (initial context root)) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  GeneralNominalFiniteProgress.accessible (Step registry root) (initial context root) Holds
    (facts cover.signatures cover.sources cover.occurrences)
    (fun _ _ step => monotone step) (fun _ _ path step => fresh_fact cover path step)

def GroundCover (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, Checked registry → ∀ context (root : Occurrence roles) labels,
    GeneralNominalSourceFormation.InitialSource registry context root →
    (∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) →
    GeneralNominalGroundAccessibility.GroundRoots context root labels →
    GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation →
    Nonempty (FiniteCover registry root (initial context root))

theorem progress (covers : GroundCover roles) : GeneralNominalCenteredHeadMatStepExecutor.Progress roles := by
  intro registry checked state root reachable
  obtain ⟨start,⟨context,labels,source,point,ground,coverage,rfl⟩,path⟩ := reachable
  obtain ⟨cover⟩ := covers registry checked.2 context root labels source point ground coverage
  have accessible := accessible_of_cover cover
  induction path with
  | refl => exact accessible
  | tail path step ih => exact ih.inv step

end Yulang.GeneralNominalCenteredHeadMatStepFiniteProgress
