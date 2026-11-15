import Yulang.GeneralDictionaryDefaultMonotonicity208
import Yulang.GeneralNominalCenteredHeadMatStepFiniteProgress

/-! A finite semantic delta cover suffices for the unrestricted successor Step.
All administrative constructors use the same missing-fact measure. The cover's
producer is separate from the measure and must use total packet equations. -/
namespace Yulang.GeneralDictionaryDefaultFinite208
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalSaturationState (Generated)
open GeneralNominalSharedBudget (Signature)
open GeneralNominalCenteredAccessibility (Fact facts signature_mem known_mem equal_mem point_mem alias_mem)
variable {roles : Roles.RoleDecls} {state before after : State roles}

def Represents (signature : Signature roles) (state : State roles) (plan : Plan roles) : Prop :=
  signature.parent = plan.packet.site.occurrence ∧ signature.children = plan.packet.children ∧
    ∀ model, signature.delta model ↔
      GeneralNominalCenteredHeadMatStepPackets.Inputs plan model ∧
      GeneralDictionaryDefaultSchema208.SchemaHolds state.core plan.packet.site.occurrence plan model

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
      fun child member => GeneralDictionaryDefaultMonotonicity208.edges step.choose_spec.2 (given.2 child member)⟩
  | known => exact GeneralDictionaryDefaultMonotonicity208.known step.choose_spec.2 _
  | equal => exact fun given model valid => given model (GeneralDictionaryDefaultMonotonicity208.raw_models step.choose_spec.2 valid)
  | alias => exact GeneralNominalCenteredHeadMatStepTrustedGrowth.aliases (GeneralDictionaryDefaultGrowth208.step step)
  | point => exact GeneralDictionaryDefaultMonotonicity208.point step.choose_spec.2

structure FiniteCover (registry : Registry) (root : Occurrence roles) (start : State roles) where
  signatures : List (Signature roles)
  sources : List Nat
  occurrences : List (Occurrence roles)
  installs : ∀ state, B4Target.Steps (Step registry root) start state → ∀ effect,
    Generated state.core.erased.current root effect.plan.packet.site.occurrence →
    Installable registry state effect → ¬ Committed state effect.plan →
    ∃ signature ∈ signatures, Represents signature state effect.plan
  source_mem : ∀ state, B4Target.Steps (Step registry root) start state →
    GeneralNominalState.sources state.core.erased.current.context.state ⊆ sources
  slot_mem : ∀ state, B4Target.Steps (Step registry root) start state →
    ∀ slot, state.core.erased.current.context.state.base.source slot ∈ sources
  center_mem : ∀ state, B4Target.Steps (Step registry root) start state →
    ∀ site ∈ state.core.sites, site.occurrence ∈ occurrences

theorem novel_signature (enabled : Installable registry state effect)
    (novel : ¬ Committed state effect.plan) (represents : Represents signature state effect.plan) :
    ¬ Holds state (.signature signature) := by
  intro held
  apply novel
  have semantic := fun model valid => (represents.2.2 model).mp (held.1 model valid)
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro model valid
    have context := effect.frame.context_eq.trans
      (congrArg (fun state => state.erased.current.context) enabled.snapshot_eq)
    exact ⟨context.symm ▸ valid.1,(semantic model valid).1,(semantic model valid).2.1⟩
  · intro child member
    simpa only [represents.1] using held.2 child (represents.2.1.symm ▸ member)
  · exact fun model valid => (semantic model valid).2

theorem installed_signature (snapshot : effect.snapshot = state.core)
    (represents : Represents signature state effect.plan) : Holds (install state effect) (.signature signature) := by
  have done := installed_committed snapshot
  refine ⟨?_,?_⟩
  · intro model valid
    have parts := (install_models snapshot).mp valid
    apply (represents.2.2 model).mpr
    exact ⟨parts.2.1.2.1,GeneralDictionaryDefaultSchema208.schema_holds_iff.mpr
      ⟨parts.2.1.2.2,snapshot ▸ parts.2.2.1.2⟩⟩
  · intro child member
    rw [represents.1]
    exact done.1.2 child (represents.2.1 ▸ member)

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
      obtain ⟨site,member,same⟩ := GeneralDictionaryDefaultTrace208.generated_registered
        (GeneralDictionaryDefaultTrace208.registered_trace path) generated
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

end Yulang.GeneralDictionaryDefaultFinite208
