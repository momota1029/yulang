import Yulang.GeneralNominalCenteredHeadMatStepHistory

set_option backward.isDefEq.respectTransparency false

/-! Cached observations need a settled explanation of the exact descriptor.
The ordinary journal remains available for equations and cycle checks. -/
namespace Yulang.GeneralNominalCenteredHeadMatStepObservations
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralNominalCenteredHeadMatStepSupport (Fact Trusted)
open GeneralNominalCommonBridge (Assignment)
open GeneralCanonicalObservations (Observation Recorded)
variable {roles : Roles.RoleDecls} {state : State roles} {model : Assignment}

def Justifies (state : State roles) (claim : Assignment → Prop) : Prop :=
  ∃ facts, Trusted state facts ∧ ∀ model,
    GeneralNominalCenteredHeadMatStepSupport.Models state facts model → claim model

def CacheSound (state : State roles) (snapshot : GeneralNominalState.State) : Prop :=
  ∀ observation, Recorded snapshot observation → Justifies state observation.Holds

theorem justifies_sound (justified : Justifies state claim)
    (valid : GeneralNominalCenteredHeadMatStepJournal.Models state model) : claim model := by
  obtain ⟨facts,trusted,sound⟩ := justified
  exact sound model (GeneralNominalCenteredHeadMatStepSupport.trusted_models trusted valid)

theorem cache_sound (cache : CacheSound state snapshot) (recorded : Recorded snapshot observation)
    (valid : GeneralNominalCenteredHeadMatStepJournal.Models state model) : observation.Holds model :=
  justifies_sound (cache observation recorded) valid

theorem source_cache : CacheSound state state.core.erased.source.state := by
  intro observation recorded
  exact ⟨[],.source,fun model valid => GeneralCanonicalObservations.recorded_sound _ model valid.1 recorded⟩

theorem initial_cache (context : GeneralNominalCandidates.Context) (root : GeneralSourceDictionaries.Occurrence roles) :
    CacheSound (GeneralNominalCenteredHeadMatStepJournal.initial context root) context.state := source_cache

theorem exact_head_justified (cache : CacheSound state snapshot)
    (head : GeneralNominalSupport.Head snapshot identity test observation) :
    GeneralNominalCenteredHeadMatStepSupport.HeadJustified state identity test := by
  obtain ⟨facts,trusted,sound⟩ := cache observation (GeneralNominalSupport.head_recorded head)
  exact ⟨facts,trusted,snapshot,observation,head,sound⟩

def Cut (state : State roles) (model : Assignment) : Prop :=
  ∀ facts, Trusted state facts → GeneralNominalCenteredHeadMatStepSupport.Models state facts model

theorem cut_source (cut : Cut state model) : GeneralNominalState.Models state.core.erased.source.state model :=
  (cut [] .source).1

theorem cut_excludes (cut : Cut state model) (falseClaim : ¬ claim model) : ¬ Justifies state claim := by
  rintro ⟨facts,trusted,sound⟩
  exact falseClaim (sound model (cut facts trusted))

theorem cache_excluded (cut : Cut state model) (recorded : Recorded snapshot observation)
    (falseHead : ¬ observation.Holds model) : ¬ CacheSound state snapshot :=
  fun cache => cut_excludes cut falseHead (cache observation recorded)

theorem no_unsettled_fact (trusted : Trusted state facts)
    (unsettled : ¬ GeneralNominalSettledSupport.PacketSettled state.core.erased.current effect.plan.packet) :
    Fact.output effect ∉ facts :=
  fun member => unsettled (GeneralNominalCenteredHeadMatStepSupport.outputs_settled trusted member)

theorem cut_of_recorded
    (source : GeneralNominalState.Models state.core.erased.source.state model)
    (centers : ∀ site ∈ state.core.sourceSites, site.Holds model)
    (inputs : ∀ plan ∈ state.core.plans, GeneralNominalCenteredHeadMatStepPackets.Inputs plan model)
    (outputs : ∀ effect ∈ state.effects, effect.plan ∈ state.core.plans →
      GeneralNominalSettledSupport.PacketSettled state.core.erased.current effect.plan.packet →
      GeneralNominalCenteredHeadMatStepPackets.Outputs effect.plan model ∧ effect.Holds model)
    (merges : ∀ first ∈ state.core.sites, ∀ last ∈ state.core.sites,
      GeneralNominalSaturationState.Alias state.core.erased.current first.occurrence.identity last.occurrence.identity →
      (∀ atom ∈ GeneralNominalDemandMerging.outputAtoms first.observed last.observed,
        atom ∈ state.core.erased.current.context.state.ordinary) →
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalDemandMerging.outputAtoms first.observed last.observed)) : Cut state model := by
  intro facts trusted
  refine ⟨source,centers,?_⟩
  induction trusted with
  | source => intro fact member; cases member
  | input plan _ recorded _ ih =>
      intro fact member
      rcases List.mem_cons.mp member with rfl | member
      · exact inputs plan recorded
      · exact ih fact member
  | output effect _ recorded planRecorded _ _ settled ih =>
      intro fact member
      rcases List.mem_cons.mp member with rfl | member
      · exact outputs effect recorded planRecorded settled
      · exact ih fact member
  | merge first last _ one two alias atoms _ _ ih =>
      intro fact member
      rcases List.mem_cons.mp member with rfl | member
      · exact merges first one last two alias atoms
      · exact ih fact member

end Yulang.GeneralNominalCenteredHeadMatStepObservations
