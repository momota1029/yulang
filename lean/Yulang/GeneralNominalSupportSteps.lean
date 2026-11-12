import Yulang.GeneralNominalSupportChoices

/-! Guarded installation over the feedback/reobservation relation. Every
transition retains the source kernel. Semantic deltas have explicit finite
output dependencies; administrative observation updates add no support facts. -/
namespace Yulang.GeneralNominalSupportSteps

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalDemandMerging (Site)

abbrev PacketGuard := @GeneralNominalSupportChoices.PacketGuard

noncomputable def install (state : Tracked roles) (packet : Packet roles) (_support : List (Occurrence roles)) : Tracked roles :=
  {state with current := GeneralNominalFeedbackSites.install state.current packet (GeneralNominalFeedbackSites.emitted packet)
              facts := GeneralNominalSupportChoices.installedFacts state packet ++ state.facts}

noncomputable def merge (state : Tracked roles) (first last : Site roles) (_support : List (Occurrence roles)) : Tracked roles :=
  {state with current := GeneralNominalSaturationState.merge state.current first last
              facts := GeneralNominalSupportChoices.mergedFacts state first last ++ state.facts}

inductive Administrative (registry : Registry) (state : State roles) : Occurrence roles → State roles → Prop
  | enqueue (focus : Occurrence roles) : GeneralNominalState.Linked state.context.state focus.demand →
      (∀ site ∈ state.sites, site.occurrence ≠ focus) → Administrative registry state focus (enqueue state focus)
  | refresh (focus : Occurrence roles) (context : GeneralNominalCandidates.Context) :
      GeneralNominalFeedbackSteps.Refresh state context → (source : Nat) →
      source ∈ GeneralNominalState.sources state.context.state →
      ¬ GeneralNominalState.Known state.context.state source → GeneralNominalState.Known context.state source →
      Administrative registry state focus (regenerate state context)
  | equate (focus : Occurrence roles) (first last : Nat) :
      first ∈ GeneralNominalState.sources state.context.state → last ∈ GeneralNominalState.sources state.context.state →
      GeneralNominalFeedbackK2.Equal state first last → ¬ GeneralNominalFeedbackSteps.RawEqual state first last →
      Administrative registry state focus (GeneralNominalFeedbackSteps.equate state first last)
  | reobserve (focus : Occurrence roles) (revision : GeneralNominalReobservationSteps.Revision state) :
      GeneralNominalReobservationSteps.Certified revision → GeneralNominalReobservationSteps.Improves revision →
      Administrative registry state focus revision.result

inductive At (registry : Registry) (before : Tracked roles) : Occurrence roles → Tracked roles → Prop
  | administrative (focus : Occurrence roles) (after : State roles) : Administrative registry before.current focus after →
      At registry before focus {before with current := after}
  | install (packet : Packet roles) (support : List (Occurrence roles)) :
      GeneralNominalFeedbackSteps.Installable registry before.current packet →
      ¬ GeneralNominalFeedbackSteps.Committed before.current packet → PacketGuard before packet support →
      At registry before packet.site.occurrence (install before packet support)
  | merge (first last : Site roles) (support : List (Occurrence roles)) :
      first ∈ before.current.sites → last ∈ before.current.sites →
      GeneralNominalFeedbackSites.SameInputs before.current first last →
      ¬ Alias before.current first.occurrence.identity last.occurrence.identity →
      GeneralNominalSupportChoices.MergeGuard before first last support →
      At registry before first.occurrence (merge before first last support)

def Step (registry : Registry) (root : Occurrence roles) (before after : Tracked roles) : Prop :=
  ∃ focus, Generated before.current root focus ∧ At registry before focus after

def Stable (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state.current root focus → ∀ after, ¬ At registry state focus after

def Exact (state : Tracked roles) : Prop := ∀ model, Models state.current model ↔ AllModels state model

inductive SourceFormed (registry : Registry) (root : Occurrence roles) : Tracked roles → Prop
  | initial (context : GeneralNominalCandidates.Context) :
      GeneralNominalSourceFormation.InitialSource registry context root → SourceFormed registry root (initial context root)
  | update : SourceFormed registry root before → Step registry root before after → SourceFormed registry root after

theorem administrative_old (update : Administrative registry before focus after) :
    GeneralNominalReobservationSteps.At registry before focus after := by
  cases update with
  | enqueue linked absent => exact .ordinary _ (.enqueue _ linked absent)
  | refresh context certificate source member unknown known =>
    exact .ordinary _ (.refresh _ context certificate source member unknown known)
  | equate first last one two equal novel => exact .ordinary _ (.equate _ first last one two equal novel)
  | reobserve revision certificate improved => exact .reobserve _ revision certificate improved

theorem administrative_models (update : Administrative registry before focus after) (model : Assignment) :
    Models after model ↔ Models before model := by
  cases update with
  | enqueue => exact enqueue_models ..
  | refresh _ certificate _ _ _ _ => exact GeneralNominalCycleSteps.refresh_models certificate model
  | equate _ _ _ _ equal _ => exact GeneralNominalFeedbackSteps.equate_models _ _ _ equal model
  | reobserve _ certificate _ => exact certificate.exact model

theorem at_old (update : At registry before focus after) :
    GeneralNominalReobservationSteps.At registry before.current focus after.current := by
  cases update with
  | administrative _ _ update => exact administrative_old update
  | install packet support enabled novel _ => exact .ordinary _ (.install packet enabled novel)
  | merge first last _ one two same novel _ => exact .ordinary _ (.merge first last one two same novel)

theorem step_old (update : Step registry root before after) :
    GeneralNominalReobservationSteps.Step registry root before.current after.current :=
  ⟨update.choose,update.choose_spec.1,at_old update.choose_spec.2⟩

theorem stepModels (update : Step registry root before after) (model : Assignment)
    (valid : Models after.current model) : Models before.current model :=
  GeneralNominalReobservationSteps.stepModels (step_old update) model valid

theorem steps_models (path : B4Target.Steps (Step registry root) before after)
    (model : Assignment) (valid : Models after.current model) : Models before.current model := by
  induction path with
  | refl => exact valid
  | tail previous update ih => exact ih (stepModels update model valid)

theorem generated_monotone (update : Step registry root before after) (reached : Generated before.current root child) :
    Generated after.current root child := GeneralNominalReobservationSteps.generated_monotone (step_old update) reached

theorem at_exact (exact : Exact before) (update : At registry before focus after) : Exact after := by
  intro model
  cases update with
  | administrative _ _ update => exact (administrative_models update model).trans (exact model)
  | install packet support enabled novel guard =>
    change Models (GeneralNominalFeedbackSites.install _ _ _) model ↔ _
    rw [GeneralNominalFeedbackSites.install_models _ packet _ enabled.1.2.1 model]
    have facts := GeneralNominalSupportChoices.facts_exact before packet support guard model
    constructor
    · rintro ⟨old,packetValid⟩
      obtain ⟨_,inputs,outputs⟩ := (GeneralNominalPacketSupport.packet_exact packet model).mp packetValid
      refine ⟨((exact model).mp old).1,?_⟩
      intro fact member
      rcases List.mem_append.mp member with added | prior
      · exact facts.mpr ⟨inputs,outputs⟩ fact added
      · exact ((exact model).mp old).2 fact prior
    · intro valid
      have old : Models before.current model := (exact model).mpr
        ⟨valid.1,fun fact member => valid.2 fact (List.mem_append_right _ member)⟩
      have constraints := facts.mp (fun fact member => valid.2 fact (List.mem_append_left _ member))
      exact ⟨old,(GeneralNominalPacketSupport.packet_exact packet model).mpr
        ⟨enabled.1.2.1.symm ▸ old.1,constraints⟩⟩
  | merge first last support one two same novel supported =>
    change Models (GeneralNominalSaturationState.merge _ _ _) model ↔ _
    rw [GeneralNominalSaturationState.merge_models]
    have facts := GeneralNominalSupportChoices.merged_facts_exact before first last support supported model
    constructor
    · rintro ⟨old,atoms⟩
      refine ⟨((exact model).mp old).1,?_⟩
      intro fact member
      rcases List.mem_append.mp member with added | prior
      · exact facts.mpr atoms fact added
      · exact ((exact model).mp old).2 fact prior
    · intro valid
      exact ⟨(exact model).mpr ⟨valid.1,fun fact member => valid.2 fact (List.mem_append_right _ member)⟩,
        facts.mp (fun fact member => valid.2 fact (List.mem_append_left _ member))⟩

theorem formed_exact (formed : SourceFormed registry root state) : Exact state := by
  induction formed with
  | initial context valid =>
    intro model
    exact (initial_models context root model).trans (by simp [AllModels,GeneralNominalSupport.initial])
  | update _ step ih => exact at_exact ih step.choose_spec.2

theorem at_source (update : At registry before focus after) : after.source = before.source := by cases update <;> rfl

theorem closure (halted : ∀ after, ¬ Step registry root state after) :
    Stable registry state root ∧ ∀ child, Generated state.current root child → Stable registry state child := by
  have stable : Stable registry state root := fun focus reached after step => halted after ⟨focus,reached,step⟩
  exact ⟨stable,fun child generated focus reached => stable focus (generated_trans generated reached)⟩

theorem stable_committed {state : Tracked roles} (stable : Stable registry state root) (packet : Packet roles)
    (generated : Generated state.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (support : List (Occurrence roles)) (guard : PacketGuard state packet support) :
    GeneralNominalFeedbackSteps.Committed state.current packet := by
  classical
  by_cases done : GeneralNominalFeedbackSteps.Committed state.current packet
  · exact done
  · exact False.elim (stable packet.site.occurrence generated _ (.install packet support enabled done guard))

end Yulang.GeneralNominalSupportSteps
