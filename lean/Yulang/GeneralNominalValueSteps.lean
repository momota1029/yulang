import Yulang.GeneralNominalValueSupport
import Yulang.GeneralNominalDownstreamSteps

/-! Additive installation guard with value-subterm dependencies. Ordinary
constraints, named equalities, observations and diagnostic identities retain
the existing transitions. Stronger support never deletes a journal fact. -/
namespace Yulang.GeneralNominalValueSteps
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralNominalDemandMerging (Site)

abbrev PacketGuard := @GeneralNominalValueSupport.PacketGuard
noncomputable abbrev install := @GeneralNominalSupportSteps.install
noncomputable abbrev merge := @GeneralNominalSupportSteps.merge
abbrev Administrative := @GeneralNominalSupportSteps.Administrative

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

inductive SourceFormed (registry : Registry) (root : Occurrence roles) : Tracked roles → Prop
  | initial (context : GeneralNominalCandidates.Context) :
      GeneralNominalSourceFormation.InitialSource registry context root → SourceFormed registry root (initial context root)
  | update : SourceFormed registry root before → Step registry root before after → SourceFormed registry root after

theorem at_old (update : At registry before focus after) :
    GeneralNominalDownstreamSteps.At registry before focus after := by
  cases update with
  | administrative _ _ action => exact .administrative _ _ action
  | install packet support enabled novel guard => exact .install packet support enabled novel (GeneralNominalValueSupport.packet_old guard)
  | merge first last support one two same novel guard => exact .merge first last support one two same novel guard

theorem step_old (update : Step registry root before after) :
    GeneralNominalDownstreamSteps.Step registry root before after :=
  ⟨update.choose,update.choose_spec.1,at_old update.choose_spec.2⟩

theorem formed_old (formed : SourceFormed registry root state) :
    GeneralNominalDownstreamSteps.SourceFormed registry root state := by
  induction formed with
  | initial context source => exact .initial context source
  | update _ step ih => exact .update ih (step_old step)

theorem formed_exact (formed : SourceFormed registry root state) : GeneralNominalSupportSteps.Exact state :=
  GeneralNominalDownstreamSteps.formed_exact (formed_old formed)

theorem stepModels (update : Step registry root before after) (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models after.current model) : Models before.current model :=
  GeneralNominalDownstreamSteps.stepModels (step_old update) model valid

theorem steps_models (path : B4Target.Steps (Step registry root) before after)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after.current model) : Models before.current model := by
  induction path with
  | refl => exact valid
  | tail _ update ih => exact ih (stepModels update model valid)

theorem generated_monotone (update : Step registry root before after) (reached : Generated before.current root child) :
    Generated after.current root child := GeneralNominalDownstreamSteps.generated_monotone (step_old update) reached

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

/-- The existing administrative order is inherited without an installation
measure. This theorem does not supply the missing generation budget. -/
def Passive (registry : Registry) (root : Occurrence roles) (before after : Tracked roles) : Prop :=
  Step registry root before after ∧ GeneralNominalReobservationOrder.Update registry before.current after.current

theorem passive_accessible (registry : Registry) (root : Occurrence roles) (state : Tracked roles) :
    Acc (fun next current => Passive registry root current next) state := by
  have old := GeneralNominalDownstreamSteps.passive_accessible registry root state
  induction old with
  | intro state below ih =>
    exact Acc.intro state (fun next step => ih next ⟨step_old step.1,step.2⟩)

theorem source_install (state : Tracked roles) (packet : Packet roles)
    (generated : Generated state.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.current packet)
    (guard : GeneralNominalSupportChoices.PacketGuard state packet []) :
    Step registry root state (install state packet []) :=
  ⟨_,generated,.install packet [] enabled novel (GeneralNominalValueSupport.source_packet state packet guard)⟩

theorem empty_ledger_at (empty : before.facts = [])
    (step : GeneralNominalDownstreamSteps.At registry before focus after) : At registry before focus after := by
  cases step with
  | administrative _ _ action => exact .administrative _ _ action
  | install packet support enabled novel guard =>
    exact .install packet support enabled novel ⟨guard.1,fun producer _ =>
      GeneralNominalValueSupport.empty_ledger_grounded packet.registry before empty producer⟩
  | merge first last support one two same novel guard => exact .merge first last support one two same novel guard

theorem empty_ledger_step (empty : before.facts = [])
    (step : GeneralNominalDownstreamSteps.Step registry root before after) : Step registry root before after :=
  ⟨step.choose,step.choose_spec.1,empty_ledger_at empty step.choose_spec.2⟩

theorem available_recorded (state : Tracked roles) (exact : GeneralNominalSupportSteps.Exact state)
    (head : Head state.current.context.state identity test observation) :
    GeneralNominalValueSupport.Available state identity test := by
  refine ⟨state.current.context.state,observation,head,?_⟩
  intro model valid
  have full := (exact model).mpr ((GeneralNominalDownstreamSupport.pool_exact state model).mp valid)
  exact GeneralCanonicalObservations.recorded_sound _ model full.1 (head_recorded head)

end Yulang.GeneralNominalValueSteps
