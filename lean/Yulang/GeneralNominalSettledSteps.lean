import Yulang.GeneralNominalSettledSupport
import Yulang.GeneralNominalDownstreamOrder

/-! An additive relation for decision 7. Administrative work and merging keep
their full journal semantics. Only expansion requires a settled explanation.
No finite budget is included in formation. -/
namespace Yulang.GeneralNominalSettledSteps
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralNominalDemandMerging (Site)
open GeneralNominalSettledSupport (PacketSettled HeadJustified)

abbrev PacketGuard := @GeneralNominalSettledSupport.PacketGuard
noncomputable abbrev install := @GeneralNominalValueSteps.install
noncomputable abbrev merge := @GeneralNominalValueSteps.merge
abbrev Administrative := @GeneralNominalValueSteps.Administrative

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

theorem at_old (update : At registry before focus after) : GeneralNominalValueSteps.At registry before focus after := by
  cases update with
  | administrative _ _ action => exact .administrative _ _ action
  | install packet support enabled novel guard => exact .install packet support enabled novel guard.1
  | merge first last support one two same novel guard => exact .merge first last support one two same novel guard

theorem step_old (update : Step registry root before after) : GeneralNominalValueSteps.Step registry root before after :=
  ⟨update.choose,update.choose_spec.1,at_old update.choose_spec.2⟩

theorem formed_old (formed : SourceFormed registry root state) : GeneralNominalValueSteps.SourceFormed registry root state := by
  induction formed with
  | initial context source => exact .initial context source
  | update _ step ih => exact .update ih (step_old step)

theorem formed_exact (formed : SourceFormed registry root state) : GeneralNominalSupportSteps.Exact state :=
  GeneralNominalValueSteps.formed_exact (formed_old formed)

theorem stepModels (update : Step registry root before after) (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models after.current model) : Models before.current model :=
  GeneralNominalValueSteps.stepModels (step_old update) model valid

theorem settled_monotone (update : At registry before focus after)
    (done : PacketSettled before.current packet) : PacketSettled after.current packet :=
  ⟨GeneralNominalValueBudget.at_packets (at_old update) packet done.1,
    fun child member => GeneralNominalValueBudget.at_discharged (at_old update) (done.2 child member)⟩

/-- Every existing head explanation survives every new transition, including
installation, alias merging, equality feedback, and both observation updates. -/
theorem head_step (update : Step registry root before after)
    (known : HeadJustified before identity test) : HeadJustified after identity test :=
  GeneralNominalSettledSupport.head_monotone
    (GeneralNominalSupportSteps.at_source (GeneralNominalDownstreamSteps.at_old
      (GeneralNominalValueSteps.at_old (at_old update.choose_spec.2))))
    (GeneralNominalValueBudget.at_facts (at_old update.choose_spec.2))
    (fun _ done => settled_monotone update.choose_spec.2 done) known

theorem closure (halted : ∀ after, ¬ Step registry root state after) :
    Stable registry state root ∧ ∀ child, Generated state.current root child → Stable registry state child := by
  have stable : Stable registry state root := fun focus reached after step => halted after ⟨focus,reached,step⟩
  exact ⟨stable,fun child generated focus reached => stable focus (generated_trans generated reached)⟩

def Passive (registry : Registry) (root : Occurrence roles) (before after : Tracked roles) : Prop :=
  Step registry root before after ∧ GeneralNominalReobservationOrder.Update registry before.current after.current

theorem passive_accessible (registry : Registry) (root : Occurrence roles) (state : Tracked roles) :
    Acc (fun next current => Passive registry root current next) state := by
  induction GeneralNominalValueSteps.passive_accessible registry root state with
  | intro state below ih => exact Acc.intro state (fun next step => ih next ⟨step_old step.1,step.2⟩)

theorem formed_step_cases {roles : Roles.RoleDecls} {registry : Registry}
    {root : Occurrence roles} {before after : Tracked roles}
    (formed : SourceFormed registry root before) (step : Step registry root before after) :
    Passive registry root before after ∨ ∃ packet : Packet roles, ∃ support,
      Generated before.current root packet.site.occurrence ∧
      GeneralNominalFeedbackSteps.Installable registry before.current packet ∧
      ¬ GeneralNominalFeedbackSteps.Committed before.current packet ∧
      PacketGuard before packet support ∧ after = install before packet support := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | install packet support enabled novel guard => exact Or.inr ⟨packet,support,generated,enabled,novel,guard,rfl⟩
  | merge first last support one two same novel guard =>
    exact Or.inl ⟨⟨_,generated,.merge first last support one two same novel guard⟩,
      .ordinary (.merge first last one two same novel)⟩
  | administrative focus after action =>
    have given : Step registry root before {before with current := after} := ⟨focus,generated,.administrative focus after action⟩
    cases action with
    | enqueue linked absent =>
      obtain ⟨site,member,same⟩ := GeneralNominalSupportOrder.generated_registered
        (GeneralNominalDownstreamSteps.formed_old (GeneralNominalValueSteps.formed_old (formed_old formed))) generated
      exact False.elim (absent site member same)
    | refresh context certificate source member unknown known =>
      exact Or.inl ⟨given,.ordinary (.refresh focus context certificate source member unknown known)⟩
    | equate first last one two equal novel => exact Or.inl ⟨given,.ordinary (.equate focus first last one two equal novel)⟩
    | reobserve revision certificate improved => exact Or.inl ⟨given,.reobserve revision certificate improved⟩

def SupportPending (registry : Registry) (state : Tracked roles) (focus : Occurrence roles) : Prop :=
  ¬ GeneralNominalSettledSupport.DecisionGuard registry state focus

def Installable (registry : Registry) (state : Tracked roles) (packet : Packet roles) : Prop :=
  GeneralNominalFeedbackSteps.Installable registry state.current packet ∧ ∃ support, PacketGuard state packet support

theorem pending_not_installable (pending : SupportPending registry state packet.site.occurrence) :
    ¬ Installable registry state packet := by
  rintro ⟨enabled,support,guard⟩
  apply pending
  have context := enabled.1.2.1
  have reg := enabled.1.1
  simpa only [context,reg] using guard.2

/-- No infinite administrative suffix can hide a failure of the installation
budget. This statement retains the new guard at every witnessed installation. -/
theorem infinitely_often_installation {roles : Roles.RoleDecls} {registry : Registry}
    {root : Occurrence roles} (trace : Nat → Tracked roles)
    (initial : SourceFormed registry root (trace 0))
    (steps : ∀ n, Step registry root (trace n) (trace (n+1))) (cutoff : Nat) :
    ∃ n, cutoff ≤ n ∧ ∃ packet : Packet roles, ∃ support,
      Generated (trace n).current root packet.site.occurrence ∧
      GeneralNominalFeedbackSteps.Installable registry (trace n).current packet ∧
      ¬ GeneralNominalFeedbackSteps.Committed (trace n).current packet ∧
      PacketGuard (trace n) packet support ∧ trace (n+1) = install (trace n) packet support := by
  classical
  have formed : ∀ n, SourceFormed registry root (trace n) := by
    intro n
    induction n with
    | zero => exact initial
    | succ n ih => exact .update ih (steps n)
  apply Classical.byContradiction
  intro absent
  have passive : ∀ n, cutoff ≤ n → Passive registry root (trace n) (trace (n+1)) := by
    intro n bounded
    rcases formed_step_cases (formed n) (steps n) with quiet | active
    · exact quiet
    · exact False.elim (absent ⟨n,bounded,active⟩)
  have excludes : ∀ state, Acc (fun next current => Passive registry root current next) state →
      ∀ n, cutoff ≤ n → state = trace n → False := by
    intro state accessible
    induction accessible with
    | intro state below ih =>
      intro n bounded equal
      subst state
      exact ih (trace (n+1)) (passive n bounded) (n+1) (by omega) rfl
  exact excludes (trace cutoff) (passive_accessible registry root _) cutoff (Nat.le_refl _) rfl

end Yulang.GeneralNominalSettledSteps
