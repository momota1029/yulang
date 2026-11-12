import Yulang.GeneralNominalReobservationOrder
import Yulang.GeneralNominalSupportBoundary
import Yulang.GeneralNominalFeedbackDescent

/-! The exact guarded relation has no enqueue steps on formed states. Its
non-installation steps have derived accessibility, including descriptor
replacement. Full progress is reduced to an arbitrary installation order. -/
namespace Yulang.GeneralNominalSupportOrder

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
open GeneralNominalSaturationInvariants (EdgesRecorded)

universe u
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {before after state : Tracked roles}

private theorem edges_reobserved {first last : State roles} (recorded : EdgesRecorded first)
    (update : GeneralNominalReobservationSteps.At registry first focus last) : EdgesRecorded last := by
  cases update with
  | ordinary action => exact GeneralNominalFeedbackDescent.edges_update recorded action
  | reobserve => exact recorded

theorem edges_update (recorded : EdgesRecorded before.current)
    (update : At registry before focus after) : EdgesRecorded after.current :=
  edges_reobserved recorded (at_old update)

theorem formed_journal (formed : SourceFormed registry root state) :
    EdgesRecorded state.current ∧ ∃ site ∈ state.current.sites, site.occurrence = root := by
  induction formed with
  | initial context valid =>
    exact ⟨(by intro parent child member; cases member),GeneralNominalDemandMerging.pointSite root,
      by simp [GeneralNominalSupport.initial,GeneralNominalSaturationState.initial],rfl⟩
  | update _ step ih =>
    obtain ⟨site,member,same⟩ := ih.2
    exact ⟨edges_update ih.1 step.choose_spec.2,site,
      (GeneralNominalReobservationSteps.at_extends (at_old step.choose_spec.2)).journal.sites site member,same⟩

theorem generated_registered (formed : SourceFormed registry root state)
    (generated : Generated state.current root child) : ∃ site ∈ state.current.sites, site.occurrence = child := by
  have journal := formed_journal formed
  induction generated with
  | root => exact journal.2
  | child _ member _ => exact (journal.1 _ _ member).2
  | alias _ _ member _ _ => exact ⟨_,member,rfl⟩

def Passive (registry : Registry) (root : Occurrence roles) (before after : Tracked roles) : Prop :=
  Step registry root before after ∧
    GeneralNominalReobservationOrder.Update registry before.current after.current

theorem passive_accessible (registry : Registry) (root : Occurrence roles) (state : Tracked roles) :
    Acc (fun next current => Passive registry root current next) state := by
  have all : ∀ current, Acc (fun next current => GeneralNominalReobservationOrder.Update registry current next) current →
      ∀ tracked : Tracked roles, tracked.current = current → Acc (fun next current => Passive registry root current next) tracked := by
    intro current accessible
    induction accessible with
    | intro current below ih =>
      intro tracked equal
      refine Acc.intro tracked ?_
      intro next step
      exact ih next.current (equal ▸ step.2) next rfl
  exact all state.current (GeneralNominalReobservationOrder.accessible registry state.current) state rfl

theorem formed_step_cases (formed : SourceFormed registry root before) (step : Step registry root before after) :
    Passive registry root before after ∨
      ∃ packet : Packet roles, ∃ support,
        Generated before.current root packet.site.occurrence ∧
        GeneralNominalFeedbackSteps.Installable registry before.current packet ∧
        ¬ GeneralNominalFeedbackSteps.Committed before.current packet ∧
        PacketGuard before packet support ∧ after = GeneralNominalSupportSteps.install before packet support := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | install packet support enabled novel guard => exact Or.inr ⟨packet,support,generated,enabled,novel,guard,rfl⟩
  | merge first last support one two same novel guard =>
    exact Or.inl ⟨⟨_,generated,.merge first last support one two same novel guard⟩,
      .ordinary (.merge first last one two same novel)⟩
  | administrative focus after action =>
    have given : Step registry root before {before with current := after} :=
      ⟨focus,generated,.administrative focus after action⟩
    cases action with
    | enqueue linked absent =>
      obtain ⟨site,member,same⟩ := generated_registered formed generated
      exact False.elim (absent site member same)
    | refresh context certificate source member unknown known =>
      exact Or.inl ⟨given,.ordinary (.refresh focus context certificate source member unknown known)⟩
    | equate first last one two equal novel =>
      exact Or.inl ⟨given,.ordinary (.equate focus first last one two equal novel)⟩
    | reobserve revision certificate improved => exact Or.inl ⟨given,.reobserve revision certificate improved⟩

structure InstallationOrder (registry : Registry) (root : Occurrence roles) where
  Measure : Type u
  before : Measure → Measure → Prop
  wellFounded : WellFounded before
  rank : Tracked roles → Measure
  passive : ∀ first last, SourceFormed registry root first → Passive registry root first last →
    rank last = rank first ∨ before (rank last) (rank first)
  installation : ∀ state, SourceFormed registry root state → ∀ packet : Packet roles, ∀ support,
    Generated state.current root packet.site.occurrence →
    GeneralNominalFeedbackSteps.Installable registry state.current packet →
    ¬ GeneralNominalFeedbackSteps.Committed state.current packet → PacketGuard state packet support →
    before (rank (GeneralNominalSupportSteps.install state packet support)) (rank state)

theorem accessible (order : InstallationOrder registry root)
    (state : Tracked roles) (formed : SourceFormed registry root state) :
    Acc (fun next current => Step registry root current next) state := by
  have all : ∀ measure, ∀ current, order.rank current = measure → SourceFormed registry root current →
      Acc (fun next current => Step registry root current next) current := by
    intro measure
    induction order.wellFounded.apply measure with
    | intro measure below lower =>
      intro current
      induction passive_accessible registry root current with
      | intro current predecessors admin =>
        intro equal formed
        refine Acc.intro current ?_
        intro next step
        have nextFormed := SourceFormed.update formed step
        rcases formed_step_cases formed step with update | ⟨packet,support,generated,enabled,novel,guard,rfl⟩
        · rcases order.passive current next formed update with same | smaller
          · exact admin next update (same.trans equal) nextFormed
          · exact lower _ (equal ▸ smaller) next rfl nextFormed
        · exact lower _ (equal ▸ order.installation current formed packet support generated enabled novel guard) _ rfl nextFormed
  exact all (order.rank state) state rfl formed

theorem boundary_progress (roles : Roles.RoleDecls) (registry : Registry) (root : Occurrence roles)
    (order : InstallationOrder registry root) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state) :
    Acc (fun next current => (GeneralNominalSupportBoundary.boundary roles).Step registry root current next) state :=
  accessible order state (GeneralNominalSupportBoundary.reachable_formed registry state root reachable)

/-- An inconsistent journal cannot enable an installation. Its remaining
updates are precisely the already bounded administrative work. -/
theorem empty_models_accessible (formed : SourceFormed registry root state)
    (empty : ∀ model, ¬ Models state.current model) :
    Acc (fun next current => Step registry root current next) state := by
  induction passive_accessible registry root state with
  | intro state predecessors ih =>
    refine Acc.intro state ?_
    intro next step
    rcases formed_step_cases formed step with passive | ⟨packet,support,generated,enabled,novel,guard,rfl⟩
    · exact ih next passive (.update formed step) (fun model valid => empty model (stepModels step model valid))
    · obtain ⟨_,_,_,_,_,_,_,_,_,_,⟨model,valid,_⟩,_⟩ := enabled.1
      exact False.elim (empty model valid)

end Yulang.GeneralNominalSupportOrder
