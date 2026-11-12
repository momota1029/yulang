import Yulang.GeneralNominalDownstreamBoundary
import Yulang.GeneralNominalDownstreamDepth

/-! Exact remaining installation-order contract for the downstream relation.
Finite support depth at one snapshot is kept separate from a decreasing order
across snapshots. No generation bound is inserted into source formation. -/
namespace Yulang.GeneralNominalDownstreamOrder
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalDownstreamSteps
universe u
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {before after state : Tracked roles}

theorem formed_step_cases (formed : SourceFormed registry root before) (step : Step registry root before after) :
    Passive registry root before after ∨
      ∃ packet : Packet roles, ∃ support,
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
    have given : Step registry root before {before with current := after} :=
      ⟨focus,generated,.administrative focus after action⟩
    cases action with
    | enqueue linked absent =>
      obtain ⟨site,member,same⟩ := GeneralNominalSupportOrder.generated_registered (formed_old formed) generated
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
    before (rank (install state packet support)) (rank state)

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
    (reachable : B4TargetV5.Reachable (GeneralNominalDownstreamBoundary.boundary roles) registry root state) :
    Acc (fun next current => (GeneralNominalDownstreamBoundary.boundary roles).Step registry root current next) state :=
  accessible order state (GeneralNominalDownstreamBoundary.reachable_formed registry state root reachable)

end Yulang.GeneralNominalDownstreamOrder
