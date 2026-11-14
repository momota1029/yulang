import Yulang.GeneralNominalCenteredSnapshot

/-! Fixed-hole phase accessibility for the full centered transition relation. -/
namespace Yulang.GeneralNominalCenteredHolePhases
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalHoleElimination
open GeneralNominalHolePhases (History history_count history_valid refinement_cases)
open GeneralNominalSharedBudget (Signature Represents remaining novel_signature installed_signature)

variable {roles : Roles.RoleDecls}

/-- Only the finite source frontier fixes hole identities. A cover can grow
after a genuine elimination, with no source-wide size bound in this contract. -/
structure PhaseCover (registry : Registry) (context : GeneralNominalCandidates.Context) (root : Occurrence roles) where
  start : Inventory
  tests : List GeneralNominalRecursiveInspection.Test
  holes : start.holes = List.range (GeneralNominalSourceFrontier.frontier context.state).length
  valid : Valid tests start
  invariant : State roles → Inventory → Prop
  initial : invariant (GeneralNominalCenteredSteps.initial context root) start
  basis : Inventory → List (Signature roles)
  next : ∀ state, B4Target.Steps (Step registry root) (GeneralNominalCenteredSteps.initial context root) state →
    ∀ inventory, invariant state inventory → ∀ after, Step registry root state after →
      ∃ updated growth count, Trace tests growth inventory updated count ∧ invariant after updated
  covers : ∀ state, B4Target.Steps (Step registry root) (GeneralNominalCenteredSteps.initial context root) state →
    ∀ inventory, invariant state inventory → ∀ plan : Plan roles, ∀ support,
      GeneralNominalSaturationState.Generated state.erased.current root plan.packet.site.occurrence →
      GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet →
      ¬ GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet → PacketGuard state plan support →
      ∃ signature ∈ basis inventory, Represents signature plan.packet

theorem replay (cover : PhaseCover registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (GeneralNominalCenteredSteps.initial context root) state) :
    ∃ inventory count, History cover.tests cover.start inventory count ∧
      cover.invariant state inventory ∧ count ≤ cover.start.holes.length ∧ Valid cover.tests inventory := by
  have run : ∀ state, B4Target.Steps (Step registry root) (GeneralNominalCenteredSteps.initial context root) state →
      ∃ inventory count, History cover.tests cover.start inventory count ∧ cover.invariant state inventory := by
    intro state trace
    induction trace with
    | refl => exact ⟨cover.start,0,.refl _,cover.initial⟩
    | @tail before after trace step ih =>
      obtain ⟨inventory,count,history,invariant⟩ := ih
      obtain ⟨updated,growth,additions,update,next⟩ := cover.next before trace inventory invariant after step
      exact ⟨updated,count+additions,.tail history update,next⟩
  obtain ⟨inventory,count,history,invariant⟩ := run state path
  exact ⟨inventory,count,history,invariant,by have length := history_count history; omega,history_valid history cover.valid⟩

theorem accessible (cover : PhaseCover registry context (root : Occurrence roles)) :
    Acc (fun next current => Step registry root current next) (GeneralNominalCenteredSteps.initial context root) := by
  have all : ∀ h, ∀ inventory : Inventory, inventory.holes.length = h →
      ∀ state, B4Target.Steps (Step registry root) (GeneralNominalCenteredSteps.initial context root) state → cover.invariant state inventory →
      Acc (fun next current => Step registry root current next) state := by
    intro h
    induction Nat.lt_wfRel.wf.apply h with
    | intro h below outer =>
      intro inventory height
      have phase : ∀ n, ∀ state : State roles, remaining (cover.basis inventory) state.erased = n →
          B4Target.Steps (Step registry root) (GeneralNominalCenteredSteps.initial context root) state → cover.invariant state inventory →
          Acc (fun next current => Step registry root current next) state := by
        intro n
        induction Nat.lt_wfRel.wf.apply n with
        | intro n below inner =>
          intro state
          induction GeneralNominalCenteredProgress.passive_accessible state with
          | intro state predecessors admin =>
            intro equal path invariant
            refine Acc.intro state ?_
            intro after step
            have nextPath := B4Target.Steps.tail path step
            obtain ⟨updated,growth,count,trace,next⟩ := cover.next state path inventory invariant after step
            rcases refinement_cases trace with same | less
            · subst updated
              rcases GeneralNominalCenteredProgress.step_cases path step with passive | ⟨plan,support,generated,enabled,novel,guard,rfl⟩
              · have weak := GeneralNominalCenteredProgress.signatures_remaining_monotone (cover.basis inventory) step
                rcases Nat.lt_or_eq_of_le weak with strict | same
                · exact inner _ (equal ▸ strict) _ rfl nextPath next
                · exact admin after passive (same.trans equal) nextPath next
              · obtain ⟨signature,member,represents⟩ := cover.covers state path inventory invariant plan support generated enabled novel guard
                have strict := GeneralNominalCenteredProgress.signatures_remaining_decreases (cover.basis inventory) step member
                  (novel_signature enabled novel represents) (installed_signature represents support)
                exact inner _ (equal ▸ strict) _ rfl nextPath next
            · exact outer _ (height ▸ less) updated rfl after nextPath next
      intro state path invariant
      exact phase _ state rfl path invariant
  exact all _ cover.start rfl _ .refl cover.initial

end Yulang.GeneralNominalCenteredHolePhases
