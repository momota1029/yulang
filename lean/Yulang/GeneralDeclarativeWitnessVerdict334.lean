import Yulang.GeneralDeclarativeWitnessRowProjection334

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessVerdict334
open GeneralDeclarations (Checked)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeLowerKnown321 (ready_iff_not_delayed)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeWitnessClassify334 (Rule)
open GeneralDeclarativeWitnessReadout334 (chosen_declaration)
open GeneralDeclarativeWitnessHead334 (current_heads)
open GeneralDeclarativeUnfinishedRoot330 (blocked_and_cyclic)
open GeneralDeclarativePriority321 (Local overlap_outside_fragment)
open CommonRoleOutermostResolver (Frontier)

inductive Verdict
  | pending | rejected | ambiguous | selected (declaration : Nat)
  deriving DecidableEq

def verdict : Frontier α → Verdict
  | .pending => .pending
  | .rejected => .rejected
  | .ambiguous => .ambiguous
  | .selected key _ => .selected key

private theorem prior_no_choice {s : State} {p : Supported s done}
    (pick : Elected s r i p tests d impl)
    (old : Local s r i p tests (fun _ _ _ => False) d outcome) : False := by
  cases old with
  | unsupported delayed _ => exact (ready_iff_not_delayed _ _).mp pick.ready delayed
  | recursive _ cycle => exact pick.guarded cycle
  | unresolved _ _ blocked => exact pick.clear blocked
  | noCandidate _ _ _ empty => exact empty _ pick.viable
  | ambiguous _ _ _ a b different => exact different ((pick.unique _ a).trans (pick.unique _ b).symm)
  | selected _ _ _ _ _ impossible => exact impossible

private theorem prior_functional {s : State} {p : Supported s done}
    (a : Local s r i p tests (fun _ _ _ => False) d one)
    (b : Local s r i p tests (fun _ _ _ => False) d two) : one = two := by
  cases a with
  | unsupported delayed safe =>
    cases b with
    | unsupported => rfl
    | recursive _ cycle => exact (safe cycle).elim
    | unresolved => rfl
    | noCandidate ready _ _ _ => exact False.elim ((ready_iff_not_delayed _ _).mp ready delayed)
    | ambiguous ready _ _ _ _ _ => exact False.elim ((ready_iff_not_delayed _ _).mp ready delayed)
    | selected _ _ _ _ _ impossible => exact impossible.elim
  | recursive ready cycle =>
    cases b with
    | unsupported delayed _ => exact False.elim ((ready_iff_not_delayed _ _).mp ready delayed)
    | recursive => rfl
    | unresolved _ safe _ => exact (safe cycle).elim
    | noCandidate => rfl
    | ambiguous _ safe _ _ _ _ => exact (safe cycle).elim
    | selected _ _ _ _ _ impossible => exact impossible.elim
  | unresolved _ safe blocked =>
    cases b with
    | unsupported => rfl
    | recursive _ cycle => exact (safe cycle).elim
    | unresolved => rfl
    | noCandidate _ _ clear _ => exact (clear blocked).elim
    | ambiguous _ _ clear _ _ _ => exact (clear blocked).elim
    | selected _ _ _ _ _ impossible => exact impossible.elim
  | noCandidate ready safe clear empty =>
    cases b with
    | unsupported delayed _ => exact False.elim ((ready_iff_not_delayed _ _).mp ready delayed)
    | recursive => rfl
    | unresolved _ _ blocked => exact (clear blocked).elim
    | noCandidate => rfl
    | ambiguous _ _ _ visible _ _ => exact (empty _ visible).elim
    | selected _ _ _ _ _ impossible => exact impossible.elim
  | ambiguous ready safe clear visible _ _ =>
    cases b with
    | unsupported delayed _ => exact False.elim ((ready_iff_not_delayed _ _).mp ready delayed)
    | recursive _ cycle => exact (safe cycle).elim
    | unresolved _ _ blocked => exact (clear blocked).elim
    | noCandidate _ _ _ empty => exact (empty _ visible).elim
    | ambiguous => rfl
    | selected _ _ _ _ _ impossible => exact impossible.elim
  | selected _ _ _ _ _ impossible => exact impossible.elim

private theorem no_k2_choice {s : State} {p : Supported s done}
    (pick : Elected s r i p tests d impl)
    (bad : GeneralDeclarativeUnfinishedRoot330.UnfinishedRoot p d) : False :=
  pick.guarded (.inl (blocked_and_cyclic bad).2)

private theorem no_k2_prior {s : State} {p : Supported s done}
    (bad : GeneralDeclarativeUnfinishedRoot330.UnfinishedRoot p d)
    (old : Local s r i p tests (fun _ _ _ => False) d outcome) : False := by
  have h := blocked_and_cyclic bad
  exact overlap_outside_fragment h.1 (.inl h.2) old

private theorem same_decl {s : State} {p : Supported s done} (checked : Checked r)
    (a : Elected s r i p tests d impl) (b : Elected s r i p tests d second) :
    impl = second :=
  GeneralDeclarativeWitnessStopped334.same_key_of_visible checked _ _
    a.viable.1.1 b.viable.1.1 (a.unique _ b.viable).symm

/-- No successful witnessed node competes with pending/rejected/
ambiguous at the same supported state. This proves equality only
of the classification tag and selected declaration id. Different
valid logical placements are not assumed to have identical lists. -/
theorem verdict_functional {s : State} {p : Supported s done} (checked : Checked r)
    (first : Rule p r i waiting d a) (second : Rule p r i waiting d b) :
    verdict a = verdict b := by
  cases first with
  | selected w =>
    cases second with
    | selected v => cases chosen_declaration checked w v; rfl
    | existing old => exact (prior_no_choice w.chosen old).elim
    | rootK2 bad => exact (no_k2_choice w.chosen bad).elim
    | unread pick missing =>
      cases same_decl checked w.chosen pick
      exact (missing (current_heads w.slice w.source)).elim
  | existing old =>
    cases second with
    | selected w => exact (prior_no_choice w.chosen old).elim
    | existing prior => rw [prior_functional old prior]
    | rootK2 bad => exact (no_k2_prior bad old).elim
    | unread pick _ => exact (prior_no_choice pick old).elim
  | rootK2 bad =>
    cases second with
    | selected w => exact (no_k2_choice w.chosen bad).elim
    | existing old => exact (no_k2_prior bad old).elim
    | rootK2 => rfl
    | unread pick _ => exact (no_k2_choice pick bad).elim
  | unread pick missing =>
    cases second with
    | selected w =>
      cases same_decl checked w.chosen pick
      exact (missing (current_heads w.slice w.source)).elim
    | existing old => exact (prior_no_choice pick old).elim
    | rootK2 bad => exact (no_k2_choice pick bad).elim
    | unread => rfl

theorem only_lists_can_differ {s : State} {p : Supported s done} (checked : Checked r)
    (first : Rule p r i waiting d a) (second : Rule p r i waiting d b) (different : a ≠ b) :
    ∃ key one two, a = .selected key one ∧ b = .selected key two ∧ one ≠ two := by
  have same := verdict_functional checked first second
  cases a <;> cases b <;> try cases same <;> try exact (different rfl).elim
  rename_i key one two
  exact ⟨key,one,two,rfl,rfl,fun h => different (congrArg (Frontier.selected key) h)⟩

end Yulang.GeneralDeclarativeWitnessVerdict334
