import Yulang.GeneralDeclarativeI65I74ScopedOriginalVisits487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open LiteralVisits473 (StepWire)
open Producer479 (Site readHop)
open ObservationAlternatives473 (Positions graphOf)
open CommonRoleRegularGraph (successors)

def finitePrefixCheckedHops487 {n : Nat} {s : GeneralDeclarativeI65.State}
    {pos : Positions n} (head : OriginalVisitPrefix487 n) (here : Site s pos)
    (allow : CandidateVisitKey485 n → Bool) : List (StepWire × Site s pos) :=
  (possibleOriginalSteps486 here.pattern).flatMap fun w =>
    (successors (graphOf s pos) here.index).filterMap fun idx =>
      if allow (head.withNext w idx).key then
        (readHop here w idx).map (fun next => (w,next))
      else none

private theorem filter_old_hops_moves_through_each_candidate_proposal487
    {α β : Type} (inputs : List α) (make : α → Option β) (before : α → Bool) (after : β → Bool)
    (exact : ∀ x y, make x = some y → before x = after y) :
    (inputs.filterMap make).filter after =
      inputs.filterMap (fun x => if before x then make x else none) := by
  induction inputs with
  | nil => rfl
  | cons x rest ih =>
    cases made : make x with
    | none =>
      cases yes : before x <;> simp [made,yes,ih]
    | some val =>
      have h := exact x val made
      cases yes : before x <;> simp [made,yes,← h,ih]

private theorem filter_commutes_with_ordered_flatmap487 {α β : Type} (f : α → List β)
    (ok : β → Bool) (l : List α) :
    (l.flatMap f).filter ok = l.flatMap fun a => (f a).filter ok := by
  induction l with
  | nil => rfl
  | cons a rest ih => simp [List.filter_append,ih]

theorem early_original_prefix_gate_and_late_hop_filter_return_identical_ordered_entries487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (head : OriginalVisitPrefix487 n) (here : Site s pos) (allow : CandidateVisitKey485 n → Bool) :
    finitePrefixCheckedHops487 head here allow =
      (finiteExistingHops486 here).filter (fun pair => allow (head.withNext pair.1 pair.2.index).key) := by
  unfold finitePrefixCheckedHops487 finiteExistingHops486
  rw [filter_commutes_with_ordered_flatmap487]
  congr 1
  funext w
  symm
  apply filter_old_hops_moves_through_each_candidate_proposal487
  intro idx pair exact
  cases sub : readHop here w idx with
  | none => simp [sub] at exact
  | some next =>
    have eq : (w,next) = pair := Option.some.inj (by simpa [sub] using exact)
    subst pair
    have point := (Producer479.reified_hop_keeps_the_same_old_place479 sub).1
    rw [point]

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
