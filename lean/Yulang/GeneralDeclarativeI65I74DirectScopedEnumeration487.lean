import Yulang.GeneralDeclarativeI65I74PermitBeforeOriginalHop487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open LiteralVisits473 (StepWire)
open Producer479 (Site)
open ObservationAlternatives473 (Positions)

def extendOriginalHop487 {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (pair : StepWire × Site s pos) (suffix : GeometricVisit486 s pos) : GeometricVisit486 s pos :=
  ⟨pair.1::suffix.moves,pair.2.index::suffix.points,suffix.last,suffix.bit⟩

/-- Compute the next candidate key before invoking the exact hop reader.
Global old quotient certificates are still checked as before. -/
def enumerateDirectScopedOldSuffixes487 {n : Nat} {s : GeneralDeclarativeI65.State}
    {pos : Positions n} (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n)
    (allow : CandidateVisitKey485 n → Bool) : Nat → OriginalVisitPrefix487 n → Site s pos →
      Option (List (GeometricVisit486 s pos))
  | 0,_,here => (oldObservedSign486 s pos rel palette here.index).map fun b => [⟨[],[],here,b⟩]
  | fuel+1,head,here =>
    match oldObservedSign486 s pos rel palette here.index with
    | none => none
    | some true => some [⟨[],[],here,true⟩]
    | some false => do
      let levels ← (finitePrefixCheckedHops487 head here allow).mapM fun pair =>
        (enumerateDirectScopedOldSuffixes487 rel palette allow fuel (head.withNext pair.1 pair.2.index)
          pair.2).map (List.map (extendOriginalHop487 pair))
      pure (⟨[],[],here,false⟩ :: levels.flatten)

private theorem early_list_filter_and_empty_denied_branches_have_same_option_flatten487
    {α β : Type} (xs : List α) (allow : α → Bool) (f : α → Option (List β)) :
    (((xs.filter allow).mapM f : Option (List (List β))).map List.flatten) =
      ((xs.mapM (fun a => if allow a then f a else some []) : Option (List (List β))).map List.flatten) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    cases r : (((rest.filter allow).mapM f : Option (List (List β)))) with
    | none =>
      have right : (rest.mapM (fun a => if allow a then f a else some []) : Option (List (List β))) = none := by
        cases got : (rest.mapM (fun a => if allow a then f a else some []) : Option (List (List β))) with
        | none => rfl
        | some blocks => simp [r,got] at ih
      cases h : allow a <;> cases f a <;> simp [r,right,h,List.mapM_cons,Option.bind]
    | some leftPackets =>
      cases right : (rest.mapM (fun a => if allow a then f a else some []) : Option (List (List β))) with
      | none => simp [r,right] at ih
      | some rightPackets =>
        have same : leftPackets.flatten = rightPackets.flatten := by simpa [r,right] using ih
        cases h : allow a <;> cases fa : f a <;> simp [r,right,h,fa,List.mapM_cons,same,Option.bind]

private theorem prepend_flatten_map_matches_the_option_program487 {α : Type} (init : α)
    (packets : Option (List (List α))) :
    (do
      let levels ← packets
      pure (init :: levels.flatten)) = packets.map (fun rows => init :: rows.flatten) := by
  cases packets <;> rfl

theorem moving_prefix_checks_before_each_hop_preserves_the_exact_scoped_result487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (rel : List (Fin n × Fin n)) (palette : SignedPalette486 n)
    (allow : CandidateVisitKey485 n → Bool) (fuel : Nat)
    (head : OriginalVisitPrefix487 n) (here : Site s pos) :
    enumerateDirectScopedOldSuffixes487 rel palette allow fuel head here =
      enumeratePermittedOldSuffixes487 rel palette allow fuel head here := by
  induction fuel generalizing head here with
  | zero => rfl
  | succ k ih =>
    rw [enumerateDirectScopedOldSuffixes487,enumeratePermittedOldSuffixes487]
    cases sign : oldObservedSign486 s pos rel palette here.index with
    | none => rfl
    | some bit =>
      cases bit with
      | true => rfl
      | false =>
        let allowed := fun pair : StepWire × Site s pos => allow (head.withNext pair.1 pair.2.index).key
        let f := fun pair : StepWire × Site s pos =>
          (enumeratePermittedOldSuffixes487 rel palette allow k (head.withNext pair.1 pair.2.index)
            pair.2).map (List.map (extendOriginalHop487 pair))
        have next :
            (fun pair : StepWire × Site s pos =>
              (enumerateDirectScopedOldSuffixes487 rel palette allow k (head.withNext pair.1 pair.2.index)
                pair.2).map (List.map (extendOriginalHop487 pair))) = f := by
          funext pair
          rw [ih]
        rw [next,early_original_prefix_gate_and_late_hop_filter_return_identical_ordered_entries487]
        have left :=
          early_list_filter_and_empty_denied_branches_have_same_option_flatten487
            (finiteExistingHops486 here) allowed f
        have output := congrArg (Option.map (List.cons (⟨[],[],here,false⟩ : GeometricVisit486 s pos))) left
        simp only [Option.map_map,Function.comp_def] at output
        change (do
            let levels ← ((finiteExistingHops486 here).filter allowed).mapM (m := Option) f
            pure ((⟨[],[],here,false⟩ : GeometricVisit486 s pos) :: levels.flatten)) =
          (do
            let levels ← (finiteExistingHops486 here).mapM (m := Option)
              (fun pair => if allowed pair then f pair else some [])
            pure ((⟨[],[],here,false⟩ : GeometricVisit486 s pos) :: levels.flatten))
        rw [prepend_flatten_map_matches_the_option_program487,prepend_flatten_map_matches_the_option_program487]
        exact output

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
