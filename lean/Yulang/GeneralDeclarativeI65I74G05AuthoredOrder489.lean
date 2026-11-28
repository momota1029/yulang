import Yulang.GeneralDeclarativeI65I74G05ExactPreflightHits489

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)

theorem exact_g05_signed_roster_ordinals_strictly_follow_original_registration489
    {p : FullProblem} {recurs : Nat → Prop} {bits : List (Nat × Bool)}
    (exactRoster : G05ExactSignedRoster489 p recurs bits) :
    List.Pairwise (fun a b => a.1 < b.1) bits := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj order
  let s : Fin (visible485 p).length := ⟨i,exactRoster.1 ▸ hi⟩
  let t : Fin (visible485 p).length := ⟨j,exactRoster.1 ▸ hj⟩
  obtain ⟨a,d,x,sourceA,atA,_⟩ := exactRoster.2 s
  obtain ⟨b,e,y,sourceB,atB,_⟩ := exactRoster.2 t
  have aPair : bits[i] = (a,x) := Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans atA)
  have bPair : bits[j] = (b,y) := Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans atB)
  change bits[i].1 < bits[j].1
  rw [aPair,bPair]
  exact unfilter_keeps_original_order405 (role485 p) (declared485 p) order sourceA.2.1 sourceB.2.1

theorem successful_g05_k2_hits_are_strictly_ordered_without_duplicates489
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {coords : List (Fin n)}
    {permit : Nat → CandidateVisitKey485 n → Bool} {hits : List Nat}
    (ran : readG05Preflight489 p gd pos rel coords permit = some (.recursive hits))
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key) :
    List.Pairwise (· < ·) hits := by
  obtain ⟨_,bits,ledger,gate⟩ := g05_preflight_has_the_actual_roots_and_independent_ordered_signs489 ran Allowed lawful
  have together := exact_g05_signed_roster_ordinals_strictly_follow_original_registration489 ledger
  rw [(signed_gate_recursive_iff_it_returns_the_nonempty_exact_positive_subsequence489.mp gate).1]
  exact (together.filter Prod.snd).map Prod.fst (fun _ _ earlier => earlier)

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
