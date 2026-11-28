import Yulang.GeneralDeclarativeI65I74IndependentScopedPriority487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint)

theorem independent_prefix_permissions_are_monotone_under_true_authority_extension487
    {n : Nat} {Left Right : CandidateVisitKey485 n → Prop}
    (step : ∀ key, Left key → Right key)
    {head : OriginalVisitPrefix487 n} {path points}
    (given : IndependentPrefixPermission487 Left head path points) :
    IndependentPrefixPermission487 Right head path points := by
  induction given with
  | empty atRoot => exact .empty atRoot
  | extend h _ ih => exact .extend (step _ h) ih

theorem widening_independent_original_authority_keeps_each_exact_recursive_local_candidate487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {roots : List (Fin n)}
    {Left Right : Nat → CandidateVisitKey485 n → Prop}
    (expand : ∀ ord key, Left ord key → Right ord key)
    {i : Nat}
    (hit : IndependentScopedReturn487 p gd pos rel roots Left i) :
    IndependentScopedReturn487 p gd pos rel roots Right i := by
  obtain ⟨ord,d,slot,root,arg,source,head,key,⟨v,trail,proper,allowed,word⟩,j,terminal,cyclic⟩ := hit
  exact ⟨ord,d,slot,root,arg,source,head,key,⟨v,trail,proper,
    independent_prefix_permissions_are_monotone_under_true_authority_extension487 (expand ord) allowed,word⟩,
    j,terminal,cyclic⟩

theorem an_independently_prefix_authorized_recursion_is_reported_at_its_exact_original_ordinal487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {roots : List (Checkpoint n)} {permit : Nat → CandidateVisitKey485 n → Bool}
    {out : PreElection485}
    (run : readScopedPreElection487 p gd pos rel palette roots permit = some out)
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key)
    (seat : Fin (visible485 p).length)
    (hit : IndependentScopedReturn487 p gd pos rel (roots.map Checkpoint.which) Allowed seat) :
    ∃ ord d hits, OriginalRosterCell485 p seat.val (ord,d) ∧ out = .recursive hits ∧ ord ∈ hits := by
  obtain ⟨bits,result,each⟩ := scoped_pre_election_bits_are_exactly_the_independent_prefix_authorized_old_returns487
    run Allowed lawful
  obtain ⟨ord,d,flag,original,atIndex,exact⟩ := each seat
  have h : flag = true := exact.mpr hit
  subst flag
  obtain ⟨got,found⟩ := every_real_positive_is_kept_before_any_election485 bits ord (List.mem_of_getElem? atIndex)
  exact ⟨ord,d,_,original,result.symm.trans got,found⟩

theorem no_successful_scoped_all_safe_can_hide_an_independent_prefix_authorized_return487
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    {roots : List (Checkpoint n)} {permit : Nat → CandidateVisitKey485 n → Bool}
    {ords : List Nat}
    (run : readScopedPreElection487 p gd pos rel palette roots permit = some (.allSafe ords))
    (Allowed : Nat → CandidateVisitKey485 n → Prop)
    (lawful : ∀ ord key, permit ord key = true ↔ Allowed ord key)
    (seat : Fin (visible485 p).length) :
    ¬ IndependentScopedReturn487 p gd pos rel (roots.map Checkpoint.which) Allowed seat := by
  intro hit
  obtain ⟨_,_,_,_,impossible,_⟩ :=
    an_independently_prefix_authorized_recursion_is_reported_at_its_exact_original_ordinal487
      run Allowed lawful seat hit
  cases impossible

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
