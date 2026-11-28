import Yulang.GeneralDeclarativeI65I74PreElectionTape485

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open GeneralDeclarations (Declaration)

/-- The second component is an independent election result. The first
component contains all positive authored ordinals, not a guessed winner.
An incomplete tape is not an all-negative tape. -/
def routeAfterVerifiedTape485 (p : FullProblem) (check : CandidateCheck Wire)
    (packets : List (Nat × Wire)) (elect : List Nat → Option Result) :
    Option (Sum (List Nat) Result) :=
  match beforeElection485 p check packets with
  | none => none
  | some (.recursive hits) => some (.inl hits)
  | some (.allSafe ords) => (elect ords).map Sum.inr

theorem true_in_a_complete_tape_preempts_every_possible_election485
    (p : FullProblem) (check : CandidateCheck Wire) (packets : List (Nat × Wire))
    (elect : List Nat → Option Result) {bits : List (Nat × Bool)} {ord : Nat}
    (complete : readTape485 p check packets = some bits) (hit : (ord,true) ∈ bits) :
    routeAfterVerifiedTape485 p check packets elect = some (.inl (positiveOrdinals485 bits)) ∧
    ord ∈ positiveOrdinals485 bits := by
  obtain ⟨blocked,saved⟩ := every_real_positive_is_kept_before_any_election485 bits ord hit
  exact ⟨by simp [routeAfterVerifiedTape485,beforeElection485,complete,blocked],saved⟩

theorem selection_can_only_follow_a_complete_independently_all_safe_tape485
    (p : FullProblem) (check : CandidateCheck Wire) (meaning : CandidateLocal Wire)
    (localExact : ∀ ord d wire bit, check ord d wire = some bit ↔ meaning ord d wire bit)
    (packets : List (Nat × Wire)) (elect : List Nat → Option Result) (chosen : Result) :
    routeAfterVerifiedTape485 p check packets elect = some (.inr chosen) ↔
      ∃ bits, ExactTape485 p meaning (List.range (visible485 p).length) packets bits ∧
        (∀ i, (i,true) ∉ bits) ∧ elect (bits.map Prod.fst) = some chosen := by
  constructor
  · intro ran
    cases scan : beforeElection485 p check packets with
    | none => simp [routeAfterVerifiedTape485,scan] at ran
    | some reading =>
      cases reading with
      | recursive hits => simp [routeAfterVerifiedTape485,scan] at ran
      | allSafe ords =>
        obtain ⟨bits,independent,gate⟩ :=
          (ordered_pre_election_gate_is_exact_on_the_whole_independent_tape485
            p check meaning localExact packets (.allSafe ords)).mp scan
        obtain ⟨rfl,always⟩ := (safe_before_election_means_every_exact_slot_has_negative_result485 _ _).mp gate
        refine ⟨bits,independent,always,?_⟩
        cases election : elect (bits.map Prod.fst) with
        | none => simp [routeAfterVerifiedTape485,scan,election] at ran
        | some result => simpa [routeAfterVerifiedTape485,scan,election] using ran
  · rintro ⟨bits,independent,safe,result⟩
    have localGate :=
      (safe_before_election_means_every_exact_slot_has_negative_result485 bits _).mpr ⟨rfl,safe⟩
    have scan := (ordered_pre_election_gate_is_exact_on_the_whole_independent_tape485 p check meaning
      localExact packets _).mpr ⟨bits,independent,localGate⟩
    simp [routeAfterVerifiedTape485,scan,result]

theorem an_unverified_tape_never_reaches_the_election_callback485
    (p : FullProblem) (check : CandidateCheck Wire) (packets : List (Nat × Wire))
    (elect : List Nat → Option Result) (noneYet : readTape485 p check packets = none) :
    routeAfterVerifiedTape485 p check packets elect = none := by
  simp [routeAfterVerifiedTape485,beforeElection485,noneYet]

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
