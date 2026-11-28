import Yulang.GeneralDeclarativeI65I74G05OrderedMarks487

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open GeneralDeclarations (Declaration)

/-- A translation need only preserve an actually decoded verdict, at
the exact original visible index, ordinal and declaration. -/
def G05LocalCodecCovers490 (left right : G05LocalChecker487) : Prop :=
  ∀ i ord d data v, left i ord d data = some v → ∃ fresh, right i ord d fresh = some v

theorem two_exact_local_protocols_cover_all_decoded_g05_verdicts490
    {a b : G05LocalChecker487} {meaning : G05LocalMeaning487}
    (left : G05ExactLocalProtocol487 a meaning) (right : G05ExactLocalProtocol487 b meaning) :
    G05LocalCodecCovers490 a b :=
  fun i ord d data v ran => right.2 i ord d v (left.1 i ord d data v ran)

abbrev G05TokenMap490 :=
  Nat → Nat → Declaration → List Nat → G05LocalVerdict487 → Option (List Nat)

/-- Caller-supplied token translation. This is not a local-rule implementation:
it must target the same checked original slot and the already decoded verdict. -/
def G05TokenMapPreservesDecoded490 (left right : G05LocalChecker487) (translate : G05TokenMap490) : Prop :=
  ∀ i ord d data verdict, left i ord d data = some verdict →
    ∃ fresh, translate i ord d data verdict = some fresh ∧ right i ord d fresh = some verdict

noncomputable def chooseG05CodecTokenMap490 (left right : G05LocalChecker487)
    (covers : G05LocalCodecCovers490 left right) : G05TokenMap490 :=
  fun i ord d data verdict =>
    if replay : left i ord d data = some verdict
    then some (Classical.choose (covers i ord d data verdict replay))
    else none

theorem chosen_g05_token_map_is_lawful_when_the_target_codec_covers_the_source490
    {left right : G05LocalChecker487} (covers : G05LocalCodecCovers490 left right) :
    G05TokenMapPreservesDecoded490 left right (chooseG05CodecTokenMap490 left right covers) := by
  intro i ord d data verdict replay
  exact ⟨Classical.choose (covers i ord d data verdict replay),
    by simp [chooseG05CodecTokenMap490,replay],
    Classical.choose_spec (covers i ord d data verdict replay)⟩

def translateG05LocalToken490 (p : FullProblem) (left : G05LocalChecker487)
    (translate : G05TokenMap490) (i : Nat) : Option (List Nat) → Option (Option (List Nat))
  | none => some none
  | some data => do
    let (ord,d) ← rosterCell485 p i
    let verdict ← left i ord d data
    let fresh ← translate i ord d data verdict
    pure (some fresh)

def translateG05LocalTokenList490 (p : FullProblem) (left : G05LocalChecker487) (translate : G05TokenMap490) :
    Nat → List (Option (List Nat)) → Option (List (Option (List Nat)))
  | _,[] => some []
  | pos,token::more => do
    let localToken ← translateG05LocalToken490 p left translate pos token
    let tail ← translateG05LocalTokenList490 p left translate (pos+1) more
    pure (localToken::tail)

def translateG05WitnessTokens490 {n : Nat} (p : FullProblem) (left : G05LocalChecker487)
    (translate : G05TokenMap490) (wire : G05FiniteWitness487 n) : Option (G05FiniteWitness487 n) :=
  (translateG05LocalTokenList490 p left translate 0 wire.localTokens).map
    fun fresh => {wire with localTokens := fresh}

private theorem translate_g05_row_preserves_accepted_structure490
    {n : Nat} {p : FullProblem} {left right : G05LocalChecker487} {translate : G05TokenMap490} {i : Nat}
    {candidate : ComputedOriginalCandidate486 n} {signed : Nat × Bool}
    {token : Option (List Nat)} {row : G05CandidateRow487 n}
    (lawful : G05TokenMapPreservesDecoded490 left right translate)
    (accepted : readG05OneRow487 p left i candidate signed token = some row) :
    ∃ fresh, translateG05LocalToken490 p left translate i token = some fresh ∧
      readG05OneRow487 p right i candidate signed fresh = some row := by
  obtain ⟨d,origin,a,b,obs,atIndex,mark⟩ :=
    new_g05_row_preserves_original_slot_signed_bit_observed_keys_and_actual_local_mark487 accepted
  have roster := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr origin
  have localReplay : ∃ fresh, translateG05LocalToken490 p left translate i token = some fresh ∧
      readG05LocalMark487 right i row.ordinal d signed.2 fresh = some row.mark := by
    cases flag : row.mark with
    | requiredCycle =>
      rw [flag] at mark
      obtain ⟨positive,empty⟩ := a_local_k2_mark_is_exactly_a_checked_true_bit_and_no_local_selection_token487.mp mark
      exact ⟨none,by rw [empty]; rfl,
        a_local_k2_mark_is_exactly_a_checked_true_bit_and_no_local_selection_token487.mpr ⟨positive,rfl⟩⟩
    | nonrecursive verdict =>
      rw [flag] at mark
      obtain ⟨negative,data,atData,checked⟩ :=
        a_local_nonrecursive_mark_requires_a_real_local_receipt_not_failed_read487.mp mark
      obtain ⟨fresh,encoded,rechecked⟩ := lawful i row.ordinal d data verdict checked
      exact ⟨some fresh,by simp [translateG05LocalToken490,atData,roster,checked,encoded],
        a_local_nonrecursive_mark_requires_a_real_local_receipt_not_failed_read487.mpr
          ⟨negative,fresh,rfl,rechecked⟩⟩
  obtain ⟨fresh,translated,verified⟩ := localReplay
  refine ⟨fresh,translated,?_⟩
  unfold readG05OneRow487
  simp only [roster,bind,Option.bind]
  have exactHead :
      (decide (row.ordinal = signed.1) && decide (row.ordinal = candidate.authoredOrdinal) &&
        decide (i = candidate.packet.visibleOrdinal)) = true := by
    simp only [decide_eq_true a,decide_eq_true b,decide_eq_true atIndex,Bool.and_self]
  rw [ite_eq_left exactHead,verified]
  exact congrArg some (by cases row; simp_all)

theorem a_checked_g05_ordered_assembly_is_preserved_by_a_lawful_computable_token_map490
    {n : Nat} {p : FullProblem} {left right : G05LocalChecker487} {translate : G05TokenMap490}
    {offset : Nat} {candidates : List (ComputedOriginalCandidate486 n)}
    {signed : List (Nat × Bool)} {tokens : List (Option (List Nat))}
    {rows : List (G05CandidateRow487 n)}
    (lawful : G05TokenMapPreservesDecoded490 left right translate)
    (accepted : readG05OrderedRows487 p left offset candidates signed tokens = some rows) :
    ∃ fresh, translateG05LocalTokenList490 p left translate offset tokens = some fresh ∧
      readG05OrderedRows487 p right offset candidates signed fresh = some rows := by
  induction candidates generalizing signed tokens rows offset with
  | nil =>
    cases signed <;> cases tokens <;> simp_all [readG05OrderedRows487]
    exact ⟨[],rfl,rfl⟩
  | cons candidate rest ih =>
    cases signed with
    | nil => simp [readG05OrderedRows487] at accepted
    | cons sign other =>
      cases tokens with
      | nil => simp [readG05OrderedRows487] at accepted
      | cons one more =>
        cases head : readG05OneRow487 p left offset candidate sign one with
        | none => simp [readG05OrderedRows487,head] at accepted
        | some first =>
          cases tail : readG05OrderedRows487 p left (offset+1) rest other more with
          | none => simp [readG05OrderedRows487,head,tail,Option.bind] at accepted
          | some restRows =>
            have eq : first::restRows = rows :=
              Option.some.inj (by simpa [readG05OrderedRows487,head,tail,Option.bind] using accepted)
            obtain ⟨newHead,converted,checkHead⟩ := translate_g05_row_preserves_accepted_structure490 lawful head
            obtain ⟨newTail,changed,checkTail⟩ := ih tail
            exact ⟨newHead::newTail,
              by simp [translateG05LocalTokenList490,converted,changed,Option.bind],
              by simp [readG05OrderedRows487,checkHead,checkTail,Option.bind,eq]⟩

theorem any_successful_g05_row_assembly_can_reencode_only_its_local_token_list490
    {n : Nat} {p : FullProblem} {left right : G05LocalChecker487} {offset : Nat}
    {candidates : List (ComputedOriginalCandidate486 n)}
    {signed : List (Nat × Bool)} {tokens : List (Option (List Nat))}
    {rows : List (G05CandidateRow487 n)}
    (covers : G05LocalCodecCovers490 left right)
    (accepted : readG05OrderedRows487 p left offset candidates signed tokens = some rows) :
    ∃ fresh, readG05OrderedRows487 p right offset candidates signed fresh = some rows := by
  obtain ⟨fresh,_,replayed⟩ :=
    a_checked_g05_ordered_assembly_is_preserved_by_a_lawful_computable_token_map490
      (chosen_g05_token_map_is_lawful_when_the_target_codec_covers_the_source490 covers) accepted
  exact ⟨fresh,replayed⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
