import Yulang.GeneralDeclarativeI65I74G05TokenMap490

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)

/-- Adjacent receipt migrations are composed at the same original
candidate and with the same decoded verdict at both steps. -/
def composeG05TokenMaps490 (first second : G05TokenMap490) : G05TokenMap490 :=
  fun i ord decl bytes verdict => do
    let mid ← first i ord decl bytes verdict
    second i ord decl mid verdict

theorem lawful_g05_token_maps_compose_without_changing_original_verdicts490
    {left middle right : G05LocalChecker487} {first second : G05TokenMap490}
    (a : G05TokenMapPreservesDecoded490 left middle first)
    (b : G05TokenMapPreservesDecoded490 middle right second) :
    G05TokenMapPreservesDecoded490 left right (composeG05TokenMaps490 first second) := by
  intro i ord decl old verdict accepted
  obtain ⟨mid,mapA,replayA⟩ := a i ord decl old verdict accepted
  obtain ⟨fresh,mapB,replayB⟩ := b i ord decl mid verdict replayA
  exact ⟨fresh,by simp [composeG05TokenMaps490,mapA,mapB],replayB⟩

private theorem g05_token_composition_matches_two_lookup_steps490
    (p : FullProblem) {left middle : G05LocalChecker487} {first : G05TokenMap490}
    (second : G05TokenMap490) (known : G05TokenMapPreservesDecoded490 left middle first)
    (i : Nat) (token : Option (List Nat)) :
    translateG05LocalToken490 p left (composeG05TokenMaps490 first second) i token =
      (translateG05LocalToken490 p left first i token).bind (translateG05LocalToken490 p middle second i) := by
  cases token with
  | none => rfl
  | some bytes =>
    cases atSlot : rosterCell485 p i with
    | none => simp [translateG05LocalToken490,atSlot]
    | some cell =>
      obtain ⟨ord,decl⟩ := cell
      cases read : left i ord decl bytes with
      | none => simp [translateG05LocalToken490,atSlot,read]
      | some verdict =>
        obtain ⟨mid,mapped,accepted⟩ := known i ord decl bytes verdict read
        simp [translateG05LocalToken490,atSlot,read,composeG05TokenMaps490,mapped,accepted]

theorem one_composed_g05_receipt_map_is_identical_to_two_sequential_token_list_migrations490
    (p : FullProblem) {left middle : G05LocalChecker487} {first : G05TokenMap490}
    (second : G05TokenMap490) (known : G05TokenMapPreservesDecoded490 left middle first)
    (offset : Nat) (tokens : List (Option (List Nat))) :
    translateG05LocalTokenList490 p left (composeG05TokenMaps490 first second) offset tokens =
      (translateG05LocalTokenList490 p left first offset tokens).bind
        (translateG05LocalTokenList490 p middle second offset) := by
  induction tokens generalizing offset with
  | nil => rfl
  | cons token more ih =>
    simp only [translateG05LocalTokenList490]
    rw [g05_token_composition_matches_two_lookup_steps490 p second known offset token,ih (offset+1)]
    cases head : translateG05LocalToken490 p left first offset token with
    | none => rfl
    | some firstHead =>
      cases tail : translateG05LocalTokenList490 p left first (offset+1) more with
      | none =>
        cases secondHead : translateG05LocalToken490 p middle second offset firstHead <;> simp [secondHead]
      | some firstTail =>
        cases secondHead : translateG05LocalToken490 p middle second offset firstHead <;>
          simp [translateG05LocalTokenList490,secondHead,Option.bind]

theorem one_composed_g05_witness_migration_has_exactly_the_same_wire_as_two_sequential_migrations490
    {n : Nat} (p : FullProblem) {left middle : G05LocalChecker487} {first : G05TokenMap490}
    (second : G05TokenMap490) (known : G05TokenMapPreservesDecoded490 left middle first)
    (wire : G05FiniteWitness487 n) :
    translateG05WitnessTokens490 p left (composeG05TokenMaps490 first second) wire =
      (translateG05WitnessTokens490 p left first wire).bind (translateG05WitnessTokens490 p middle second) := by
  unfold translateG05WitnessTokens490
  rw [one_composed_g05_receipt_map_is_identical_to_two_sequential_token_list_migrations490 p second known]
  cases ran : translateG05LocalTokenList490 p left first 0 wire.localTokens with
  | none => simp
  | some mapped =>
    cases wire
    rfl

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
