import Yulang.GeneralDeclarativeI65I74X6AmbiguousEntry417

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open PlainMerged416 (PlainRows)
open Checker408 (Problem Result)

theorem readCandidate_keeps_authored_ordinal417 {s q j c}
    (found : readCandidate417 s q j = some c) : c.ordinal = j := by
  dsimp only [readCandidate417] at found
  repeat' (first | split at found | contradiction)
  all_goals (cases Option.some.inj found <;> rfl)

theorem readPlainHit_keeps_authored_ordinal417 {s q} {rows : PlainRows s q} {j h}
    (found : readPlainHit417 rows j = some h) : h.candidate.ordinal = j := by
  cases candidateAt : readCandidate417 s q j with
  | none => simp [readPlainHit417,candidateAt] at found
  | some c =>
    simp only [readPlainHit417,candidateAt,Option.bind_eq_bind,Option.bind_some] at found
    repeat' (first | split at found | contradiction)
    all_goals
      cases Option.some.inj found
      exact readCandidate_keeps_authored_ordinal417 candidateAt

theorem readGroundHit_preserves_candidate_ordinal_and_origin417 {s q} {rows : PlainRows s q} {source : IntegerOrigin rows} {j h}
    (found : readGroundHit417 rows source j = some h) :
    h.candidate.ordinal = j ∧ h.source = source := by
  cases candidateAt : readCandidate417 s q j with
  | none => simp [readGroundHit417,candidateAt] at found
  | some c =>
    simp only [readGroundHit417,candidateAt,Option.bind_eq_bind,Option.bind_some] at found
    repeat' (first | split at found | contradiction)
    all_goals
      cases Option.some.inj found
      exact ⟨readCandidate_keeps_authored_ordinal417 candidateAt,rfl⟩

theorem readIntegerOrigin_keeps_its_original_index417 {s q} {rows : PlainRows s q} {j source}
    (found : readIntegerOrigin417 rows j = some source) :
    s.core.origins[j]? = some source.original := by
  dsimp only [readIntegerOrigin417] at found
  split at found
  · contradiction
  · rename_i a indexed
    repeat' (first | split at found | contradiction)
    all_goals
      cases Option.some.inj found
      exact indexed

theorem both_wire_ordinals_and_int_origin_are_exact417 {p : Problem} {w a}
    (found : replayAmbiguity417 p w = some a) :
    a.plain.candidate.ordinal = w.plainOrdinal ∧ a.ground.candidate.ordinal = w.groundOrdinal ∧
    p.state.core.origins[w.payloadOrigin]? = some a.ground.source.original := by
  let curr := PlainMerged416.readRows416 p
    ⟨w.origin,w.variantRow,w.intRow,w.joinRow,w.plainOrdinal,w.rootEscape⟩
  cases read : curr with
  | none =>
    have eqRead : PlainMerged416.readRows416 p
        ⟨w.origin,w.variantRow,w.intRow,w.joinRow,w.plainOrdinal,w.rootEscape⟩ = none := read
    simp [replayAmbiguity417,eqRead] at found
  | some rows =>
    have eqRead : PlainMerged416.readRows416 p
        ⟨w.origin,w.variantRow,w.intRow,w.joinRow,w.plainOrdinal,w.rootEscape⟩ = some rows := read
    cases typed : readIntegerOrigin417 rows w.payloadOrigin with
    | none => simp [replayAmbiguity417,eqRead,typed] at found
    | some src =>
      cases actualPlain : readPlainHit417 rows w.plainOrdinal with
      | none => simp [replayAmbiguity417,eqRead,typed,actualPlain] at found
      | some plain =>
        cases actualGround : readGroundHit417 rows src w.groundOrdinal with
        | none => simp [replayAmbiguity417,eqRead,typed,actualPlain,actualGround] at found
        | some ground =>
          simp only [replayAmbiguity417,eqRead,typed,actualPlain,actualGround,Option.bind_eq_bind,Option.bind_some] at found
          repeat' (first | split at found | contradiction)
          all_goals
            cases Option.some.inj found
            have keep := readGroundHit_preserves_candidate_ordinal_and_origin417 actualGround
            exact ⟨readPlainHit_keeps_authored_ordinal417 actualPlain,keep.1,
              keep.2.symm ▸ readIntegerOrigin_keeps_its_original_index417 typed⟩

theorem result_includes_actual_replayed_ordinals417 {p : Problem} {r : Result}
    {w : AmbiguityWire} (yes : check p r (.x6Ambiguity w) = true) :
    ∃ a, replayAmbiguity417 p w = some a ∧ r = report417 ∧
      (authoredRegistry p.state.core.current).declarations[w.plainOrdinal]? = some a.plain.candidate.decl ∧
      (authoredRegistry p.state.core.current).declarations[w.groundOrdinal]? = some a.ground.candidate.decl := by
  obtain ⟨a,found,report⟩ := checked_x6_reflects_exact_candidates_and_report417 p r w yes
  have addresses := both_wire_ordinals_and_int_origin_are_exact417 found
  exact ⟨a,found,report,addresses.1 ▸ a.plain.candidate.authored,
    addresses.2.1 ▸ a.ground.candidate.authored⟩

theorem checked_ground_uses_exact_original_integer_input417 {p : Problem} {report : Result} {w}
    (yes : check p report (.x6Ambiguity w) = true) :
    ∃ a, replayAmbiguity417 p w = some a ∧
      p.state.core.origins[w.payloadOrigin]? = some a.ground.source.original ∧
      a.ground.source.original.slot = a.rows.payload ∧
      a.ground.source.original.endpoint = integerOriginSyntax := by
  obtain ⟨a,got,_⟩ := checked_x6_reflects_exact_candidates_and_report417 p report w yes
  exact ⟨a,got,(both_wire_ordinals_and_int_origin_are_exact417 got).2.2,
    a.ground.source.slot,a.ground.source.typed⟩

end Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
