import Yulang.GeneralDeclarativeI65I74RigidRivalEntry418
import Yulang.GeneralDeclarativeI65I74X6AmbiguousLocator417

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RigidRival418
open GeneralDeclarativeI65
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open PlainMerged416 (PlainRows)
open Checker408 (Problem Result)
open X6Ambiguous417 (readPlainHit417 readIntegerOrigin417 readCandidate417
  readCandidate_keeps_authored_ordinal417 readPlainHit_keeps_authored_ordinal417
  readIntegerOrigin_keeps_its_original_index417 integerOriginSyntax)

theorem readStrRival_keeps_ordinal418 {s q} {rows : PlainRows s q} {j h}
    (found : readStrRival418 rows j = some h) :
    h.candidate.ordinal = j := by
  cases candidateAt : readCandidate417 s q j with
  | none => simp [readStrRival418,candidateAt] at found
  | some c =>
    simp only [readStrRival418,candidateAt,Option.bind_eq_bind,Option.bind_some] at found
    repeat' (first | split at found | contradiction)
    all_goals
      cases Option.some.inj found
      exact readCandidate_keeps_authored_ordinal417 candidateAt

theorem winner_wire_resolves_original_ordinals418 {p : Problem} {w a}
    (found : replayWinner418 p w = some a) :
    a.winner.candidate.ordinal = w.plainOrdinal ∧ a.mismatch.rival.candidate.ordinal = w.rivalOrdinal ∧
    p.state.core.origins[w.payloadOrigin]? = some a.mismatch.source.original := by
  let curr := PlainMerged416.readRows416 p
    ⟨w.origin,w.variantRow,w.intRow,w.joinRow,w.plainOrdinal,w.rootEscape⟩
  cases read : curr with
  | none =>
    have eqRead : PlainMerged416.readRows416 p
        ⟨w.origin,w.variantRow,w.intRow,w.joinRow,w.plainOrdinal,w.rootEscape⟩ = none := read
    simp [replayWinner418,eqRead] at found
  | some rows =>
    have eqRead : PlainMerged416.readRows416 p
        ⟨w.origin,w.variantRow,w.intRow,w.joinRow,w.plainOrdinal,w.rootEscape⟩ = some rows := read
    cases typed : readIntegerOrigin417 rows w.payloadOrigin with
    | none => simp [replayWinner418,eqRead,typed] at found
    | some src =>
      cases actualPlain : readPlainHit417 rows w.plainOrdinal with
      | none => simp [replayWinner418,eqRead,typed,actualPlain] at found
      | some plain =>
        cases actualGround : readStrRival418 rows w.rivalOrdinal with
        | none => simp [replayWinner418,eqRead,typed,actualPlain,actualGround] at found
        | some ground =>
          simp only [replayWinner418,eqRead,typed,actualPlain,actualGround,Option.bind_eq_bind,Option.bind_some] at found
          repeat' (first | split at found | contradiction)
          all_goals
            cases Option.some.inj found
            exact ⟨readPlainHit_keeps_authored_ordinal417 actualPlain,readStrRival_keeps_ordinal418 actualGround,
              readIntegerOrigin_keeps_its_original_index417 typed⟩

theorem check_uses_both_actual_declarations_and_original_rigid_input418
    {p : Problem} {r : Result} {w : RivalWire} (yes : check p r (.rigidRival w) = true) :
    ∃ a, replayWinner418 p w = some a ∧ r = Check408.nullaryReport a.winner.candidate.decl ∧
      (authoredRegistry p.state.core.current).declarations[w.plainOrdinal]? = some a.winner.candidate.decl ∧
      (authoredRegistry p.state.core.current).declarations[w.rivalOrdinal]? = some a.mismatch.rival.candidate.decl ∧
      p.state.core.origins[w.payloadOrigin]? = some a.mismatch.source.original ∧
      a.mismatch.source.original.slot = a.rows.payload ∧
      a.mismatch.source.original.endpoint = integerOriginSyntax := by
  obtain ⟨a,found,report⟩ := checked_plain_merge_reflects_original418 p r w yes
  have atSource := winner_wire_resolves_original_ordinals418 found
  exact ⟨a,found,report,atSource.1 ▸ a.winner.candidate.authored,
    atSource.2.1 ▸ a.mismatch.rival.candidate.authored,atSource.2.2,
    a.mismatch.source.slot,a.mismatch.source.typed⟩

end Yulang.GeneralDeclarativeI65.I72.RigidRival418
