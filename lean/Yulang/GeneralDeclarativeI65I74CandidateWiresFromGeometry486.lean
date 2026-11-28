import Yulang.GeneralDeclarativeI65I74BoundedCandidateGeometry486

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open ObservationAlternatives473 (Positions oldPosition)
open LiteralVisits473 (Checkpoint StepWire GuardedObservationInput readCheck)
open Producer479 (Site Trail TrailWire readTrail)

def paletteTail486 {n : Nat} (palette : SignedPalette486 n) :
    List StepWire → List (Fin n) → Option (List (StepWire × Checkpoint n))
  | [],[] => some []
  | a::as,i::is => do
      let hit ← palette i
      let rest ← paletteTail486 palette as is
      pure ((a,hit)::rest)
  | _,_ => none

def wireFromGeometry486 {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (palette : SignedPalette486 n) (first : Site s pos) (visit : GeometricVisit486 s pos) :
    Option (TrailWire n) := do
  let head ← palette first.index
  let tail ← paletteTail486 palette visit.moves visit.points
  pure ⟨head,tail⟩

private theorem finite_report_uses_existing_palette_for_its_original_point
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n} {i bit}
    (ran : oldObservedSign486 s pos rel palette i = some bit) :
    ∃ cp, palette i = some cp ∧ cp.which = i ∧
      readCheck s pos rel (oldPosition pos i) cp = some bit := by
  unfold oldObservedSign486 at ran
  cases hit : palette i with
  | none => simp [hit] at ran
  | some cp =>
    simp only [hit,bind,Option.bind] at ran
    split at ran
    · exact ⟨cp,rfl,by assumption,ran⟩
    · cases ran

theorem direct_geometry_wire_computes_and_checks_the_same_original_signed_trail486
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {palette : SignedPalette486 n}
    (complete : CompletePalette486 s pos rel palette)
    {first last : Site s pos} {moves points bit}
    (actual : Trail s pos rel first moves points last bit) :
    ∃ w, wireFromGeometry486 palette first ⟨moves,points,last,bit⟩ = some w ∧
      palette first.index = some w.cursor ∧
      paletteTail486 palette moves points = some w.tail ∧
      w.cursor.which = first.index ∧
      w.tail.map Prod.fst = moves ∧ w.tail.map (fun pair => pair.2.which) = points ∧
      readTrail rel first w = some (last,bit) := by
  induction actual with
  | @stop here sign guard meaning =>
    have run := complete_palette_checks_the_exact_independent_sign complete guard meaning
    obtain ⟨current,made,chosen,result⟩ := finite_report_uses_existing_palette_for_its_original_point run
    refine ⟨⟨current,[]⟩,?_,made,rfl,chosen,rfl,rfl,?_⟩
    · simp [wireFromGeometry486,paletteTail486,made,Option.bind]
    · simp [readTrail,Producer479.readTrailAux,chosen,result]
  | @step here next finish a moves points sign hop guard safe later ih =>
    obtain ⟨w,_,prior,rest,oldSite,oldMoves,oldPoints,checked⟩ := ih
    have run := complete_palette_checks_the_exact_independent_sign complete guard
      (bit := false) (by simp [safe])
    obtain ⟨current,made,chosen,result⟩ := finite_report_uses_existing_palette_for_its_original_point run
    let all := (a,w.cursor)::w.tail
    refine ⟨⟨current,all⟩,?_,made,?_,chosen,
      by simp [all,oldMoves],by simp [all,oldSite,oldPoints],?_⟩
    · simp [wireFromGeometry486,made,paletteTail486,prior,rest,all,Option.bind]
    · simp [paletteTail486,prior,rest,all,Option.bind]
    · rw [readTrail,Producer479.readTrailAux]
      simp only [chosen,ite_true,result,all,bind,Option.bind,oldSite,
        Producer479.exact_hop_has_a_unique_replay479 hop]
      exact checked

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
