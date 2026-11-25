import Yulang.GeneralDeclarativeI65I74MixedRecordOrder413

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MixedRecord413
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open CommonRoleOutermostResolver (Summarizes)
open Checker408 (Problem Result)
open RecordK2412 (query412)
open GeneralDeclarativeInspect321 (Visit)
open GeneralDeclarativeGraphRows321 (structural)

abbrev Rival413 (shape : MixedRecordRejection s q) (i : Nat) (r : Declaration) : Prop :=
  (visible s.core q)[i]? = some r ∧ i ≠ shape.tape.opening.ordinal ∧
    Nonempty (SourceHead s.core q r)

theorem actual_rival_cannot_be_missing413 {s q} (shape : MixedRecordRejection s q) :
    ∃ i d, Rival413 shape i d := by
  let rows := visible s.core q
  let index := if shape.tape.opening.ordinal = 0 then 1 else 0
  have within : index < rows.length := by
    have atLeast := shape.rivalsExist
    change 2 ≤ rows.length at atLeast
    unfold index
    split <;> omega
  have apart : index ≠ shape.tape.opening.ordinal := by
    unfold index
    split <;> omega
  let d := rows[index]
  have seen : rows[index]? = some d := List.getElem?_eq_getElem within
  exact ⟨index,d,seen,apart,matched_rival_is_real413 shape index seen apart⟩

/-- If there are at least three visible rows, two distinct, genuine
binding-only heads already match even before considering the rigid
row. Its actual K2 still vetoes a dictionary or ambiguity result. -/
theorem two_distinct_actual_matches_when_three413 {s q} (shape : MixedRecordRejection s q)
    (atLeast : 3 ≤ (visible s.core q).length) :
    ∃ i j d e, Rival413 shape i d ∧ Rival413 shape j e ∧ d.id ≠ e.id := by
  let rows := visible s.core q
  let pivot := shape.tape.opening.ordinal
  let i := if pivot = 0 then 1 else 0
  let j := if pivot = 2 then 1 else 2
  change 3 ≤ rows.length at atLeast
  have hi : i < rows.length := by unfold i; split <;> omega
  have hj : j < rows.length := by unfold j; split <;> omega
  have apartI : i ≠ pivot := by unfold i; split <;> omega
  have apartJ : j ≠ pivot := by unfold j; split <;> omega
  have notEqual : i ≠ j := by unfold i j; split <;> split <;> omega
  let d := rows[i]
  let e := rows[j]
  have atI : rows[i]? = some d := List.getElem?_eq_getElem hi
  have atJ : rows[j]? = some e := List.getElem?_eq_getElem hj
  have left : (rows.map Declaration.id)[i]? = some d.id := by rw [List.getElem?_map,atI]; rfl
  have right : (rows.map Declaration.id)[j]? = some e.id := by rw [List.getElem?_map,atJ]; rfl
  have bound : i < (rows.map Declaration.id).length := by simpa using hi
  refine ⟨i,j,d,e,⟨atI,apartI,matched_rival_is_real413 shape i atI apartI⟩,
    ⟨atJ,apartJ,matched_rival_is_real413 shape j atJ apartJ⟩,?_⟩
  intro same
  apply notEqual
  exact (List.Nodup.getElem?_inj bound shape.distinctIds).mp (left.trans (same ▸ right.symm))

structure MixedLocation where
  occurrence : List Nat
  orderedCandidateIds : List Nat
  inspectedOrdinal : Nat
  inspectedId : Nat
  fieldLabel : Nat
  root : Nat
  site : Nat
  deriving DecidableEq, Repr

def MixedVerified.location {p : Problem} (pack : MixedVerified p) : MixedLocation :=
  ⟨p.root.occurrence,(visible p.state.core p.root).map Declaration.id,
    pack.rejection.tape.opening.ordinal,pack.rejection.tape.opening.decl.id,
    pack.rejection.outer.box,pack.rejection.outer.root,pack.rejection.outer.site⟩

def locate (p : Problem) (r : Result) (w : MixedWire) : Option MixedLocation :=
  if Check408.matchesNoWrites r .rejected .rejected then
    (replayMixed413 p w).map MixedVerified.location
  else none

theorem same_exact_report_controls_location413 (p : Problem) (r : Result) (w : MixedWire) :
    (locate p r w).isSome = check p r (.mixedHead w) := by
  cases b : Check408.matchesNoWrites r .rejected .rejected <;> simp [locate,check,b]

theorem checked_location_is_original_candidate_and_visit413 (p : Problem) (r : Result) (w : MixedWire)
    {location : MixedLocation} (got : locate p r w = some location) :
    ∃ packet : MixedVerified p, packet.location = location ∧
      (visible p.state.core p.root)[location.inspectedOrdinal]? = some packet.rejection.tape.opening.decl ∧
      location.orderedCandidateIds = (visible p.state.core p.root).map Declaration.id ∧
      Visit (structural p.state.core.current.ordinary) location.root
        (query412 location.fieldLabel packet.rejection.tape.opening.source.nextField
          packet.rejection.tape.opening.source.binder) location.site ∧
      ¬RootCycle p.state p.root ∧ r = Check408.rawReport := by
  have yes : check p r (.mixedHead w) = true := by
    rw [← same_exact_report_controls_location413,got]
    rfl
  obtain ⟨packet,replayed,same⟩ := checked_mixed_head_reflects_original413 p r w yes
  have exact : Check408.matchesNoWrites r .rejected .rejected = true := by
    rw [same]
    decide +kernel
  have indexed : packet.location = location := by simpa [locate,exact,replayed] using got
  subst location
  exact ⟨packet,rfl,packet.rejection.tape.opening.fromOriginalList,rfl,
    actual_nested_candidate_enters413 packet.rejection.tape.opening.source,packet.rootSafe,same⟩

/-- Keep the same whole visible tape, root, entered field and trace
before quantifying over models. All real other head matches remain
in the original sequence. -/
theorem same_tape_and_trace_before_models413 (p : Problem) (r : Result) (w : MixedWire)
    (accepted : check p r (.mixedHead w) = true) :
    ∃ (packet : MixedVerified p) (trace : SourceTrace R5 p.state p.root r.tree none),
      replayMixed413 p w = some packet ∧
      (∀ i row, (visible p.state.core p.root)[i]? = some row →
        i ≠ packet.rejection.tape.opening.ordinal → Nonempty (SourceHead p.state.core p.root row)) ∧
      Summarizes r.tree r.verdict ∧ r.writes = writes trace ∧
      ∀ m, Fits p.state m → TraceMeaning p.state m trace := by
  obtain ⟨packet,replay,same⟩ := checked_mixed_head_reflects_original413 p r w accepted
  subst r
  let original : SourceTrace R5 p.state p.root .rejected none :=
    .other .rejected packet.rootSafe (.inr ⟨rfl,rfl,⟨packet.rejection⟩⟩) .nil
  exact ⟨packet,original,replay,fun i _ atRow other => matched_rival_is_real413 packet.rejection i atRow other,
    .rejected,rfl,fun m fit => mixed_R5_trace_model_meaning413 original m fit⟩

end Yulang.GeneralDeclarativeI65.I72.MixedRecord413
