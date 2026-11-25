import Yulang.GeneralDeclarativeI65I74RecordFidelity412

namespace Yulang.GeneralDeclarativeI65.I72.RecordK2412
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeInspect321 (Visit)
open GeneralDeclarativeGraphRows321 (structural)
open Checker408 (Problem Result)

/-- Optional diagnostic detail. The fixed Result remains unchanged.
This path is within the original candidate argument, not a request
occurrence invented for the cyclic field. -/
structure FieldLocation where
  occurrence : List Nat
  declarationId : Nat
  argumentOrdinal : Nat
  fieldLabel : Nat
  root : Nat
  site : Nat
  deriving DecidableEq, Repr

def VerifiedField.location {p : Problem} (fields : VerifiedField p) : FieldLocation :=
  ⟨p.root.occurrence,fields.rejection.decl.id,0,
    fields.rejection.field.box,fields.rejection.field.input.lower,fields.rejection.field.site⟩

def locate (p : Problem) (r : Result) (w : FieldWire) : Option FieldLocation :=
  match scope : visible p.state.core p.root with
  | [d] =>
    if Check408.matchesNoWrites r .rejected .rejected then
      (replayField412 p d scope w).map VerifiedField.location
    else none
  | _ => none

/-- Diagnostic detail is available exactly for this checked branch,
without demanding or using another replay result or a model. -/
theorem location_exists_exactly_for_field_branch412 (p : Problem) (r : Result) (w : FieldWire) :
    (locate p r w).isSome = check p r (.fieldCycle w) := by
  simp only [locate,check]
  split
  · rename_i d left
    split
    · rename_i test
      split
      · rename_i e right
        have equal := (List.cons.inj (left.symm.trans right)).1
        cases equal
        simp [test]
      · rename_i impossible
        exact (impossible d left).elim
    · rename_i test
      split
      · simp [test]
      · rfl
  · rename_i impossible
    split
    · rename_i e right
      exact (impossible e right).elim
    · rfl

theorem located_record_diagnostic_keeps_actual_path412
    (p : Problem) (r : Result) (w : FieldWire) (whereAt : FieldLocation)
    (read : locate p r w = some whereAt) :
    ∃ (d : Declaration) (a : ActualRecordField p.state p.root d),
      whereAt.occurrence = p.root.occurrence ∧ whereAt.declarationId = d.id ∧
      whereAt.argumentOrdinal = 0 ∧ whereAt.fieldLabel = a.box ∧
      whereAt.root = a.input.lower ∧ whereAt.site = a.site ∧
      Visit (structural p.state.core.current.ordinary) whereAt.root
        (query412 a.box a.tick a.binder) whereAt.site ∧
      ¬RootCycle p.state p.root ∧ r = Check408.rawReport := by
  have checked : check p r (.fieldCycle w) = true := by
    rw [←location_exists_exactly_for_field_branch412,read]
    rfl
  obtain ⟨chosen,scope,packet,view,report⟩ :=
    checked_field_reflects_actual_original_rejection412 p r w checked
  have location : packet.location = whereAt := by
    unfold locate at read
    split at read
    · rename_i d q
      have same := (List.cons.inj (scope.symm.trans q)).1
      cases same
      have result : Check408.matchesNoWrites r .rejected .rejected = true := by
        rw [report]
        decide +kernel
      simp [result,view] at read
      exact read
    · contradiction
  subst whereAt
  exact ⟨packet.rejection.decl,packet.rejection.field,rfl,rfl,rfl,rfl,rfl,rfl,
    actual_record_field_is_entered412 packet.rejection.field,packet.rootSafe,report⟩

end Yulang.GeneralDeclarativeI65.I72.RecordK2412
