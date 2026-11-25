import Yulang.GeneralDeclarativeI65I74ExplicitPickReport419

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
open GeneralDeclarativeI65
open Checker408 (Problem Result)
open GeneralDeclarativeWitnessTree349 (eqTree eq_tree eqResult eq_result)

def pickReport {p : Problem} (a : PickPacket p) : Result :=
  ⟨.selected a.declaration.decl.id [],.selected (.node a.declaration.decl.id []),[a.retained.write]⟩

theorem actual_event_has_only_its_original_output419 {p : Problem} (a : PickPacket p) :
    Check408.encodedEventWrites a.event = [a.retained.write] := by
  apply List.ext_getElem
  · simp [Check408.encodedEventWrites,a.single]
  · intro n hA hB
    have zero : n = 0 := by simpa using hB
    subst n
    simp [Check408.encodedEventWrites,PickPacket.event,RetainedOutput.write,exactlyOneOutput]

theorem pick_report_of_actual_source419 {p : Problem} (a : PickPacket p) :
    ClassifiedAs p.state p.root (pickReport a) := by
  let kidProof := actual_pick_never_switches_to_a_where_child419 a
  let kids : WhereForest R11 p.state a.event.kids [] :=
    kidProof.symm ▸ (.nil : WhereForest R11 p.state [] [])
  let actual : SourceTrace R11 p.state p.root (.selected a.declaration.decl.id []) (some a.event) :=
    .selected a.event a.rawSafe (.inr ⟨rfl,⟨.actual a⟩⟩) .nil kids
  have empty : ∀ qs (h : qs = []),
      forestWrites (h.symm ▸ (.nil : WhereForest R11 p.state [] [])) = [] := by
    intro qs h
    cases h
    rfl
  have only : writes actual = [a.retained.write] := by
    change Check408.encodedEventWrites a.event ++ forestWrites kids = [a.retained.write]
    rw [actual_event_has_only_its_original_output419 a,empty _ kidProof]
    rfl
  exact ⟨some a.event,actual,.selected .nil (.selected rfl),only.symm⟩

def matchesPick {p : Problem} (a : PickPacket p) (r : Result) : Bool :=
  (eqTree r.tree (pickReport a).tree && eqResult r.verdict (pickReport a).verdict) &&
    (match r.writes with | [out] => eqWrite out a.retained.write | _ => false)

theorem matches_original_pick_report419 {p : Problem} (a : PickPacket p) (r : Result) :
    matchesPick a r = true ↔ r = pickReport a := by
  cases r with
  | mk tree verdict ledger =>
    cases ledger with
    | nil => simp [matchesPick,pickReport]
    | cons head rest =>
      cases rest with
      | nil => simp [matchesPick,pickReport,Bool.and_eq_true,eq_tree,eq_result,eq_write419,and_assoc]
      | cons => simp [matchesPick,pickReport]

inductive Witness where
  | previous (old : RigidRival418.Witness)
  | explicitPick (wire : PickWire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous old => RigidRival418.check p r old
  | .explicitPick w => ((replayPick419 p w).map fun a => matchesPick a r).getD false
  | .unsupported => false

theorem previous_entry_unchanged419 (p : Problem) (r : Result) (w : RigidRival418.Witness) :
    check p r (.previous w) = RigidRival418.check p r w := rfl

theorem checked_report_uses_original_pick419 {p : Problem} {r : Result} {w : PickWire}
    (yes : check p r (.explicitPick w) = true) :
    ∃ a, replayPick419 p w = some a ∧ r = pickReport a := by
  cases ready : replayPick419 p w with
  | none => simp [check,ready] at yes
  | some a => exact ⟨a,rfl,(matches_original_pick_report419 a r).mp (by simpa [check,ready] using yes)⟩

theorem check_has_exact_original_report419 (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) : ClassifiedAs p.state p.root r := by
  cases w with
  | previous old => exact existing_exact_report_lifts419 (RigidRival418.check_sound p r old yes).1
  | explicitPick data =>
    obtain ⟨a,_,exactReport⟩ := checked_report_uses_original_pick419 yes
    exact exactReport ▸ pick_report_of_actual_source419 a
  | unsupported => simp [check] at yes

theorem check_sound (p : Problem) (r : Result) (w : Witness) (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧ ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  have ok := check_has_exact_original_report419 p r w yes
  refine ⟨ok,?_⟩
  obtain ⟨e,t,summary,out⟩ := ok
  exact fun m fit => ⟨e,t,summary,out,pick_R11_trace_model_meaning419 t m fit⟩

end Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
