import Yulang.GeneralDeclarativeI65I74RoleDefaultReport420

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoleDefault420
open GeneralDeclarativeI65
open ExplicitPick419 (RetainedOutput exactlyOneOutput eqWrite eq_write419)
open Checker408 (Problem Result)
open GeneralDeclarativeWitnessTree349 (eqTree eq_tree eqResult eq_result)

def defaultReport {p : Problem} (a : DefaultPacket p) : Result :=
  ⟨.selected a.declaration.decl.id [],.selected (.node a.declaration.decl.id []),[a.retained.write]⟩

theorem actual_event_has_only_its_original_output420 {p : Problem} (a : DefaultPacket p) :
    Check408.encodedEventWrites a.event = [a.retained.write] := by
  apply List.ext_getElem
  · simp [Check408.encodedEventWrites,a.single]
  · intro n hA hB
    have zero : n = 0 := by simpa using hB
    subst n
    simp [Check408.encodedEventWrites,DefaultPacket.event,RetainedOutput.write,exactlyOneOutput]

theorem default_report_of_actual_source420 {p : Problem} (a : DefaultPacket p) :
    ClassifiedAs p.state p.root (defaultReport a) := by
  let kidProof := actual_default_never_switches_to_a_where_child420 a
  let kids : WhereForest R12 p.state a.event.kids [] :=
    kidProof.symm ▸ (.nil : WhereForest R12 p.state [] [])
  let actual : SourceTrace R12 p.state p.root (.selected a.declaration.decl.id []) (some a.event) :=
    .selected a.event a.rawSafe (.inr ⟨rfl,⟨.actual a⟩⟩) .nil kids
  have empty : ∀ qs (h : qs = []),
      forestWrites (h.symm ▸ (.nil : WhereForest R12 p.state [] [])) = [] := by
    intro qs h
    cases h
    rfl
  have only : writes actual = [a.retained.write] := by
    change Check408.encodedEventWrites a.event ++ forestWrites kids = [a.retained.write]
    rw [actual_event_has_only_its_original_output420 a,empty _ kidProof]
    rfl
  exact ⟨some a.event,actual,.selected .nil (.selected rfl),only.symm⟩

def matchesDefault {p : Problem} (a : DefaultPacket p) (r : Result) : Bool :=
  (eqTree r.tree (defaultReport a).tree && eqResult r.verdict (defaultReport a).verdict) &&
    (match r.writes with | [out] => eqWrite out a.retained.write | _ => false)

theorem matches_original_default_report420 {p : Problem} (a : DefaultPacket p) (r : Result) :
    matchesDefault a r = true ↔ r = defaultReport a := by
  cases r with
  | mk tree verdict ledger =>
    cases ledger with
    | nil => simp [matchesDefault,defaultReport]
    | cons head rest =>
      cases rest with
      | nil => simp [matchesDefault,defaultReport,Bool.and_eq_true,eq_tree,eq_result,eq_write419,and_assoc]
      | cons => simp [matchesDefault,defaultReport]

inductive Witness where
  | previous (old : ExplicitPick419.Witness)
  | roleDefault (wire : DefaultWire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous old => ExplicitPick419.check p r old
  | .roleDefault w => ((replayDefault420 p w).map fun a => matchesDefault a r).getD false
  | .unsupported => false

theorem previous_entry_unchanged420 (p : Problem) (r : Result) (w : ExplicitPick419.Witness) :
    check p r (.previous w) = ExplicitPick419.check p r w := rfl

theorem checked_report_uses_original_default420 {p : Problem} {r : Result} {w : DefaultWire}
    (yes : check p r (.roleDefault w) = true) :
    ∃ a, replayDefault420 p w = some a ∧ r = defaultReport a := by
  cases ready : replayDefault420 p w with
  | none => simp [check,ready] at yes
  | some a => exact ⟨a,rfl,(matches_original_default_report420 a r).mp (by simpa [check,ready] using yes)⟩

theorem check_has_exact_original_report420 (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) : ClassifiedAs p.state p.root r := by
  cases w with
  | previous old => exact existing_exact_report_lifts420 (ExplicitPick419.check_sound p r old yes).1
  | roleDefault data =>
    obtain ⟨a,_,exactReport⟩ := checked_report_uses_original_default420 yes
    exact exactReport ▸ default_report_of_actual_source420 a
  | unsupported => simp [check] at yes

theorem check_sound (p : Problem) (r : Result) (w : Witness) (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧ ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  have ok := check_has_exact_original_report420 p r w yes
  refine ⟨ok,?_⟩
  obtain ⟨e,t,summary,out⟩ := ok
  exact fun m fit => ⟨e,t,summary,out,default_R12_trace_model_meaning420 t m fit⟩

end Yulang.GeneralDeclarativeI65.I72.RoleDefault420
