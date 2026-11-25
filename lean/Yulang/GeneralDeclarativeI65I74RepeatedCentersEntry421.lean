import Yulang.GeneralDeclarativeI65I74RepeatedCentersReport421

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
open GeneralDeclarativeI65
open Checker408 (Problem Result)
open GeneralDeclarativeWitnessTree349 (eqTree eq_tree eqResult eq_result)

def outcomeReport {p} {a : Choice p} : Outcome a → Result
  | .accepted _ => Check408.nullaryReport a.decl
  | .incompatible _ => ⟨.rejected,.rejected,[]⟩

theorem no_original_outputs_in_selected_report421 {p} {a : Choice p} (b : Accepted a) :
    Check408.encodedEventWrites (acceptedEvent b) = [] := by
  have len : p.root.demand.outputs.length = 0 := by simp [a.noOutputs]
  have writesLen : (Check408.encodedEventWrites (acceptedEvent b)).length = 0 := by
    simp [Check408.encodedEventWrites,len]
  exact List.length_eq_zero_iff.mp writesLen

theorem output_is_real_post_selection_report421 {p} {a : Choice p} (out : Outcome a) :
    ClassifiedAs p.state p.root (outcomeReport out) := by
  cases out with
  | accepted b =>
    let kidProof := acceptedEvent_has_no_where421 b
    let kids : WhereForest R13 p.state (acceptedEvent b).kids [] :=
      kidProof.symm ▸ (.nil : WhereForest R13 p.state [] [])
    let actual : SourceTrace R13 p.state p.root (.selected a.decl.id []) (some (acceptedEvent b)) :=
      .selected (acceptedEvent b) a.rawSafe (.inr ⟨rfl,⟨.actual b⟩⟩) .nil kids
    have empty : ∀ qs (h : qs = []),
        forestWrites (h.symm ▸ (.nil : WhereForest R13 p.state [] [])) = [] := by
      intro qs h
      cases h
      rfl
    have noWrites : writes actual = [] := by
      change Check408.encodedEventWrites (acceptedEvent b) ++ forestWrites kids = []
      rw [no_original_outputs_in_selected_report421 b,empty _ kidProof]
      rfl
    exact ⟨some (acceptedEvent b),actual,.selected .nil (.selected rfl),noWrites.symm⟩
  | incompatible b =>
    exact ⟨none,.other .rejected a.rawSafe (.inr ⟨rfl,rfl,⟨⟨a,b⟩⟩⟩) .nil,.rejected,rfl⟩

def matchesResult (actual expected : Result) : Bool :=
  (eqTree actual.tree expected.tree && eqResult actual.verdict expected.verdict) && actual.writes.isEmpty

theorem matches_exact_empty_ledger421 (r expected : Result) (empty : expected.writes = []) :
    matchesResult r expected = true ↔ r = expected := by
  cases r
  cases expected with | mk tree verdict ledger =>
    dsimp at empty
    subst ledger
    simp [matchesResult,Bool.and_eq_true,eq_tree,eq_result,and_assoc]

structure Wire where
  pre : ChoiceWire
  post : PostWire

def replay421 (p : Problem) (w : Wire) : Option (Σ a : Choice p, Outcome a) := do
  let a ← readChoice421 p w.pre
  let checked ← readAfterChoice421 a w.post
  pure ⟨a,checked⟩

inductive Witness where
  | previous (old : RoleDefault420.Witness)
  | repeatedCenters (wire : Wire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous old => RoleDefault420.check p r old
  | .repeatedCenters w => ((replay421 p w).map fun out => matchesResult r (outcomeReport out.2)).getD false
  | .unsupported => false

theorem previous_entry_unchanged421 (p : Problem) (r : Result) (w : RoleDefault420.Witness) :
    check p r (.previous w) = RoleDefault420.check p r w := rfl

theorem accepted_report_has_exact_pre_then_post_evidence421 {p : Problem} {r : Result} {w : Wire}
    (yes : check p r (.repeatedCenters w) = true) :
    ∃ a : Choice p, ∃ b : Outcome a,
      readChoice421 p w.pre = some a ∧ readAfterChoice421 a w.post = some b ∧ r = outcomeReport b := by
  cases ready : replay421 p w with
  | none => simp [check,ready] at yes
  | some pair =>
    obtain ⟨a,b⟩ := pair
    have empty : (outcomeReport b).writes = [] := by cases b <;> rfl
    have eq := (matches_exact_empty_ledger421 r (outcomeReport b) empty).mp (by simpa [check,ready] using yes)
    simp only [replay421,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def] at ready
    obtain ⟨a',e,b',g,final⟩ := ready
    cases Option.some.inj final
    exact ⟨a,b,e,g,eq⟩

theorem check_has_exact_original_report421 (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) : ClassifiedAs p.state p.root r := by
  cases w with
  | previous old => exact existing_exact_report_lifts421 (RoleDefault420.check_sound p r old yes).1
  | repeatedCenters data =>
    obtain ⟨a,b,_,_,report⟩ := accepted_report_has_exact_pre_then_post_evidence421 yes
    exact report ▸ output_is_real_post_selection_report421 b
  | unsupported => simp [check] at yes

theorem check_sound (p : Problem) (r : Result) (w : Witness) (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧ ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  have ok := check_has_exact_original_report421 p r w yes
  refine ⟨ok,?_⟩
  obtain ⟨e,t,summary,out⟩ := ok
  exact fun m fit => ⟨e,t,summary,out,repeated_R13_trace_model_meaning421 t m fit⟩

end Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
