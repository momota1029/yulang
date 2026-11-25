import Yulang.GeneralDeclarativeI65I74X6AmbiguousReport417
import Yulang.GeneralDeclarativeI65I74X6AmbiguousReplay417

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
open GeneralDeclarativeI65
open Checker408 (Problem Result)

def report417 : Result := ⟨.ambiguous,.ambiguous,[]⟩

theorem both_actual_matches_classify_as_ambiguity417 {p : Problem}
    (a : Ambiguous p.state p.root) : ClassifiedAs p.state p.root report417 := by
  let trace : SourceTrace R9 p.state p.root .ambiguous none :=
    .other .ambiguous (root_safe417 a.visits) (.inr ⟨rfl,rfl,⟨a⟩⟩) .nil
  exact ⟨none,trace,.ambiguous,rfl⟩

inductive Witness where
  | previous (old : PlainMerged416.Witness)
  | x6Ambiguity (w : AmbiguityWire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous old => PlainMerged416.check p r old
  | .x6Ambiguity w =>
    match replayAmbiguity417 p w with
    | none => false
    | some _ => Check408.matchesNoWrites r report417.tree report417.verdict
  | .unsupported => false

theorem previous_entry_unchanged417 (p : Problem) (r : Result) (w : PlainMerged416.Witness) :
    check p r (.previous w) = PlainMerged416.check p r w := rfl

theorem checked_x6_reflects_exact_candidates_and_report417 (p : Problem) (r : Result) (w : AmbiguityWire)
    (yes : check p r (.x6Ambiguity w) = true) :
    ∃ v, replayAmbiguity417 p w = some v ∧ r = report417 := by
  cases seen : replayAmbiguity417 p w with
  | none => simp [check,seen] at yes
  | some a =>
    have result : Check408.matchesNoWrites r report417.tree report417.verdict = true := by
      simpa [check,seen] using yes
    obtain ⟨tree,verdict,output⟩ := Check408.matchesNoWrites_exact408.mp result
    refine ⟨a,rfl,?_⟩
    cases r
    simp only at tree verdict output
    subst_vars
    rfl

theorem check_has_exact_original_report417 (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) : ClassifiedAs p.state p.root r := by
  cases w with
  | previous old => exact existing_exact_report_lifts417 (PlainMerged416.check_sound p r old yes).1
  | x6Ambiguity fresh =>
    obtain ⟨v,_,report⟩ := checked_x6_reflects_exact_candidates_and_report417 p r fresh yes
    exact report ▸ both_actual_matches_classify_as_ambiguity417 v
  | unsupported => simp [check] at yes

theorem check_sound (p : Problem) (r : Result) (w : Witness) (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧ ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  have ok := check_has_exact_original_report417 p r w yes
  refine ⟨ok,?_⟩
  obtain ⟨e,t,summary,out⟩ := ok
  exact fun m fit => ⟨e,t,summary,out,R9_trace_model_meaning417 t m fit⟩

end Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
