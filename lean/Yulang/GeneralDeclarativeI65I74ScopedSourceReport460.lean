import Yulang.GeneralDeclarativeI65I74ScopedGrammarTraversal460
import Yulang.GeneralDeclarativeI65I74GrammarBoundaries460

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open Checker408 (Problem)
open RetainedFull445 (FullProblem)
open RoutedReadyMixed457 (ReportAtField)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open RoutedMixed456 (endsAtField)

def scopedSourceReport (p : Problem) (r : ReportAtField) : Prop :=
  ∃ (a : OriginalAnchor p) (last : Term) (used : Bool),
    ScopedRaw p.state.core a.capture.lower (normalized (readTerm a.original))
      a.code r.path r.terminal last used ∧
    endsAtField r.path r.terminal = true ∧
    AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) r.terminal ∧
    exactReport a r.path r.terminal = r

theorem grammar_scoped_source_receipt_iff_anchored_compiled_field {p : Problem} {r : ReportAtField} :
    scopedSourceReport p r ↔ anchored p r := by
  constructor
  · rintro ⟨a,last,used,scope,lastField,raw,identity⟩
    exact ⟨a,last,⟨⟨used,exact_scope_reifies_full_trace_by_descent
      (anchor_compiles_the_normalized_original a) scope⟩,lastField,raw⟩,identity⟩
  · rintro ⟨a,last,⟨⟨used,h⟩,field,raw⟩,report⟩
    exact ⟨a,last,used,full_trace_reflects_exact_compiled_scope h,field,raw,report⟩

/-- Structural completeness of the source-and-raw *receipt* for every
finite in-scope actual route in the current carrier. The theorem does not
establish that every G04 source claim supplies those authorisation and
scope premises, and is not a cumulative diagnostic checker. -/
theorem any_actual_scoped_source_report_has_an_exact_finite_wire {p : Problem} {r : ReportAtField} :
    scopedSourceReport p r ↔ ∃ w, readAnchoredField p w = some r :=
  grammar_scoped_source_receipt_iff_anchored_compiled_field.trans
    attained_exact_report_iff_finite_anchored_read.symm

theorem any_scoped_source_receipt_is_the_same_field_in_every_fit
    {p : FullProblem} {r : ReportAtField}
    (exact : scopedSourceReport p.old r) (m : I72.Model) (fit : I72.FitsFull p.state m) :
    ∃ (a : OriginalAnchor p.old) (last : Term) (used : Bool),
      exactReport a r.path r.terminal = r ∧
      RoutedInlineStructural458.ModelTrail p.state.base.core m a.capture.lower a.code
        r.path r.terminal used ∧
      CoordinateWalk (fun _ => queryKeys p.state.base.core) a.capture.lower
        (normalized (readTerm a.original)) r.path r.terminal last ∧
      AliasCycle p.state.base.core.current.ordinary
        (observed p.state.base.core.current.ordinary) r.terminal :=
  addressed_field_holds_in_every_same_fit
    (grammar_scoped_source_receipt_iff_anchored_compiled_field.mp exact) m fit

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
