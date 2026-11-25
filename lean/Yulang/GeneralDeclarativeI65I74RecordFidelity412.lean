import Yulang.GeneralDeclarativeI65I74RecordPriority412

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordK2412
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeInspect321 (Visit PatternK2)
open GeneralDeclarativeGraphRows321 (observed structural)
open CommonRoleOutermostResolver (Summarizes)
open Checker408 (Problem Result)

theorem fitting_record_reads_have_same_exact_field412 {s q d other}
    (a : ActualRecordField s q d) (b : ActualRecordField s q other)
    (m : I72.Model) (fit : Fits s m) : a.box = b.box ∧ a.site = b.site := by
  have arg := (List.cons.inj (a.asked.symm.trans b.asked)).1
  have identicalSlot := a.originLower.trans ((congrArg Capture.lower arg).trans b.originLower.symm)
  have aSyntax := fit.2 _ a.original
  have bSyntax := fit.2 _ b.original
  rw [identicalSlot] at aSyntax
  have endpoint := Option.some.inj (aSyntax.symm.trans bSyntax)
  rw [a.endpoint,b.endpoint] at endpoint
  change CommonRecursiveNominalIntervals.Endpoint.ordinary
    (.record a.box (.var a.site) .emptyRecord) =
    CommonRecursiveNominalIntervals.Endpoint.ordinary
      (.record b.box (.var b.site) .emptyRecord) at endpoint
  injection endpoint with same
  injection same with label payload
  exact ⟨label,Core.PresenceGeneration.TyTerm.var.inj payload⟩

/-- The finite rejection trace and its literal inspected site are fixed
before quantifying over models. A supplied proof of cycle does not
identify the occurrence or authorize the pattern visit. -/
theorem checked_record_fixes_actual_site_and_trace_before_models412
    (p : Problem) (r : Result) (w : FieldWire) (yes : check p r (.fieldCycle w) = true) :
    ∃ (v : VerifiedField p) (t : SourceTrace R4 p.state p.root r.tree none),
      r = Check408.rawReport ∧
      Visit (structural p.state.core.current.ordinary) v.rejection.field.input.lower
        (query412 v.rejection.field.box v.rejection.field.tick v.rejection.field.binder)
        v.rejection.field.site ∧
      ¬ GeneralDeclarativeLowerKnown321.Alias p.state.core.current.ordinary
        v.rejection.field.input.lower v.rejection.field.site ∧
      Summarizes r.tree r.verdict ∧ r.writes = writes t ∧
      ∀ m, Fits p.state m → TraceMeaning p.state m t := by
  obtain ⟨_,_,v,_,report⟩ := checked_field_reflects_actual_original_rejection412 p r w yes
  subst r
  let actual : SourceTrace R4 p.state p.root .rejected none :=
    .other .rejected v.rootSafe (.inr ⟨rfl,rfl,⟨v.rejection⟩⟩) .nil
  exact ⟨v,actual,rfl,actual_record_field_is_entered412 v.rejection.field,
    actual_entered_site_is_not_even_a_root_alias412 v,.rejected,rfl,
    fun m fit => mixed_R4_trace_model_meaning412 actual m fit⟩

theorem same_fitting_input_cannot_change_checked_field412
    (p : Problem) (r t : Result) (w v : FieldWire)
    (first : check p r (.fieldCycle w) = true) (second : check p t (.fieldCycle v) = true)
    (m : I72.Model) (fit : Fits p.state m) :
    ∃ (d e : Declaration) (a : VerifiedField p) (b : VerifiedField p)
      (left : visible p.state.core p.root = [d]) (right : visible p.state.core p.root = [e]),
      replayField412 p d left w = some a ∧ replayField412 p e right v = some b ∧
      d = e ∧ a.rejection.field.box = b.rejection.field.box ∧
      a.rejection.field.site = b.rejection.field.site := by
  obtain ⟨d,left,a,firstRead,_⟩ := checked_field_reflects_actual_original_rejection412 p r w first
  obtain ⟨e,right,b,secondRead,_⟩ := checked_field_reflects_actual_original_rejection412 p t v second
  exact ⟨d,e,a,b,left,right,firstRead,secondRead,(List.cons.inj (left.symm.trans right)).1,
    fitting_record_reads_have_same_exact_field412 a.rejection.field b.rejection.field m fit⟩

end Yulang.GeneralDeclarativeI65.I72.RecordK2412
