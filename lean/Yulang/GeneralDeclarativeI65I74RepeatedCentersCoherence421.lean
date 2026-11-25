import Yulang.GeneralDeclarativeI65I74RepeatedCentersLegacy421

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open CommonRoleOutermostResolver (Dictionary Summarizes)
open Checker408 (Problem Result)

private theorem no_where_exact421 {s qs ts} (kids : WhereForest R13 s qs ts)
    (empty : qs = []) : ts = [] ∧ forestWrites kids = [] := by
  cases kids with
  | nil => exact ⟨rfl,rfl⟩
  | cons _ _ => cases empty

private theorem empty_choice_has_its_literal_dictionary421 {id d}
    (summary : Summarizes (.selected id []) (.selected d)) : d = .node id [] := by
  cases summary with
  | selected child combine =>
    cases child
    cases combine with
    | selected ds =>
      simp at ds
      cases ds
      rfl

/-- The selected report is exact regardless of whether the derivation
uses the new local rule or an old compatible selecting rule. The two
proofs need not be equal. This does not assert uniqueness of every
diagnostic outside the selected verdict. -/
theorem any_selected_R13_report_uses_the_original_repeated_source421 (p : Problem)
    (a : Choice p) {r : Result} {d : Dictionary}
    (classified : ClassifiedAs p.state p.root r) (selected : r.verdict = .selected d) :
    r = Check408.nullaryReport a.decl := by
  rcases r with ⟨tree,verdict,rs⟩
  dsimp at selected
  cases selected
  obtain ⟨event,trace,summary,ledger⟩ := classified
  dsimp only at trace summary ledger ⊢
  cases trace with
  | rootK2 _ => cases summary
  | other v _ _ _ => cases v <;> cases summary
  | selected event _ _ _ kids =>
    have source : event.frame.decl = a.decl := by simpa [a.only] using event.frame.inScope
    have kidless : event.kids = [] := by
      simp [Event.kids,frameWhereKids400,AuthoredBodyFrame393.clauses,children,source,a.noWhere]
    obtain ⟨empty,emptyWrites⟩ := no_where_exact421 kids kidless
    have noW : Check408.encodedEventWrites event = [] := by
      apply List.length_eq_zero_iff.mp
      simp [Check408.encodedEventWrites,a.noOutputs]
    change rs = Check408.encodedEventWrites event ++ forestWrites kids at ledger
    rw [noW,emptyWrites,List.nil_append] at ledger
    rw [empty] at summary ⊢
    rw [empty_choice_has_its_literal_dictionary421 summary,ledger]
    simp [Check408.nullaryReport,source]

/-- In particular every accepted executable selected report has this
same exact original key and no synthesized child or fixed target. -/
theorem accepted_selected_checker_report_is_original_repeated_source421 (p : Problem)
    (a : Choice p) (r : Result) (w : Witness) {d : Dictionary}
    (yes : check p r w = true) (selected : r.verdict = .selected d) :
    r = Check408.nullaryReport a.decl :=
  any_selected_R13_report_uses_the_original_repeated_source421 p a
    (check_has_exact_original_report421 p r w yes) selected

end Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
