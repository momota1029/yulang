import Yulang.GeneralDeclarativeI65I74RepeatedCentersCoherence421

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration)
open Checker408 (Problem Result)
open CommonRoleOutermostResolver (Summarizes)

private theorem only_one421 {p} (a : Choice p)
    (many : 2 ≤ (visible p.state.core p.root).length) : False := by
  simp [a.only] at many

private theorem no_unary_syntax421 {p} (a : Choice p) {d : Declaration}
    (seen : d ∈ visible p.state.core p.root) {pat : Pattern}
    (h : d.head = [pat]) : False := by
  have same : d = a.decl := by simpa [a.only] using seen
  have len := congrArg List.length (h.symm.trans ((congrArg Declaration.head same).trans a.literal))
  simp at len

private theorem no_repeat_diag421 {p v} (a : Choice p) (h : RepeatedOther403 p.state p.root v) : False := by
  cases h with
  | ambiguous _ many => exact only_one421 a many

private theorem no_native_diag421 {p v needs} (a : Choice p)
    (h : variableWithNativeK2403.other p.state p.root v needs) : False := by
  rcases h.2 with repeated|⟨_,_,entry,_⟩
  · exact no_repeat_diag421 a repeated
  · exact no_unary_syntax421 a entry.visibleRow entry.exactHead

private theorem no_completed_native_diag421 {p v needs} (a : Choice p)
    (h : completedNativePrioritySource404.other p.state p.root v needs) : False := by
  rcases h with old|⟨_,⟨view⟩⟩
  · exact no_native_diag421 a old
  · exact no_unary_syntax421 a view.entry.visibleRow view.entry.exactHead

private theorem no_completed_choice_diag421 {p v needs} (a : Choice p)
    (h : completedChoiceSource404.other p.state p.root v needs) : False := by
  rcases h with old|⟨_,⟨view⟩⟩
  · exact no_completed_native_diag421 a old
  · exact only_one421 a view.two

/-- Every older non-root diagnostic independently requires a genuine
different source shape: at least two rivals, an inspected unary
candidate, or a single record argument. No unavailable proof is used
as a language diagnostic. -/
theorem earlier_diagnostics_excluded_on_actual_repeated_choice421 {p v needs} (a : Choice p) :
    ¬ RoleDefault420.R12.other p.state p.root v needs := by
  rintro ((((⟨_,family,old⟩|⟨_,_,⟨closed⟩⟩)|mixed)|opened)|⟨_,_,⟨ambiguity⟩⟩)
  · cases family with
    | variableOnly =>
      cases old.2 with
      | ambiguous _ many => exact only_one421 a many
    | repeated | whereTree => exact no_repeat_diag421 a old.2
    | nativeK2 | supported => exact no_native_diag421 a old
    | supportedK2 => exact no_completed_native_diag421 a old
    | supportedAmbiguity | authoredNative => exact no_completed_choice_diag421 a old
  · have len := congrArg List.length (closed.field.asked.symm.trans a.originalArgs)
    simp at len
  · obtain ⟨_,_,⟨view⟩⟩ := mixed
    exact only_one421 a view.rivalsExist
  · obtain ⟨_,_,⟨view⟩⟩ := opened
    have len := congrArg List.length (view.input.args.symm.trans a.originalArgs)
    simp at len
  · have count := congrArg List.length a.only
    rcases ambiguity.ordered with h|h <;> simp [h] at count

private theorem where_empty_index421 {s qs ts} (kids : WhereForest R13 s qs ts) (eq : qs = []) :
    ts = [] := by
  cases kids with
  | nil => rfl
  | cons _ _ => cases eq

private theorem where_empty_selected_summary421 {id result}
    (actual : Summarizes (.selected id []) result) : result = .selected (.node id []) := by
  cases actual with
  | selected children combine =>
    cases children
    cases combine with
    | rejected impossible => cases impossible
    | ambiguous _ impossible => cases impossible
    | pending _ _ impossible => cases impossible
    | selected exact =>
      simp at exact
      cases exact
      rfl

private theorem source_report_has_only_its_two_post_outcomes421 (p : Problem)
    (a : Choice p) (r : Result) (has : ClassifiedAs p.state p.root r) :
    (r = Check408.nullaryReport a.decl) ∨
    (r = ⟨.rejected,.rejected,[]⟩ ∧ Nonempty (RejectedElection p.state p.root)) := by
  rcases r with ⟨tree,verdict,rs⟩
  have saved := has
  obtain ⟨event,trace,summary,ledger⟩ := saved
  dsimp only at trace summary ledger ⊢
  cases trace with
  | rootK2 cycle => exact False.elim (a.rawSafe cycle)
  | other v _ read _ =>
    rcases read with old|⟨rejected,_,new⟩
    · exact False.elim (earlier_diagnostics_excluded_on_actual_repeated_choice421 a old)
    · subst v
      cases summary
      exact .inr ⟨by cases ledger; rfl,new⟩
  | selected event _ _ _ kids =>
    have source : event.frame.decl = a.decl := by simpa [a.only] using event.frame.inScope
    have noKids : event.kids = [] := by
      simp [Event.kids,frameWhereKids400,AuthoredBodyFrame393.clauses,children,source,a.noWhere]
    have empty := where_empty_index421 kids noKids
    rw [empty] at summary
    have selection := where_empty_selected_summary421 summary
    exact .inl (any_selected_R13_report_uses_the_original_repeated_source421 p a has selection)

/-- Within the actual admitted repeated-binder slice, independent source
semantics yields exactly the certified post-outcome report. Neither a
different verdict nor a different ledger can be certified for this same
State and Request. Proofs/elections themselves need not be identical. -/
theorem only_exact_post_outcome_reports_on_original_repeated_choice421 (p : Problem)
    (a : Choice p) (out : Outcome a) (r : Result) :
    ClassifiedAs p.state p.root r ↔ r = outcomeReport out := by
  constructor
  · intro has
    rcases source_report_has_only_its_two_post_outcomes421 p a r has with selected|⟨no,⟨bad⟩⟩
    · cases out with
      | accepted yes => exact selected
      | incompatible bad =>
        have semantic := exact_report_is_R13_classification421 has
        rw [selected] at semantic
        exact False.elim (incompatible_request_selects_no_R13_dictionary421 bad _ semantic)
    · cases out with
      | incompatible noChoice => exact no
      | accepted yes =>
        have semantic := exact_report_is_R13_classification421
          (output_is_real_post_selection_report421 (.accepted yes))
        rcases p with ⟨s,q⟩
        exact False.elim (incompatible_request_selects_no_R13_dictionary421 bad.conflict _ semantic)
  · rintro rfl
    exact output_is_real_post_selection_report421 out

end Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
