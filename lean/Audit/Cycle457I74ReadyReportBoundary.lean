import Yulang.GeneralDeclarativeI65I74RoutedReadyMixedEntry457

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ReadyReportBoundary457
open RetainedFull445 (FullProblem)
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarationPatterns (ConservativeSmaller)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)

theorem ready_record_requires_raw_cycle_at_the_reported_site457
    (p : FullProblem) (r : RoutedReadyRecord457.FieldReport)
    (noCycle : ¬ AliasCycle p.state.base.core.current.ordinary
      (observed p.state.base.core.current.ordinary) r.terminal)
    (w : RoutedRecord455.FieldWire) :
    RoutedReadyRecord457.check_full457 p (.fieldK2 r) (.fieldK2 w) = false := by
  by_cases success : RoutedReadyRecord457.check_full457 p (.fieldK2 r) (.fieldK2 w) = true
  · obtain ⟨a,re⟩ := (RoutedReadyRecord457.check_full_sound457 p (.fieldK2 r) (.fieldK2 w) success).1
    have site : a.terminal = r.terminal := congrArg RoutedReadyRecord457.FieldReport.terminal re
    exact (noCycle (site ▸ a.visited.2.2)).elim
  · exact Bool.eq_false_iff.mpr success

theorem ready_mixed_requires_raw_cycle_at_the_reported_site457
    (p : FullProblem) (r : RoutedReadyMixed457.ReportAtField)
    (noCycle : ¬ AliasCycle p.state.base.core.current.ordinary
      (observed p.state.base.core.current.ordinary) r.terminal)
    (w : RoutedMixed456.FieldWire) :
    RoutedReadyMixed457.check_full_ready_mixed457 p (.fieldK2 r) (.fieldK2 w) = false := by
  by_cases success : RoutedReadyMixed457.check_full_ready_mixed457 p (.fieldK2 r) (.fieldK2 w) = true
  · obtain ⟨a,re⟩ := (RoutedReadyMixed457.check_full_sound457 p (.fieldK2 r) (.fieldK2 w) success).1
    have site : a.terminal = r.terminal := congrArg RoutedReadyMixed457.ReportAtField.terminal re
    exact (noCycle (site ▸ a.cycle)).elim
  · exact Bool.eq_false_iff.mpr success

theorem exact_ready_report_exposes_the_original_clause_and_candidate457
    (p : FullProblem) (r : RoutedReadyMixed457.ReportAtField) (w : RoutedMixed456.FieldWire)
    (success : RoutedReadyMixed457.check_full_ready_mixed457 p (.fieldK2 r) (.fieldK2 w) = true) :
    r.occurrence = p.root.occurrence ∧ r.originalClauseOrdinal = 0 ∧
      ∃ d c, visible p.state.base.core p.root = [d] ∧ d.requirements = [c] ∧
        r.declaration = d.id ∧ r.originalClauseId = c.id ∧
        ¬ ConservativeSmaller d.head c.arguments := by
  obtain ⟨a,re⟩ := (RoutedReadyMixed457.check_full_sound457 p (.fieldK2 r) (.fieldK2 w) success).1
  subst r
  exact ⟨rfl,rfl,a.declaration,a.source.clause,a.source.only,a.source.requirement,rfl,rfl,a.actualGap⟩

theorem existing_conservative_rules_are_not_absorbed_by_ready_mixed457
    (p : FullProblem) {d : Declaration} {c : Clause}
    (visibleOriginal : visible p.state.base.core p.root = [d])
    (originalClause : d.requirements = [c]) (legacy : ConservativeSmaller d.head c.arguments)
    (r : RoutedReadyMixed457.ReportAtField) (w : RoutedMixed456.FieldWire) :
    RoutedReadyMixed457.check_full_ready_mixed457 p (.fieldK2 r) (.fieldK2 w) = false := by
  by_cases success : RoutedReadyMixed457.check_full_ready_mixed457 p (.fieldK2 r) (.fieldK2 w) = true
  · obtain ⟨_,_,x,y,current,clause,_,_,impossible⟩ :=
      exact_ready_report_exposes_the_original_clause_and_candidate457 p r w success
    have candidateEq := List.singleton_inj.mp (current.symm.trans visibleOriginal)
    subst x
    have clauseEq := List.singleton_inj.mp (clause.symm.trans originalClause)
    subst y
    exact (impossible legacy).elim
  · exact Bool.eq_false_iff.mpr success

#print axioms ready_record_requires_raw_cycle_at_the_reported_site457
#print axioms ready_mixed_requires_raw_cycle_at_the_reported_site457
#print axioms exact_ready_report_exposes_the_original_clause_and_candidate457
#print axioms existing_conservative_rules_are_not_absorbed_by_ready_mixed457
end Yulang.GeneralDeclarativeI65.I72.ReadyReportBoundary457
