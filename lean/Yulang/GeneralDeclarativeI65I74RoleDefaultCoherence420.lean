import Yulang.GeneralDeclarativeI65I74RoleDefaultPriority420

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoleDefault420
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open CommonRoleOutermostResolver (Summarizes)
open Checker408 (Problem Result)
open ExplicitPick419 (eqWrite eq_write419 RetainedOutput eqWire eq_wire419 exactlyOneOutput
  actual_sources_agree_on_input_and_residual419)

theorem checked_defaults_agree_on_the_same_original_ledger420 {p} (a b : DefaultPacket p) :
    a.retained.write = b.retained.write := by
  have decl := (List.cons.inj (a.declaration.theOnlyOne.symm.trans b.declaration.theOnlyOne)).1
  have rows := actual_sources_agree_on_input_and_residual419 a.rows b.rows
  let table := (authoredRegistry p.state.core.current).declarations.map Declaration.id
  have left : table[a.declaration.ordinal]? = some a.declaration.decl.id := by
    simp [table,a.declaration.authored]
  have right : table[b.declaration.ordinal]? = some a.declaration.decl.id := by
    simp [table,b.declaration.authored,decl]
  obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp left
  have ordinal := (List.Nodup.getElem?_inj bound a.declaration.checked.1).mp (left.trans right.symm)
  apply (eq_write419 _ _).mp
  simp only [eqWrite,RetainedOutput.write,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨⟨True.intro,ordinal,True.intro,True.intro,True.intro,?_⟩,?_⟩
  · rw [a.actualBody,b.actualBody]
    exact congrArg (fun role => GeneralDictionaryAssociatedProvenance.Body.default role
      (p.root.demand.outputs[exactlyOneOutput p a.single].name) (.var 0)) (congrArg Declaration.role decl)
  · change eqWire a.retained.write.typedRhs b.retained.write.typedRhs = true
    rw [original_typed_default_wire_preserves_all_three_point_names420,
      original_typed_default_wire_preserves_all_three_point_names420,rows.1]
    exact (eq_wire419 _ _).mpr rfl

private theorem empty_where_retains_no_writes420 {s qs ts} (kids : WhereForest R12 s qs ts)
    (empty : qs = []) : ts = [] ∧ forestWrites kids = [] := by
  cases kids with
  | nil => exact ⟨rfl,rfl⟩
  | cons _ _ => cases empty

private theorem empty_default_tree_has_only_selected_summary420 {id result}
    (summary : Summarizes (.selected id []) result) : result = .selected (.node id []) := by
  cases summary with
  | selected child combine =>
    cases child
    cases combine with
    | rejected impossible => cases impossible
    | ambiguous _ impossible => cases impossible
    | pending _ _ impossible => cases impossible
    | selected ds =>
      simp at ds
      cases ds
      rfl

/-- Uniqueness holds at the source-rule level too; it is not an assumption
that the executable witness accepts at most one report. -/
theorem original_default_source_has_only_one_exact_report420 (p : Problem)
    (a : DefaultPacket p) (r : Result) :
    ClassifiedAs p.state p.root r ↔ r = defaultReport a := by
  constructor
  · rintro ⟨event,trace,summary,ledger⟩
    rcases p with ⟨s,q⟩
    rcases r with ⟨tree,result,rs⟩
    dsimp only at trace summary ledger ⊢
    cases trace with
    | rootK2 cycle => exact False.elim (a.rawSafe cycle)
    | other _ _ rejected _ =>
      exact False.elim (no_older_diagnostic_claims_this_actual_Default420 a rejected)
    | selected event _ elected _ kids =>
      rcases elected with earlier|⟨_,⟨chosen⟩⟩
      · exact False.elim (no_prior_election_claims_the_defaulted_source420 a event earlier)
      · cases chosen with
        | actual b =>
          obtain ⟨ts,ws⟩ := empty_where_retains_no_writes420 kids
            (actual_default_never_switches_to_a_where_child420 b)
          have declared := (List.cons.inj (b.declaration.theOnlyOne.symm.trans a.declaration.theOnlyOne)).1
          have rhs := checked_defaults_agree_on_the_same_original_ledger420 b a
          change rs = Check408.encodedEventWrites b.event ++ forestWrites kids at ledger
          rw [actual_event_has_only_its_original_output420 b,ws,List.append_nil,rhs] at ledger
          rw [ts] at summary ⊢
          rw [empty_default_tree_has_only_selected_summary420 summary,ledger]
          have id : b.event.frame.decl.id = a.declaration.decl.id := congrArg Declaration.id declared
          simp only [defaultReport,id]
  · rintro rfl
    exact default_report_of_actual_source420 a

theorem any_successful_witness_uses_exact_original_default420
    (p : Problem) (a : DefaultPacket p) (r : Result) (w : Witness) (yes : check p r w = true) :
    r = defaultReport a :=
  (original_default_source_has_only_one_exact_report420 p a r).mp
    (check_has_exact_original_report420 p r w yes)

end Yulang.GeneralDeclarativeI65.I72.RoleDefault420
