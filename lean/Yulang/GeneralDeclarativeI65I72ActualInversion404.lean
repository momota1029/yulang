import Yulang.GeneralDeclarativeI65I72CompletedNativeComparison404

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Result)
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeK2Graph321 (View)

private theorem written_variable_never_inspects404 {s : State} {q : Request}
    (all : ∀ row ∈ visible s.core q, RepeatedRow403 q row) :
    ∀ row ∈ visible s.core q, ∀ p ∈ row.head, ∃ n, p = Pattern.var n ∧
      ∀ (view : View) (root site : Nat),
        ¬ GeneralDeclarativeInspect321.Visit view root (.variable n) site := by
  intro row visibleAt p patternAt
  rw [(all row visibleAt).literal] at patternAt
  obtain ⟨name,_,rfl⟩ := List.mem_map.mp patternAt
  exact ⟨name,rfl,fun _ _ _ => GeneralDeclarativeInspect321.variable_has_no_visit⟩

/-- Derive the actual source-tape witness from the retained concrete
election. The native structural branch never makes such a selection;
the original variable-only head at each visible row justifies the
empty entered-constructor list. -/
theorem completed_choice_inverts_actual_source404
    {s q} (e : Event s q) (needs : List (OutputNeed s))
    (raw : ¬ RootCycle s q)
    (chosen : completedChoiceSource404.elected s q e needs)
    (supports : SupportForest completedChoiceSource404 s needs) :
    ∃ trace : SelectedSource completedChoiceSource404 e needs supports,
      trace.visits = [] ∧ trace.tape.waits = false ∧ trace.tape.live = [e.frame.decl] ∧
      ∀ row ∈ visible s.core q, ∀ p ∈ row.head, ∃ n, p = Pattern.var n ∧
        ∀ (view : View) (root site : Nat),
          ¬ GeneralDeclarativeInspect321.Visit view root (.variable n) site := by
  rcases chosen with old|new
  · obtain ⟨source⟩ := old.2.1
    have expected := selected_repeated_tape_exact403 source.elected source.retained
    let trace : SelectedSource completedChoiceSource404 e needs supports :=
      ⟨selectedRepeatedTape403 source.elected source.retained,source.origin,
        (congrArg AuthoredBodyFrame393.ordinal source.sameFrame).symm,[]⟩
    exact ⟨trace,rfl,expected.settled,expected.one,
      written_variable_never_inspects404 source.elected.scope.allVisible⟩
  · obtain ⟨source⟩ := new.1
    have expected := actual_supported_tape404 source.choice raw source.retained
    let trace : SelectedSource completedChoiceSource404 e needs supports :=
      ⟨supportedTape404 source.choice source.retained,source.origin,
        (congrArg AuthoredBodyFrame393.ordinal source.frame).symm,[]⟩
    exact ⟨trace,rfl,expected.settled,expected.one,
      written_variable_never_inspects404 source.choice.rowShape⟩

theorem completed_choice_instantiates_draft_S02_404 : S02 completedChoiceSource404 := by
  intro s q e needs safe chose supports
  obtain ⟨actual,_⟩ := completed_choice_inverts_actual_source404 e needs safe chose supports
  exact ⟨actual⟩

/-- Diagnoses a false provisional quantifier, without altering C402.
The visits field in arbitrary SelectedSource data is unconstrained.
Changing it to [] or to [the same marker] while keeping all genuine
indices intact forces incompatible Required conclusions. This is not
a language counterexample or a change to the frozen target. -/
theorem draft_S03_over_unconstrained_visits_is_impossible404
    {R s q} (K : SourceSpecification R) (e : Event s q) (needs : List (OutputNeed s))
    (safe : ¬ RootCycle s q) (chosen : R.elected s q e needs)
    (supports : SupportForest R s needs) (actual : SelectedSource R e needs supports)
    (marker : CandidateVisit) : ¬ S03 K := by
  intro universal
  let noVisits : SelectedSource R e needs supports := {actual with visits := []}
  let oneVisit : SelectedSource R e needs supports := {actual with visits := [marker]}
  have notThere := (universal s q e needs supports noVisits safe chosen).2.1 marker
  have appears := (universal s q e needs supports oneVisit safe chosen).2.1 marker
  exact List.not_mem_nil (notThere.mpr (appears.mp (by exact List.mem_cons_self)))

theorem actual_completed_selection_exposes_false_draft_S03_404 {s q d}
    (chosen : Classifies completedChoiceSource404 s q (.selected d))
    (K : SourceSpecification completedChoiceSource404) :
    ¬ S03 K := by
  obtain ⟨t,e,⟨trace⟩,_,_⟩ := any_selected_producer_supports_its_original_outputs404 chosen
  cases trace with
  | selected event safe elected supports children =>
    obtain ⟨actual,_⟩ := completed_choice_inverts_actual_source404 e _ safe elected supports
    exact draft_S03_over_unconstrained_visits_is_impossible404 K e _ safe elected supports actual
      ⟨0,0,[],.value,false,0⟩

end Yulang.GeneralDeclarativeI65.I72
