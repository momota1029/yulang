import Yulang.GeneralDeclarativeI65I74MixedRecordEvidence413

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MixedRecord413
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Tree Dictionary Result Summarizes Combine)

def SuccessfulChildren413 (trees : List Tree) : Prop :=
  ∀ t ∈ trees, ∃ d, Summarizes t (.selected d)

private theorem child_summaries_all_successful413 {trees results}
    (summary : All₂ Summarizes trees results)
    (all : ∀ r ∈ results, ∃ d, r = .selected d) : SuccessfulChildren413 trees := by
  induction summary with
  | nil => intro t bad; cases bad
  | cons first _ ih =>
    intro t atTree
    rcases List.mem_cons.mp atTree with here|later
    · cases here
      obtain ⟨d,status⟩ := all _ List.mem_cons_self
      exact ⟨d,status ▸ first⟩
    · exact ih (fun r passed => all r (List.mem_cons_of_mem _ passed)) t later

private theorem all_from_dictionary_results413 (ds : List Dictionary) :
    ∀ r ∈ ds.map Result.selected, ∃ d, r = .selected d := by
  intro r entry
  obtain ⟨d,_,rfl⟩ := List.mem_map.mp entry
  exact ⟨d,rfl⟩

/-- Adding only a new local rejected head cannot create a successful
dictionary. At every selected child and each support producer, keep
the original event, source request, body address, output evidence and
literal write list. This is a relation between rule sets, not solver
completeness or a statement about obtaining a witness. -/
noncomputable def previous_success_trace413 {s q t e}
    (original : SourceTrace R5 s q t e) :
    ∀ d, Summarizes t (.selected d) →
      {old : SourceTrace RecordK2412.R4 s q t e // RecordK2412.writes old = writes original} := by
  exact SourceTrace.rec (R := R5) (s := s)
    (motive_1 := fun q t e tr => ∀ d, Summarizes t (.selected d) →
      {old : SourceTrace RecordK2412.R4 s q t e // RecordK2412.writes old = writes tr})
    (motive_2 := fun qs trees f => SuccessfulChildren413 trees →
      {old : WhereForest RecordK2412.R4 s qs trees //
        RecordK2412.forestWrites old = forestWrites f})
    (motive_3 := fun needs _ => SupportForest RecordK2412.R4 s needs)
    (fun _ _ summary => False.elim (by cases summary))
    (fun v _ _ _ _ _ summary => False.elim (by cases v <;> cases summary))
    (fun {_} {_} {trees} e safe localRule _ next support kids _ summary => by
      have actualKids : SuccessfulChildren413 trees := by
        cases summary with
        | selected pair combines =>
          cases combines with
          | selected all =>
            rw [all] at pair
            exact child_summaries_all_successful413 pair (all_from_dictionary_results413 _)
      let kept := kids actualKids
      refine ⟨.selected e safe localRule support kept.val,?_⟩
      change Check408.encodedEventWrites e ++ RecordK2412.forestWrites kept.val =
        Check408.encodedEventWrites e ++ forestWrites next
      rw [kept.property])
    (fun _ => ⟨.nil,rfl⟩)
    (fun first rest head tail all => by
      have found := all _ List.mem_cons_self
      let a := head (Classical.choose found) (Classical.choose_spec found)
      let b := tail (fun t included => all t (List.mem_cons_of_mem _ included))
      refine ⟨.cons a.val b.val,?_⟩
      change RecordK2412.writes a.val ++ RecordK2412.forestWrites b.val =
        writes first ++ forestWrites rest
      rw [a.property,b.property])
    .nil
    (fun _ summary emitted _ producer rest => .cons (producer _ summary).val summary emitted rest)
    original

theorem selected_exact_reports_conservative413 {s q r d}
    (exactSelection : r.verdict = .selected d) :
    ClassifiedAs s q r ↔ RecordK2412.ClassifiedAs s q r := by
  constructor
  · rintro ⟨e,tree,summary,out⟩
    have actual : Summarizes r.tree (.selected d) := exactSelection ▸ summary
    let previous := previous_success_trace413 tree d actual
    exact ⟨e,previous.val,summary,out.trans previous.property.symm⟩
  · exact existing_exact_report_lifts413

theorem selected_classification_conservative413 {s q d} :
    Classifies R5 s q (.selected d) ↔ Classifies RecordK2412.R4 s q (.selected d) := by
  constructor
  · rintro ⟨t,e,⟨trace⟩,done⟩
    exact ⟨t,e,⟨(previous_success_trace413 trace d done).val⟩,done⟩
  · rintro ⟨t,e,⟨trace⟩,done⟩
    exact ⟨t,e,⟨(liftTrace trace).val⟩,done⟩

end Yulang.GeneralDeclarativeI65.I72.MixedRecord413
