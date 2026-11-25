import Yulang.GeneralDeclarativeI65I73UnifiedAcceptance408

namespace Yulang.GeneralDeclarativeI65.I72.Check408
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Tree Dictionary Summarizes)

mutual
/-- Model meaning at the *same* reported trace. Local facts and fixed
writes are checked even before the where tree's summary; the
dictionary conclusion is attached to every successful subtree. -/
inductive TraceMeaning (s : I72.State) (m : I72.Model) :
    {q : I72.Request} → {t : Tree} → {e : Option (Event s q)} →
    SourceTrace R0 s q t e → Prop where
  | raw {q} {cycle : RootCycle s q} :
      TraceMeaning s m (.rootK2 cycle)
  | other {q needs verdict safe} {localRule : R0.other s q verdict needs}
      {support : SupportForest R0 s needs} :
      TraceMeaning s m (.other verdict safe localRule support)
  | node {q needs trees} {e : Event s q} {safe : ¬RootCycle s q}
      {localRule : R0.elected s q e needs} {support : SupportForest R0 s needs}
      {kids : WhereForest R0 s e.kids trees} :
      LocalMeaning m e → FixedTargets m e → ForestMeaning s m kids →
      (∀ d, Summarizes (.selected e.frame.decl.id trees) (.selected d) →
        DictionaryEvidence s m q d) →
      TraceMeaning s m (.selected e safe localRule support kids)

inductive ForestMeaning (s : I72.State) (m : I72.Model) :
    {qs : List I72.Request} → {ts : List Tree} → WhereForest R0 s qs ts → Prop where
  | nil : ForestMeaning s m .nil
  | cons {q t event qs ts} {first : SourceTrace R0 s q t event}
      {rest : WhereForest R0 s qs ts} :
      TraceMeaning s m first → ForestMeaning s m rest → ForestMeaning s m (.cons first rest)
end

def ReportEvidence (s : I72.State) (m : I72.Model) (q : I72.Request) (r : Result) : Prop :=
  ∃ e, ∃ actual : SourceTrace R0 s q r.tree e,
    Summarizes r.tree r.verdict ∧ r.writes = traceWrites actual ∧ TraceMeaning s m actual

theorem mixed_R0_trace_model_meaning408 {s q t e} (trace : SourceTrace R0 s q t e)
    (m : I72.Model) (fit : Fits s m) : TraceMeaning s m trace := by
  exact SourceTrace.rec (R := R0) (s := s)
    (motive_1 := fun _ _ _ actual => TraceMeaning s m actual)
    (motive_2 := fun _ _ children => ForestMeaning s m children)
    (motive_3 := fun _ _ => True)
    (fun _ => .raw) (fun _ _ _ _ _ => .other)
    (fun {q} {needs} {trees} event safe localRule support kids _ below => by
      have localData := R0_elected_has_local_evidence407 s q event needs localRule
      refine .node (semantic_node_in_signature s q event localData.1 m fit)
        (localData.2.elim (fun plain => retained_variable_targets_sound403 plain m fit)
          (fun typed => retained_typed_rows_satisfy_fixed_targets403 typed m fit)) below ?_
      intro d summaries
      exact dictionary_sound_R0 s q d ⟨_,_,⟨.selected event safe localRule support kids⟩,summaries⟩ m fit)
    .nil (fun _ _ first rest => .cons first rest)
    True.intro (fun _ _ _ _ _ _ => True.intro) trace

/-- The fixed I-65(3) shape. The model is universally quantified over
the same input and the exact reported trace/receipts are used. A false
checker result still says nothing about language resolution. -/
theorem check_sound (p : Problem) (r : Result) (w : Witness)
    (accepted : check p r w = true) :
    ClassifiedAs p.state p.root r ∧
      ∀ (m : I72.Model), Fits p.state m → ReportEvidence p.state m p.root r := by
  have hope := check_reflects_same_original_report408 p r w accepted
  refine ⟨hope,?_⟩
  obtain ⟨e,trace,summary,writes⟩ := hope
  exact fun m fit => ⟨e,trace,summary,writes,mixed_R0_trace_model_meaning408 trace m fit⟩

theorem accepted_selected_dictionary_in_every_model408 (p : Problem) (r : Result) (w : Witness)
    (accepted : check p r w = true) (d : Dictionary) (selected : r.verdict = .selected d) :
    ∀ m : I72.Model, Fits p.state m → DictionaryEvidence p.state m p.root d := by
  have actual := exact_report_is_R0_classification408 (check_sound p r w accepted).1
  rw [selected] at actual
  exact dictionary_sound_R0 _ _ _ actual

end Yulang.GeneralDeclarativeI65.I72.Check408
