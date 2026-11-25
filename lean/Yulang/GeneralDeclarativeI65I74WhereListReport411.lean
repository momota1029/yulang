import Yulang.GeneralDeclarativeI65I74WhereListRule411

namespace Yulang.GeneralDeclarativeI65.I72.WhereCycle411
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Tree Dictionary Summarizes)
open Check408 (Write Result)
open Checker408 (Problem)

noncomputable def writes {s q t e} (trace : SourceTrace R3 s q t e) : List Write :=
  SourceTrace.rec (R := R3) (s := s)
    (motive_1 := fun _ _ _ _ => List Write)
    (motive_2 := fun _ _ _ => List Write)
    (motive_3 := fun _ _ => Unit)
    (fun _ => []) (fun _ _ _ _ _ => [])
    (fun event _ _ _ _ _ kids => Check408.encodedEventWrites event ++ kids)
    [] (fun _ _ a b => a ++ b)
    () (fun _ _ _ _ _ _ => ()) trace

noncomputable def forestWrites {s qs ts} (forest : WhereForest R3 s qs ts) : List Write :=
  WhereForest.rec (R := R3) (s := s)
    (motive_1 := fun _ _ _ _ => List Write)
    (motive_2 := fun _ _ _ => List Write)
    (motive_3 := fun _ _ => Unit)
    (fun _ => []) (fun _ _ _ _ _ => [])
    (fun event _ _ _ _ _ kids => Check408.encodedEventWrites event ++ kids)
    [] (fun _ _ a b => a ++ b)
    () (fun _ _ _ _ _ _ => ()) forest

/-- Preserve all old local proofs and the literal report; recursive source
dependencies are transported, not read again against a different State. -/
noncomputable def liftTrace {s q t e} (trace : SourceTrace List410.R2 s q t e) :
    {a : SourceTrace R3 s q t e // writes a = List410.writes trace} := by
  exact SourceTrace.rec (R := List410.R2) (s := s)
    (motive_1 := fun q t e old => {a : SourceTrace R3 s q t e // writes a = List410.writes old})
    (motive_2 := fun qs ts old => {a : WhereForest R3 s qs ts // forestWrites a = List410.forestWrites old})
    (motive_3 := fun needs _ => SupportForest R3 s needs)
    (fun cycle => ⟨.rootK2 cycle,rfl⟩)
    (fun verdict safe localRule _ lower => ⟨.other verdict safe localRule lower,rfl⟩)
    (fun event safe localRule _ oldKids lower children =>
      ⟨.selected event safe (.inl localRule) lower children.val,by
        change Check408.encodedEventWrites event ++ forestWrites children.val =
          Check408.encodedEventWrites event ++ List410.forestWrites oldKids
        rw [children.property]⟩)
    ⟨.nil,rfl⟩
    (fun oldA oldB a b => ⟨.cons a.val b.val,by
      change writes a.val ++ forestWrites b.val = List410.writes oldA ++ List410.forestWrites oldB
      rw [a.property,b.property]⟩)
    .nil
    (fun _ done emit _ lower rest => .cons lower done emit rest)
    trace

def ClassifiedAs (s : I72.State) (q : I72.Request) (r : Result) : Prop :=
  ∃ e, ∃ actual : SourceTrace R3 s q r.tree e,
    Summarizes r.tree r.verdict ∧ r.writes = writes actual

theorem existing_exact_report_lifts411 {s q r} (old : List410.ClassifiedAs s q r) :
    ClassifiedAs s q r := by
  obtain ⟨e,trace,summary,written⟩ := old
  let lifted := liftTrace trace
  exact ⟨e,lifted.val,summary,written.trans lifted.property.symm⟩

theorem exact_report_is_R3_classification411 {s q r} (classification : ClassifiedAs s q r) :
    I72.Classifies R3 s q r.verdict := by
  obtain ⟨e,trace,summary,_⟩ := classification
  exact ⟨r.tree,e,⟨trace⟩,summary⟩

mutual
/-- Model meaning at the *same* reported trace. Local facts and fixed
writes are checked even before the where tree's summary; the
dictionary conclusion is attached to every successful subtree. -/
inductive TraceMeaning (s : I72.State) (m : I72.Model) :
    {q : I72.Request} → {t : Tree} → {e : Option (Event s q)} →
    SourceTrace R3 s q t e → Prop where
  | raw {q} {cycle : RootCycle s q} :
      TraceMeaning s m (.rootK2 cycle)
  | other {q needs verdict safe} {localRule : R3.other s q verdict needs}
      {support : SupportForest R3 s needs} :
      TraceMeaning s m (.other verdict safe localRule support)
  | node {q needs trees} {e : Event s q} {safe : ¬RootCycle s q}
      {localRule : R3.elected s q e needs} {support : SupportForest R3 s needs}
      {kids : WhereForest R3 s e.kids trees} :
      LocalMeaning m e → FixedTargets m e → ForestMeaning s m kids →
      (∀ d, Summarizes (.selected e.frame.decl.id trees) (.selected d) →
        DictionaryEvidence s m q d) →
      TraceMeaning s m (.selected e safe localRule support kids)

inductive ForestMeaning (s : I72.State) (m : I72.Model) :
    {qs : List I72.Request} → {ts : List Tree} → WhereForest R3 s qs ts → Prop where
  | nil : ForestMeaning s m .nil
  | cons {q t event qs ts} {first : SourceTrace R3 s q t event}
      {rest : WhereForest R3 s qs ts} :
      TraceMeaning s m first → ForestMeaning s m rest → ForestMeaning s m (.cons first rest)
end

def ReportEvidence (s : I72.State) (m : I72.Model) (q : I72.Request) (r : Result) : Prop :=
  ∃ e, ∃ actual : SourceTrace R3 s q r.tree e,
    Summarizes r.tree r.verdict ∧ r.writes = writes actual ∧ TraceMeaning s m actual

theorem mixed_R3_trace_model_meaning411 {s q t e} (trace : SourceTrace R3 s q t e)
    (m : I72.Model) (fit : Fits s m) : TraceMeaning s m trace := by
  exact SourceTrace.rec (R := R3) (s := s)
    (motive_1 := fun _ _ _ actual => TraceMeaning s m actual)
    (motive_2 := fun _ _ children => ForestMeaning s m children)
    (motive_3 := fun _ _ => True)
    (fun _ => .raw) (fun _ _ _ _ _ => .other)
    (fun {q} {needs} {trees} event safe localRule support kids _ below => by
      have localData := R3_local_evidence411 s q event needs localRule
      refine .node (semantic_node_in_signature s q event localData.1 m fit)
        (localData.2.elim (fun plain => retained_variable_targets_sound403 plain m fit)
          (fun typed => retained_typed_rows_satisfy_fixed_targets403 typed m fit)) below ?_
      intro d summaries
      exact dictionary_sound_R3 s q d ⟨_,_,⟨.selected event safe localRule support kids⟩,summaries⟩ m fit)
    .nil (fun _ _ first rest => .cons first rest)
    True.intro (fun _ _ _ _ _ _ => True.intro) trace


end Yulang.GeneralDeclarativeI65.I72.WhereCycle411
