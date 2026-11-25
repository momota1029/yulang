import Yulang.GeneralDeclarativeI65I74ExplicitPickRule419

namespace Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Tree Dictionary Summarizes)
open Check408 (Write Result)
open Checker408 (Problem)

noncomputable def writes {s q t e} (trace : SourceTrace R11 s q t e) : List Write :=
  SourceTrace.rec (R := R11) (s := s)
    (motive_1 := fun _ _ _ _ => List Write)
    (motive_2 := fun _ _ _ => List Write)
    (motive_3 := fun _ _ => Unit)
    (fun _ => []) (fun _ _ _ _ _ => [])
    (fun event _ _ _ _ _ kids => Check408.encodedEventWrites event ++ kids)
    [] (fun _ _ a b => a ++ b)
    () (fun _ _ _ _ _ _ => ()) trace

noncomputable def forestWrites {s qs ts} (forest : WhereForest R11 s qs ts) : List Write :=
  WhereForest.rec (R := R11) (s := s)
    (motive_1 := fun _ _ _ _ => List Write)
    (motive_2 := fun _ _ _ => List Write)
    (motive_3 := fun _ _ => Unit)
    (fun _ => []) (fun _ _ _ _ _ => [])
    (fun event _ _ _ _ _ kids => Check408.encodedEventWrites event ++ kids)
    [] (fun _ _ a b => a ++ b)
    () (fun _ _ _ _ _ _ => ()) forest

/-- Preserve all old local proofs and the literal report; recursive source
dependencies are transported, not read again against a different State. -/
noncomputable def liftTrace {s q t e} (trace : SourceTrace RigidRival418.R10 s q t e) :
    {a : SourceTrace R11 s q t e // writes a = RigidRival418.writes trace} := by
  exact SourceTrace.rec (R := RigidRival418.R10) (s := s)
    (motive_1 := fun q t e old => {a : SourceTrace R11 s q t e // writes a = RigidRival418.writes old})
    (motive_2 := fun qs ts old => {a : WhereForest R11 s qs ts // forestWrites a = RigidRival418.forestWrites old})
    (motive_3 := fun needs _ => SupportForest R11 s needs)
    (fun cycle => ⟨.rootK2 cycle,rfl⟩)
    (fun verdict safe localRule _ lower => ⟨.other verdict safe localRule lower,rfl⟩)
    (fun event safe localRule _ oldKids lower children =>
      ⟨.selected event safe (.inl localRule) lower children.val,by
        change Check408.encodedEventWrites event ++ forestWrites children.val =
          Check408.encodedEventWrites event ++ RigidRival418.forestWrites oldKids
        rw [children.property]⟩)
    ⟨.nil,rfl⟩
    (fun oldA oldB a b => ⟨.cons a.val b.val,by
      change writes a.val ++ forestWrites b.val = RigidRival418.writes oldA ++ RigidRival418.forestWrites oldB
      rw [a.property,b.property]⟩)
    .nil
    (fun _ done emit _ lower rest => .cons lower done emit rest)
    trace

def ClassifiedAs (s : I72.State) (q : I72.Request) (r : Result) : Prop :=
  ∃ e, ∃ actual : SourceTrace R11 s q r.tree e,
    Summarizes r.tree r.verdict ∧ r.writes = writes actual

theorem existing_exact_report_lifts419 {s q r} (old : RigidRival418.ClassifiedAs s q r) :
    ClassifiedAs s q r := by
  obtain ⟨e,trace,summary,written⟩ := old
  let lifted := liftTrace trace
  exact ⟨e,lifted.val,summary,written.trans lifted.property.symm⟩

theorem exact_report_is_R11_classification419 {s q r} (classification : ClassifiedAs s q r) :
    I72.Classifies R11 s q r.verdict := by
  obtain ⟨e,trace,summary,_⟩ := classification
  exact ⟨r.tree,e,⟨trace⟩,summary⟩

mutual
/-- Model meaning at the *same* reported trace. Local facts and fixed
writes are checked even before the where tree's summary; the
dictionary conclusion is attached to every successful subtree. -/
inductive TraceMeaning (s : I72.State) (m : I72.Model) :
    {q : I72.Request} → {t : Tree} → {e : Option (Event s q)} →
    SourceTrace R11 s q t e → Prop where
  | raw {q} {cycle : RootCycle s q} :
      TraceMeaning s m (.rootK2 cycle)
  | other {q needs verdict safe} {localRule : R11.other s q verdict needs}
      {support : SupportForest R11 s needs} :
      TraceMeaning s m (.other verdict safe localRule support)
  | node {q needs trees} {e : Event s q} {safe : ¬RootCycle s q}
      {localRule : R11.elected s q e needs} {support : SupportForest R11 s needs}
      {kids : WhereForest R11 s e.kids trees} :
      LocalMeaning m e → FixedTargets m e → ForestMeaning s m kids →
      (∀ d, Summarizes (.selected e.frame.decl.id trees) (.selected d) →
        DictionaryEvidence s m q d) →
      TraceMeaning s m (.selected e safe localRule support kids)

inductive ForestMeaning (s : I72.State) (m : I72.Model) :
    {qs : List I72.Request} → {ts : List Tree} → WhereForest R11 s qs ts → Prop where
  | nil : ForestMeaning s m .nil
  | cons {q t event qs ts} {first : SourceTrace R11 s q t event}
      {rest : WhereForest R11 s qs ts} :
      TraceMeaning s m first → ForestMeaning s m rest → ForestMeaning s m (.cons first rest)
end

def ReportEvidence (s : I72.State) (m : I72.Model) (q : I72.Request) (r : Result) : Prop :=
  ∃ e, ∃ actual : SourceTrace R11 s q r.tree e,
    Summarizes r.tree r.verdict ∧ r.writes = writes actual ∧ TraceMeaning s m actual

theorem pick_R11_trace_model_meaning419 {s q t e} (trace : SourceTrace R11 s q t e)
    (m : I72.Model) (fit : Fits s m) : TraceMeaning s m trace := by
  exact SourceTrace.rec (R := R11) (s := s)
    (motive_1 := fun _ _ _ actual => TraceMeaning s m actual)
    (motive_2 := fun _ _ children => ForestMeaning s m children)
    (motive_3 := fun _ _ => True)
    (fun _ => .raw) (fun _ _ _ _ _ => .other)
    (fun {q} {needs} {trees} event safe localRule support kids _ below => by
      have localData := selected_pick_local_sound419 localRule m fit
      refine .node localData.1 localData.2 below ?_
      intro d summaries
      exact dictionary_sound_R11 s q d ⟨_,_,⟨.selected event safe localRule support kids⟩,summaries⟩ m fit)
    .nil (fun _ _ first rest => .cons first rest)
    True.intro (fun _ _ _ _ _ _ => True.intro) trace


end Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
