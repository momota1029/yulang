import Yulang.GeneralDeclarativeI65I74WhereForest450

namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Tree Dictionary Summarizes)
open Check408 (Write Result)
open RetainedFull445
open GeneralDeclarations (Declaration)
open Checker408 (Problem)

noncomputable def writes {s q t e} (trace : SourceTrace parentWhereRule450 s q t e) : List Write :=
  SourceTrace.rec (R := parentWhereRule450) (s := s)
    (motive_1 := fun _ _ _ _ => List Write)
    (motive_2 := fun _ _ _ => List Write)
    (motive_3 := fun _ _ => Unit)
    (fun _ => []) (fun _ _ _ _ _ => [])
    (fun event _ _ _ _ _ kids => Check408.encodedEventWrites event ++ kids)
    [] (fun _ _ a b => a ++ b)
    () (fun _ _ _ _ _ _ => ()) trace

noncomputable def forestWrites {s qs ts} (forest : WhereForest parentWhereRule450 s qs ts) : List Write :=
  WhereForest.rec (R := parentWhereRule450) (s := s)
    (motive_1 := fun _ _ _ _ => List Write)
    (motive_2 := fun _ _ _ => List Write)
    (motive_3 := fun _ _ => Unit)
    (fun _ => []) (fun _ _ _ _ _ => [])
    (fun event _ _ _ _ _ kids => Check408.encodedEventWrites event ++ kids)
    [] (fun _ _ a b => a ++ b)
    () (fun _ _ _ _ _ _ => ()) forest

mutual
/-- Model meaning at the *same* reported trace. Local facts and fixed
writes are checked even before the where tree's summary; the
dictionary conclusion is attached to every successful subtree. -/
inductive TraceMeaning (s : I72.State) (m : I72.Model) :
    {q : I72.Request} → {t : Tree} → {e : Option (Event s q)} →
    SourceTrace parentWhereRule450 s q t e → Prop where
  | raw {q} {cycle : RootCycle s q} :
      TraceMeaning s m (.rootK2 cycle)
  | other {q needs verdict safe} {localRule : parentWhereRule450.other s q verdict needs}
      {support : SupportForest parentWhereRule450 s needs} :
      TraceMeaning s m (.other verdict safe localRule support)
  | node {q needs trees} {e : Event s q} {safe : ¬RootCycle s q}
      {localRule : parentWhereRule450.elected s q e needs} {support : SupportForest parentWhereRule450 s needs}
      {kids : WhereForest parentWhereRule450 s e.kids trees} :
      LocalMeaning m e → FixedTargets m e → ForestMeaning s m kids →
      (∀ d, Summarizes (.selected e.frame.decl.id trees) (.selected d) →
        DictionaryEvidence s m q d) →
      TraceMeaning s m (.selected e safe localRule support kids)

inductive ForestMeaning (s : I72.State) (m : I72.Model) :
    {qs : List I72.Request} → {ts : List Tree} → WhereForest parentWhereRule450 s qs ts → Prop where
  | nil : ForestMeaning s m .nil
  | cons {q t event qs ts} {first : SourceTrace parentWhereRule450 s q t event}
      {rest : WhereForest parentWhereRule450 s qs ts} :
      TraceMeaning s m first → ForestMeaning s m rest → ForestMeaning s m (.cons first rest)
end

def ReportEvidence (s : I72.State) (m : I72.Model) (q : I72.Request) (r : Result) : Prop :=
  ∃ e, ∃ actual : SourceTrace parentWhereRule450 s q r.tree e,
    Summarizes r.tree r.verdict ∧ r.writes = writes actual ∧ TraceMeaning s m actual

theorem exact_where_trace_model_meaning450 {s q t e} (trace : SourceTrace parentWhereRule450 s q t e)
    (m : I72.Model) (fit : Fits s m) : TraceMeaning s m trace := by
  exact SourceTrace.rec (R := parentWhereRule450) (s := s)
    (motive_1 := fun _ _ _ actual => TraceMeaning s m actual)
    (motive_2 := fun _ _ children => ForestMeaning s m children)
    (motive_3 := fun _ _ => True)
    (fun _ => .raw) (fun _ _ _ _ _ => .other)
    (fun {q} {needs} {trees} event safe localRule support kids _ below => by
      have localData := parent_where_local_evidence450 s q event needs localRule
      refine .node (semantic_node_in_signature s q event localData.1 m fit)
        (localData.2.elim (fun plain => retained_variable_targets_sound403 plain m fit)
          (fun typed => retained_typed_rows_satisfy_fixed_targets403 typed m fit)) below ?_
      intro d summaries
      exact dictionary_sound_parent_where450 s q d ⟨_,_,⟨.selected event safe localRule support kids⟩,summaries⟩ m fit)
    .nil (fun _ _ first rest => .cons first rest)
    True.intro (fun _ _ _ _ _ _ => True.intro) trace


structure OriginalRejection (p : Problem) where
  parent : ParentSelection p
  trees : List Tree
  plan : OrderedPlan p.state parent.children trees
  containsRaw : .rejected ∈ trees

def OriginalRejection.report {p : Problem} (a : OriginalRejection p) : Result :=
  ⟨.selected a.parent.decl.id a.trees,.rejected,[]⟩

def ExactReport (p : Problem) (r : Result) : Prop :=
  ∃ ev, ∃ tr : SourceTrace parentWhereRule450 p.state p.root r.tree ev,
    Summarizes r.tree r.verdict ∧ r.writes = writes tr

theorem parent_rule_writes_none450 {s q e needs} (h : parentWhereRule450.elected s q e needs) :
    Check408.encodedEventWrites e = [] := by
  have absent : q.demand.outputs = [] := by
    rcases h.2 with ⟨a,_,_⟩|⟨_,a,_,_⟩
    · exact a.chosen.noOutputs
    · exact a.chosen.noOutputs
  exact List.length_eq_zero_iff.mp (by simp [Check408.encodedEventWrites,absent])

theorem all_scoped_traces_have_no_writes450 {s q t e}
    (trace : SourceTrace parentWhereRule450 s q t e) : writes trace = [] := by
  exact SourceTrace.rec (R := parentWhereRule450) (s := s)
    (motive_1 := fun _ _ _ tr => writes tr = [])
    (motive_2 := fun _ _ forest => forestWrites forest = [])
    (motive_3 := fun _ _ => True)
    (fun _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun event _ localRule _ kids _ below => by
      change Check408.encodedEventWrites event ++ forestWrites kids = []
      rw [parent_rule_writes_none450 localRule, below]
      rfl)
    rfl (fun first rest a b => by
      change writes first ++ forestWrites rest = []
      rw [a,b]; rfl)
    True.intro (fun _ _ _ _ _ _ => True.intro) trace

theorem independent_original_rejection_has_real_trace450 {p : Problem} (a : OriginalRejection p) :
    ExactReport p a.report := by
  let parent := a.parent
  obtain ⟨source⟩ := selected_head_original_origin395
    (actual_single_declaration_list_frame_is_settled450 parent.chosen)
  let e := parent.event source
  obtain ⟨children⟩ := a.plan.forestSound
  let kids : WhereForest parentWhereRule450 p.state e.kids a.trees :=
    (literal_parent_reconstructs_all_original_children450 parent source).symm ▸ children
  let tr : SourceTrace parentWhereRule450 p.state p.root a.report.tree (some e) :=
    .selected e parent.chosen.safe ⟨rfl,.inl ⟨parent,source,rfl⟩⟩ .nil kids
  exact ⟨some e,tr,where_summary_keeps_every_child450 _ a.containsRaw,
    (all_scoped_traces_have_no_writes450 tr).symm⟩

def ClassifiedAs450 (p : FullProblem) (r : Result) : Prop :=
  ListSites449.Frame.ClassifiedAs449 p r ∨ (∃ a : OriginalRejection p.old, r = a.report)

def ReportEvidence450 (p : FullProblem) (m : I72.Model) (r : Result) : Prop :=
  ListSites449.Frame.ReportEvidence449 p m r ∨ ReportEvidence p.state.base m p.root r

structure WhereWire where
  parent : ParentWire
  children : List ChildWire

inductive Witness where
  | previous (w : ListSites449.Frame.Witness)
  | whereRoot (w : WhereWire)

/-- Wire contains only indices and raw evidence; child roles, occurrences and
raw demanded roots are read from all actual original parent clauses in order. -/
def check_full450 (p : FullProblem) (r : Result) : Witness → Bool
  | .previous w => ListSites449.Frame.check_full449 p r w
  | .whereRoot w =>
    match whole : visible p.state.base.core p.root with
    | [d] =>
      match readParentChoice p.old d whole w.parent with
      | none => false
      | some read =>
        let parent : ParentSelection p.old := ⟨d,read⟩
        match readOrdered p.state.base parent.children w.children with
        | none => false
        | some ⟨trees,_⟩ => hasRawRejection trees &&
            Check408.matchesNoWrites r (.selected d.id trees) .rejected
    | _ => false

theorem all_previous_witnesses_unchanged450 (p : FullProblem) (r : Result) (w : ListSites449.Frame.Witness) :
    check_full450 p r (.previous w) = ListSites449.Frame.check_full449 p r w := rfl

theorem only_true_original_ordered_reports_are_accepted450 {p r w}
    (yes : check_full450 p r (.whereRoot w) = true) :
    ∃ a : OriginalRejection p.old, r = a.report ∧
      readParentChoice p.old a.parent.decl a.parent.chosen.only w.parent = some a.parent.chosen ∧
      readOrdered p.state.base a.parent.children w.children = some ⟨a.trees,a.plan⟩ := by
  simp only [check_full450] at yes
  split at yes
  · rename_i d all
    split at yes
    · cases yes
    · rename_i label read readParent
      split at yes
      · cases yes
      · rename_i first trees plan readPlan
        obtain ⟨cycling,content⟩ := Bool.and_eq_true_iff.mp yes
        let source : OriginalRejection p.old :=
          ⟨⟨d,read⟩,trees,plan,(raw_rejection_is_same_position450 _).mp cycling⟩
        obtain ⟨tree,verdict,writes⟩ := Check408.matchesNoWrites_exact408.mp content
        have exactReport : r = source.report := by
          cases r
          simp only at tree verdict writes
          subst_vars
          rfl
        exact ⟨source,exactReport,readParent,readPlan⟩
  · cases yes

theorem original_ordered_rejection_reifies_same_report450 (p : FullProblem)
    (a : OriginalRejection p.old) : ∃ w, check_full450 p a.report (.whereRoot w) = true := by
  obtain ⟨parent,parentOK⟩ := independent_list_frame_replays_exactly450 a.parent.chosen
  obtain ⟨ws,kidsOK⟩ := all_original_children_have_ordered_wires450 a.plan
  refine ⟨⟨parent,ws⟩,?_⟩
  simp only [check_full450]
  split
  · rename_i d roster
    have same : d = a.parent.decl := List.singleton_inj.mp (roster.symm.trans a.parent.chosen.only)
    subst d
    rw [parentOK]
    cases a with
    | mk par trees plan containsRaw =>
      cases par with
      | mk decl chosen =>
        dsimp only at kidsOK ⊢
        have readBack : readOrdered p.state.base (ParentSelection.children ⟨decl,chosen⟩) ws = some ⟨trees,plan⟩ := kidsOK
        rw [readBack]
        exact Bool.and_eq_true_iff.mpr ⟨(raw_rejection_is_same_position450 _).mpr containsRaw,
          Check408.matchesNoWrites_exact408.mpr ⟨rfl,rfl,rfl⟩⟩
  · rename_i missing
    exact (missing _ a.parent.chosen.only).elim


theorem exact_original_where_report_iff_finite_only_data450 (p : FullProblem) (r : Result) :
    (∃ w, check_full450 p r (.whereRoot w) = true) ↔
      ∃ a : OriginalRejection p.old, r = a.report := by
  constructor
  · rintro ⟨w,ok⟩
    obtain ⟨a,report,_,_⟩ := only_true_original_ordered_reports_are_accepted450 ok
    exact ⟨a,report⟩
  · rintro ⟨a,rfl⟩
    exact original_ordered_rejection_reifies_same_report450 p a

theorem actual_parent_K2_cannot_be_relabelled_as_child450 {p : FullProblem}
    (cycle : RootCycle p.state.base p.root) (r : Result) (w : WhereWire) :
    check_full450 p r (.whereRoot w) = false := by
  cases tried : check_full450 p r (.whereRoot w) with
  | false => rfl
  | true =>
    obtain ⟨a,_,_,_⟩ := only_true_original_ordered_reports_are_accepted450 tried
    exact (a.parent.chosen.safe cycle).elim

theorem check_full_sound450 (p : FullProblem) (r : Result) (w : Witness)
    (ok : check_full450 p r w = true) :
    ClassifiedAs450 p r ∧ ∀ m, FitsFull p.state m → ReportEvidence450 p m r := by
  cases w with
  | previous w =>
    have old := ListSites449.Frame.check_full_sound449 p r w ok
    exact ⟨.inl old.1,fun m h => .inl (old.2 m h)⟩
  | whereRoot w =>
    obtain ⟨a,rfl,_,_⟩ := only_true_original_ordered_reports_are_accepted450 ok
    obtain ⟨e,tr,sum,intact⟩ := independent_original_rejection_has_real_trace450 a
    exact ⟨.inr ⟨a,rfl⟩,fun m fit =>
      .inr ⟨e,tr,sum,intact,exact_where_trace_model_meaning450 tr m fit.1⟩⟩
end Yulang.GeneralDeclarativeI65.I72.WhereSites450
