import Yulang.GeneralDeclarativeI65I74WhereInternalK2452

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.LiteralAndInternal452
open Yulang.GeneralDeclarativeI65
open CommonRoleOutermostResolver (Tree)
open ListSites449.Frame (FrameWire FramedSelection readListFrameChoice)
open RetainedFull445
open InternalK2452
open Checker408 (Result)

inductive AdditionalChoice where
  | useRawStatus
  | leaf (data : FrameWire)

/-- A raw-safe mark is not a successful selection. This separate
wire is checked only for a genuinely authored same-state safe leaf. -/
def resolveLiteralChild {s q b} (r : RawRead s q b) : AdditionalChoice → Option (Σ t, ChildPlan s q t)
  | .useRawStatus =>
    match r with
    | .cycle h => some ⟨.rejected,.cycle h⟩
    | .safe _ => none
  | .leaf w =>
    match r with
    | .cycle _ => none
    | .safe _ => readChild s q (.leaf w)

theorem remove_repeated_cycle_input_preserves_actual_plan452 {s q b t} (r : RawRead s q b)
    (a : ChildPlan s q t) : ∃ w, resolveLiteralChild r w = some ⟨t,a⟩ := by
  cases r with
  | cycle cy =>
    cases a with
    | cycle a => exact ⟨.useRawStatus,rfl⟩
    | leaf leaf => exact (leaf.chosen.safe cy).elim
  | safe no =>
    cases a with
    | cycle cy => exact (no cy).elim
    | leaf framed =>
      obtain ⟨w,yes⟩ := ListSites449.Frame.independent_list_frame_replays_exactly449 framed.chosen
      refine ⟨.leaf w,?_⟩
      simp only [resolveLiteralChild,readChild]
      split
      · rename_i d witnessed
        have same := List.singleton_inj.mp (witnessed.symm.trans framed.chosen.only)
        subst d
        rw [yes]
        rfl
      · rename_i lost
        exact (lost _ framed.chosen.only).elim

def replayLiteralChildPlans {s qs bs} (r : RawStatuses s qs bs) :
    List AdditionalChoice → Option (Σ ts, OrderedPlan s qs ts) :=
  match r with
  | .nil => fun ws => if ws.isEmpty then some ⟨[],.nil⟩ else none
  | .cons h t => fun ws =>
    match ws with
    | [] => none
    | w::ws => do
      let ⟨x,first⟩ ← resolveLiteralChild h w
      let ⟨xs,rest⟩ ← replayLiteralChildPlans t ws
      pure ⟨x::xs,.cons first rest⟩

theorem same_status_lifts_any_actual_supported_ordered_plan452 {s qs bs ts}
    (status : RawStatuses s qs bs) (choice : OrderedPlan s qs ts) :
    ∃ ws, replayLiteralChildPlans status ws = some ⟨ts,choice⟩ := by
  induction choice generalizing bs with
  | nil =>
    cases status
    exact ⟨[],rfl⟩
  | cons head _ ih =>
    cases status with
    | cons r tail =>
      obtain ⟨w,ro⟩ := remove_repeated_cycle_input_preserves_actual_plan452 r head
      obtain ⟨ws,rs⟩ := ih tail
      exact ⟨w::ws,by simp [replayLiteralChildPlans,ro,rs,Bind.bind,Option.bind,Option.pure_def]⟩

structure ScopedLiteralInput where
  original : SourceDiagnosticWire
  extra : List AdditionalChoice

structure ScopedLiteralReport (p : FullProblem) where
  actual : AnnotatedOriginalDiagnostics p.old
  localK2 : OriginalRejection p.old
  sameOriginal : localK2.parent = actual.parent

def ScopedLiteralReport.internal {p : FullProblem} (q : ScopedLiteralReport p) : InternalReport p :=
  ⟨q.actual⟩

def readScopedLiteralReport (p : FullProblem) (wire : ScopedLiteralInput) :
    Option (ScopedLiteralReport p) := do
  let actual ← readOriginalWhereProfiles451 p wire.original
  let ⟨ts,plan⟩ ← replayLiteralChildPlans actual.diagnostics.status wire.extra
  if k2 : hasRawRejection ts = true then
    some ⟨actual,⟨actual.parent,ts,plan,(raw_rejection_is_same_position450 _).mp k2⟩,rfl⟩
  else none

theorem source_cohorts_and_literal_report_replay_together452 (p : FullProblem)
    (a : ScopedLiteralReport p) :
    ∃ w, readScopedLiteralReport p w = some a := by
  cases a with
  | mk actual original shared =>
    cases original with
    | mk parent ts plan contains =>
      dsimp only at shared
      subst parent
      obtain ⟨w,proof⟩ := independent_selected_original_profiles_have_finite_wire451 p actual
      obtain ⟨ws,body⟩ := same_status_lifts_any_actual_supported_ordered_plan452 actual.diagnostics.status plan
      exact ⟨⟨w,ws⟩,by simp [readScopedLiteralReport,proof,body,
        (raw_rejection_is_same_position450 _).mpr contains,Bind.bind,Option.bind]⟩

theorem any_literal_replay_preserves_original_scoped_report_meaning452 (p : FullProblem)
    (q : ScopedLiteralReport p) :
    ExactReport p.old q.localK2.report ∧
      ∀ m, FitsFull p.state m → WhereSites450.ReportEvidence p.state.base m p.root q.localK2.report := by
  have proven := independent_original_rejection_has_real_trace450 q.localK2
  refine ⟨proven,?_⟩
  obtain ⟨e,tr,sm,wr⟩ := proven
  exact fun m fit => ⟨e,tr,sm,wr,exact_where_trace_model_meaning450 tr m fit.1⟩

theorem read_both_retains_the_same_checked_profile_and_internal_groups452
    {p : FullProblem} {w : ScopedLiteralInput} {q : ScopedLiteralReport p}
    (parsed : readScopedLiteralReport p w = some q) :
    readInternalReport452 p w.original = some q.internal := by
  unfold readScopedLiteralReport at parsed
  cases first : readOriginalWhereProfiles451 p w.original with
  | none => simp [first,Bind.bind,Option.bind] at parsed
  | some d =>
    cases second : replayLiteralChildPlans d.diagnostics.status w.extra with
    | none => simp [first,second,Bind.bind,Option.bind] at parsed
    | some pair =>
      rcases pair with ⟨trees,plan⟩
      by_cases exact : hasRawRejection trees = true
      · simp [first,second,exact,Bind.bind,Option.bind] at parsed
        subst q
        simp [readInternalReport452,first,ScopedLiteralReport.internal]
      · simp [first,second,exact,Bind.bind,Option.bind] at parsed

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451.LiteralAndInternal452
