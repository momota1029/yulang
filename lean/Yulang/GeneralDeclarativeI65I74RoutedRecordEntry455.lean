import Yulang.GeneralDeclarativeI65I74RecordTreeHeader455
import Yulang.GeneralDeclarativeI65I74RecordRoutedOrigin455
import Yulang.GeneralDeclarativeI65I74RecordTrailEntry455

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoutedRecord455
open Yulang.GeneralDeclarativeI65
open RecordTraversal455
open RecordTraversal455 (TrailPath)
open RetainedFull445
open RecordTrail455 (FieldReport tokenOps ModelTrail routedOps independent_routed_trail_observes_same_model455)
open GeneralDeclarations (Declaration)
open Checker408 (Problem)
open CommonRoleOutermostResolver (Tree Summarizes)

abbrev OldRoutedEntry := WhereSites450.OriginalCohorts451.SamePhase454.Report
abbrev OldRoutedWitness := WhereSites450.OriginalCohorts451.SamePhase454.Witness

structure FieldDerivation (p : Problem) where
  declaration : Declaration
  source : AuthoredHeader p declaration
  path : TrailPath
  terminal : Nat
  visited : ExactCycleVisit p.state.core.current.ordinary (routedOps p.state.core)
    source.arg.lower source.query path terminal

def FieldDerivation.report {p : Problem} (a : FieldDerivation p) : FieldReport :=
  ⟨p.root.occurrence,a.declaration.id,a.path,a.terminal⟩

def ExactField (p : Problem) (r : FieldReport) : Prop :=
  ∃ a : FieldDerivation p, a.report = r

def liftTokens (s : GeneralDeclarativeI65.State) :
    TrailWire tokenOps → TrailWire (routedOps s)
  | .stop => .stop
  | .down x esc rest =>
    .down ⟨x.rawRow,x.owner,x.fieldOrdinal,x.patternOrdinal,x.token⟩ esc (liftTokens s rest)

def eraseTokens (s : GeneralDeclarativeI65.State) :
    TrailWire (routedOps s) → TrailWire tokenOps
  | .stop => .stop
  | .down x esc rest =>
    .down ⟨x.rawRow,x.owner,x.fieldOrdinal,x.patternOrdinal,x.token⟩ esc (eraseTokens s rest)

theorem replay_routed_tokens_preserve_finite_data455 (s : GeneralDeclarativeI65.State)
    (w : TrailWire (routedOps s)) : liftTokens s (eraseTokens s w) = w := by
  induction w with
  | stop => rfl
  | down x escape rest ih =>
    cases x
    simp [liftTokens,eraseTokens,ih]

def liftCursor (s : GeneralDeclarativeI65.State) (w : CycleVisitWire tokenOps) :
    CycleVisitWire (routedOps s) := ⟨liftTokens s w.trail,w.cycle⟩

def eraseCursor (s : GeneralDeclarativeI65.State) (w : CycleVisitWire (routedOps s)) :
    CycleVisitWire tokenOps := ⟨eraseTokens s w.trail,w.cycle⟩

theorem lift_eraseCursor (s : GeneralDeclarativeI65.State) (w : CycleVisitWire (routedOps s)) :
    liftCursor s (eraseCursor s w) = w := by
  cases w
  simp [liftCursor,eraseCursor,replay_routed_tokens_preserve_finite_data455]

structure FieldWire where
  emptyKey : Nat
  cursor : CycleVisitWire tokenOps

def readField (p : Problem) (w : FieldWire) : Option (FieldDerivation p) :=
  match only : visible p.state.core p.root with
  | [d] => do
    let source ← readHeader p d only w.emptyKey
    match read : readCycleVisit p.state.core.current.ordinary (routedOps p.state.core)
        source.arg.lower source.query (liftCursor p.state.core w.cursor) with
    | some (path,last) => some ⟨d,source,path,last,read_cycle_visit_sound455 read⟩
    | none => none
  | _ => none

theorem independent_routed_field_derivation_replays455 (p : Problem) (source : FieldDerivation p) :
    ∃ w, readField p w = some source := by
  obtain ⟨cursor,read⟩ := exact_cycle_visit_has_finite_wire455 source.visited
  refine ⟨⟨source.source.emptyKey,eraseCursor p.state.core cursor⟩,?_⟩
  have ok := independently_authored_record_tree_header_replays455 source.source
  unfold readField
  split
  · rename_i row one
    have same := List.singleton_inj.mp (one.symm.trans source.source.only)
    subst row
    simp only [ok,Bind.bind,Option.bind]
    split
    · rename_i path last found
      rw [lift_eraseCursor] at found
      obtain ⟨first,endName⟩ := Prod.mk.inj (Option.some.inj (found.symm.trans read))
      subst path
      subst last
      cases source
      rfl
    · rename_i found
      rw [lift_eraseCursor,read] at found
      cases found
  · rename_i missed
    exact (missed _ source.source.only).elim

def checkField (p : Problem) (r : FieldReport) (w : FieldWire) : Bool :=
  ((readField p w).map fun result => decide (result.report = r)).getD false

theorem actual_routed_field_report_iff_finite_wire455 (p : Problem) (r : FieldReport) :
    (∃ w, checkField p r w = true) ↔ ExactField p r := by
  constructor
  · rintro ⟨w,ok⟩
    cases found : readField p w with
    | none => simp [checkField,found] at ok
    | some a => exact ⟨a,of_decide_eq_true (by simpa [checkField,found] using ok)⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨w,there⟩ := independent_routed_field_derivation_replays455 p a
    exact ⟨w,by simp [checkField,there]⟩

theorem routed_field_rejection_is_not_parent_root455 {p : Problem} (how : FieldDerivation p) :
    ¬ RootCycle p.state p.root := by
  have safe := (exact_cycle_visit_is_safe_at_root_and_real_at_site455 how.visited).1
  rintro ⟨q,found,cycle⟩
  rw [how.source.argv] at found
  cases List.mem_singleton.mp found
  exact safe cycle

def recordLocalRule455 : SourcePrimitives where
  elected := fun _ _ _ _ => False
  other := fun s q v needs =>
    needs = [] ∧ v = .rejected ∧ Nonempty (FieldDerivation ⟨s,q⟩)

theorem routed_field_diagnosis_is_precise_source_trace455 {p : Problem} (how : FieldDerivation p) :
    Nonempty (SourceTrace recordLocalRule455 p.state p.root .rejected none) :=
  ⟨.other .rejected (routed_field_rejection_is_not_parent_root455 how) ⟨rfl,rfl,⟨how⟩⟩ .nil⟩

theorem no_routed_field_rule_selects_or_emits_where455 {p : Problem} {e : Event p.state p.root}
    {tr : Tree} : ¬ Nonempty (SourceTrace recordLocalRule455 p.state p.root tr (some e)) := by
  rintro ⟨trace⟩
  cases trace with
  | selected _ _ impossible _ _ => exact impossible.elim

def FieldEvidence (p : Problem) (m : I72.Model) (r : FieldReport) : Prop :=
  ∃ a : FieldDerivation p, a.report = r ∧
    ModelTrail p.state.core m a.source.arg.lower a.source.query a.path a.terminal ∧
    Nonempty (SourceTrace recordLocalRule455 p.state p.root .rejected none)

theorem routed_field_report_is_sound_in_every_same_fit455 {p : Problem} {r : FieldReport}
    (exact : ExactField p r) (m : I72.Model) (fit : I72.Fits p.state m) :
    FieldEvidence p m r := by
  obtain ⟨a,rfl⟩ := exact
  exact ⟨a,rfl,independent_routed_trail_observes_same_model455 a.visited.1 m fit,
    routed_field_diagnosis_is_precise_source_trace455 a⟩

inductive Report where
  | previous (r : OldRoutedEntry)
  | fieldK2 (r : FieldReport)

inductive Witness where
  | previous (w : OldRoutedWitness)
  | fieldK2 (w : FieldWire)

/-- Canonical C455: delegate exact C454, not the raw-only trial lane. -/
def check_full455 (p : FullProblem) : Report → Witness → Bool
  | .previous r, .previous w => WhereSites450.OriginalCohorts451.SamePhase454.check_full454 p r w
  | .fieldK2 r, .fieldK2 w => checkField p.old r w
  | _,_ => false

theorem all_previous_canonical_Bools_unchanged455 (p : FullProblem) (r : OldRoutedEntry) (w : OldRoutedWitness) :
    check_full455 p (.previous r) (.previous w) =
    WhereSites450.OriginalCohorts451.SamePhase454.check_full454 p r w := rfl

def ClassifiedAs (p : FullProblem) : Report → Prop
  | .previous r => WhereSites450.OriginalCohorts451.SamePhase454.ClassifiedAs p r
  | .fieldK2 r => ExactField p.old r

def ReportEvidence (p : FullProblem) (m : I72.Model) : Report → Prop
  | .previous r => WhereSites450.OriginalCohorts451.SamePhase454.ReportEvidence p m r
  | .fieldK2 r => FieldEvidence p.old m r

theorem check_full_sound455 (p : FullProblem) (r : Report) (w : Witness)
    (ok : check_full455 p r w = true) :
    ClassifiedAs p r ∧ ∀ m, FitsFull p.state m → ReportEvidence p m r := by
  cases r with
  | previous r =>
    cases w with
    | previous w => exact WhereSites450.OriginalCohorts451.SamePhase454.check_full_sound454 p r w ok
    | fieldK2 w => cases ok
  | fieldK2 r =>
    cases w with
    | previous w => cases ok
    | fieldK2 w =>
      have exact := (actual_routed_field_report_iff_finite_wire455 p.old r).mp ⟨w,ok⟩
      exact ⟨exact,fun m fit => routed_field_report_is_sound_in_every_same_fit455 exact m fit.1⟩

theorem independent_routed_field_derivation_has_cumulative_witness455
    (p : FullProblem) (r : FieldReport) (exact : ExactField p.old r) :
    ∃ w, check_full455 p (.fieldK2 r) (.fieldK2 w) = true :=
  (actual_routed_field_report_iff_finite_wire455 p.old r).mpr exact

end Yulang.GeneralDeclarativeI65.I72.RoutedRecord455
