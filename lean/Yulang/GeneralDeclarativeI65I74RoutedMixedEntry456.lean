import Yulang.GeneralDeclarativeI65I74MixedTraversal456
import Yulang.GeneralDeclarativeI65I74MixedNative456

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoutedMixed456
open Yulang.GeneralDeclarativeI65
open RecordTraversal455 RecordTraversal455.MixedQA
open RecordTrail455 (tokenOps routed_read_keeps_original_physical_owner_and_source_in_each_fit455 closedRecordTerm)
open RecordTrail455.MixedNative456
open RetainedFull445
open GeneralDeclarations (Declaration)
open Checker408 (Problem)
open CommonRoleOutermostResolver (Tree Summarizes)
open GeneralDeclarativeInspect321 (Visit)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed shapeOf)

def endsAtField (path : MixedPath) (site : Nat) : Bool :=
  match path.getLast? with
  | some (.field _,n) => n == site
  | _ => false

theorem ending_field_nonempty456 {path site} (ok : endsAtField path site = true) :
    path ≠ [] := by rintro rfl; simp [endsAtField] at ok

structure MixedReport where
  occurrence : List Nat
  declaration : Nat
  path : MixedPath
  terminal : Nat
  deriving DecidableEq

structure FieldDerivation (p : Problem) where
  declaration : Declaration
  source : RoutedRecord455.AuthoredHeader p declaration
  path : MixedPath
  terminal : Nat
  visited : MixedTrail p.state.core.current.ordinary (extraOpenOps p.state.core)
    source.arg.lower source.query path terminal
  cycle : AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) terminal
  fieldEnd : endsAtField path terminal = true

def FieldDerivation.report {p : Problem} (a : FieldDerivation p) : MixedReport :=
  ⟨p.root.occurrence,a.declaration.id,a.path,a.terminal⟩

def ExactField (p : Problem) (r : MixedReport) : Prop :=
  ∃ a : FieldDerivation p, a.report = r

def liftTokens (s : GeneralDeclarativeI65.State) :
    MixedWire tokenOps → MixedWire (extraOpenOps s)
  | .stop => .stop
  | .down x edge esc rest =>
    .down ⟨x.ordinal,x.rawAlias,x.token⟩ edge esc (liftTokens s rest)

def eraseTokens (s : GeneralDeclarativeI65.State) :
    MixedWire (extraOpenOps s) → MixedWire tokenOps
  | .stop => .stop
  | .down x edge esc rest =>
    .down ⟨x.ordinal,x.rawAlias,x.token⟩ edge esc (eraseTokens s rest)

theorem replay_routed_tokens_preserve_finite_data456 (s : GeneralDeclarativeI65.State)
    (w : MixedWire (extraOpenOps s)) : liftTokens s (eraseTokens s w) = w := by
  induction w with
  | stop => rfl
  | down x edge escape rest ih =>
    cases x
    simp [liftTokens,eraseTokens,ih]

def liftCursor (s : GeneralDeclarativeI65.State) (w : MixedCycleWire tokenOps) :
    MixedCycleWire (extraOpenOps s) := ⟨liftTokens s w.start,w.finish⟩

def eraseCursor (s : GeneralDeclarativeI65.State) (w : MixedCycleWire (extraOpenOps s)) :
    MixedCycleWire tokenOps := ⟨eraseTokens s w.start,w.finish⟩

theorem lift_eraseCursor (s : GeneralDeclarativeI65.State) (w : MixedCycleWire (extraOpenOps s)) :
    liftCursor s (eraseCursor s w) = w := by
  cases w
  simp [liftCursor,eraseCursor,replay_routed_tokens_preserve_finite_data456]

structure FieldWire where
  emptyKey : Nat
  cursor : MixedCycleWire tokenOps

def packRead (p : Problem) (d : Declaration) (source : RoutedRecord455.AuthoredHeader p d)
    (w : FieldWire) : Option (FieldDerivation p) :=
  match read : readMixedCycle p.state.core.current.ordinary (extraOpenOps p.state.core)
        source.arg.lower source.query (liftCursor p.state.core w.cursor) with
  | some (path,last) =>
    if endAt : endsAtField path last = true then
      let facts := (mixed_cycle_has_actual_finite_wire _ _ _ _ _ _).mp ⟨_,read⟩
      some ⟨d,source,path,last,facts.1,facts.2.2,endAt⟩
    else none
  | none => none

def readField (p : Problem) (w : FieldWire) : Option (FieldDerivation p) :=
  match only : visible p.state.core p.root with
  | [d] => do
    let source ← RoutedRecord455.readHeader p d only w.emptyKey
    packRead p d source w
  | _ => none

theorem independent_routed_field_derivation_replays456 (p : Problem) (source : FieldDerivation p) :
    ∃ w, readField p w = some source := by
  obtain ⟨cursor,read⟩ := (mixed_cycle_has_actual_finite_wire _ _ _ _ _ _).mpr
    ⟨source.visited,ending_field_nonempty456 source.fieldEnd,source.cycle⟩
  refine ⟨⟨source.source.emptyKey,eraseCursor p.state.core cursor⟩,?_⟩
  have ok := RoutedRecord455.independently_authored_record_tree_header_replays455 source.source
  unfold readField
  split
  · rename_i row one
    have same := List.singleton_inj.mp (one.symm.trans source.source.only)
    subst row
    simp only [ok,Bind.bind,Option.bind,packRead]
    split
    · rename_i path last found
      rw [lift_eraseCursor,read] at found
      obtain ⟨eqPath,eqLast⟩ := Prod.mk.inj (Option.some.inj found)
      subst path
      subst last
      simp [source.fieldEnd]
    · rename_i found
      rw [lift_eraseCursor,read] at found
      cases found
  · rename_i missed
    exact (missed _ source.source.only).elim

def checkField (p : Problem) (r : MixedReport) (w : FieldWire) : Bool :=
  ((readField p w).map fun result => decide (result.report = r)).getD false

theorem actual_routed_field_report_iff_finite_wire456 (p : Problem) (r : MixedReport) :
    (∃ w, checkField p r w = true) ↔ ExactField p r := by
  constructor
  · rintro ⟨w,ok⟩
    cases found : readField p w with
    | none => simp [checkField,found] at ok
    | some a => exact ⟨a,of_decide_eq_true (by simpa [checkField,found] using ok)⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨w,there⟩ := independent_routed_field_derivation_replays456 p a
    exact ⟨w,by simp [checkField,there]⟩

theorem mixed_nonempty_trail_has_safe_root456 {s o root code path site}
    (v : MixedTrail s o root code path site) (nonempty : path ≠ []) :
    ¬ AliasCycle s (observed s) root := by
  cases v with
  | stop => exact (nonempty rfl).elim
  | down h => exact h

theorem routed_field_rejection_is_not_parent_root456 {p : Problem} (how : FieldDerivation p) :
    ¬ RootCycle p.state p.root := by
  have safe := mixed_nonempty_trail_has_safe_root456 how.visited (ending_field_nonempty456 how.fieldEnd)
  rintro ⟨q,found,cycle⟩
  rw [how.source.argv] at found
  cases List.mem_singleton.mp found
  exact safe cycle

def recordLocalRule456 : SourcePrimitives where
  elected := fun _ _ _ _ => False
  other := fun s q v needs =>
    needs = [] ∧ v = .rejected ∧ Nonempty (FieldDerivation ⟨s,q⟩)

theorem routed_field_diagnosis_is_precise_source_trace456 {p : Problem} (how : FieldDerivation p) :
    Nonempty (SourceTrace recordLocalRule456 p.state p.root .rejected none) :=
  ⟨.other .rejected (routed_field_rejection_is_not_parent_root456 how) ⟨rfl,rfl,⟨how⟩⟩ .nil⟩

theorem no_routed_field_rule_selects_or_emits_where456 {p : Problem} {e : Event p.state p.root}
    {tr : Tree} : ¬ Nonempty (SourceTrace recordLocalRule456 p.state p.root tr (some e)) := by
  rintro ⟨trace⟩
  cases trace with
  | selected _ _ impossible _ _ => exact impossible.elim

open GeneralDeclarativeK2Graph321 (Shape)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeHead320 (Equation)
open Core.PresenceGeneration (TyTerm)

def MeaningOfOpen (s : GeneralDeclarativeI65.State) (m : I72.Model) (logical : Nat)
    (row : Equation) : Prop :=
  (∃ o ∈ s.origins, OriginRoute s o logical ∧ o.slot = row.left ∧ ∃ ty : TyTerm Nat,
    m.nativeSyntax row.left = some (.ordinary ty) ∧
    (closedRecordTerm ty = some row.right ∨ ExactExtra ty row.right))

inductive ModelMixedTrail (s : GeneralDeclarativeI65.State) (m : I72.Model) :
    Nat → Expr → MixedPath → Nat → Prop where
  | stop : GeneralDeclarativeInspect321.Inspects code → ModelMixedTrail s m root code [] root
  | down : (∃ row ∈ s.current.ordinary.equations,
      GeneralDeclarativeLowerKnown321.Alias s.current.ordinary root row.left ∧ shapeOf row.right = some sh ∧
      MeaningOfOpen s m root row) → ChildAt sh code a child next →
      ModelMixedTrail s m child next tail site →
      ModelMixedTrail s m root code ((a,child)::tail) site

theorem routed_mixed_trail_is_same_model456 {s : GeneralDeclarativeI65.State} {root code path site}
    (actual : MixedTrail s.current.ordinary (extraOpenOps s) root code path site)
    (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m) :
    ModelMixedTrail s m root code path site := by
  induction actual with
  | stop inspected => exact .stop inspected
  | down _ auth hop _ ih =>
    obtain ⟨row,mem,alias,shape,valid⟩ := auth
    refine .down ⟨row,mem,alias,shape,?_⟩ hop ih
    rcases valid with rec | other
    · obtain ⟨o,seen,route,owner,ty,native,rowEq⟩ :=
        routed_read_keeps_original_physical_owner_and_source_in_each_fit455 rec m fit
      exact ⟨o,seen,route,owner,ty,native,.inl rowEq⟩
    · obtain ⟨prior,priorMem,priorRoute,ownerEq,t,origEq,tyEq⟩ := other
      -- The independently reflected origin above came from this exact source membership.
      exact ⟨prior,priorMem,priorRoute,ownerEq,t,by simpa only [ownerEq,origEq] using fit.2 prior priorMem,
        .inr tyEq⟩

def FieldEvidence (p : Problem) (m : I72.Model) (r : MixedReport) : Prop :=
  ∃ a : FieldDerivation p, a.report = r ∧
    ModelMixedTrail p.state.core m a.source.arg.lower a.source.query a.path a.terminal ∧
    Nonempty (SourceTrace recordLocalRule456 p.state p.root .rejected none)

theorem routed_field_report_is_sound_in_every_same_fit456 {p : Problem} {r : MixedReport}
    (exact : ExactField p r) (m : I72.Model) (fit : I72.Fits p.state m) :
    FieldEvidence p m r := by
  obtain ⟨a,rfl⟩ := exact
  exact ⟨a,rfl,routed_mixed_trail_is_same_model456 a.visited m fit,
    routed_field_diagnosis_is_precise_source_trace456 a⟩

abbrev OldRoutedEntry := RoutedRecord455.Report
abbrev OldRoutedWitness := RoutedRecord455.Witness

inductive Report where
  | previous (r : OldRoutedEntry)
  | fieldK2 (r : MixedReport)

inductive Witness where
  | previous (w : OldRoutedWitness)
  | fieldK2 (w : FieldWire)

/-- Cumulative C456 directly delegates the exact C455 canonical entry. -/
def check_full456 (p : FullProblem) : Report → Witness → Bool
  | .previous r, .previous w => RoutedRecord455.check_full455 p r w
  | .fieldK2 r, .fieldK2 w => checkField p.old r w
  | _,_ => false

theorem all_previous_canonical_Bools_unchanged456 (p : FullProblem) (r : OldRoutedEntry) (w : OldRoutedWitness) :
    check_full456 p (.previous r) (.previous w) =
    RoutedRecord455.check_full455 p r w := rfl

def ClassifiedAs (p : FullProblem) : Report → Prop
  | .previous r => RoutedRecord455.ClassifiedAs p r
  | .fieldK2 r => ExactField p.old r

def ReportEvidence (p : FullProblem) (m : I72.Model) : Report → Prop
  | .previous r => RoutedRecord455.ReportEvidence p m r
  | .fieldK2 r => FieldEvidence p.old m r

theorem check_full_sound456 (p : FullProblem) (r : Report) (w : Witness)
    (ok : check_full456 p r w = true) :
    ClassifiedAs p r ∧ ∀ m, FitsFull p.state m → ReportEvidence p m r := by
  cases r with
  | previous r =>
    cases w with
    | previous w => exact RoutedRecord455.check_full_sound455 p r w ok
    | fieldK2 w => cases ok
  | fieldK2 r =>
    cases w with
    | previous w => cases ok
    | fieldK2 w =>
      have exact := (actual_routed_field_report_iff_finite_wire456 p.old r).mp ⟨w,ok⟩
      exact ⟨exact,fun m fit => routed_field_report_is_sound_in_every_same_fit456 exact m fit.1⟩

theorem independent_routed_field_derivation_has_cumulative_witness456
    (p : FullProblem) (r : MixedReport) (exact : ExactField p.old r) :
    ∃ w, check_full456 p (.fieldK2 r) (.fieldK2 w) = true :=
  (actual_routed_field_report_iff_finite_wire456 p.old r).mpr exact

end Yulang.GeneralDeclarativeI65.I72.RoutedMixed456
