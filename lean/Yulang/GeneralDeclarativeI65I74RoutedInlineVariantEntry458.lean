import Yulang.GeneralDeclarativeI65I74VariantInlinePolicy458

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoutedInlineVariant458
open Yulang.GeneralDeclarativeI65
open RecordTraversal455 RecordTraversal455.MixedQA
open RecordTrail455 (tokenOps routed_read_keeps_original_physical_owner_and_source_in_each_fit455 closedRecordTerm)
open RecordTrail455.MixedNative456
open RetainedFull445
open RoutedReadyHeader457 (AuthoredHeader readReadyHeader exact_same_written_local_ready_header_replays457)
open AuthenticatedHop458 (AtStep Policy CycleWire readCycle exact_used_cycle_has_finite_wire458
  used_trace_is_root_safe_and_nonempty458)
open VariantInlinePolicy458 (policy emptyPolicy liftCycle eraseCycle lift_erase_cycle458 InlineMeaning)
open RoutedNominalMixed456 (actualQueryDecoder MeaningOfOpen)
open RoutedReadyMixed457 (ReportAtField)
open RoutedMixed456 (endsAtField)
open GeneralDeclarations (Declaration)
open Checker408 (Problem)
open CommonRoleOutermostResolver (Tree Summarizes)
open GeneralDeclarativeInspect321 (Visit Inspects)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed shapeOf)

structure FieldDerivation (p : Problem) where
  declaration : Declaration
  source : AuthoredHeader p (actualQueryDecoder p.state.core) declaration
  path : MixedPath
  terminal : Nat
  visited : AuthenticatedHop458.Trail p.state.core.current.ordinary (policy p.state.core)
    source.arg.lower source.query path terminal true
  cycle : AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) terminal
  fieldEnd : endsAtField path terminal = true

def FieldDerivation.report {p : Problem} (a : FieldDerivation p) : ReportAtField :=
  ⟨p.root.occurrence,a.declaration.id,0,a.source.clause.id,a.path,a.terminal⟩

def ExactField (p : Problem) (r : ReportAtField) : Prop :=
  ∃ a : FieldDerivation p, a.report = r

structure FieldWire where
  emptyKey : Nat
  cursor : CycleWire emptyPolicy

def packRead (p : Problem) (d : Declaration) (source : AuthoredHeader p (actualQueryDecoder p.state.core) d)
    (w : FieldWire) : Option (FieldDerivation p) :=
  match read : readCycle p.state.core.current.ordinary (policy p.state.core)
      source.arg.lower source.query (liftCycle p.state.core w.cursor) with
  | some (path,last) =>
    if terminal : endsAtField path last = true then
      let shape := (exact_used_cycle_has_finite_wire458 _ _ _ _ _ _).mp ⟨_,read⟩
      some ⟨d,source,path,last,shape.1,shape.2,terminal⟩
    else none
  | none => none

def readField (p : Problem) (w : FieldWire) : Option (FieldDerivation p) :=
  match only : visible p.state.core p.root with
  | [d] => do
    let source ← readReadyHeader p (actualQueryDecoder p.state.core) d only w.emptyKey
    packRead p d source w
  | _ => none

theorem independent_routed_field_derivation_replays458 (p : Problem) (source : FieldDerivation p) :
    ∃ w, readField p w = some source := by
  obtain ⟨cursor,read⟩ := (exact_used_cycle_has_finite_wire458 _ _ _ _ _ _).mpr
    ⟨source.visited,source.cycle⟩
  refine ⟨⟨source.source.emptyKey,eraseCycle p.state.core cursor⟩,?_⟩
  have ok := exact_same_written_local_ready_header_replays457 source.source
  unfold readField
  split
  · rename_i row one
    have same := List.singleton_inj.mp (one.symm.trans source.source.only)
    subst row
    simp only [ok,Bind.bind,Option.bind,packRead]
    split
    · rename_i path last found
      rw [lift_erase_cycle458,read] at found
      obtain ⟨eqPath,eqLast⟩ := Prod.mk.inj (Option.some.inj found)
      subst path
      subst last
      simp [source.fieldEnd]
    · rename_i found
      rw [lift_erase_cycle458,read] at found
      cases found
  · rename_i missed
    exact (missed _ source.source.only).elim

def checkField (p : Problem) (r : ReportAtField) (w : FieldWire) : Bool :=
  ((readField p w).map fun result => decide (result.report = r)).getD false

theorem actual_routed_field_report_iff_finite_wire458 (p : Problem) (r : ReportAtField) :
    (∃ w, checkField p r w = true) ↔ ExactField p r := by
  constructor
  · rintro ⟨w,ok⟩
    cases found : readField p w with
    | none => simp [checkField,found] at ok
    | some a => exact ⟨a,of_decide_eq_true (by simpa [checkField,found] using ok)⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨w,there⟩ := independent_routed_field_derivation_replays458 p a
    exact ⟨w,by simp [checkField,there]⟩

theorem routed_field_rejection_is_not_parent_root458 {p : Problem} (how : FieldDerivation p) :
    ¬ RootCycle p.state p.root := by
  have safe := (used_trace_is_root_safe_and_nonempty458 how.visited rfl).1
  rintro ⟨q,found,cycle⟩
  rw [how.source.argv] at found
  cases List.mem_singleton.mp found
  exact safe cycle

def recordLocalRule458 : SourcePrimitives where
  elected := fun _ _ _ _ => False
  other := fun s q v needs =>
    needs = [] ∧ v = .rejected ∧ Nonempty (FieldDerivation ⟨s,q⟩)

theorem routed_field_diagnosis_is_precise_source_trace458 {p : Problem} (how : FieldDerivation p) :
    Nonempty (SourceTrace recordLocalRule458 p.state p.root .rejected none) :=
  ⟨.other .rejected (routed_field_rejection_is_not_parent_root458 how) ⟨rfl,rfl,⟨how⟩⟩ .nil⟩

theorem no_routed_field_rule_selects_or_emits_where458 {p : Problem} {e : Event p.state p.root}
    {tr : Tree} : ¬ Nonempty (SourceTrace recordLocalRule458 p.state p.root tr (some e)) := by
  rintro ⟨trace⟩
  cases trace with
  | selected _ _ impossible _ _ => exact impossible.elim

open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open RecordTrail455 (routed_read_keeps_original_physical_owner_and_source_in_each_fit455)
open RecordTrail455.MixedNative456
open RoutedNominalPoint456

def ModelOpening (s : GeneralDeclarativeI65.State) (m : I72.Model)
    (root : Nat) (row : Equation) (sh : Shape) (code : Expr) (a : Address)
    (c : Nat) (next : Expr) : Bool → Prop
  | false => MeaningOfOpen s m root row sh code a c next
  | true => InlineMeaning s m root row a c

inductive ModelTrail (s : GeneralDeclarativeI65.State) (m : I72.Model) :
    Nat → Expr → MixedPath → Nat → Bool → Prop where
  | stop : Inspects code → ModelTrail s m root code [] root false
  | down : ¬ AliasCycle s.current.ordinary (observed s.current.ordinary) root →
    (∃ row ∈ s.current.ordinary.equations, ∃ shape, GeneralDeclarativeLowerKnown321.Alias
      s.current.ordinary root row.left ∧ shapeOf row.right = some shape ∧
      ChildAt shape code a c next ∧ ModelOpening s m root row shape code a c next stamp) →
    ModelTrail s m c next tail terminal rest →
    ModelTrail s m root code ((a,c)::tail) terminal (stamp || rest)

theorem used_source_hops_hold_in_the_same_model458 {s : GeneralDeclarativeI65.State} {root code path terminal stamp}
    (actual : AuthenticatedHop458.Trail s.current.ordinary (policy s) root code path terminal stamp)
    (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m) :
    ModelTrail s m root code path terminal stamp := by
  induction actual with
  | stop yes => exact .stop yes
  | @down root code a c next stamp tail terminal rest safe atHop t ih =>
    obtain ⟨row,seen,sh,alias,form,hop,ok⟩ := atHop
    refine .down safe ⟨row,seen,sh,alias,form,hop,?_⟩ ih
    cases stamp with
    | true =>
      exact VariantInlinePolicy458.inline_meaning_keeps_the_same_raw_child_and_two_native_reads458
        ok.1 ok.2 m fit
    | false =>
      change (nominalOps s).allowed _ _ at ok
      rcases ok with ordinary | typed
      · left
        rcases ordinary with rec | other
        · obtain ⟨o,seen,route,owner,ty,native,rowEq⟩ :=
            routed_read_keeps_original_physical_owner_and_source_in_each_fit455 rec m fit
          exact ⟨o,seen,route,owner,ty,native,.inl rowEq⟩
        · obtain ⟨o,seen,route,owner,ty,original,equal⟩ := other
          exact ⟨o,seen,route,owner,ty,by simpa only [owner,original] using fit.2 o seen,.inr equal⟩
      · right
        obtain ⟨nominal⟩ := typed
        have actual := literal_covariant_point_child_is_only_original_ordinal456 nominal form hop
        exact ⟨nominal,(original_point_compares_in_the_same_model456 nominal m fit false).1,
          fun context => (original_point_compares_in_the_same_model456 nominal m fit context).2,form,actual⟩

def FieldEvidence (p : Problem) (m : I72.Model) (r : ReportAtField) : Prop :=
  ∃ a : FieldDerivation p, a.report = r ∧
    ModelTrail p.state.core m a.source.arg.lower a.source.query a.path a.terminal true ∧
    Nonempty (SourceTrace recordLocalRule458 p.state p.root .rejected none)

theorem routed_field_report_is_sound_in_every_same_fit458 {p : Problem} {r : ReportAtField}
    (exact : ExactField p r) (m : I72.Model) (fit : I72.Fits p.state m) :
    FieldEvidence p m r := by
  obtain ⟨a,rfl⟩ := exact
  exact ⟨a,rfl,used_source_hops_hold_in_the_same_model458 a.visited m fit,
    routed_field_diagnosis_is_precise_source_trace458 a⟩

abbrev OldRoutedEntry := RoutedReadyMixed457.Report
abbrev OldRoutedWitness := RoutedReadyMixed457.Witness

inductive Report where
  | previous (r : OldRoutedEntry)
  | fieldK2 (r : ReportAtField)

inductive Witness where
  | previous (w : OldRoutedWitness)
  | fieldK2 (w : FieldWire)

/-- Cumulative C458 directly delegates the exact latest C457 mixed Ready entry. -/
def check_full458 (p : FullProblem) : Report → Witness → Bool
  | .previous r, .previous w => RoutedReadyMixed457.check_full_ready_mixed457 p r w
  | .fieldK2 r, .fieldK2 w => checkField p.old r w
  | _,_ => false

theorem all_previous_canonical_Bools_unchanged458 (p : FullProblem) (r : OldRoutedEntry) (w : OldRoutedWitness) :
    check_full458 p (.previous r) (.previous w) =
    RoutedReadyMixed457.check_full_ready_mixed457 p r w := rfl

def ClassifiedAs (p : FullProblem) : Report → Prop
  | .previous r => RoutedReadyMixed457.ClassifiedAs p r
  | .fieldK2 r => ExactField p.old r

def ReportEvidence (p : FullProblem) (m : I72.Model) : Report → Prop
  | .previous r => RoutedReadyMixed457.ReportEvidence p m r
  | .fieldK2 r => FieldEvidence p.old m r

theorem check_full_sound458 (p : FullProblem) (r : Report) (w : Witness)
    (ok : check_full458 p r w = true) :
    ClassifiedAs p r ∧ ∀ m, FitsFull p.state m → ReportEvidence p m r := by
  cases r with
  | previous r =>
    cases w with
    | previous w => exact RoutedReadyMixed457.check_full_sound457 p r w ok
    | fieldK2 w => cases ok
  | fieldK2 r =>
    cases w with
    | previous w => cases ok
    | fieldK2 w =>
      have exact := (actual_routed_field_report_iff_finite_wire458 p.old r).mp ⟨w,ok⟩
      exact ⟨exact,fun m fit => routed_field_report_is_sound_in_every_same_fit458 exact m fit.1⟩

theorem independent_routed_field_derivation_has_cumulative_witness458
    (p : FullProblem) (r : ReportAtField) (exact : ExactField p.old r) :
    ∃ w, check_full458 p (.fieldK2 r) (.fieldK2 w) = true :=
  (actual_routed_field_report_iff_finite_wire458 p.old r).mpr exact

end Yulang.GeneralDeclarativeI65.I72.RoutedInlineVariant458
