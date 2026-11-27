import Yulang.GeneralDeclarativeI65I74HomogeneousReadyHeader459
import Yulang.GeneralDeclarativeI65I74ProjectedClosedEntry459
import Yulang.GeneralDeclarativeI65I74RoutedInlineStructuralEntry458

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.HomogeneousClosedEntry459
open Yulang.GeneralDeclarativeI65
open RecordTraversal455 RecordTraversal455.MixedQA
open RecordTrail455 (tokenOps routed_read_keeps_original_physical_owner_and_source_in_each_fit455 closedRecordTerm)
open RecordTrail455.MixedNative456
open RetainedFull445
open HomogeneousReadyHeader459 (AuthoredHeader readReadyHeader actual_original_homogeneous_header_replays459)
open AuthenticatedHop458 (AtStep Policy CycleWire readCycle exact_used_cycle_has_finite_wire458
  used_trace_is_root_safe_and_nonempty458)
open InlineStructuralPolicy458 (policy emptyPolicy liftCycle eraseCycle lift_erase_cycle458)
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

abbrev FieldWire := ProjectedClosedEntry459.FieldWire

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

theorem independent_routed_field_derivation_replays459 (p : Problem) (source : FieldDerivation p) :
    ∃ w, readField p w = some source := by
  obtain ⟨cursor,read⟩ := (exact_used_cycle_has_finite_wire458 _ _ _ _ _ _).mpr
    ⟨source.visited,source.cycle⟩
  refine ⟨⟨source.source.emptyKey,eraseCycle p.state.core cursor⟩,?_⟩
  have ok := actual_original_homogeneous_header_replays459 source.source
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

theorem actual_routed_field_report_iff_finite_wire459 (p : Problem) (r : ReportAtField) :
    (∃ w, checkField p r w = true) ↔ ExactField p r := by
  constructor
  · rintro ⟨w,ok⟩
    cases found : readField p w with
    | none => simp [checkField,found] at ok
    | some a => exact ⟨a,of_decide_eq_true (by simpa [checkField,found] using ok)⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨w,there⟩ := independent_routed_field_derivation_replays459 p a
    exact ⟨w,by simp [checkField,there]⟩

theorem routed_field_rejection_is_not_parent_root459 {p : Problem} (how : FieldDerivation p) :
    ¬ RootCycle p.state p.root := by
  have safe := (used_trace_is_root_safe_and_nonempty458 how.visited rfl).1
  rintro ⟨q,found,cycle⟩
  rw [how.source.argv] at found
  cases List.mem_singleton.mp found
  exact safe cycle

def recordLocalRule459 : SourcePrimitives where
  elected := fun _ _ _ _ => False
  other := fun s q v needs =>
    needs = [] ∧ v = .rejected ∧ Nonempty (FieldDerivation ⟨s,q⟩)

theorem routed_field_diagnosis_is_precise_source_trace459 {p : Problem} (how : FieldDerivation p) :
    Nonempty (SourceTrace recordLocalRule459 p.state p.root .rejected none) :=
  ⟨.other .rejected (routed_field_rejection_is_not_parent_root459 how) ⟨rfl,rfl,⟨how⟩⟩ .nil⟩

theorem no_routed_field_rule_selects_or_emits_where459 {p : Problem} {e : Event p.state p.root}
    {tr : Tree} : ¬ Nonempty (SourceTrace recordLocalRule459 p.state p.root tr (some e)) := by
  rintro ⟨trace⟩
  cases trace with
  | selected _ _ impossible _ _ => exact impossible.elim

open RoutedInlineStructural458 (ModelTrail used_source_hops_hold_in_the_same_model458)

def FieldEvidence (p : Problem) (m : I72.Model) (r : ReportAtField) : Prop :=
  ∃ a : FieldDerivation p, a.report = r ∧
    ModelTrail p.state.core m a.source.arg.lower a.source.query a.path a.terminal true ∧
    Nonempty (SourceTrace recordLocalRule459 p.state p.root .rejected none)

theorem routed_field_report_is_sound_in_every_same_fit459 {p : Problem} {r : ReportAtField}
    (exact : ExactField p r) (m : I72.Model) (fit : I72.Fits p.state m) :
    FieldEvidence p m r := by
  obtain ⟨a,rfl⟩ := exact
  exact ⟨a,rfl,used_source_hops_hold_in_the_same_model458 a.visited m fit,
    routed_field_diagnosis_is_precise_source_trace459 a⟩

abbrev OldRoutedEntry := ProjectedClosedEntry459.Report
abbrev OldRoutedWitness := ProjectedClosedEntry459.Witness

inductive Report where
  | previous (r : OldRoutedEntry)
  | fieldK2 (r : ReportAtField)

inductive Witness where
  | previous (w : OldRoutedWitness)
  | fieldK2 (w : FieldWire)

/-- Homogeneous exact original tags add a disjoint closed-source route while retaining the preceding exact cumulative checker. -/
def check_full_homogeneous459 (p : FullProblem) : Report → Witness → Bool
  | .previous r, .previous w => ProjectedClosedEntry459.check_full_projected459 p r w
  | .fieldK2 r, .fieldK2 w => checkField p.old r w
  | _,_ => false

theorem all_previous_canonical_Bools_unchanged459 (p : FullProblem) (r : OldRoutedEntry) (w : OldRoutedWitness) :
    check_full_homogeneous459 p (.previous r) (.previous w) =
    ProjectedClosedEntry459.check_full_projected459 p r w := rfl

def ClassifiedAs (p : FullProblem) : Report → Prop
  | .previous r => ProjectedClosedEntry459.ClassifiedAs p r
  | .fieldK2 r => ExactField p.old r

def ReportEvidence (p : FullProblem) (m : I72.Model) : Report → Prop
  | .previous r => ProjectedClosedEntry459.ReportEvidence p m r
  | .fieldK2 r => FieldEvidence p.old m r

theorem check_full_sound459 (p : FullProblem) (r : Report) (w : Witness)
    (ok : check_full_homogeneous459 p r w = true) :
    ClassifiedAs p r ∧ ∀ m, FitsFull p.state m → ReportEvidence p m r := by
  cases r with
  | previous r =>
    cases w with
    | previous w => exact ProjectedClosedEntry459.check_full_sound459 p r w ok
    | fieldK2 w => cases ok
  | fieldK2 r =>
    cases w with
    | previous w => cases ok
    | fieldK2 w =>
      have exact := (actual_routed_field_report_iff_finite_wire459 p.old r).mp ⟨w,ok⟩
      exact ⟨exact,fun m fit => routed_field_report_is_sound_in_every_same_fit459 exact m fit.1⟩

theorem independent_routed_field_derivation_has_cumulative_witness459
    (p : FullProblem) (r : ReportAtField) (exact : ExactField p.old r) :
    ∃ w, check_full_homogeneous459 p (.fieldK2 r) (.fieldK2 w) = true :=
  (actual_routed_field_report_iff_finite_wire459 p.old r).mpr exact

theorem accepted_exact_homogeneous_report_retains_original_projected_head459
    (p : FullProblem) (r : ReportAtField) (w : FieldWire)
    (yes : check_full_homogeneous459 p (.fieldK2 r) (.fieldK2 w) = true) :
    ∃ a : FieldDerivation p.old, a.report = r ∧
      ∃ originalProjection,
        NestedIdenticalTagProjection459.ProjectionArgs a.declaration.head originalProjection ∧
        RecordTree455.WrittenArgs a.source.emptyKey originalProjection ∧ originalProjection ≠ a.declaration.head := by
  obtain ⟨a,item⟩ := (check_full_sound459 p _ _ yes).1
  exact ⟨a,item,HomogeneousReadyHeader459.original_homogeneous_head_has_independent_exact_projection459 a.source⟩

end Yulang.GeneralDeclarativeI65.I72.HomogeneousClosedEntry459
