import Yulang.GeneralDeclarativeI65I74RoutedReadyRecordEntry457

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoutedReadyMixed457
open Yulang.GeneralDeclarativeI65
open RecordTraversal455 RecordTraversal455.MixedQA
open RecordTrail455 (tokenOps routed_read_keeps_original_physical_owner_and_source_in_each_fit455 closedRecordTerm)
open RecordTrail455.MixedNative456
open RetainedFull445
open RoutedReadyHeader457 (AuthoredHeader readReadyHeader exact_same_written_local_ready_header_replays457)
open RoutedReadyRecord457 (outsideConservative outside_conservative_exact457)
open RoutedNominalMixed456 (actualQueryDecoder liftCursor eraseCursor lift_eraseCursor ModelMixedTrail routed_mixed_trail_is_same_model456)
open GeneralDeclarationPatterns (ConservativeSmaller)
open RoutedNominalPoint456
open RoutedMixed456 (FieldWire endsAtField ending_field_nonempty456 mixed_nonempty_trail_has_safe_root456)
open GeneralDeclarations (Declaration)
open Checker408 (Problem)
open CommonRoleOutermostResolver (Tree Summarizes)
open GeneralDeclarativeInspect321 (Visit)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed shapeOf)

def isMixedHop : Address × Nat → Bool
  | (.field _,_) => false
  | _ => true

def includesMix (path : MixedPath) : Bool := path.any isMixedHop

structure ReportAtField where
  occurrence : List Nat
  declaration : Nat
  originalClauseOrdinal : Nat
  originalClauseId : Nat
  path : MixedPath
  terminal : Nat
  deriving DecidableEq

structure FieldDerivation (p : Problem) where
  declaration : Declaration
  source : AuthoredHeader p (actualQueryDecoder p.state.core) declaration
  actualGap : ¬ ConservativeSmaller declaration.head source.clause.arguments
  path : MixedPath
  terminal : Nat
  visited : MixedTrail p.state.core.current.ordinary (nominalOps p.state.core)
    source.arg.lower source.query path terminal
  cycle : AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) terminal
  fieldEnd : endsAtField path terminal = true
  containsMix : includesMix path = true

def FieldDerivation.report {p : Problem} (a : FieldDerivation p) : ReportAtField :=
  ⟨p.root.occurrence,a.declaration.id,0,a.source.clause.id,a.path,a.terminal⟩

def ExactField (p : Problem) (r : ReportAtField) : Prop :=
  ∃ a : FieldDerivation p, a.report = r

def packRead (p : Problem) (d : Declaration) (source : AuthoredHeader p (actualQueryDecoder p.state.core) d)
    (w : FieldWire) : Option (FieldDerivation p) :=
  if gap : outsideConservative d.head source.clause.arguments = true then
    match read : readMixedCycle p.state.core.current.ordinary (nominalOps p.state.core)
        source.arg.lower source.query (liftCursor p.state.core w.cursor) with
    | some (path,last) =>
      if endAt : endsAtField path last = true ∧ includesMix path = true then
        let facts := (mixed_cycle_has_actual_finite_wire _ _ _ _ _ _).mp ⟨_,read⟩
        some ⟨d,source,(outside_conservative_exact457 ..).mp gap,path,last,facts.1,facts.2.2,endAt.1,endAt.2⟩
      else none
    | none => none
  else none

def readField (p : Problem) (w : FieldWire) : Option (FieldDerivation p) :=
  match only : visible p.state.core p.root with
  | [d] => do
    let source ← readReadyHeader p (actualQueryDecoder p.state.core) d only w.emptyKey
    packRead p d source w
  | _ => none

theorem independent_routed_field_derivation_replays457 (p : Problem) (source : FieldDerivation p) :
    ∃ w, readField p w = some source := by
  obtain ⟨cursor,read⟩ := (mixed_cycle_has_actual_finite_wire _ _ _ _ _ _).mpr
    ⟨source.visited,ending_field_nonempty456 source.fieldEnd,source.cycle⟩
  refine ⟨⟨source.source.emptyKey,eraseCursor p.state.core cursor⟩,?_⟩
  have ok := exact_same_written_local_ready_header_replays457 source.source
  have gap := (outside_conservative_exact457 ..).mpr source.actualGap
  unfold readField
  split
  · rename_i row one
    have same := List.singleton_inj.mp (one.symm.trans source.source.only)
    subst row
    simp only [ok,Bind.bind,Option.bind,packRead,gap,dite_true]
    split
    · rename_i path last found
      rw [lift_eraseCursor,read] at found
      obtain ⟨eqPath,eqLast⟩ := Prod.mk.inj (Option.some.inj found)
      subst path
      subst last
      simp [source.fieldEnd,source.containsMix]
    · rename_i found
      rw [lift_eraseCursor,read] at found
      cases found
  · rename_i missed
    exact (missed _ source.source.only).elim

def checkField (p : Problem) (r : ReportAtField) (w : FieldWire) : Bool :=
  ((readField p w).map fun result => decide (result.report = r)).getD false

theorem actual_routed_field_report_iff_finite_wire457 (p : Problem) (r : ReportAtField) :
    (∃ w, checkField p r w = true) ↔ ExactField p r := by
  constructor
  · rintro ⟨w,ok⟩
    cases found : readField p w with
    | none => simp [checkField,found] at ok
    | some a => exact ⟨a,of_decide_eq_true (by simpa [checkField,found] using ok)⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨w,there⟩ := independent_routed_field_derivation_replays457 p a
    exact ⟨w,by simp [checkField,there]⟩

theorem routed_field_rejection_is_not_parent_root457 {p : Problem} (how : FieldDerivation p) :
    ¬ RootCycle p.state p.root := by
  have safe := mixed_nonempty_trail_has_safe_root456 how.visited (ending_field_nonempty456 how.fieldEnd)
  rintro ⟨q,found,cycle⟩
  rw [how.source.argv] at found
  cases List.mem_singleton.mp found
  exact safe cycle

def recordLocalRule457 : SourcePrimitives where
  elected := fun _ _ _ _ => False
  other := fun s q v needs =>
    needs = [] ∧ v = .rejected ∧ Nonempty (FieldDerivation ⟨s,q⟩)

theorem routed_field_diagnosis_is_precise_source_trace457 {p : Problem} (how : FieldDerivation p) :
    Nonempty (SourceTrace recordLocalRule457 p.state p.root .rejected none) :=
  ⟨.other .rejected (routed_field_rejection_is_not_parent_root457 how) ⟨rfl,rfl,⟨how⟩⟩ .nil⟩

theorem no_routed_field_rule_selects_or_emits_where457 {p : Problem} {e : Event p.state p.root}
    {tr : Tree} : ¬ Nonempty (SourceTrace recordLocalRule457 p.state p.root tr (some e)) := by
  rintro ⟨trace⟩
  cases trace with
  | selected _ _ impossible _ _ => exact impossible.elim

def FieldEvidence (p : Problem) (m : I72.Model) (r : ReportAtField) : Prop :=
  ∃ a : FieldDerivation p, a.report = r ∧
    ModelMixedTrail p.state.core m a.source.arg.lower a.source.query a.path a.terminal ∧
    Nonempty (SourceTrace recordLocalRule457 p.state p.root .rejected none)

theorem routed_field_report_is_sound_in_every_same_fit457 {p : Problem} {r : ReportAtField}
    (exact : ExactField p r) (m : I72.Model) (fit : I72.Fits p.state m) :
    FieldEvidence p m r := by
  obtain ⟨a,rfl⟩ := exact
  exact ⟨a,rfl,routed_mixed_trail_is_same_model456 a.visited m fit,
    routed_field_diagnosis_is_precise_source_trace457 a⟩

abbrev OldRoutedEntry := RoutedReadyRecord457.Report
abbrev OldRoutedWitness := RoutedReadyRecord457.Witness

inductive Report where
  | previous (r : OldRoutedEntry)
  | fieldK2 (r : ReportAtField)

inductive Witness where
  | previous (w : OldRoutedWitness)
  | fieldK2 (w : FieldWire)

/-- Cumulative C456 directly delegates the exact C457 pure-field Ready entry, which delegates C456. -/
def check_full_ready_mixed457 (p : FullProblem) : Report → Witness → Bool
  | .previous r, .previous w => RoutedReadyRecord457.check_full457 p r w
  | .fieldK2 r, .fieldK2 w => checkField p.old r w
  | _,_ => false

theorem all_previous_canonical_Bools_unchanged457 (p : FullProblem) (r : OldRoutedEntry) (w : OldRoutedWitness) :
    check_full_ready_mixed457 p (.previous r) (.previous w) =
    RoutedReadyRecord457.check_full457 p r w := rfl

def ClassifiedAs (p : FullProblem) : Report → Prop
  | .previous r => RoutedReadyRecord457.ClassifiedAs p r
  | .fieldK2 r => ExactField p.old r

def ReportEvidence (p : FullProblem) (m : I72.Model) : Report → Prop
  | .previous r => RoutedReadyRecord457.ReportEvidence p m r
  | .fieldK2 r => FieldEvidence p.old m r

theorem check_full_sound457 (p : FullProblem) (r : Report) (w : Witness)
    (ok : check_full_ready_mixed457 p r w = true) :
    ClassifiedAs p r ∧ ∀ m, FitsFull p.state m → ReportEvidence p m r := by
  cases r with
  | previous r =>
    cases w with
    | previous w => exact RoutedReadyRecord457.check_full_sound457 p r w ok
    | fieldK2 w => cases ok
  | fieldK2 r =>
    cases w with
    | previous w => cases ok
    | fieldK2 w =>
      have exact := (actual_routed_field_report_iff_finite_wire457 p.old r).mp ⟨w,ok⟩
      exact ⟨exact,fun m fit => routed_field_report_is_sound_in_every_same_fit457 exact m fit.1⟩

theorem independent_routed_field_derivation_has_cumulative_witness457
    (p : FullProblem) (r : ReportAtField) (exact : ExactField p.old r) :
    ∃ w, check_full_ready_mixed457 p (.fieldK2 r) (.fieldK2 w) = true :=
  (actual_routed_field_report_iff_finite_wire457 p.old r).mpr exact

end Yulang.GeneralDeclarativeI65.I72.RoutedReadyMixed457
