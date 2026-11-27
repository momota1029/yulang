import Yulang.GeneralDeclarativeI65I74RoutedReadyHeader457

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoutedReadyRecord457
open Yulang.GeneralDeclarativeI65
open RecordTraversal455
open RecordTraversal455 (TrailPath)
open RoutedReadyHeader457 (AuthoredHeader readReadyHeader exact_same_written_local_ready_header_replays457)
open RoutedNominalMixed456 (actualQueryDecoder)
open GeneralDeclarationPatterns (ConservativeSmaller)
open RetainedFull445
open RecordTrail455 (tokenOps ModelTrail routedOps independent_routed_trail_observes_same_model455)
open GeneralDeclarations (Declaration)
open Checker408 (Problem)
open CommonRoleOutermostResolver (Tree Summarizes)

abbrev OldRoutedEntry := RoutedNominalMixed456.Report
abbrev OldRoutedWitness := RoutedNominalMixed456.Witness

def outsideConservative (head body : List GeneralDeclarationPatterns.Pattern) : Bool :=
  !CheckedRoles.checkCondition (GeneralDeclarationPatterns.lowerArgs (GeneralDeclarationPatterns.normalizeArgs head))
    ⟨0,GeneralDeclarationPatterns.counted body⟩

theorem outside_conservative_exact457 (head body) :
    outsideConservative head body = true ↔ ¬ ConservativeSmaller head body := by
  simp [outsideConservative,ConservativeSmaller]

/-- The clause address authenticates the written declaration only.
    The actual diagnostic is at the field, not a generated where child. -/
structure FieldReport where
  occurrence : List Nat
  declaration : Nat
  originalClauseOrdinal : Nat
  originalClauseId : Nat
  path : TrailPath
  terminal : Nat
  deriving DecidableEq, Repr

structure FieldDerivation (p : Problem) where
  declaration : Declaration
  source : AuthoredHeader p (actualQueryDecoder p.state.core) declaration
  notConservative : ¬ ConservativeSmaller declaration.head source.clause.arguments
  path : TrailPath
  terminal : Nat
  visited : ExactCycleVisit p.state.core.current.ordinary (routedOps p.state.core)
    source.arg.lower source.query path terminal

def FieldDerivation.report {p : Problem} (a : FieldDerivation p) : FieldReport :=
  ⟨p.root.occurrence,a.declaration.id,0,a.source.clause.id,a.path,a.terminal⟩

def ExactField (p : Problem) (r : FieldReport) : Prop :=
  ∃ a : FieldDerivation p, a.report = r

open RoutedRecord455 (FieldWire liftCursor eraseCursor lift_eraseCursor)

theorem exact_local_ready_does_not_supply_legacy_checked457 {p : Problem} (x : FieldDerivation p) :
    ¬ GeneralDeclarations.DeclarationChecked
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry p.state.core.current).constructors
      (GeneralDeclarativeWitnessDeclaredState357.authoredRegistry p.state.core.current).roles x.declaration :=
  fun old => x.notConservative ((RecordDiagnosticReady457.conservativity_is_the_only_missing_closed_header_field457
    x.source.preserved).mp old)

def readField (p : Problem) (w : FieldWire) : Option (FieldDerivation p) :=
  match only : visible p.state.core p.root with
  | [d] => do
    let source ← readReadyHeader p (actualQueryDecoder p.state.core) d only w.emptyKey
    if gap : outsideConservative d.head source.clause.arguments = true then
      match read : readCycleVisit p.state.core.current.ordinary (routedOps p.state.core)
        source.arg.lower source.query (liftCursor p.state.core w.cursor) with
      | some (path,last) => some ⟨d,source,(outside_conservative_exact457 ..).mp gap,path,last,read_cycle_visit_sound455 read⟩
      | none => none
    else none
  | _ => none

theorem independent_routed_field_derivation_replays457 (p : Problem) (source : FieldDerivation p) :
    ∃ w, readField p w = some source := by
  obtain ⟨cursor,read⟩ := exact_cycle_visit_has_finite_wire455 source.visited
  refine ⟨⟨source.source.emptyKey,eraseCursor p.state.core cursor⟩,?_⟩
  have ok := exact_same_written_local_ready_header_replays457 source.source
  have gap := (outside_conservative_exact457 ..).mpr source.notConservative
  unfold readField
  split
  · rename_i row one
    have same := List.singleton_inj.mp (one.symm.trans source.source.only)
    subst row
    simp only [ok,Bind.bind,Option.bind,gap,dite_true]
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

theorem actual_routed_field_report_iff_finite_wire457 (p : Problem) (r : FieldReport) :
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
  have safe := (exact_cycle_visit_is_safe_at_root_and_real_at_site455 how.visited).1
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

def FieldEvidence (p : Problem) (m : I72.Model) (r : FieldReport) : Prop :=
  ∃ a : FieldDerivation p, a.report = r ∧
    ModelTrail p.state.core m a.source.arg.lower a.source.query a.path a.terminal ∧
    Nonempty (SourceTrace recordLocalRule457 p.state p.root .rejected none)

theorem routed_field_report_is_sound_in_every_same_fit457 {p : Problem} {r : FieldReport}
    (exact : ExactField p r) (m : I72.Model) (fit : I72.Fits p.state m) :
    FieldEvidence p m r := by
  obtain ⟨a,rfl⟩ := exact
  exact ⟨a,rfl,independent_routed_trail_observes_same_model455 a.visited.1 m fit,
    routed_field_diagnosis_is_precise_source_trace457 a⟩

inductive Report where
  | previous (r : OldRoutedEntry)
  | fieldK2 (r : FieldReport)

inductive Witness where
  | previous (w : OldRoutedWitness)
  | fieldK2 (w : FieldWire)

/-- Canonical C457: delegate precisely C456; new branch uses local Ready only for K2. -/
def check_full457 (p : FullProblem) : Report → Witness → Bool
  | .previous r, .previous w => RoutedNominalMixed456.check_full_nominal456 p r w
  | .fieldK2 r, .fieldK2 w => checkField p.old r w
  | _,_ => false

theorem all_previous_canonical_Bools_unchanged457 (p : FullProblem) (r : OldRoutedEntry) (w : OldRoutedWitness) :
    check_full457 p (.previous r) (.previous w) =
    RoutedNominalMixed456.check_full_nominal456 p r w := rfl

def ClassifiedAs (p : FullProblem) : Report → Prop
  | .previous r => RoutedNominalMixed456.ClassifiedAs p r
  | .fieldK2 r => ExactField p.old r

def ReportEvidence (p : FullProblem) (m : I72.Model) : Report → Prop
  | .previous r => RoutedNominalMixed456.ReportEvidence p m r
  | .fieldK2 r => FieldEvidence p.old m r

theorem check_full_sound457 (p : FullProblem) (r : Report) (w : Witness)
    (ok : check_full457 p r w = true) :
    ClassifiedAs p r ∧ ∀ m, FitsFull p.state m → ReportEvidence p m r := by
  cases r with
  | previous r =>
    cases w with
    | previous w => exact RoutedNominalMixed456.check_full_sound456 p r w ok
    | fieldK2 w => cases ok
  | fieldK2 r =>
    cases w with
    | previous w => cases ok
    | fieldK2 w =>
      have exact := (actual_routed_field_report_iff_finite_wire457 p.old r).mp ⟨w,ok⟩
      exact ⟨exact,fun m fit => routed_field_report_is_sound_in_every_same_fit457 exact m fit.1⟩

theorem independent_routed_field_derivation_has_cumulative_witness457
    (p : FullProblem) (r : FieldReport) (exact : ExactField p.old r) :
    ∃ w, check_full457 p (.fieldK2 r) (.fieldK2 w) = true :=
  (actual_routed_field_report_iff_finite_wire457 p.old r).mpr exact

end Yulang.GeneralDeclarativeI65.I72.RoutedReadyRecord457
