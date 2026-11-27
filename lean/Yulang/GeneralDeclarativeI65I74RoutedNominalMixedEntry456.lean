import Yulang.GeneralDeclarativeI65I74RoutedQueryHeader456
import Yulang.GeneralDeclarativeI65I74AuthoredInspectQuery456

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoutedNominalMixed456
open Yulang.GeneralDeclarativeI65
open RecordTraversal455 RecordTraversal455.MixedQA
open RecordTrail455 (tokenOps routed_read_keeps_original_physical_owner_and_source_in_each_fit455 closedRecordTerm)
open RecordTrail455.MixedNative456
open RetainedFull445
open RoutedQueryHeader456 (QueryDecoder AuthoredHeader)

def actualQueryDecoder (s : GeneralDeclarativeI65.State) : QueryDecoder s where
  declarative := AuthoredInspectQuery456.AuthoredQuery s
  decode := AuthoredInspectQuery456.compileQuery s
  exact := AuthoredInspectQuery456.compile_query_exact s
open RoutedNominalPoint456
open RoutedMixed456 (MixedReport FieldWire endsAtField ending_field_nonempty456 mixed_nonempty_trail_has_safe_root456)
open GeneralDeclarations (Declaration)
open Checker408 (Problem)
open CommonRoleOutermostResolver (Tree Summarizes)
open GeneralDeclarativeInspect321 (Visit)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed shapeOf)

def isNominalHop : Address × Nat → Bool
  | (.nominal _ _,_) => true
  | _ => false

def includesNominal (path : MixedPath) : Bool := path.any isNominalHop

theorem contains_nominal_iff_true456 (path : MixedPath) :
    includesNominal path = true ↔ ∃ key i site, (.nominal key i,site) ∈ path := by
  simp only [includesNominal,List.any_eq_true]
  constructor
  · rintro ⟨⟨addr,site⟩,member,yes⟩
    cases addr <;> try cases yes
    case mp.nominal.refl tag pos => exact ⟨tag,pos,site,member⟩
  · rintro ⟨key,i,site,member⟩
    exact ⟨_,member,rfl⟩

structure FieldDerivation (p : Problem) where
  declaration : Declaration
  source : AuthoredHeader p (actualQueryDecoder p.state.core) declaration
  path : MixedPath
  terminal : Nat
  visited : MixedTrail p.state.core.current.ordinary (nominalOps p.state.core)
    source.arg.lower source.query path terminal
  cycle : AliasCycle p.state.core.current.ordinary (observed p.state.core.current.ordinary) terminal
  fieldEnd : endsAtField path terminal = true
  containsNominal : includesNominal path = true

def FieldDerivation.report {p : Problem} (a : FieldDerivation p) : MixedReport :=
  ⟨p.root.occurrence,a.declaration.id,a.path,a.terminal⟩

def ExactField (p : Problem) (r : MixedReport) : Prop :=
  ∃ a : FieldDerivation p, a.report = r

def liftTokens (s : GeneralDeclarativeI65.State) :
    MixedWire tokenOps → MixedWire (nominalOps s)
  | .stop => .stop
  | .down x edge esc rest =>
    .down ⟨x.ordinal,x.rawAlias,x.token⟩ edge esc (liftTokens s rest)

def eraseTokens (s : GeneralDeclarativeI65.State) :
    MixedWire (nominalOps s) → MixedWire tokenOps
  | .stop => .stop
  | .down x edge esc rest =>
    .down ⟨x.ordinal,x.rawAlias,x.token⟩ edge esc (eraseTokens s rest)

theorem replay_routed_tokens_preserve_finite_data456 (s : GeneralDeclarativeI65.State)
    (w : MixedWire (nominalOps s)) : liftTokens s (eraseTokens s w) = w := by
  induction w with
  | stop => rfl
  | down x edge escape rest ih =>
    cases x
    simp [liftTokens,eraseTokens,ih]

def liftCursor (s : GeneralDeclarativeI65.State) (w : MixedCycleWire tokenOps) :
    MixedCycleWire (nominalOps s) := ⟨liftTokens s w.start,w.finish⟩

def eraseCursor (s : GeneralDeclarativeI65.State) (w : MixedCycleWire (nominalOps s)) :
    MixedCycleWire tokenOps := ⟨eraseTokens s w.start,w.finish⟩

theorem lift_eraseCursor (s : GeneralDeclarativeI65.State) (w : MixedCycleWire (nominalOps s)) :
    liftCursor s (eraseCursor s w) = w := by
  cases w
  simp [liftCursor,eraseCursor,replay_routed_tokens_preserve_finite_data456]

def packRead (p : Problem) (d : Declaration) (source : AuthoredHeader p (actualQueryDecoder p.state.core) d)
    (w : FieldWire) : Option (FieldDerivation p) :=
  match read : readMixedCycle p.state.core.current.ordinary (nominalOps p.state.core)
        source.arg.lower source.query (liftCursor p.state.core w.cursor) with
  | some (path,last) =>
    if endAt : endsAtField path last = true ∧ includesNominal path = true then
      let facts := (mixed_cycle_has_actual_finite_wire _ _ _ _ _ _).mp ⟨_,read⟩
      some ⟨d,source,path,last,facts.1,facts.2.2,endAt.1,endAt.2⟩
    else none
  | none => none

def readField (p : Problem) (w : FieldWire) : Option (FieldDerivation p) :=
  match only : visible p.state.core p.root with
  | [d] => do
    let source ← RoutedQueryHeader456.readHeader p (actualQueryDecoder p.state.core) d only w.emptyKey
    packRead p d source w
  | _ => none

theorem independent_routed_field_derivation_replays456 (p : Problem) (source : FieldDerivation p) :
    ∃ w, readField p w = some source := by
  obtain ⟨cursor,read⟩ := (mixed_cycle_has_actual_finite_wire _ _ _ _ _ _).mpr
    ⟨source.visited,ending_field_nonempty456 source.fieldEnd,source.cycle⟩
  refine ⟨⟨source.source.emptyKey,eraseCursor p.state.core cursor⟩,?_⟩
  have ok := RoutedQueryHeader456.exact_same_written_header_replays456 source.source
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
      simp [source.fieldEnd,source.containsNominal]
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

open CommonRecursiveNominalIntervals (ContextWellFormed)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)

def MeaningOfOpen (s : GeneralDeclarativeI65.State) (m : I72.Model) (logical : Nat)
    (row : Equation) (sh : Shape) (code : Expr) (addr : Address) (child : Nat) (next : Expr) : Prop :=
  RoutedMixed456.MeaningOfOpen s m logical row ∨
    ∃ p : Opened s logical row,
      m.nativeSyntax row.left = some (marker p.key p.child) ∧
      (∀ context, ContextWellFormed s.modes context (marker p.key p.child) ∧
        ContextDerives s.modes m.assignment context (marker p.key p.child) (marker p.key p.child)) ∧
      shapeOf row.right = some sh ∧ addr = .nominal p.key 0 ∧ child = p.child ∧
      ∃ arguments, code = .nominal p.key arguments ∧ arguments[0]? = some next

inductive ModelMixedTrail (s : GeneralDeclarativeI65.State) (m : I72.Model) :
    Nat → Expr → MixedPath → Nat → Prop where
  | stop : GeneralDeclarativeInspect321.Inspects code → ModelMixedTrail s m root code [] root
  | down : (∃ row ∈ s.current.ordinary.equations,
      GeneralDeclarativeLowerKnown321.Alias s.current.ordinary root row.left ∧ shapeOf row.right = some sh ∧
      MeaningOfOpen s m root row sh code a child next) → ChildAt sh code a child next →
      ModelMixedTrail s m child next tail site →
      ModelMixedTrail s m root code ((a,child)::tail) site

theorem routed_mixed_trail_is_same_model456 {s : GeneralDeclarativeI65.State} {root code path site}
    (actual : MixedTrail s.current.ordinary (nominalOps s) root code path site)
    (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m) :
    ModelMixedTrail s m root code path site := by
  induction actual with
  | stop inspected => exact .stop inspected
  | down _ auth hop _ ih =>
    obtain ⟨row,mem,alias,shape,valid⟩ := auth
    refine .down ⟨row,mem,alias,shape,?_⟩ hop ih
    change (extraOpenOps s).allowed _ _ ∨ Nonempty (Opened s _ _) at valid
    rcases valid with ordinary | branch
    · left
      rcases ordinary with rec | other
      · obtain ⟨o,seen,route,owner,ty,native,rowEq⟩ :=
          routed_read_keeps_original_physical_owner_and_source_in_each_fit455 rec m fit
        exact ⟨o,seen,route,owner,ty,native,.inl rowEq⟩
      · obtain ⟨o,seen,route,owner,ty,original,equal⟩ := other
        exact ⟨o,seen,route,owner,ty,by simpa only [owner,original] using fit.2 o seen,.inr equal⟩
    · right
      obtain ⟨nominal⟩ := branch
      have actual := literal_covariant_point_child_is_only_original_ordinal456 nominal shape hop
      exact ⟨nominal,(original_point_compares_in_the_same_model456 nominal m fit false).1,
        fun ctx => (original_point_compares_in_the_same_model456 nominal m fit ctx).2,shape,actual⟩

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

abbrev OldRoutedEntry := RoutedMixed456.Report
abbrev OldRoutedWitness := RoutedMixed456.Witness

inductive Report where
  | previous (r : OldRoutedEntry)
  | fieldK2 (r : MixedReport)

inductive Witness where
  | previous (w : OldRoutedWitness)
  | fieldK2 (w : FieldWire)

/-- Cumulative C456 directly delegates the exact prior C456 variant/pair entry. -/
def check_full_nominal456 (p : FullProblem) : Report → Witness → Bool
  | .previous r, .previous w => RoutedMixed456.check_full456 p r w
  | .fieldK2 r, .fieldK2 w => checkField p.old r w
  | _,_ => false

theorem all_previous_canonical_Bools_unchanged456 (p : FullProblem) (r : OldRoutedEntry) (w : OldRoutedWitness) :
    check_full_nominal456 p (.previous r) (.previous w) =
    RoutedMixed456.check_full456 p r w := rfl

def ClassifiedAs (p : FullProblem) : Report → Prop
  | .previous r => RoutedMixed456.ClassifiedAs p r
  | .fieldK2 r => ExactField p.old r

def ReportEvidence (p : FullProblem) (m : I72.Model) : Report → Prop
  | .previous r => RoutedMixed456.ReportEvidence p m r
  | .fieldK2 r => FieldEvidence p.old m r

theorem check_full_sound456 (p : FullProblem) (r : Report) (w : Witness)
    (ok : check_full_nominal456 p r w = true) :
    ClassifiedAs p r ∧ ∀ m, FitsFull p.state m → ReportEvidence p m r := by
  cases r with
  | previous r =>
    cases w with
    | previous w => exact RoutedMixed456.check_full_sound456 p r w ok
    | fieldK2 w => cases ok
  | fieldK2 r =>
    cases w with
    | previous w => cases ok
    | fieldK2 w =>
      have exact := (actual_routed_field_report_iff_finite_wire456 p.old r).mp ⟨w,ok⟩
      exact ⟨exact,fun m fit => routed_field_report_is_sound_in_every_same_fit456 exact m fit.1⟩

theorem independent_routed_field_derivation_has_cumulative_witness456
    (p : FullProblem) (r : MixedReport) (exact : ExactField p.old r) :
    ∃ w, check_full_nominal456 p (.fieldK2 r) (.fieldK2 w) = true :=
  (actual_routed_field_report_iff_finite_wire456 p.old r).mpr exact

end Yulang.GeneralDeclarativeI65.I72.RoutedNominalMixed456
