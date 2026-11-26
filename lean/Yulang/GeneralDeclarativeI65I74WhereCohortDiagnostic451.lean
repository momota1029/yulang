import Yulang.GeneralDeclarativeI65I74WhereCohortRead451

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Clause)
open Checker408 (Problem)
open List410 (ExactEscapeWire)
open SplitEscape446 (splitCheck446 checked_split_escape_excludes_exact_raw_K2446)
open SplitEscape446.SplitCompact447 (raw_safe_iff_small_witness447)
open GeneralDeclarativeWitnessCycle350 (Wire)

inductive RawRead (s : I72.State) (q : I72.Request) : Bool → Type where
  | cycle : RootCycle s q → RawRead s q true
  | safe : ¬RootCycle s q → RawRead s q false

theorem RawRead.exact {s q b} (data : RawRead s q b) : b = true ↔ RootCycle s q := by
  cases data with
  | cycle h => simp [h]
  | safe h => simp [h]

inductive RootWire where
  | cycle (w : Wire)
  | safe (w : ExactEscapeWire)

def readRawStatus (s : I72.State) (q : I72.Request) :
    RootWire → Option (Σ b, RawRead s q b)
  | .cycle w =>
      if cy : GeneralDeclarativeWitnessCycle350.check s.core.current.ordinary q.demand w = true
      then some ⟨true,.cycle (GeneralDeclarativeWitnessCycle350.rooted cy)⟩ else none
  | .safe w =>
      (readPoint q).bind fun a =>
        if esc : splitCheck446 s.core.current.ordinary a.center w = true
        then some ⟨false,.safe (fun cy => checked_split_escape_excludes_exact_raw_K2446 esc
          ((root_cycle_exact_named_point451 a).mp cy))⟩ else none

theorem original_status_has_exact_wire451 {s q b} (a : ActualPoint q) (data : RawRead s q b) :
    ∃ w, readRawStatus s q w = some ⟨b,data⟩ := by
  cases data with
  | cycle yes =>
    have fact : GeneralDeclarativePriority321.RootRecurs s.core.current.ordinary q.demand := yes
    obtain ⟨w,ok⟩ := (raw_child_cycle_has_finite_original_wire450 _ _).mp fact
    exact ⟨.cycle w,by simp [readRawStatus,ok]⟩
  | safe no =>
    have safe := fun h => no ((root_cycle_exact_named_point451 a).mpr h)
    obtain ⟨w,ok,_,_⟩ := (raw_safe_iff_small_witness447 s.core.current.ordinary a.center).mp safe
    exact ⟨.safe w,by simp [readRawStatus,point_reader_recovers_independent_actual_named_center451 a,
      ok,Option.bind]⟩

inductive RawStatuses (s : I72.State) : List I72.Request → List Bool → Type where
  | nil : RawStatuses s [] []
  | cons {q qs b bs} (read : RawRead s q b) (rest : RawStatuses s qs bs) :
      RawStatuses s (q::qs) (b::bs)

def readStatuses (s : I72.State) : (qs : List I72.Request) → List RootWire →
    Option (Σ bs, RawStatuses s qs bs)
  | [],[] => some ⟨[],.nil⟩
  | q::qs,w::ws => do
    let ⟨b,read⟩ ← readRawStatus s q w
    let ⟨bs,other⟩ ← readStatuses s qs ws
    pure ⟨b::bs,.cons read other⟩
  | _,_ => none

theorem every_original_status_has_exact_replay451 {s qs bs} (a : RawStatuses s qs bs)
    (points : Points qs) : ∃ w, readStatuses s qs w = some ⟨bs,a⟩ := by
  induction a with
  | nil => exact ⟨[],rfl⟩
  | cons head _ next =>
    cases points with
    | cons first later =>
      obtain ⟨w,okay⟩ := original_status_has_exact_wire451 first head
      obtain ⟨ws,okTail⟩ := next later
      exact ⟨w::ws,by simp [readStatuses,okay,okTail,Bind.bind,Option.bind,Option.pure_def]⟩

theorem every_original_request_has_a_raw_status451 (s : I72.State) (qs : List I72.Request) :
    ∃ bs, Nonempty (RawStatuses s qs bs) := by
  classical
  induction qs with
  | nil => exact ⟨[],⟨.nil⟩⟩
  | cons q qs ih =>
    obtain ⟨later,⟨trail⟩⟩ := ih
    by_cases cy : RootCycle s q
    · exact ⟨true::later,⟨.cons (.cycle cy) trail⟩⟩
    · exact ⟨false::later,⟨.cons (.safe cy) trail⟩⟩

theorem status_position_is_actual_child451 {s qs bs} (a : RawStatuses s qs bs)
    (i : Nat) {q : I72.Request} (original : qs[i]? = some q) :
    ∃ b, bs[i]? = some b ∧ (b = true ↔ RootCycle s q) := by
  induction a generalizing i with
  | nil => simp at original
  | cons first _ tail =>
    cases i with
    | zero =>
      have exact := Option.some.inj original
      cases exact
      exact ⟨_,rfl,first.exact⟩
    | succ i => exact tail _ (by simpa using original)

structure DiagnosticWire where
  cohorts : CohortWire
  allOriginalStatus : List RootWire

structure OriginalDiagnostic {p : Problem} (a : ParentSelection p) where
  cohorts : OriginalCohort a
  bits : List Bool
  status : RawStatuses p.state a.children bits

def readDiagnostic {p : Problem} (a : ParentSelection p) (w : DiagnosticWire) :
    Option (OriginalDiagnostic a) := do
  let c ← readCohort a w.cohorts
  let ⟨bs,states⟩ ← readStatuses p.state a.children w.allOriginalStatus
  pure ⟨c,bs,states⟩

theorem actual_diagnostic_preparation_has_finite_exact_data451
    {p : Problem} (a : ParentSelection p) (d : OriginalDiagnostic a) :
    ∃ w, readDiagnostic a w = some d := by
  obtain ⟨p,yes⟩ := actually_selected_parent_has_exact_finite_cohort_wire451 a d.cohorts
  obtain ⟨ws,ok⟩ := every_original_status_has_exact_replay451 d.status d.cohorts.points
  cases d
  exact ⟨⟨p,ws⟩,by simp [readDiagnostic,yes,ok,Bind.bind,Option.bind,Option.pure_def]⟩

theorem equal_label_is_same_raw_diagnostic_at_each_original_location451
    {p : Problem} {a : ParentSelection p} (out : OriginalDiagnostic a)
    {i j : Nat} {q v : I72.Request} (left : a.children[i]? = some q) (right : a.children[j]? = some v)
    {x y : Labeled} (lx : out.cohorts.labelled[i]? = some x) (ly : out.cohorts.labelled[j]? = some y)
    (same : x.2 = y.2) : out.bits[i]? = out.bits[j]? := by
  obtain ⟨_,_,a,b,first,last,_,common⟩ :=
    equal_label_links_actual_child_roots451 out.cohorts left right
  have la := (congrArg Prod.snd (Option.some.inj (first.symm.trans lx)))
  have lb := (congrArg Prod.snd (Option.some.inj (last.symm.trans ly)))
  have same := la.trans (same.trans lb.symm)
  obtain ⟨u,atU,hu⟩ := status_position_is_actual_child451 out.status i left
  obtain ⟨v,atV,hv⟩ := status_position_is_actual_child451 out.status j right
  rw [atU,atV]
  have agree : (u = true ↔ v = true) := hu.trans ((common same).trans hv.symm)
  cases u <;> cases v <;> simp_all

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451
