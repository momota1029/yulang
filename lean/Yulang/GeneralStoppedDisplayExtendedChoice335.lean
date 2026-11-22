import Yulang.GeneralStoppedDisplayExtended335
import Yulang.GeneralStoppedDisplayChoice335

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralStoppedDisplayExtendedChoice335
open GeneralStoppedDisplayProjection335 (ordinary supported parentDemand)
open GeneralStoppedDisplayExtended335
open GeneralStoppedDisplayCut335 (reminted protect)
open GeneralStoppedDisplayGuard335 (waiting list_print int_print listCode intCode parent_declared)
open GeneralStoppedDisplayChoice335 (right_of_row no_ending no_prefix)
open GeneralNominalExamples (registry interpretation intDisplay)
open GeneralDeclarationExamples (display wrap constructors)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (restriction from_source)
open GeneralDeclarativeLowerKnown321 (Alias Ready knows_row alias_refl alias_mono)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeObserverGrowth330 (trace sources_grow)
open GeneralDeclarativeGrowth327 (fits Extends)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def mark (n : Nat) := if n = 0 then (1 : Nat) else 0

def atomOK (a : PresenceNormalForm.Atom Nat) : Bool :=
  match a with
  | .tyLe (.var x) (.var y) => decide (mark x = mark y)
  | _ => true

theorem atom_check : expanded.normal.ordinary.all atomOK = true := by decide +kernel
theorem interval_check : expanded.normal.intervals.all (fun p => decide (mark p.1 = mark p.2)) = true := rfl

theorem bound_mark (path : Bound expanded.normal a b) : mark a = mark b := by
  induction path with
  | interval h => exact of_decide_eq_true (List.all_eq_true.mp interval_check _ h)
  | constraint h => exact of_decide_eq_true (List.all_eq_true.mp atom_check _ h)
  | refl => rfl
  | trans _ _ a b => exact a.trans b

theorem alias_mark (a : Alias expanded x y) : mark x = mark y := by
  induction a with
  | bounds a _ => exact bound_mark a
  | forward h | backward h =>
    rcases List.mem_cons.mp h with l|r
    · cases l
    · have impossible := List.mem_singleton.mp r
      cases impossible
  | trans _ _ a b => exact a.trans b

theorem src_original (h : e ∈ (restriction (augmented done)).equations) :
    e ∈ (restriction (supported done)).equations := (keeps_original_rows done) ▸ h

theorem aliases_support (a : Alias (restriction (augmented done)) x y) : mark x = mark y := by
  apply alias_mark
  exact alias_mono (s := restriction (augmented done)) (t := expanded) rfl
    (fun _ h => GeneralStoppedDisplayGuard335.original_rows (src_original h)) a

theorem no_cycles : ∀ src, ¬AliasCycle expanded (observed expanded) src := by
  apply graph_no_cycle mark (fun _ _ h => alias_mark h)
  rintro n tag child ⟨e,h,code⟩ member
  rcases List.mem_cons.mp h with l|r
  · cases l
    cases code
    cases List.mem_singleton.mp member
    decide +kernel
  · have impossible := List.mem_singleton.mp r
    cases impossible
    cases code
    cases member

theorem safe (tests : Candidates) (d : Demand) : ¬Recurs expanded registry interpretation tests d := by
  rintro (⟨a,_,c⟩|⟨_,_,_,_,_,_,_,_,_,src,_,c⟩)
  · exact no_cycles a.lower c
  · exact no_cycles src c

theorem same_read_rows {done : Nat → Prop} :
    Extends (restriction (supported done)) (restriction (augmented done)) :=
  ⟨contains_raw.constraints,contains_raw.intervals,fun _ found => (keeps_original_rows done).symm ▸ found⟩

theorem direct_list (done : Nat → Prop) (mode) :
    Trace (restriction (augmented done)) mode 0 listCode [⟨0,.actual,1⟩] :=
  trace same_read_rows (GeneralStoppedDisplayGuard335.list_trace done mode)

theorem scalar_from {done : Nat → Prop} (link : Alias (restriction (augmented done)) src 1) (mode) :
    Trace (restriction (augmented done)) mode src intCode [] :=
  .primitive (args := []) link ((same_read_rows (done := done)).equations
    (GeneralStoppedDisplayProjection335.int_allowed done)) .nil

theorem lo_alias {done : Nat → Prop} : Alias (restriction (augmented done)) 2 1 := by
  refine .bounds (.constraint ?_) (.constraint ?_)
  all_goals apply List.mem_append_right _; decide +kernel

theorem hi_alias {done : Nat → Prop} : Alias (restriction (augmented done)) 3 1 := by
  refine .bounds (.constraint ?_) (.constraint ?_)
  all_goals apply List.mem_append_right _; decide +kernel

theorem child_bounds : Bounds expanded ⟨2,1,3⟩ := by
  refine ⟨.constraint ?_,.constraint ?_⟩
  all_goals apply List.mem_append_right _; decide +kernel

theorem positive_parent (done : Nat → Prop) :
    HeadMatches (restriction (augmented done)) constructors interpretation parentDemand display :=
  .cons ⟨GeneralDeclarativeOpaqueNominal328.point_bounded _ _,_,_,_,list_print,
    direct_list done .lower,direct_list done .upper⟩ .nil

theorem positive_child (done : Nat → Prop) :
    HeadMatches (restriction (augmented done)) constructors interpretation reminted intDisplay :=
  .cons ⟨child_bounds,_,_,_,int_print,scalar_from lo_alias .lower,scalar_from hi_alias .upper⟩ .nil

theorem no_spine (found : Spine (restriction (augmented done)) n fs t) : False := by
  cases found with
  | width _ row | exactEnd _ row | cons _ row _ =>
    rcases right_of_row (src_original row) with ⟨_,bad⟩|⟨_,bad⟩ <;> cases bad
  | inline _ ending row => exact no_ending ending (src_original row)
  | prefixed _ row _ => exact no_prefix (src_original row)

theorem start (read : Read (restriction (augmented done)) mode (.variable s) code used) :
    (∃ v, code = .variable v) ∨ ∃ site rhs, Alias (restriction (augmented done)) s site ∧
      (⟨site,rhs⟩ : Equation) ∈ (restriction (augmented done)).equations ∧
      Read (restriction (augmented done)) mode rhs code used := by
  cases read with
  | capture => exact .inl ⟨_,rfl⟩
  | expose _ link placed next => exact .inr ⟨_,_,link,placed,next⟩
  | record sp _ _ _ _ _ _ =>
    cases sp with
    | terminal t => cases t
    | name r => exact (no_spine r).elim

theorem parent_wrong_trace (read : Trace (restriction (augmented done)) mode 0 intCode uses) :
    False := by
  cases read with
  | primitive via row _ =>
    rcases right_of_row (src_original row) with ⟨_,same⟩|⟨where_,_⟩
    · cases same
    · have h := aliases_support via
      rw [where_] at h
      cases h

theorem child_wrong_trace (read : Trace (restriction (augmented done)) mode 2 listCode uses) :
    False := by
  cases read with
  | nominal via row _ =>
    rcases right_of_row (src_original row) with ⟨where_,_⟩|⟨_,same⟩
    · have h := aliases_support via
      rw [where_] at h
      cases h
    · cases same

theorem parent_wrong_read (read : Read (restriction (augmented done)) mode (.variable 0) intCode uses) :
    False := by
  rcases start read with ⟨_,bad⟩|⟨_,_,linked,row,more⟩
  · cases bad
  · rcases right_of_row (src_original row) with ⟨_,same⟩|⟨where_,_⟩
    · cases same
      generalize expected : intCode = code at more
      cases more with
      | capture => cases expected
      | nominal => cases expected
      | record sp _ _ _ _ _ _ => cases sp with | terminal t => cases t
    · have h := aliases_support linked
      rw [where_] at h
      cases h

theorem child_wrong_read (read : Read (restriction (augmented done)) mode (.variable 2) listCode uses) :
    False := by
  rcases start read with ⟨_,bad⟩|⟨_,_,linked,row,more⟩
  · cases bad
  · rcases right_of_row (src_original row) with ⟨where_,_⟩|⟨_,same⟩
    · have h := aliases_support linked
      rw [where_] at h
      cases h
    · cases same
      generalize expected : listCode = code at more
      cases more with
      | capture => cases expected
      | primitive => cases expected
      | record sp _ _ _ _ _ _ => cases sp with | terminal t => cases t

theorem wrong_parent :
    ¬(candidates (augmented done) registry interpretation waiting).viable parentDemand intDisplay := by
  rintro (one|two)
  · cases one with
    | cons h _ =>
      obtain ⟨_,_,_,_,decoded,seen,_⟩ := h
      cases Option.some.inj (decoded.symm.trans int_print)
      exact parent_wrong_trace seen
  · cases two with
    | cons h _ =>
      obtain ⟨_,_,_,_,decoded,seen,_⟩ := h
      cases Option.some.inj (decoded.symm.trans int_print)
      exact parent_wrong_read seen

theorem wrong_child :
    ¬(candidates (augmented done) registry interpretation waiting).viable reminted display := by
  rintro (one|two)
  · cases one with
    | cons h _ =>
      obtain ⟨_,_,_,_,decoded,seen,_⟩ := h
      cases Option.some.inj (decoded.symm.trans list_print)
      exact child_wrong_trace seen
  · cases two with
    | cons h _ =>
      obtain ⟨_,_,_,_,decoded,seen,_⟩ := h
      cases Option.some.inj (decoded.symm.trans list_print)
      exact child_wrong_read seen

theorem elect_parent (done : Nat → Prop) :
    Elected expanded registry interpretation (augmented done) (candidates (augmented done) registry interpretation waiting)
      parentDemand display := by
  have ready : Ready (augmented done) parentDemand := by
    intro arg seen; cases List.mem_singleton.mp seen
    exact ⟨_,knows_row (same_read_rows.equations (GeneralStoppedDisplayProjection335.list_allowed done)) rfl⟩
  refine ⟨ready,safe _ _,fun ⟨_,_,no⟩ => no,⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,.inl (positive_parent done)⟩,?_⟩
  rintro decl ⟨⟨present,role⟩,hit⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl|rfl|rfl
  · exact (wrong_parent hit).elim
  · rfl
  · cases role

theorem elect_child (done : Nat → Prop) :
    Elected expanded registry interpretation (augmented done) (candidates (augmented done) registry interpretation waiting)
      reminted intDisplay := by
  have ready : Ready (augmented done) reminted := by
    intro arg seen; cases List.mem_singleton.mp seen
    exact ⟨_,GeneralDeclarativeLowerKnown321.knows_alias lo_alias
      (knows_row (same_read_rows.equations (GeneralStoppedDisplayProjection335.int_allowed done)) rfl)⟩
  refine ⟨ready,safe _ _,fun ⟨_,_,no⟩ => no,⟨⟨List.mem_cons_self,rfl⟩,.inl (positive_child done)⟩,?_⟩
  rintro decl ⟨⟨present,role⟩,hit⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl|rfl|rfl
  · rfl
  · exact (wrong_child hit).elim
  · cases role

end Yulang.GeneralStoppedDisplayExtendedChoice335
