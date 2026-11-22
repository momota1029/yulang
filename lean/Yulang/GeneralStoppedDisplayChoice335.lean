import Yulang.GeneralStoppedDisplayGuard335

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralStoppedDisplayChoice335
open GeneralNominalExamples (registry interpretation intDisplay)
open GeneralDeclarationExamples (display wrap)
open GeneralStoppedDisplayProjection335
open GeneralStoppedDisplayGuard335
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativePriority321 (Survives)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeDemand320 (Demand)
open CommonRoleCanonicalRows (Row)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRecordSpine330 (Terminal)

theorem right_of_row {n : Nat} {e : Expr} (inView : (⟨n,e⟩ : Equation) ∈ (restriction (supported done)).equations) :
    (n = 0 ∧ e = listRow.right) ∨ (n = 1 ∧ e = scalarRow.right) := by
  rcases List.mem_cons.mp (original_rows inView) with a|h
  · cases a; exact Or.inl ⟨rfl,rfl⟩
  · have b := List.mem_singleton.mp h
    cases b; exact Or.inr ⟨rfl,rfl⟩

theorem row_zero (inView : (⟨0,e⟩ : Equation) ∈ (restriction (supported done)).equations) :
    e = listRow.right := by
  rcases right_of_row inView with ⟨_,rfl⟩|⟨bad,_⟩
  · rfl
  · cases bad

theorem row_one (inView : (⟨1,e⟩ : Equation) ∈ (restriction (supported done)).equations) :
    e = scalarRow.right := by
  rcases right_of_row inView with ⟨bad,_⟩|⟨_,rfl⟩
  · cases bad
  · rfl

theorem no_prefix {front : Row Expr}
    (stored : (⟨owner,withTail front (.variable rest)⟩ : Equation) ∈ (restriction (supported done)).equations) :
    False := by
  cases front <;> rcases right_of_row stored with ⟨_,bad⟩|⟨_,bad⟩ <;> cases bad

theorem no_ending {fields : Row Expr} (endOf : Terminal last)
    (stored : (⟨owner,withTail fields last⟩ : Equation) ∈ (restriction (supported done)).equations) :
    False := by
  cases fields with
  | nil =>
    cases endOf <;> rcases right_of_row stored with ⟨_,bad⟩|⟨_,bad⟩ <;> cases bad
  | cons field rest =>
    rcases right_of_row stored with ⟨_,bad⟩|⟨_,bad⟩ <;> cases bad

theorem no_spine (found : Spine (restriction (supported done)) n fields tail) : False := by
  cases found with
  | width _ row | exactEnd _ row | cons _ row _ =>
    rcases right_of_row row with ⟨_,bad⟩|⟨_,bad⟩ <;> cases bad
  | inline _ terminal row => exact no_ending terminal row
  | prefixed _ row _ => exact no_prefix row

theorem starts (found : Read (restriction (supported done)) mode (.variable n) code used) :
    (∃ name, code = .variable name) ∨
      ∃ owner rhs, Alias (restriction (supported done)) n owner ∧
        (⟨owner,rhs⟩ : Equation) ∈ (restriction (supported done)).equations ∧
        Read (restriction (supported done)) mode rhs code used := by
  cases found with
  | capture => exact .inl ⟨_,rfl⟩
  | expose _ alias row next => exact .inr ⟨_,_,alias,row,next⟩
  | record shape _ _ _ _ _ _ =>
    cases shape with
    | terminal t => cases t
    | name seen => exact (no_spine seen).elim

theorem nominal_stays
    (found : Read (restriction (supported done)) mode (.nominal n src) code used) :
    (∃ name, code = .variable name) ∨ ∃ args, code = .nominal n args := by
  cases found with
  | capture => exact .inl ⟨_,rfl⟩
  | nominal => exact .inr ⟨_,rfl⟩
  | record shape _ _ _ _ _ _ =>
    cases shape with
    | terminal endOf => cases endOf

theorem int_stays
    (found : Read (restriction (supported done)) mode intCode code used) :
    (∃ name, code = .variable name) ∨ ∃ args, code = .primitive (.scalar .int) args := by
  cases found with
  | capture => exact .inl ⟨_,rfl⟩
  | primitive => exact .inr ⟨_,rfl⟩
  | record shape _ _ _ _ _ _ =>
    cases shape with
    | terminal endOf => cases endOf

theorem wrong_trace_scalar (found : Trace (restriction (supported done)) mode 0 intCode used) : False := by
  cases found with
  | primitive alias row _ =>
    cases supported_alias_identity alias
    cases row_zero row

theorem wrong_trace_list (found : Trace (restriction (supported done)) mode 1 listCode used) : False := by
  cases found with
  | nominal alias row _ =>
    cases supported_alias_identity alias
    cases row_one row

theorem wrong_inline_scalar (found : Read (restriction (supported done)) mode (.variable 0) intCode used) :
    False := by
  rcases starts found with ⟨_,bad⟩|⟨_,rhs,alias,row,next⟩
  · cases bad
  · cases supported_alias_identity alias
    cases row_zero row
    rcases nominal_stays next with ⟨_,bad⟩|⟨_,bad⟩ <;> cases bad

theorem wrong_inline_list (found : Read (restriction (supported done)) mode (.variable 1) listCode used) :
    False := by
  rcases starts found with ⟨_,bad⟩|⟨_,rhs,alias,row,next⟩
  · cases bad
  · cases supported_alias_identity alias
    cases row_one row
    rcases int_stays next with ⟨_,bad⟩|⟨_,bad⟩ <;> cases bad

theorem no_parent_scalar :
    ¬(candidates (supported done) registry interpretation waiting).viable parentDemand intDisplay := by
  intro viable
  rcases viable with probe|probe
  · cases probe with
    | cons matchHead _ =>
      obtain ⟨_,_,_,_,printed,seen,_⟩ := matchHead
      cases Option.some.inj (printed.symm.trans int_print)
      exact wrong_trace_scalar seen
  · cases probe with
    | cons matchHead _ =>
      obtain ⟨_,_,_,_,printed,seen,_⟩ := matchHead
      cases Option.some.inj (printed.symm.trans int_print)
      exact wrong_inline_scalar seen

theorem no_child_list :
    ¬(candidates (supported done) registry interpretation waiting).viable childDemand display := by
  intro viable
  rcases viable with probe|probe
  · cases probe with
    | cons matchHead _ =>
      obtain ⟨_,_,_,_,printed,seen,_⟩ := matchHead
      cases Option.some.inj (printed.symm.trans list_print)
      exact wrong_trace_list seen
  · cases probe with
    | cons matchHead _ =>
      obtain ⟨_,_,_,_,printed,seen,_⟩ := matchHead
      cases Option.some.inj (printed.symm.trans list_print)
      exact wrong_inline_list seen

theorem parent_choice (done : Nat → Prop) :
    Elected ordinary registry interpretation (supported done) (candidates (supported done) registry interpretation waiting)
      parentDemand display := by
  refine ⟨parent_ready done,safe _ _,fun ⟨_,_,no⟩ => no,
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,.inl (parent_matches done)⟩,?_⟩
  rintro candidate ⟨⟨visible,role⟩,hit⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl|rfl|rfl
  · exact (no_parent_scalar hit).elim
  · rfl
  · cases role

theorem child_choice (done : Nat → Prop) :
    Elected ordinary registry interpretation (supported done) (candidates (supported done) registry interpretation waiting)
      childDemand intDisplay := by
  refine ⟨child_ready done,safe _ _,fun ⟨_,_,no⟩ => no,
    ⟨⟨List.mem_cons_self,rfl⟩,.inl (child_matches done)⟩,?_⟩
  rintro candidate ⟨⟨visible,role⟩,hit⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl|rfl|rfl
  · rfl
  · exact (no_child_list hit).elim
  · cases role

end Yulang.GeneralStoppedDisplayChoice335
