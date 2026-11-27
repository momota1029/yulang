import Yulang.GeneralDeclarativeI65I74OriginalPatternSite460
import Yulang.GeneralDeclarativeI65I74JointWrittenTrail460

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open GeneralNominalCenteredHeadMatExpressions (Expr)
open RecordTraversal455 (RawSnapshot naked_raw_cycle_has_finite_wire455)
open RecordTraversal455.MixedQA (MixedPath)
open GeneralDeclarativeInspect321 (Visit)
open GeneralDeclarativeGraphRows321 (observed structural)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open RecordK2412 (FieldCycleWire checkCycleAt412 cycle_at_sound412)
open RetainedFull445
open InlineStructuralPolicy458 (policy)
open RoutedInlineStructural458 (ModelTrail used_source_hops_hold_in_the_same_model458)
open RoutedMixed456 (endsAtField)

structure JointFieldWire (ops : AuthenticatedHop458.Policy) (align : Alignment) where
  visit : JointWire ops align
  cycle : FieldCycleWire

def ExactFieldPath (s : RawSnapshot) (ops : AuthenticatedHop458.Policy)
    (keys : Nat → KeyRead) (align : Alignment) (root : Nat)
    (t : Term) (e : Expr) (path : MixedPath) (terminal : Nat) (last : Term) : Prop :=
  (∃ used, JointTrail s ops keys align root t e path terminal last used) ∧
  endsAtField path terminal = true ∧ AliasCycle s (observed s) terminal

def readJointField (s : RawSnapshot) (ops : AuthenticatedHop458.Policy)
    (keys : Nat → KeyRead) (align : Alignment) (root : Nat) (t : Term) (e : Expr)
    (w : JointFieldWire ops align) : Option (MixedPath × Nat × Term) := do
  let (path,terminal,last,_) ← readJoint s ops keys align root t e w.visit
  if endsAtField path terminal && checkCycleAt412 s terminal w.cycle
  then some (path,terminal,last) else none

theorem read_joint_field_exact {s ops keys align root t e path terminal last} :
    (∃ w, readJointField s ops keys align root t e w = some (path,terminal,last)) ↔
    ExactFieldPath s ops keys align root t e path terminal last := by
  constructor
  · rintro ⟨w,ok⟩
    cases h : readJoint s ops keys align root t e w.visit with
    | none => simp [readJointField,h,Option.bind] at ok
    | some result =>
      obtain ⟨xs,n,u,used⟩ := result
      by_cases yes : endsAtField xs n = true ∧ checkCycleAt412 s n w.cycle = true
      · simp [readJointField,h,yes.1,yes.2,Option.bind] at ok
        obtain ⟨rfl,rfl,rfl⟩ := ok
        exact ⟨⟨used,read_joint_sound h⟩,yes.1,cycle_at_sound412 yes.2⟩
      · simp [readJointField,h,Bool.and_eq_true,yes,Option.bind] at ok
  · rintro ⟨⟨used,trace⟩,ends,cycle⟩
    obtain ⟨w,read⟩ := joint_wire_complete trace
    obtain ⟨c,check⟩ := (naked_raw_cycle_has_finite_wire455 s terminal).mp cycle
    exact ⟨⟨w,c⟩,by simp [readJointField,read,ends,check,Option.bind]⟩

theorem exact_joint_field_is_an_existing_raw_visit {s ops keys align root t e path terminal last}
    (h : ExactFieldPath s ops keys align root t e path terminal last) :
    Visit (structural s) root e terminal ∧ ¬ AliasCycle s (observed s) root ∧
      AliasCycle s (observed s) terminal := by
  obtain ⟨⟨_,trace⟩,ends,cycled⟩ := h
  have v := AuthenticatedHop458.genuine_used_hop_proves_exact_existing_raw_visit458
    (joint_has_actual_raw_trace trace)
  refine ⟨v,?_,cycled⟩
  cases trace with
  | stop => simp [endsAtField] at ends
  | down _ clear => exact clear

/-- The inner evidence on the very same FullState is inherited from the raw
authenticated policy, not from a syntactic guess about a type's shape. -/
theorem exact_joint_field_has_same_fit_evidence {p : I72.FullState} {align root t e path terminal last}
    (h : ExactFieldPath p.base.core.current.ordinary (policy p.base.core) (fun _ => queryKeys p.base.core)
        align root t e path terminal last)
    (m : I72.Model) (fit : FitsFull p m) :
    ∃ used, ModelTrail p.base.core m root e path terminal used ∧
      CoordinateWalk (fun _ => queryKeys p.base.core) root t path terminal last ∧
      AliasCycle p.base.core.current.ordinary (observed p.base.core.current.ordinary) terminal := by
  obtain ⟨⟨used,trace⟩,_,cycled⟩ := h
  exact ⟨used,used_source_hops_hold_in_the_same_model458 (joint_has_actual_raw_trace trace) m fit.1,
    joint_has_exact_written_path trace,cycled⟩

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
