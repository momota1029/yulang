import Yulang.GeneralDeclarativeWitnessNominalSource359
import Yulang.GeneralDeclarativeWitnessInheritedFullFixture357
import Yulang.GeneralDeclarativeWitnessOpenFixture359

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 53000
set_option maxHeartbeats 58000000
namespace Yulang.GeneralDeclarativeWitnessNominalRecordFixture359
open GeneralDeclarativeWitnessNominalSource359 (Location Route SlotRead compare approved_source_comparison Compared)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessCoverageFixture357 (prepare bundle)
open GeneralDeclarativeWitnessModeCoverage357 (check)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWitnessRecordWidthFixture359 (model lowTy highTy endpoints_ordered)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Subtype Equivalent subtype_trans subtype_refl)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open PresenceNormalForm (Atom)

def ctor (contravariant : Bool) : Nat := if contravariant then 42 else 20
def route (contravariant : Bool) (binder : Nat) : Route := .unary 55 (.unary (ctor contravariant) (.bind binder))

/-- Authored source is an actual declaration in the parsed bundle. Its
literal heads, not preconstructed endpoint data, are fed to the compare
entry. The body does not claim a general new solver rule. -/
def sourceDecl (negative : Bool) : Declaration :=
  ⟨72,5,[.app 55 [.app (if negative then 42 else 20) [.var 80]],
         .app 55 [.app (if negative then 42 else 20) [.var 81]]],[],[],[]⟩

def prepared (negative : Bool) : Option Environment :=
  prepare {bundle with roles := ⟨0,[⟨5,2,[]⟩]⟩,declarations := [sourceDecl negative]}

def first : Location := .head 72 0 0
def last : Location := .head 72 0 1

def slots : SlotRead
  | 80 => some ⟨60,61,62⟩
  | 81 => some ⟨65,67,66⟩
  | _ => none

def bounds (a b c d : Nat) : List (Atom Nat) :=
  [.tyLe (.var a) (.var b),.tyLe (.var a) (.var d),.tyLe (.var c) (.var b),.tyLe (.var c) (.var d)]

def exactAtoms : List (Atom Nat) :=
  bounds 60 62 60 62 ++ bounds 60 62 65 66 ++ bounds 65 66 60 62 ++ bounds 65 66 65 66

def receipt (negative : Bool) (left := first) (right := last) : Option (List (Atom Nat)) :=
  (prepared negative).bind fun e =>
    (compare e table slots false left right (route negative 80) (route negative 81)).map (fun r => r.run.rows)

theorem actual_author_bundle_covered (negative : Bool) :
    ((prepared negative).map check).getD false = true := by cases negative <;> decide +kernel

theorem actual_covariant_under_invariant : receipt false = some exactAtoms := by decide +kernel
theorem actual_contravariant_under_invariant : receipt true = some exactAtoms := by decide +kernel
theorem rejects_changed_site :
    receipt false (.head 72 0 1) last = none ∧ receipt true (.head 73 0 0) last = none := by decide +kernel

def forgettingBound (negative : Bool) : Option (List (Atom Nat)) :=
  (prepared negative).bind fun e =>
    (compare e table (fun name => if name = 80 then none else slots name) false first last
      (route negative 80) (route negative 81)).map (fun r => r.run.rows)
theorem cannot_guess_missing_actual_binding (negative : Bool) : forgettingBound negative = none := by
  cases negative <;> decide +kernel

def aliasedLow : Equation := ⟨65,.variable 60⟩
def aliasedHigh : Equation := ⟨66,.variable 62⟩
def current : State :=
  ⟨⟨[],[(60,61),(61,62),(65,67),(67,66)]⟩,
    [GeneralDeclarativeWitnessOpenFixture359.lowAuthored,GeneralDeclarativeWitnessOpenFixture359.highAuthored,
      aliasedLow,aliasedHigh]⟩

def genuine (firstUpper lastUpper : Bool) : Assignment := fun x =>
  match x with
  | 65 => (lowTy,Common.rowEmpty)
  | 66 => (highTy,Common.rowEmpty)
  | 67 => ((if lastUpper then highTy else lowTy),Common.rowEmpty)
  | n => model firstUpper n

theorem common_source_model (leftUpper rightUpper : Bool) : Models current (genuine leftUpper rightUpper) := by
  refine ⟨⟨fun _ bad => False.elim (List.not_mem_nil bad),?_⟩,?_⟩
  · intro pair member
    simp only [current,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · cases leftUpper
      · exact subtype_refl _
      · exact endpoints_ordered
    · cases leftUpper
      · exact endpoints_ordered
      · exact subtype_refl _
    · cases rightUpper
      · exact subtype_refl _
      · exact endpoints_ordered
    · cases rightUpper
      · exact endpoints_ordered
      · exact subtype_refl _
  · intro row member
    simp only [current,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> exact eqv_refl _

theorem generated_checks_follow_from_authored_base (m : Assignment) (fit : Models current m) :
    ∀ atom ∈ exactAtoms,atom.Holds CommonNominalFullCarrier.model m := by
  have base :
      Subtype (m 60).1 (m 62).1 :=
    subtype_trans (fit.1.2 (60,61) (by simp [current])) (fit.1.2 (61,62) (by simp [current]))
  have qualifiedLow : Equivalent (m 65).1 (m 60).1 := fit.2 aliasedLow (by simp [current])
  have qualifiedHigh : Equivalent (m 66).1 (m 62).1 := fit.2 aliasedHigh (by simp [current])
  have l : Subtype (m 60).1 (m 66).1 := subtype_trans base qualifiedHigh.2
  have r : Subtype (m 65).1 (m 62).1 := subtype_trans qualifiedLow.1 base
  have b : Subtype (m 65).1 (m 66).1 := subtype_trans qualifiedLow.1 l
  intro atom member
  simp only [exactAtoms,bounds,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first | exact base | exact l | exact r | exact b

theorem checked_in_actual_source_model (negative : Bool) (m : Assignment) (fit : Models current m) :
    ∃ (e : Environment) (a : Compared e table slots false first last (route negative 80) (route negative 81)),
      prepared negative = some e ∧ a.run.rows = exactAtoms ∧
      GeneralDeclarativeWitnessFullIntervals357.ContextDerives table m false a.first.endpoint a.last.endpoint := by
  have proven : receipt negative = some exactAtoms := by
    cases negative
    · exact actual_covariant_under_invariant
    · exact actual_contravariant_under_invariant
  unfold receipt at proven
  cases authored : prepared negative with
  | none => rw [authored] at proven; cases proven
  | some e =>
    rw [authored] at proven
    cases compared : compare e table slots false first last (route negative 80) (route negative 81) with
    | none => simp [compared] at proven
    | some a =>
      have exactRows : a.run.rows = exactAtoms := by simpa [compared] using proven
      refine ⟨e,a,rfl,exactRows,?_⟩
      apply ((GeneralDeclarativeWitnessFullIntervals357.compiled_full_exact table m false a.first.endpoint a.last.endpoint).mp ?_).2.2
      exact ⟨a.run.rows,a.run.exact,fun atom member => generated_checks_follow_from_authored_base m fit atom (exactRows ▸ member)⟩

end Yulang.GeneralDeclarativeWitnessNominalRecordFixture359
