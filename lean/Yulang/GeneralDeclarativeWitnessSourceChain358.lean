import Yulang.GeneralDeclarativeWitnessRecursiveFixture358

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessSourceChain358
open GeneralDeclarativeWitnessJoinedCheck357 (Answer replay)
open GeneralDeclarativeWitnessProjectionCheck358 (Certificate)
open GeneralDeclarativeWitnessRecursiveSeed358 (Data data author recipe parentLayout childLayout)
open GeneralDeclarativeWitnessJoinedFixture357 (root written)
open GeneralDeclarativeWitnessDeclaredState357 (Current)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessCompiler350 (printDemand print_injective)
open GeneralDeclarations (Clause)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

structure Edge {s : Current} {src : Source} {d child} {parentWire childWire}
    (p : Answer s d parentWire) (c : Certificate src s child childWire) (i clauseId binder : Nat) : Prop where
  emitted : p.kids[i]? = some child
  raw : ∃ clause : Clause,p.impl.requirements[i]? = some clause ∧ clause.id = clauseId ∧
    clause.arguments = [.var binder]
  captured : binder = p.localRead.head.firstBinder ∨ binder = p.localRead.head.lastBinder
  sameLeft : c.chosen.read.first = p.localRead.head.firstValue
  sameRight : c.chosen.read.last = p.localRead.head.lastValue
  samePhysicalCenter : c.chosen.read.outer.center = p.localRead.head.actualValue

def check {s : Current} {src : Source} {d child} {parentWire childWire}
    (p : Answer s d parentWire) (c : Certificate src s child childWire) (i clauseId binder : Nat) : Bool :=
  match p.kids[i]?, p.impl.requirements[i]? with
  | some demand,some clause =>
    (printDemand demand == printDemand child) &&
    decide (clause.id = clauseId ∧ clause.arguments = [.var binder] ∧
      (binder = p.localRead.head.firstBinder ∨ binder = p.localRead.head.lastBinder) ∧
      c.chosen.read.first = p.localRead.head.firstValue ∧
      c.chosen.read.last = p.localRead.head.lastValue ∧
      c.chosen.read.outer.center = p.localRead.head.actualValue)
  | _,_ => false

theorem exact {s : Current} {src : Source} {d child} {parentWire childWire}
    {p : Answer s d parentWire} {c : Certificate src s child childWire} {i clauseId binder}
    (verified : check p c i clauseId binder = true) : Edge p c i clauseId binder := by
  unfold check at verified
  cases emitted : p.kids[i]? with
  | none => simp [emitted] at verified
  | some d =>
    cases raw : p.impl.requirements[i]? with
    | none => simp [emitted,raw] at verified
    | some clause =>
      simp only [emitted,raw] at verified
      obtain ⟨printed,conditions⟩ := splitAnd verified
      have same := print_injective (beq_iff_eq.mp printed)
      subst d
      obtain ⟨id,args,cap,l,r,center⟩ := of_decide_eq_true conditions
      exact ⟨emitted,⟨clause,raw,id,args⟩,cap,l,r,center⟩

def tested (ordinal : Nat) (id binder : Nat) : Bool :=
  (data.map fun d =>
    ((replay d.current root written parentLayout d.parentWire).map fun p =>
      ((GeneralDeclarativeWitnessProjectionCheck358.replay author d.current d.reached
        recipe 33 (childLayout d.first) d.childWire).map fun c =>
        check p c ordinal id binder).getD false).getD false).getD false

theorem actual_written_edge : tested 0 81 32 = true := by decide +kernel
theorem equal_payload_does_not_change_binder : tested 0 81 31 = false := by decide +kernel
theorem actual_clause_id_not_a_renaming : tested 0 82 32 = false := by decide +kernel
theorem actual_child_position_not_a_renaming : tested 1 81 32 = false := by decide +kernel

end Yulang.GeneralDeclarativeWitnessSourceChain358
