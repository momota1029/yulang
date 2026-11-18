import Yulang.GeneralRebaseBudget258
namespace Yulang.GeneralRebaseReportDecoder259
open GeneralRebaseStep258
open GeneralNominalRecursiveInspection (Capture Report)
open GeneralDictionaryLooseIterationBook240 (context)

/-- Fixed source basis [var2,var4], not arbitrary private identifiers. -/
def atom (slot : Fin 5) : Option Nat :=
 if slot.val = 2 then some 0 else if slot.val = 4 then some 1 else none

def capture (entry : Capture (context 0).state) : Option (List Fact) := do
 if entry.name != 0 then none else
 let lower ← atom entry.bounds.1
 let upper ← atom entry.bounds.2
 pure [.lower 0 lower,.upper 0 upper,.binder 0,.binder 1]

def captures : List (Capture (context 0).state) → Option (List Fact)
 | [] => some []
 | first :: rest => do
   let one ← capture first
   let tail ← captures rest
   pure (one ++ tail)

/-- This decoder has a proved semantic bridge only on the actual I45 family.
It is not a claim that every report accepted here is a valid language packet. -/
def compile (report : Report (context 0).state) : Option Proposal := do
 if report.captures.isEmpty || !report.blocked.isEmpty || !report.conflicts.isEmpty || !report.arity.isEmpty then none else
 let entries ← captures report.captures
 pure (.installed 0 :: entries.eraseDups)

theorem source_atoms : atom 2 = some 0 ∧ atom 4 = some 1 := by decide

theorem no_private_atom (slot : Fin 5) (notTwo : slot ≠ 2) (notFour : slot ≠ 4) : atom slot = none := by
 have two : slot.val ≠ 2 := fun same => notTwo (Fin.ext same)
 have four : slot.val ≠ 4 := fun same => notFour (Fin.ext same)
 simp only [atom,two,four,ite_false]

theorem empty_rejected (report : Report (context 0).state) (empty : report.captures = []) : compile report = none := by
 simp [compile,empty]

theorem actual (n : Nat) :
 compile (GeneralDictionaryReportProjection257.transport n
   (GeneralNominalPacketSupport.report (GeneralDictionaryLooseIterationBook240.packet n))) =
 some GeneralDictionaryRebaseStep258.facts := by
 rw [GeneralDictionaryReportProjection257.actual_report]
 rw [show GeneralNominalPacketSupport.report (GeneralDictionaryLooseIterationBook240.packet 0) =
 GeneralDictionaryLooseFamilyPacket240.calculated 0
 (GeneralDictionaryLooseIterationBook240.allocations 0) (GeneralDictionaryLooseIterationBook240.reservations 0)
 (GeneralDictionaryLooseIterationBook240.atoms 0) from ?_]
 · decide
 · exact GeneralDictionaryLooseFamilyPacket240.report_exact ..
end Yulang.GeneralRebaseReportDecoder259
