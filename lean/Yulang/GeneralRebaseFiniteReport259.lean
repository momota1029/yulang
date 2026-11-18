import Yulang.GeneralVersionPublicProjection259
namespace Yulang.GeneralRebaseFiniteReport259
open GeneralRebaseStep258
open GeneralNominalRecursiveInspection (Capture Report)
variable {source : GeneralNominalState.State}

def capture (owner : Nat) (atom : Fin source.base.slots → Option Nat)
 (entry : Capture source) : Option (List Fact) := do
 if entry.name != 0 then none else
 let lower ← atom entry.bounds.1
 let upper ← atom entry.bounds.2
 pure [.lower owner lower,.upper owner upper,.binder 0,.binder 1]

def captures (owner : Nat) (atom : Fin source.base.slots → Option Nat) : List (Capture source) → Option (List Fact)
 | [] => some []
 | first :: rest => do
   let one ← capture owner atom first
   let tail ← captures owner atom rest
   pure (one ++ tail)

/-- Parametric syntactic decoder, not a semantic validator for arbitrary reports.
Soundness is supplied separately for each actual source family. -/
def compile (owner : Nat) (atom : Fin source.base.slots → Option Nat) (report : Report source) : Option Proposal := do
 if report.captures.isEmpty || !report.blocked.isEmpty || !report.conflicts.isEmpty || !report.arity.isEmpty then none else
 let entries ← captures owner atom report.captures
 pure (.installed owner :: entries.eraseDups)

theorem empty_rejected (owner : Nat) (atom : Fin source.base.slots → Option Nat)
 (report : Report source) (empty : report.captures = []) : compile owner atom report = none := by
 simp [compile,empty]
end Yulang.GeneralRebaseFiniteReport259
