# Ordinary Lean compiler smoke check (not raw/Rust execution)

Lean 4.35.0; `lake env lean --trust=0 -DwarningAsError=true` on the exact scratch source below. `exactInput` checks that the literal request equals the actual C319 source projection. The two explicit finite protection lists test the ordinary compiler only, not the full raw-journal transaction.

```text
some ([[(13, 14, 15)]], [0, 13, 14, 15, 4], [[]])
some ([[(20, 21, 22)]], [0, 20, 21, 22, 4], [[]])
```

```lean
import Yulang.GeneralDeclarativeOrderedProjection343
open Yulang
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeLogicalChild343 (fallback targets)
open GeneralDeclarativeVersionedRootShape342 (spans)
open GeneralDeclarativeVersionedRootGuard342 (observedRoot actualDemand)
open GeneralWhereOriginSingleSource318 (sourceRegistry declaration)
open GeneralDictionaryJournalRefinement228Source (interpretation)
open GeneralDeclarativeNestedBody332 (compileBody)

def fixedDemand : Demand := ⟨0,[⟨0,0,0⟩],[⟨0,4⟩]⟩
def inspect (keep : List Nat) :=
  (compileBody sourceRegistry interpretation fixedDemand declaration observedRoot spans keep fallback targets).map fun (model,kids) =>
    ((kids : List Demand).map (fun (d : Demand) => d.arguments.map (fun (p : Capture) => (p.lower,p.center,p.upper))),
      model.equations.map GeneralDeclarativeHead320.Equation.left,kids.map (fun (d : Demand) => d.outputs.map GeneralSourceState.Output.target))

theorem exactInput : fixedDemand = actualDemand := by
  cases eq : actualDemand with
  | mk role args outs =>
    have isRoot : actualDemand.role = 0 := rfl
    have as := GeneralDeclarativeVersionedRootGuard342.original_arguments
    have os := GeneralDeclarativeVersionedRootGuard342.original_targets
    rw [eq] at isRoot as os
    cases isRoot
    cases as
    cases os
    rfl

#eval inspect [0,2,4,8]
#eval inspect [0,2,4,8,13,14,15]
```
