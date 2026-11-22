# Bounded Lean 4.35.0 smoke check (C344)

Command in the verified Lean project: `lake env lean --trust=0 -DwarningAsError=true path/to/Smoke344.lean` (exit 0). This executable footprint illustration supplements, not replaces, the general proof. Mode labels 0 = lower, 1 = actual, 2 = upper. The outer field at label 0 shadows the tail field from slot 2, so only that slot disappears. The same field projection inside a nominal constructor reads actual even from the upper side.

```lean
import Yulang.GeneralDeclarativePolarCompiler344

open Yulang
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (translate value)
open GeneralNominalMaterialization (Mode)
open GeneralNominalVersionedExpressionFrame236 (reads)
open GeneralDictionaryJournalRefinement228Source (constructors interpretation)
open CommonNominalFullCarrier (Ty Equivalent)

def shadowed : Pattern := .record 0 (.var 1) (.record 0 (.var 2) (.var 3))
def nested : Pattern := .app 0 [shadowed,.var 4]
def modeLabel : Mode → Nat | .lower => 0 | .actual => 1 | .upper => 2
def showReads (p : Pattern) (mode : Mode) :=
  (translate constructors interpretation p).map (fun code =>
    (reads mode code).map fun (side,name) => (modeLabel side,name))

#eval showReads shadowed .lower
#eval showReads (normalize shadowed) .lower
#eval showReads nested .upper
#eval showReads (normalize nested) .upper
```

```text
some [(0, 1), (0, 2), (0, 3)]
some [(0, 1), (0, 3)]
some [(1, 1), (1, 2), (1, 3), (1, 4)]
some [(1, 1), (1, 3), (1, 4)]
```
