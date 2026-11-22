# C346 bounded structural where smoke check

Lean 4.35.0: `lake env lean --trust=0 -DwarningAsError=true Smoke346.lean`, exit 0. A named open record tail is structurally printable when all referenced physical slots exist; the same term has no result when the tail's slot is absent. A nominal constructor nested in a variant uses the separate descriptor path, so this raw structural compiler returns none. This is a bounded adapter test, not a Yulang source acceptance decision.

```lean
import Yulang.GeneralDeclarativeWherePlain346

open Yulang
open GeneralDeclarativeWhereRawExpr346 (compile)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def openInput : Expr :=
  .record 7 (.primitive .pair [.variable 40,.variant 3 (.variable 9)]) (.variable 17)
def places : Nat → Option (Fin 3)
  | 40 => some 2
  | 9 => some 0
  | 17 => some 1
  | _ => none
def missingTail : Nat → Option (Fin 3)
  | 17 => none
  | n => places n

#eval compile places openInput
#eval compile missingTail openInput
#eval compile places (.variant 3 (.nominal 1 [.variable 40]))
```

```text
some (Yulang.Core.PresenceGeneration.TyTerm.record
  7
  (Yulang.Core.PresenceGeneration.TyTerm.pair
    (Yulang.Core.PresenceGeneration.TyTerm.var 2)
    (Yulang.Core.PresenceGeneration.TyTerm.variant 3 (Yulang.Core.PresenceGeneration.TyTerm.var 0)))
  (Yulang.Core.PresenceGeneration.TyTerm.var 1))
none
none
```
