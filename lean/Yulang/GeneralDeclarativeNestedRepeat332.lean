import Yulang.GeneralDeclarativeNestedIndex332
import Yulang.GeneralDeclarativeNestedMaterial332
import Yulang.GeneralDeclarativeNestedBody332
import Yulang.GeneralDeclarativeInlineRepeat331

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralDeclarativeNestedRepeat332
open GeneralDeclarativeInlineRepeat331
open GeneralDeclarativeInlineRepeatDecl331
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeOrigins321 (restriction from_source)
open GeneralDeclarativeNestedIndex332 (ofRows)
open GeneralDeclarativeNestedDecode332 (normalized)
open GeneralDeclarativeNestedMaterial332 (assemble)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeStableAssemble329 (tieState)
open GeneralDeclarativeStableAttempt329 (no_success)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarations (Clause)
open GeneralDeclarativeGrowth327 (Extends restrict)
open GeneralDeclarativeStableTies329 (rows pairOf)

/-- No Read, witness model, or candidate proof is supplied to the computation.
The original row produces three occurrences, two for the same binder. -/
theorem actual_reads (done : Nat → Prop) (mode : GeneralNominalMaterialization.Mode) :
    normalized (ofRows (s := restriction (support0 done)) [row]
      (fun _ h => by cases List.mem_singleton.mp h; exact from_source _ ⟨rfl,rfl⟩))
      catalogue interpretation mode (.variable 0) pat = some (occurrences mode) := rfl

theorem actual_slots :
    assemble initial (point 0) keep normalizedExpr (occurrences .actual) = some (stage,spans) := rfl

abbrev targets (_ : Clause) (_ : Nat) := 5

theorem exact_shared_tie :
    (tieState stage spans fallback).equations = stage.equations ++ [⟨7,.variable 8⟩] := rfl

theorem tie_rejects (done : Nat → Prop) : ¬∃ m, Models (tieState stage spans fallback) m :=
  (values_incompatible done).2

/-- Even successful code generation cannot be mistaken for selection.
Any later stage retains the incompatible first ordinary tie. -/
theorem every_later_rejects (done : Nat → Prop)
    (keeps : Extends (tieState stage spans fallback) latest) : ¬∃ m, Models latest m :=
  no_success (attempt done) (values_incompatible done) keeps

end Yulang.GeneralDeclarativeNestedRepeat332
