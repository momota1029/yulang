import Yulang.GeneralDeclarativeCopyFixture326
import Yulang.GeneralDeclarativeRecordResolve326
import Yulang.GeneralDeclarativeProjectInterval326
import Yulang.GeneralDeclarativeOrderedTail326
import Yulang.GeneralDeclarativeCopiedPending326

namespace Yulang.Cycle326Independent
open GeneralDeclarativePairCenters326 (pair)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeProjectInterval326 (projectAll)
open GeneralDeclarativePairNames326 (Span)

example : projectAll
    (.join (pair (.variable 1) (.variable 3)) (pair (.variable 2) (.variable 4)))
    (pair (.variable 5) (.variable 6))
    (.join (pair (.variable 7) (.variable 8)) (pair (.variable 9) (.variable 10))) =
  some ((⟨.join (.variable 1) (.variable 2),.variable 5,.join (.variable 7) (.variable 9)⟩ : Span),
        (⟨.join (.variable 3) (.variable 4),.variable 6,.join (.variable 8) (.variable 10)⟩ : Span)) := rfl

example : GeneralDeclarativeOrderedRecord326.order
    (CommonRoleCanonicalRows.normalize GeneralDeclarativeRecordState326.raw) [8,7] =
      some [(8,.variable 4),(7,.variable 3)] := rfl

example : GeneralDeclarativeOrderedRecord326.order
    (CommonRoleCanonicalRows.normalize GeneralDeclarativeRecordState326.raw) [8,9] = none := rfl

example : GeneralDeclarativeRecordState326.tail =
    ⟨7,.record 8 (.variable 4) (.primitive .emptyRecord [])⟩ := rfl

example : GeneralDeclarativeGraphRows321.fields
  (GeneralDeclarativeRecordK2326.row [(7,3),(7,0),(8,4)]) = some [(7,3),(8,4)] := rfl

open GeneralDeclarativeCovariantState326 (assignment)
open CommonNominalFullCarrier (Equivalent)
example : (¬Equivalent ((assignment false) 1).1 ((assignment false) 0).1) ∧
    (¬Equivalent ((assignment false) 1).1 ((assignment false) 2).1) :=
  GeneralDeclarativeCovariantState326.no_substitute_end false
example : (¬Equivalent ((assignment true) 1).1 ((assignment true) 0).1) ∧
    (¬Equivalent ((assignment true) 1).1 ((assignment true) 2).1) :=
  GeneralDeclarativeCovariantState326.no_substitute_end true

#print axioms GeneralDeclarativeLateWithProvider326.certified_transition
#print axioms GeneralDeclarativeCopyFixture326.absent_before
#print axioms GeneralDeclarativeCopyFixture326.after_real_owner
#print axioms GeneralDeclarativeRecordResolve326.all_model
#print axioms GeneralDeclarativeCopiedPending326.ordinary_cycle_copied
#print axioms GeneralDeclarativeCopiedPending326.copied_stays_unbacked
#print axioms GeneralDeclarativeProjectInterval326.names_and_actual
end Yulang.Cycle326Independent
