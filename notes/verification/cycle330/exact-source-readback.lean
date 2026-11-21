import Yulang.GeneralDeclarativeArityModels330
import Yulang.GeneralDeclarativeCurrentResult330
import Yulang.GeneralDeclarativeRecordElection330
import Yulang.GeneralDeclarativeRecordInline330
import Yulang.GeneralDeclarativeRecordReconstruct330
import Yulang.GeneralDeclarativeRecordTail330
import Yulang.GeneralDeclarativeRecordSplit330

namespace Yulang.Cycle330Crosscheck

open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOpaqueNominal328 (point)

example : GeneralDeclarativeStableTies329.rows GeneralDeclarativeArityFixture330.base
    (GeneralDeclarativeArityFixture330.spans.map GeneralDeclarativeStableTies329.pairOf) =
    [⟨3,.variable 4⟩] := rfl

example : (GeneralDeclarativeArityFixture330.child : Demand) =
    ⟨2,[⟨9,10,11⟩],[⟨1,5⟩]⟩ := rfl

example : (⟨6,.variable 5⟩ : Equation) ∉ GeneralDeclarativeCurrentProbe330.final.equations :=
  GeneralDeclarativeCurrentResult330.absent

example : GeneralDeclarativeEqualities322.Derives GeneralDeclarativeCurrentProbe330.final
    (.variable 6) (.variable 5) := GeneralDeclarativeCurrentResult330.rejoined_old

example : (GeneralDeclarativeRecordReplay330.frame.capture 1).center = 16 := rfl

example : GeneralDeclarativeRecordReplay330.frame.rootRows = [⟨6,.variable 16⟩] := rfl

example : GeneralDeclarativeRecordPoints330.usesFrom GeneralDeclarativeRecordInline330.taken
    [0,1] 2 8 = [(0,point 8),(1,point 4),(2,point 9)] := rfl

example : GeneralDeclarativeRecordMaterial330.tailExpr GeneralDeclarativeRecordInline330.fields
    [7,8] GeneralDeclarativeRecordInline330.terminal =
      .record 9 (.variable 7) (.primitive .emptyRecord []) := rfl

#check GeneralDeclarativeRecordSplit330.obstruction
#check GeneralDeclarativeRecordReconstruct330.exact
#check GeneralDeclarativeRecordTail330.does_not_fix_remainder
#print axioms GeneralDeclarativeArityModels330.nonvacuous
#print axioms GeneralDeclarativeCurrentResult330.accepted_without_literal
#print axioms GeneralDeclarativeRecordElection330.protected_tail
#print axioms GeneralDeclarativeRecordInline330.inline_ready

end Yulang.Cycle330Crosscheck
