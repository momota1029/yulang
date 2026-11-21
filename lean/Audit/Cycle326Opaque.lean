import Yulang.GeneralDeclarativeOpaquePrefix326
import Yulang.GeneralDeclarativeRecordState326

namespace Yulang.Cycle326Opaque
open GeneralDeclarativeFreshTail326 (tailRow)
open GeneralDeclarativeRecordState326 (rawState raw)
open GeneralDeclarativeGraphRows321 (fields)

example : (tailRow rawState [5,6] 0 raw [8,7] (.variable 9)).right = .variable 9 := rfl

example : fields (GeneralDeclarativeRecordResidual323.withTail raw (.variable 9)) = none := rfl

#print axioms GeneralDeclarativeOpaquePrefix326.reconstruct_visible
#print axioms GeneralDeclarativeOpaquePrefix326.visible_head
#print axioms GeneralDeclarativeOpaquePrefix326.no_visible_residue
end Yulang.Cycle326Opaque
