import Yulang.GeneralDeclarativeI65I74StructuralWhereBodyReplay428
import Yulang.GeneralDeclarativeI65I74StructuralWhereMixedAuditSupport430

/-! Exact body-reader witness shared by the body and integrated legacy audits. -/

set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhereBodyReplay428
open GeneralDeclarativeI65 StructuralWhere427 StructuralWhere428 StructuralWhereMixedFixture430

def actualWire : MixedBodyWire428 := ⟨4,⟨1,placedEsc⟩,oldWire⟩
theorem body_replay_works_on_the_original_checked_frame428 :
    (readActualMixedBody428 (s:=mixedProblem.state) frame checked_parent_syntax428 actualWire).isSome = true :=
  by decide +kernel

def reconstructed : ReadActualMixedBody428 mixedProblem.state mixedProblem.root frame :=
  (readActualMixedBody428 frame checked_parent_syntax428 actualWire).get body_replay_works_on_the_original_checked_frame428

end Yulang.GeneralDeclarativeI65.I72.StructuralWhereBodyReplay428
