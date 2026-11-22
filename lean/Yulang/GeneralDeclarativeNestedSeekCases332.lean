import Yulang.GeneralDeclarativeNestedSeek332
import Yulang.GeneralDeclarativeNestedOpaque332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedSeekCases332
open GeneralDeclarativeNestedOpaque332 (visible backed actual_dependency rootRow target seen)
open GeneralDeclarativeNestedIndex332 (ofRows)
open GeneralDeclarativeNestedSeek332 (seek seeking)
open GeneralDeclarativeNestedDecode332 (normalized)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarationExamples (constructors)

noncomputable def index (first last : Bool) := ofRows (visible first last) (backed first last)

theorem finds_actual_tail : seek (index true true) 20 1 = some [21] := rfl

/-- Neither a path script nor a proposed type is supplied. The nested
residual is found from the exact supported RHSs, and the original
ordinary state is unchanged while sources become available. -/
theorem auto_read (first last : Bool) :
    normalized (seeking (index first last) 1) constructors interpretation .actual (.variable 0) target =
      if first && last then some seen else none := by
  cases first <;> cases last <;> rfl

theorem insufficient_budget :
    normalized (seeking (index true true) 0) constructors interpretation .actual (.variable 0) target =
      none := rfl

end Yulang.GeneralDeclarativeNestedSeekCases332
