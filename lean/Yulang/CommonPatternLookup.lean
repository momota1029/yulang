import Yulang.CoreCommonData
import Yulang.CommonOptionalBound
import Yulang.CommonFiniteOptionalInspection
import Yulang.ScopedCasePatterns

/-!
# Common observations reflected by actual structural pattern lookup

The independent constructor judgment for concrete data supplies the bridge.
No runtime set of values is identified with the full Common producer carrier:
all type comparisons below retain every finite depth and demand rank. The
record lookup is the actual first-wins lookup used by `ScopedCasePatterns.run`.
-/

namespace Yulang.CommonPatternLookup

open Core.CommonData (Value ValueTyping)
open Core.PresenceGeneration (Comp)
open CommonDefaultRequired (OptionalPayload)

/-- Concrete data are pure. An earlier row overapproximation therefore does
not constrain a new result row; only the Common value comparison is needed.
This uses the independent value constructors and no source lowering or solver. -/
theorem typing_change_result {value : Value} {source : Comp Common.model}
    (typed : ValueTyping Common.model value source) (target : Comp Common.model)
    (below : Common.Subtype source.1 target.1) :
    ValueTyping Common.model value target := by
  induction typed generalizing target with
  | literal bounded =>
      exact .literal ⟨Common.subtype_trans bounded.1 below, Common.rowEmpty_le _⟩
  | @pair first a last b result firstTyped lastTyped bounded firstIH lastIH =>
      refine .pair (firstIH (Comp.pure Common.model a.1) (Common.subtype_refl _))
        (lastIH (Comp.pure Common.model b.1) (Common.subtype_refl _)) ?_
      exact ⟨Common.subtype_trans bounded.1 below,
        (Common.rowJoin_le_iff _ _ _).mpr ⟨Common.rowEmpty_le _, Common.rowEmpty_le _⟩⟩
  | emptyRecord bounded =>
      exact .emptyRecord ⟨Common.subtype_trans bounded.1 below, Common.rowEmpty_le _⟩
  | @record head a rest b name result headTyped restTyped width bounded headIH restIH =>
      refine .record (headIH (Comp.pure Common.model a.1) (Common.subtype_refl _))
        (restIH (Comp.pure Common.model b.1) (Common.subtype_refl _)) width ?_
      exact ⟨Common.subtype_trans bounded.1 below,
        (Common.rowJoin_le_iff _ _ _).mpr ⟨Common.rowEmpty_le _, Common.rowEmpty_le _⟩⟩
  | @variant child a tag result childTyped bounded childIH =>
      exact .variant (childIH (Comp.pure Common.model a.1) (Common.subtype_refl _))
        ⟨Common.subtype_trans bounded.1 below, Common.rowEmpty_le _⟩

end Yulang.CommonPatternLookup
