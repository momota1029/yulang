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

/-- A required Common observation finds the actual first stored field. Every
Common subject and payload type, all result rows and duplicate record labels
are admitted. The selected value is typed by the independent data judgment. -/
theorem required_lookup (fields : CaseValues.Bindings Empty)
    (source : Comp Common.model) (label : Nat) (payload : Common.Ty)
    (typed : ValueTyping Common.model (.record fields) source)
    (required : Common.Subtype source.1 (Common.required label payload)) :
    ∃ value, CaseValues.lookup label fields = some value ∧
      ValueTyping Common.model value (Comp.pure Common.model payload) := by
  induction fields generalizing source with
  | nil =>
      cases typed with
      | emptyRecord bounded =>
          have impossible := (CommonRecordTargetProfiles.subtype_required_iff
            Common.exactEmpty payload label).mp (Common.subtype_trans bounded.1 required)
          simp [CommonPayloadProjection.ProfileBelow, CommonPayloadProjection.fieldType,
            CommonPayloadProjection.fieldProject, Common.exactEmpty] at impossible
  | cons field rest ih =>
      rcases field with ⟨current, item⟩
      cases typed with
      | record head tail width bounded =>
          have selected := Common.subtype_trans bounded.1 required
          by_cases same : label = current
          · subst current
            refine ⟨item, by simp [CaseValues.lookup], ?_⟩
            exact typing_change_result head (Comp.pure Common.model payload)
              ((Common.common_singleton_requirement_iff label _ payload _).mp selected)
          · have tailRequired := fun depth =>
              (CommonFiniteOptionalInspection.record_other_required_at_iff
                depth current label _ _ payload same).mp (selected depth)
            obtain ⟨value, found, valid⟩ := ih _ tail tailRequired
            exact ⟨value, by simpa [CaseValues.lookup, same] using found, valid⟩

end Yulang.CommonPatternLookup
