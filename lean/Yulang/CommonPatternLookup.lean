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

/-- Optional Common observations constrain the actual value when lookup finds
one. The premise preserves known absence separately: it does not invent a
field or execute a fallback. All Common source/payload assignments are allowed. -/
theorem optional_lookup (fields : CaseValues.Bindings Empty)
    (source : Comp Common.model) (label : Nat) (payload : Common.Ty) (value : Value)
    (typed : ValueTyping Common.model (.record fields) source)
    (optional : OptionalPayload label source.1 payload)
    (found : CaseValues.lookup label fields = some value) :
    ValueTyping Common.model value (Comp.pure Common.model payload) := by
  induction fields generalizing source with
  | nil => simp [CaseValues.lookup] at found
  | cons field rest ih =>
      rcases field with ⟨current, item⟩
      cases typed with
      | @record _ a _ b _ _ head tail width bounded =>
          have selected : OptionalPayload label (Common.record current a.1 b.1) payload := by
            intro depth rank env obs accepted
            exact (CommonFinite.producerLe_iff_probe _ _).mp (bounded.1 (depth + 1))
              rank env (.optional label obs) (optional depth rank env obs accepted)
          by_cases same : label = current
          · subst current
            have equal : item = value := by simpa [CaseValues.lookup] using found
            subst item
            exact typing_change_result head (Comp.pure Common.model payload)
              ((CommonDefaultRequired.optionalPayload_record_same label _ _ payload).mp selected)
          · have tailOptional : OptionalPayload label b.1 payload := by
              intro depth rank env obs accepted
              have observed := selected depth rank env obs accepted
              change CommonFinite.ProbeAt _ rank env (.record current _ _)
                (.optional label obs) at observed
              rw [CommonFinite.probeAt_record_optional] at observed
              simp only [same, ↓reduceIte] at observed
              rcases observed with observed | trivial
              · exact observed
              · subst obs
                apply (CommonFinite.producerLe_iff_probe _ _).mp (width (depth + 1))
                  rank env (.optional label .trivial)
                cases rank <;> rfl
            exact ih _ tail tailOptional (by simpa [CaseValues.lookup, same] using found)

/-- A width-record observation of a typed concrete value reflects its actual
outer runtime shape. The subject type may otherwise be any Common producer. -/
theorem records_of_width {value : Value} {source : Comp Common.model}
    (typed : ValueTyping Common.model value source)
    (width : Common.Subtype source.1 Common.emptyRecord) :
    ∃ fields, value = .record fields := by
  let env : CommonFinite.Environment Common.Row := ⟨fun _ => .bottom, fun _ => []⟩
  have observed : CommonFinite.ProbeAt Common.rowLe 0 env
      (Common.observeTy 0 source.1) .records :=
    (CommonFinite.producerLe_iff_probe _ _).mp (width 0) 0 env .records trivial
  cases typed with
  | literal bounded =>
      exact False.elim ((CommonFinite.producerLe_iff_probe _ _).mp
        (bounded.1 0) 0 env .records observed)
  | pair _ _ bounded =>
      exact False.elim ((CommonFinite.producerLe_iff_probe _ _).mp
        (bounded.1 0) 0 env .records observed)
  | emptyRecord => exact ⟨[], rfl⟩
  | record => exact ⟨_, rfl⟩
  | variant _ bounded =>
      exact False.elim ((CommonFinite.producerLe_iff_probe _ _).mp
        (bounded.1 0) 0 env .records observed)

/-- Pair demands reflect both actual component values and their Common types;
no separate constructor-support or successful-match premise is needed. -/
theorem pair_components {value : Value} {source : Comp Common.model}
    (typed : ValueTyping Common.model value source) (first last : Common.Ty)
    (below : Common.Subtype source.1 (Common.pair first last)) :
    ∃ left right, value = .pair left right ∧
      ValueTyping Common.model left (Comp.pure Common.model first) ∧
      ValueTyping Common.model right (Comp.pure Common.model last) := by
  let env : CommonFinite.Environment Common.Row := ⟨fun _ => .bottom, fun _ => []⟩
  have observed : CommonFinite.ProbeAt Common.rowLe 0 env
      (Common.observeTy 0 source.1) (.pairFirst .trivial) :=
    (CommonFinite.producerLe_iff_probe _ _).mp (below 0) 0 env (.pairFirst .trivial) trivial
  cases typed with
  | literal bounded =>
      exact False.elim ((CommonFinite.producerLe_iff_probe _ _).mp
        (bounded.1 0) 0 env (.pairFirst .trivial) observed)
  | pair left right bounded =>
      have components := (Common.common_pair_iff _ _ first last).mp
        (Common.subtype_trans bounded.1 below)
      exact ⟨_, _, rfl,
        typing_change_result left _ components.1, typing_change_result right _ components.2⟩
  | emptyRecord bounded =>
      exact False.elim ((CommonFinite.producerLe_iff_probe _ _).mp
        (bounded.1 0) 0 env (.pairFirst .trivial) observed)
  | record _ _ _ bounded =>
      exact False.elim ((CommonFinite.producerLe_iff_probe _ _).mp
        (bounded.1 0) 0 env (.pairFirst .trivial) observed)
  | variant _ bounded =>
      exact False.elim ((CommonFinite.producerLe_iff_probe _ _).mp
        (bounded.1 0) 0 env (.pairFirst .trivial) observed)

end Yulang.CommonPatternLookup
