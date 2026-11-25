import Yulang.GeneralDeclarativeI65I75CanonicalEndpointReport426
import Yulang.GeneralDeclarativeI65I74RepeatedCentersEntry421

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDeclarativeI65.I72.EndpointProjection426
open CommonRoleOutermostResolver (Dictionary)
open Checker408 (Problem Result)
open ProjectedCore425
open ProjectedRetention423

def R14 : SourcePrimitives .withEndpoint where
  elected := RepeatedCenters421.R13.elected
  other := RepeatedCenters421.R13.other

/-- The old trace kernel is exactly the original full R13 system. -/
theorem R14_named_view_is_exact_R13_426 : R14.named426 = RepeatedCenters421.R13 := rfl

theorem R13_legacy_verdicts_are_unchanged_in_R14_426 {s q r} :
    LegacyClassifies426 R14.named426 s q r ↔ Classifies RepeatedCenters421.R13 s q r := Iff.rfl

/-- This extension contributes no pending, ambiguous, or rejected
verdicts. The original diagnostic families and their raw K2 case
remain exactly the same. -/
theorem R14_keeps_all_old_nonselection_verdicts426 {s q r}
    (notSelected : ∀ d : Dictionary, r ≠ .selected d) :
    Classifies R14 s q r ↔ Classifies RepeatedCenters421.R13 s q r := by
  constructor
  · intro valid
    rcases classification_has_exact_lane_rule426 valid with legacy|⟨e,_,exact⟩
    · exact R13_legacy_verdicts_are_unchanged_in_R14_426.mp legacy
    · exact (notSelected e.dictionary exact).elim
  · intro legacy
    exact legacy_classification_included426
      (R13_legacy_verdicts_are_unchanged_in_R14_426.mpr legacy)

theorem every_R13_verdict_is_preserved_in_R14_426 {s q r}
    (legacy : Classifies RepeatedCenters421.R13 s q r) : Classifies R14 s q r :=
  legacy_classification_included426 (R13_legacy_verdicts_are_unchanged_in_R14_426.mpr legacy)

theorem dictionary_sound_R14 : DictionarySound R14 := by
  intro s q d localRule m fit
  rcases classification_has_exact_lane_rule426 localRule with ordinary|endpoint
  · exact RepeatedCenters421.dictionary_sound_R13 s q d
      (R13_legacy_verdicts_are_unchanged_in_R14_426.mp ordinary) m fit
  · obtain ⟨e,⟨kept⟩,same⟩ := endpoint
    cases same
    exact original_projected_leaf_with_retention_has_dictionary_evidence426 e kept m fit

/-- Internal projected report encoding tag, outside the old root tag
range. This does not change the surface language or legacy encoding. -/
def projectedTag : Nat := 9

def ClassifiedAs (s : I72.State) (q : I72.Request) (r : Result) : Prop :=
  RepeatedCenters421.ClassifiedAs s q r ∨
    ∃ a : ProjectedLeafPacket426 ⟨s,q⟩, r = a.exactReport projectedTag

def ReportEvidence (s : I72.State) (m : I72.Model) (q : I72.Request) (r : Result) : Prop :=
  RepeatedCenters421.ReportEvidence s m q r ∨
    ∃ a : ProjectedLeafPacket426 ⟨s,q⟩, r = a.exactReport projectedTag ∧
      DictionaryEvidence s m q a.original.dictionary

theorem exact_projected_and_legacy_reports_classify_R14_426 {s q r}
    (out : ClassifiedAs s q r) : Classifies R14 s q r.verdict := by
  rcases out with old|⟨a,exactReport⟩
  · exact legacy_classification_included426
      (R13_legacy_verdicts_are_unchanged_in_R14_426.mpr
        (RepeatedCenters421.exact_report_is_R13_classification421 old))
  · subst r
    exact endpoint_classification_included426 ⟨a.original,⟨a.retained⟩,rfl⟩

inductive Witness where
  | previous (old : RepeatedCenters421.Witness)
  | projectedRecord (w : ProjectedRowsWire426)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous old => RepeatedCenters421.check p r old
  | .projectedRecord w => checkProjectedLeafReport426 p projectedTag r w
  | .unsupported => false

theorem R13_checker_behavior_is_identical426 (p : Problem) (r : Result)
    (w : RepeatedCenters421.Witness) :
    check p r (.previous w) = RepeatedCenters421.check p r w := rfl

theorem check_sound (p : Problem) (r : Result) (w : Witness) (good : check p r w = true) :
    ClassifiedAs p.state p.root r ∧ ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  cases w with
  | previous w =>
    obtain ⟨old,oldMeaning⟩ := RepeatedCenters421.check_sound p r w good
    exact ⟨.inl old,fun m fit => .inl (oldMeaning m fit)⟩
  | projectedRecord w =>
    obtain ⟨a,_,result,meaning⟩ :=
      checked_projected_report_has_canonical_dictionary_evidence426
        (p:=p) (tag:=projectedTag) (r:=r) (w:=w) good
    exact ⟨.inr ⟨a,result⟩,fun m fit => .inr ⟨a,result,meaning m fit⟩⟩
  | unsupported => simp [check] at good

theorem verified_R14_result_classifies_in_same_State426 (p : Problem) (r : Result)
    (w : Witness) (good : check p r w = true) :
    Classifies R14 p.state p.root r.verdict ∧
      ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r :=
  let verified := check_sound p r w good
  ⟨exact_projected_and_legacy_reports_classify_R14_426 verified.1,verified.2⟩

theorem original_raw_K2_rules_out_any_R14_selection426 {s q}
    (raw : RootCycle s q) (d : Dictionary) : ¬ Classifies R14 s q (.selected d) :=
  root_k2_never_selects raw

end Yulang.GeneralDeclarativeI65.I72.EndpointProjection426
