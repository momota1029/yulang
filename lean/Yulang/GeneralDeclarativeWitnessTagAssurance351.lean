import Yulang.GeneralDeclarativeWitnessTagFixture351
import Yulang.GeneralDeclarativeWitnessReleaseExact351

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTagAssurance351
open GeneralDeclarativeHead320 (Equation State)
open GeneralDeclarativeWitnessTagFixture351
open GeneralDeclarativeWitnessOrigins350 (Table attach support visible_iff)
open GeneralDeclarativeWitnessTagSources351 (directBounds namedBounds)
open GeneralDeclarativeTaggedFixture340 (a whole)
open GeneralDeclarativeOrigins321 (restriction)

def ordinaryLow : Equation := ⟨0,.variant 7 whole⟩
def ordinaryHigh : Equation := ⟨2,.variant 7 whole⟩
def current : State := GeneralDeclarativeEntailment320.appendFacts original [ordinaryLow,ordinaryHigh]

/-- Adding a literal normalization to ordinary equations is not evidence
that it is source-authored or released. The direct checker still sees
the original recursively named RHS at the actual source coordinates. -/
theorem ordinary_addition_not_authentication :
    ((attach current manifest).map (fun src => (directBounds src a 7 span (ref 0) (ref 1)).isSome)).getD false
      = false := by decide +kernel

theorem guessed_ordinary_index_not_authentication :
    ((attach current manifest).map (fun src => (directBounds src a 7 span (ref 4) (ref 5)).isSome)).getD false
      = false := by decide +kernel

theorem same_named_script_remains_valid :
    ((attach current manifest).map (fun src => (namedBounds src a 7 span atLower atUpper).isSome)).getD false
      = true := by decide +kernel

def genuineManifest : Table :=
  {manifest with authored := ordinaryLow :: ordinaryHigh :: manifest.authored}

theorem independent_literal_author_can_be_read :
    ((attach current genuineManifest).map (fun src => (directBounds src a 7 span (ref 0) (ref 1)).isSome)).getD false
      = true := by decide +kernel

end Yulang.GeneralDeclarativeWitnessTagAssurance351
