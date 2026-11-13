import Yulang.GeneralDictionarySharedCapturedProducer
import Yulang.GeneralDictionarySharedTrustTransport

/-! Semantic consequences after the actual producer packet has been recorded.
The membership/path premises are explicit: these lemmas do not claim that the
producer is enabled or installed, nor that an entailed scalar is already Known. -/
namespace Yulang.GeneralDictionarySharedCapturedConsequences
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalCommonBridge
open GeneralDictionarySharedOutputBinderScope GeneralDictionarySharedCapturedTargets
open GeneralDictionarySharedCapturedRefresh GeneralDictionarySharedCapturedProducer
open GeneralDeclarationExamples (roles)

/-- Every actual Shared transition restricts the journal's model set. -/
theorem path_models {rs : Roles.RoleDecls} {r : Registry} {root : Occurrence rs}
    {before after : Tracked rs}
    (path : B4Target.Steps (GeneralNominalSharedSteps.Step r root) before after)
    (assignment : Assignment) (valid : Models after.current assignment) :
    Models before.current assignment := by
  induction path with
  | refl => exact valid
  | tail previous update ih => exact ih (GeneralNominalSharedSteps.step_models update assignment valid)

/-- A recorded producer constrains its named output in every current model. -/
theorem recorded_output_int (state : Tracked roles)
    (recorded : candidate ∈ state.current.packets)
    (assignment : Assignment) (valid : Models state.current assignment) :
    CommonNominalFullCarrier.Equivalent (assignment target).1 (.base .int) :=
  output_int assignment (valid.2.1 candidate recorded)

/-- The actual prefix preserves the parent's output/captured-source equation;
recording the producer then fixes captured source2 in all current models. -/
theorem recorded_captured_int (state : Tracked roles)
    (path : B4Target.Steps (GeneralNominalSharedSteps.Step registry root) refreshed state)
    (recorded : candidate ∈ state.current.packets)
    (assignment : Assignment) (valid : Models state.current assignment) :
    CommonNominalFullCarrier.Equivalent (assignment 2).1 (.base .int) :=
  captured_int assignment (path_models path assignment valid) (valid.2.1 candidate recorded)

/-- Once established, the captured scalar consequence survives every later
Shared transition, including exact refresh and reobservation. -/
theorem captured_int_after_path {before after : Tracked roles}
    (prior : B4Target.Steps (GeneralNominalSharedSteps.Step registry root) refreshed before)
    (recorded : candidate ∈ before.current.packets)
    (suffix : B4Target.Steps (GeneralNominalSharedSteps.Step registry root) before after)
    (assignment : Assignment) (valid : Models after.current assignment) :
    CommonNominalFullCarrier.Equivalent (assignment 2).1 (.base .int) :=
  recorded_captured_int before prior recorded assignment (path_models suffix assignment valid)

end Yulang.GeneralDictionarySharedCapturedConsequences
