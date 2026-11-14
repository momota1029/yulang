import Yulang.GeneralNominalModeLedger181
import Yulang.GeneralNominalFramedExtension181

/-! The support-relative finite extension theorem instantiated by the proved
mode-sensitive full centered frame. No caller-supplied frame hypothesis remains. -/
namespace Yulang.GeneralNominalModeExtension181
open GeneralNominalCenters GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalModeLedger181 (fullSources)

theorem extension_iff (state : GeneralNominalCenteredSteps.State roles)
    (arguments : Fin count → NominalArgument) (previous : Assignment)
    (valid : GeneralNominalCenteredSteps.Models state previous)
    (linked : ∀ i, (arguments i).argument.endpoints.1 ∈ fullSources state ∧
      (arguments i).argument.endpoints.2 ∈ fullSources state ∧
      originSource (arguments i).origin ∈ fullSources state) :
    (∃ extended, GeneralNominalCenteredSteps.Models state extended ∧
      (∀ name ∈ fullSources state, extended name = previous name) ∧
      ∀ i, (arguments i).Holds extended) ↔
    (∀ i, ∃ actual, Observes previous (arguments i).origin actual) ∧
    (∀ i actual, Observes previous (arguments i).origin actual →
      GeneralNominalCaptureMerges.Fits previous (arguments i).argument.endpoints actual) ∧
    (∀ i j first last, (arguments i).argument.center = (arguments j).argument.center →
      Observes previous (arguments i).origin first → Observes previous (arguments j).origin last →
      Equivalent first last) ∧
    (∀ i actual, (arguments i).argument.center ∈ fullSources state →
      Observes previous (arguments i).origin actual →
      Equivalent actual (previous (arguments i).argument.center).1) :=
  GeneralNominalFramedExtension181.extension_iff state (fullSources state)
    (fun _ _ same valid => GeneralNominalModeLedger181.centered_models_frame state same valid)
    arguments previous valid linked

end Yulang.GeneralNominalModeExtension181
