import Yulang.GeneralNominalHeadLedgerFrame182
import Yulang.GeneralNominalPredicateExtension182

/-! The support-relative finite extension theorem instantiated by the proved
full historical/live effect-ledger frame. No caller-supplied frame hypothesis remains. -/
namespace Yulang.GeneralNominalHeadLedgerExtension182
open GeneralNominalCenters GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalHeadLedgerFrame182 (fullSources)

theorem extension_iff (state : GeneralNominalCenteredHeadStepEffects.State roles)
    (arguments : Fin count → NominalArgument) (previous : Assignment)
    (valid : GeneralNominalCenteredHeadStepEffects.Models state previous)
    (linked : ∀ i, (arguments i).argument.endpoints.1 ∈ fullSources state ∧
      (arguments i).argument.endpoints.2 ∈ fullSources state ∧
      originSource (arguments i).origin ∈ fullSources state) :
    (∃ extended, GeneralNominalCenteredHeadStepEffects.Models state extended ∧
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
  GeneralNominalPredicateExtension182.extension_iff (GeneralNominalCenteredHeadStepEffects.Models state) (fullSources state)
    (fun _ _ same valid => (GeneralNominalHeadLedgerFrame182.models_iff state same).mp valid)
    arguments previous valid linked

end Yulang.GeneralNominalHeadLedgerExtension182
