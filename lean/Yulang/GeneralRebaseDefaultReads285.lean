import Yulang.GeneralRebaseCoordinateProfile285
import Yulang.GeneralDictionaryVersionedGap206Install233
import Yulang.GeneralDictionaryVersionedGap206Feedback234

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 8500000
namespace Yulang.GeneralRebaseDefaultReads285
open GeneralDictionaryDefaultGap206Source (plan root registry model counter)
open GeneralDictionaryVersionedGap206Install233 (installed)
open GeneralRebaseCoordinateProfile285 (Profile ofBody ofEquation)
open GeneralNominalRebaseEffectView243 (Equation body)
open Core.PresenceGeneration (CompTerm)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)

abbrev default : Body := .default 0 0 (.var 0)

theorem positional_leaf (mode : GeneralNominalMaterialization.Mode) :
    GeneralNominalRebaseEffectView243.bodyVariables plan CompTerm.var default mode 0 = .var 1 := rfl

theorem translates : GeneralNominalCenteredHeadMatEffects.compileBody plan default =
    some (.variable 0) := rfl

abbrev eqn : Equation := ⟨.var 0,.source (.var 1)⟩

theorem exact_body : body plan CompTerm.var 0 default = some eqn := by
  unfold body
  rw [translates]
  simp only [Option.map_some,GeneralNominalRebaseEffectView243.compile,positional_leaf]
  rfl

theorem rhs_only : ofBody plan CompTerm.var default = some ⟨[1],[]⟩ := by
  unfold ofBody GeneralRebaseCoordinateProfile285.ofExpr
  rw [translates]
  simp only [Option.map_some,GeneralRebaseSourceDemands285.demands,List.flatMap_cons,List.flatMap_nil,
    GeneralRebaseSourceDemands285.expand,positional_leaf,List.append_nil]
  rfl

theorem coordinates : ofEquation plan CompTerm.var 0 default = some ⟨[0,1],[]⟩ := by
  rw [ofEquation,rhs_only]
  rfl

theorem installed_valid (a : Assignment) (valid : Models installed a) : eqn.Holds a :=
  GeneralDictionaryVersionedGap206Feedback234.installed_equal a valid

theorem compare_actual : Models installed model ∧ ¬ Models installed counter ∧
    ofBody plan CompTerm.var default = some ⟨[1],[]⟩ ∧
    ofEquation plan CompTerm.var 0 default = some ⟨[0,1],[]⟩ ∧
    (∀ a, Models installed a → eqn.Holds a) :=
  ⟨GeneralDictionaryVersionedGap206Install233.installed_model,
    GeneralDictionaryVersionedGap206Install233.bottom_removed,rhs_only,coordinates,installed_valid⟩

end Yulang.GeneralRebaseDefaultReads285
