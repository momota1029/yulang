import Yulang.GeneralDeclarativeWitnessInheritedModeFixture357
import Yulang.GeneralDeclarativeWitnessDeclaredState357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessInheritedModeModel357
open GeneralDeclarativeWitnessSparseIntervals357 (Compiled declared_context_meaning)
open GeneralDeclarativeWitnessDeclaredState357 (Current)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCommonBridge (lift atoms_exact)
open CommonRecursiveNominalIntervals (ContextWellFormed ContextDerives)
open PresenceNormalForm (Atom All)
open Core.PresenceGeneration (Comp)

theorem proved_in_same_lifted_state {s : Current} {r ctx lo hi}
    (checked : Compiled s.environment r ctx lo hi)
    (retained : ∀ a ∈ checked.rows,a ∈ s.ordinary.normal.ordinary)
    (m : Nat → Comp Common.model) (fit : Models s.ordinary (lift m)) :
    ContextWellFormed r ctx lo ∧ ContextWellFormed r ctx hi ∧ ContextDerives r m ctx lo hi := by
  have all : All CommonNominalFullCarrier.model (lift m) checked.rows :=
    fun atom used => fit.1.1 _ (retained atom used)
  exact declared_context_meaning checked m ((atoms_exact m checked.rows).mp all)

end Yulang.GeneralDeclarativeWitnessInheritedModeModel357
