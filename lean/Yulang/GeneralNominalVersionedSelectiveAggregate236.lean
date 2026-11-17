import Yulang.GeneralNominalSelectiveEquationRealization236
import Yulang.GeneralNominalVersionedAggregateRealization236
import Yulang.GeneralNominalVersionedAggregateEntries236
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedSelectiveAggregate236
open GeneralNominalAllocation (Bindings occurrences lower upper)
open GeneralNominalAggregateVersion231 (slot)
open GeneralNominalVersionedAggregateRealization236 (entries member_iff coherent supported)
open GeneralNominalCommonBridge (Assignment)
noncomputable def patch (seed root declaration : Nat) (bindings : Bindings) (names : List Nat) (pool : List Nat) (model : Assignment) : Assignment :=
  GeneralNominalSelectiveEquationRealization236.patch (entries seed root declaration bindings names) pool model

theorem equations (seed root declaration : Nat) (bindings : Bindings) (names : List Nat) (pool : List Nat) (model : Assignment)
    (linked : GeneralNominalAllocationSupport.Endpoints bindings pool)
    (old : ∀ entry ∈ entries seed root declaration bindings names, entry.1 ∈ pool →
      PresenceNormalForm.All CommonNominalFullCarrier.model model (GeneralNominalAllocation.equations entry.1 entry.2)) :
    ∀ entry ∈ entries seed root declaration bindings names,
      PresenceNormalForm.All CommonNominalFullCarrier.model (patch seed root declaration bindings names pool model)
        (GeneralNominalAllocation.equations entry.1 entry.2) :=
  GeneralNominalSelectiveEquationRealization236.equations _ _ (coherent seed root declaration bindings names)
    (supported seed root declaration bindings names linked) old

theorem merges (state : GeneralNominalState.State) (registry : GeneralDeclarations.Registry)
    (root : Nat) (declaration : GeneralDeclarations.Declaration) (bindings : Bindings) (model : Assignment)
    (old : ∀ entry ∈ entries state.seed root declaration.id bindings declaration.inputNames, entry.1 ∈ pool →
      PresenceNormalForm.All CommonNominalFullCarrier.model model (GeneralNominalAllocation.equations entry.1 entry.2))
    (linked : GeneralNominalAllocationSupport.Endpoints bindings pool) :
    PresenceNormalForm.All CommonNominalFullCarrier.model
      (patch state.seed root declaration.id bindings declaration.inputNames pool model)
      (GeneralNominalVersionedAllocation231.merges state registry root declaration bindings) := by
  apply (GeneralNominalVersionedAggregateEntries236.holds_iff state registry root declaration bindings _).mpr
  exact equations state.seed root declaration.id bindings declaration.inputNames pool model linked old
end Yulang.GeneralNominalVersionedSelectiveAggregate236
