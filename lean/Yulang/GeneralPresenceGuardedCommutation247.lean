import Yulang.GeneralPresenceGuardedEnvironment247

/-! Literal commutation for independent guarded owners. Target sets are
separate and neither owner's type parameters read the other's targets. Row
reads may name private targets because every row coordinate remains unchanged.
No actual cross-owner allocation or dependency producer is claimed here. -/
namespace Yulang.GeneralPresenceGuardedCommutation247
open Core.PresenceGeneration
open GeneralPresenceGuardedBlock246 GeneralPresenceGuardedEnvironment247
open CommonNominalFullCarrier
variable {Name : Type} [DecidableEq Name]

theorem values_after (first last : Closure Name)
    (independent : ∀ index parameter, last.targets index ≠ first.parametersAt parameter)
    (assignment : Name → Comp model) :
    values first.body first.parametersAt (last.read assignment) =
      values first.body first.parametersAt assignment := by
  have sameBody : compiled first.body (last.read assignment) = compiled first.body assignment := by
    funext index
    exact GeneralPresenceGuardedLayer246.lower_rows (last.read assignment) assignment
      (last.rows assignment) (first.body index)
  have sameArguments : arguments first.parametersAt (last.read assignment) =
      arguments first.parametersAt assignment := by
    funext parameter
    exact congrArg Prod.fst
      (last.outside assignment (first.parametersAt parameter) (fun index => independent index parameter))
  unfold values
  rw [sameBody,sameArguments]

theorem target_value (closure : Closure Name) (assignment : Name → Comp model)
    (index : Fin closure.nodes) :
    (closure.read assignment (closure.targets index)).1 =
      values closure.body closure.parametersAt assignment index :=
  extend_at closure.body closure.targets closure.injective closure.parametersAt assignment index

theorem read_commute (first last : Closure Name)
    (disjoint : ∀ firstIndex lastIndex, first.targets firstIndex ≠ last.targets lastIndex)
    (firstIndependent : ∀ lastIndex firstParameter,
      last.targets lastIndex ≠ first.parametersAt firstParameter)
    (lastIndependent : ∀ firstIndex lastParameter,
      first.targets firstIndex ≠ last.parametersAt lastParameter)
    (assignment : Name → Comp model) :
    first.read (last.read assignment) = last.read (first.read assignment) := by
  funext name
  apply Prod.ext
  · by_cases inFirst : ∃ index, first.targets index = name
    · obtain ⟨index,rfl⟩ := inFirst
      have outsideLast : ∀ other, last.targets other ≠ first.targets index :=
        fun other => Ne.symm (disjoint index other)
      rw [last.outside (first.read assignment) (first.targets index) outsideLast,
        target_value first (last.read assignment) index,target_value first assignment index]
      exact congrFun (values_after first last firstIndependent assignment) index
    · have outsideFirst : ∀ index, first.targets index ≠ name :=
        fun index same => inFirst ⟨index,same⟩
      by_cases inLast : ∃ index, last.targets index = name
      · obtain ⟨index,rfl⟩ := inLast
        rw [first.outside (last.read assignment) (last.targets index) outsideFirst,
          target_value last assignment index,target_value last (first.read assignment) index]
        exact (congrFun (values_after last first lastIndependent assignment) index).symm
      · have outsideLast : ∀ index, last.targets index ≠ name :=
          fun index same => inLast ⟨index,same⟩
        rw [first.outside (last.read assignment) name outsideFirst,
          last.outside (first.read assignment) name outsideLast,
          last.outside assignment name outsideLast,first.outside assignment name outsideFirst]
  · rfl

end Yulang.GeneralPresenceGuardedCommutation247
