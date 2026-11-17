import Yulang.GeneralPresenceGuardedCommutation247

/-! Local deletion of a redundant guarded closure across independent owners.
This bounds neither live body syntax nor operational transitions. The actual
cross-owner independence producer and a global normalizer remain separate. -/
namespace Yulang.GeneralPresenceGuardedCompression247
open Core.PresenceGeneration
open GeneralPresenceGuardedEnvironment247 GeneralPresenceGuardedCommutation247
open CommonNominalFullCarrier
variable {Name : Type} [DecidableEq Name]

structure Independent (first last : Closure Name) : Prop where
  disjoint : ∀ firstIndex lastIndex, first.targets firstIndex ≠ last.targets lastIndex
  firstParameters : ∀ lastIndex firstParameter, last.targets lastIndex ≠ first.parametersAt firstParameter
  lastParameters : ∀ firstIndex lastParameter, first.targets firstIndex ≠ last.parametersAt lastParameter

theorem commute_middle (old : Closure Name) (middle : List (Closure Name))
    (independent : ∀ closure ∈ middle, Independent old closure)
    (assignment : Name → Comp model) :
    old.read (read middle assignment) = read middle (old.read assignment) := by
  induction middle with
  | nil => rfl
  | cons closure rest ih =>
    have pair := independent closure (by simp)
    have tail := ih (fun item member => independent item (List.mem_cons_of_mem _ member))
    change old.read (closure.read (read rest assignment)) = closure.read (read rest (old.read assignment))
    rw [read_commute old closure pair.disjoint pair.firstParameters pair.lastParameters,tail]

/-- Subset inclusion of target images suffices; equal layouts are a special case. -/
def TargetsWithin (fresh old : Closure Name) : Prop :=
  ∀ index, ∃ original, old.targets original = fresh.targets index

theorem absorbs_within (old fresh : Closure Name) (within : TargetsWithin fresh old)
    (assignment : Name → Comp model) : old.read (fresh.read assignment) = old.read assignment := by
  have separate : ∀ index parameter, fresh.targets index ≠ old.parametersAt parameter := by
    intro index parameter
    obtain ⟨original,equal⟩ := within index
    rw [← equal]
    exact old.separate original parameter
  funext name
  apply Prod.ext
  · by_cases inside : ∃ index, old.targets index = name
    · obtain ⟨index,rfl⟩ := inside
      rw [target_value old (fresh.read assignment) index,target_value old assignment index]
      exact congrFun (values_after old fresh separate assignment) index
    · have outsideOld : ∀ index, old.targets index ≠ name := fun index same => inside ⟨index,same⟩
      have outsideFresh : ∀ index, fresh.targets index ≠ name := by
        intro index
        obtain ⟨original,equal⟩ := within index
        rw [← equal]
        exact outsideOld original
      rw [old.outside (fresh.read assignment) name outsideOld,
        old.outside assignment name outsideOld,fresh.outside assignment name outsideFresh]
  · rfl

theorem delete_inner (old fresh : Closure Name) (middle : List (Closure Name))
    (independent : ∀ closure ∈ middle, Independent old closure)
    (within : TargetsWithin fresh old) (assignment : Name → Comp model) :
    old.read (read middle (fresh.read assignment)) = old.read (read middle assignment) := by
  rw [commute_middle old middle independent (fresh.read assignment),
    absorbs_within old fresh within assignment,commute_middle old middle independent assignment]

theorem delete_repeated (front middle suffix : List (Closure Name)) (old fresh : Closure Name)
    (independent : ∀ closure ∈ middle, Independent old closure)
    (within : TargetsWithin fresh old) (assignment : Name → Comp model) :
    read (front ++ old :: (middle ++ fresh :: suffix)) assignment =
      read (front ++ old :: (middle ++ suffix)) assignment := by
  simp only [read_append,GeneralPresenceGuardedEnvironment247.read]
  rw [delete_inner old fresh middle independent within]

end Yulang.GeneralPresenceGuardedCompression247
