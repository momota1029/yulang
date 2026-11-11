import Yulang.GeneralDictionaryBatchRecording
import Yulang.GeneralDictionaryEquationExamples
import Yulang.CommonRigidHeadInspection

/-!
# Sibling equations require one common model

Each scalar package below is separately satisfiable in the same original
unconstrained snapshot. Their joint transaction is inconsistent. This is an
equation-evidence regression, not a role classifier or candidate selection rule.
-/
namespace Yulang.GeneralDictionaryBatchExamples
open GeneralSourceState
open GeneralDictionaryStateEquations
open GeneralDictionaryBatchRecording
open GeneralDictionaryEquationExamples (roles demand)

abbrev free : State where
  slots := 1
  source := fun _ => 10
  source_injective := by intro _ _ _; exact Subsingleton.elim _ _
  rowSource := fun _ => 20
  ordinary := []
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro index; exact Fin.elim0 index
  heads := fun _ => .unresolved
  intervals := [(0, 0)]
  heads_sound := by intro _ _ _ _ impossible; cases impossible
  intervals_sound := by
    intro assignment _ pair member
    have same := List.mem_singleton.mp member
    subst pair
    exact Common.subtype_refl _

abbrev package (base : Inference.Base) : Item roles free where
  demand := demand
  located :=
    { lower := fun _ => 0
      upper := fun _ => 0
      head := fun _ => .base base
      target := fun _ => 0
      output := fun _ => .base base
      arguments := fun _ => rfl
      targets := by
        intro index
        change ((List.replicate 2 (⟨0, 10⟩ : Output))[index.val]' _).target = 10
        simp only [List.getElem_replicate] }

abbrev valuation (base : Inference.Base) : Assignment := fun _ => (.base base, Common.rowEmpty)

theorem free_models (assignment : Assignment) : Models free assignment :=
  (models_ordinary free assignment).mpr (by intro atom impossible; cases impossible)

theorem package_holds (base : Inference.Base) :
    (package base).located.equations.Holds (valuation base) := by
  constructor
  · intro index; exact ⟨Common.subtype_refl _, Common.subtype_refl _⟩
  · intro index; exact Common.equivalent_refl _

theorem separately_satisfiable (base : Inference.Base) :
    Models (record [package base]) (valuation base) := by
  apply (batch_models [package base] (valuation base)).mpr
  refine ⟨free_models _, ?_⟩
  intro item member
  have same := List.mem_singleton.mp member
  subst item
  exact package_holds base

/-- Separate witness models for sibling obligations cannot replace one shared
assignment. No assumption that int equals str is hidden by universal quantifiers. -/
theorem joint_inconsistent : ¬ ∃ assignment, Models (record [package .int, package .str]) assignment := by
  rintro ⟨assignment, valid⟩
  have all := ((batch_models [package .int, package .str] assignment).mp valid).2
  have first := (all (package .int) (by simp)).1 ⟨0, by decide⟩
  have last := (all (package .str) (by simp)).1 ⟨0, by decide⟩
  change Common.Subtype (assignment 10).1 (.base .int) ∧
    Common.Subtype (.base .int) (assignment 10).1 at first
  change Common.Subtype (assignment 10).1 (.base .str) ∧
    Common.Subtype (.base .str) (assignment 10).1 at last
  have impossible := (CommonRigidHeadInspection.base_iff .int .str).mp
    (Common.subtype_trans first.2 last.1)
  cases impossible

theorem order_preserves_joint_failure :
    ¬ ∃ assignment, Models (record [package .str, package .int]) assignment := by
  rintro ⟨assignment, valid⟩
  apply joint_inconsistent
  exact ⟨assignment, (batch_order_models [package .int, package .str]
    [package .str, package .int] (.swap _ _ []) assignment).mpr valid⟩

/-- Repeated node packages are recorded with multiplicity, even when their
semantic equations happen to coincide. -/
theorem repeated_package_atoms : (batchAtoms [package .int, package .int]).length = 12 := rfl

end Yulang.GeneralDictionaryBatchExamples
