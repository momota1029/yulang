import Yulang.CommonBoundCoalescing

/-!
# Bound renaming commutes with variable propagation

Renaming constructor references leaves every variable-flow path unchanged.
Lower/upper propagation and rigid comparison discovery therefore commute
literally with any bound map, even one that shares formerly distinct names.
No semantic assignment, injectivity, model or successful solver is needed.
-/

namespace Yulang.CommonBoundMap

open LayerBoundTemplates

universe u v
variable {n : Nat} {Bound : Type u} {Other : Type v}

theorem successors_map (rename : Bound → Other) (problem : Problem n Bound) (source : Fin n) :
    successors (mapBounds rename problem) source = successors problem source := by
  simp only [successors, mapBounds, List.filterMap_map]
  congr 1
  funext constraint
  cases constraint <;> rfl

theorem reachable_map (rename : Bound → Other) (problem : Problem n Bound) (source : Fin n) :
    reachable (mapBounds rename problem) source = reachable problem source := by
  have same : successors (mapBounds rename problem) = successors problem :=
    funext (successors_map rename problem)
  simp only [reachable, same]

theorem lowerSeeds_map (rename : Bound → Other) (problem : Problem n Bound) :
    lowerSeeds (mapBounds rename problem) =
      (lowerSeeds problem).map (fun entry => (rename entry.1, entry.2)) := by
  induction problem with
  | nil => rfl
  | cons constraint rest ih =>
      cases constraint <;> simp_all [lowerSeeds, mapBounds, Constraint.map]

theorem upperSeeds_map (rename : Bound → Other) (problem : Problem n Bound) :
    upperSeeds (mapBounds rename problem) =
      (upperSeeds problem).map (fun entry => (entry.1, rename entry.2)) := by
  induction problem with
  | nil => rfl
  | cons constraint rest ih =>
      cases constraint <;> simp_all [upperSeeds, mapBounds, Constraint.map]

theorem lowerBounds_map (rename : Bound → Other) (problem : Problem n Bound) (target : Fin n) :
    lowerBounds (mapBounds rename problem) target = (lowerBounds problem target).map rename := by
  simp only [lowerBounds, lowerSeeds_map, List.filterMap_map, reachable_map, List.map_filterMap]
  congr 1
  funext entry
  by_cases reachable : target ∈ LayerBoundTemplates.reachable problem entry.2 <;> simp [reachable]

theorem upperBounds_map (rename : Bound → Other) (problem : Problem n Bound) (source : Fin n) :
    upperBounds (mapBounds rename problem) source = (upperBounds problem source).map rename := by
  simp only [upperBounds, upperSeeds_map, List.filterMap_map, reachable_map, List.map_filterMap]
  congr 1
  funext entry
  by_cases reachable : entry.1 ∈ LayerBoundTemplates.reachable problem source <;> simp [reachable]

theorem ancestors_map (rename : Bound → Other) (problem : Problem n Bound) (target : Fin n) :
    ancestors (mapBounds rename problem) target = ancestors problem target := by
  simp only [ancestors, reachable_map]

/-- In particular, identifying duplicate optional-bound terms does not
change the set or order of rigid comparisons except for the same renaming. -/
theorem rigidComparisons_map (rename : Bound → Other) (problem : Problem n Bound) :
    CommonBoundCoalescing.rigidComparisons (mapBounds rename problem) =
      (CommonBoundCoalescing.rigidComparisons problem).map
        (fun edge => (rename edge.1, rename edge.2)) := by
  simp only [CommonBoundCoalescing.rigidComparisons, mapBounds, List.flatMap_map, List.map_flatMap]
  congr 1
  funext constraint
  cases constraint with
  | lower | flow | check => rfl
  | upper source bound =>
      change (lowerBounds (mapBounds rename problem) source).map _ = _
      rw [lowerBounds_map, List.map_map]
      simp only [List.map_map, Function.comp_def]

theorem lower_map (rename : Bound → Other) (evaluate : Other → Common.Ty)
    (problem : Problem n Bound) (target : Fin n) :
    CommonBoundCoalescing.lower evaluate (mapBounds rename problem) target =
      CommonBoundCoalescing.lower (evaluate ∘ rename) problem target := by
  simp only [CommonBoundCoalescing.lower, lowerBounds_map, List.map_map]

theorem upper_map (rename : Bound → Other) (evaluate : Other → Common.Ty)
    (problem : Problem n Bound) (source : Fin n) :
    CommonBoundCoalescing.upper evaluate (mapBounds rename problem) source =
      CommonBoundCoalescing.upper (evaluate ∘ rename) problem source := by
  simp only [CommonBoundCoalescing.upper, upperBounds_map, List.map_map]

theorem variablePart_map (rename : Bound → Other) (evaluate : Other → Common.Ty)
    (problem : Problem n Bound) (parameters : Fin n → Common.Ty) (target : Fin n) :
    CommonBoundCoalescing.variablePart evaluate (mapBounds rename problem) parameters target =
      CommonBoundCoalescing.variablePart (evaluate ∘ rename) problem parameters target := by
  simp only [CommonBoundCoalescing.variablePart, ancestors_map, upper_map]

theorem expand_map (rename : Bound → Other) (evaluate : Other → Common.Ty)
    (problem : Problem n Bound) (parameters : Fin n → Common.Ty) (target : Fin n) :
    CommonBoundCoalescing.expand evaluate (mapBounds rename problem) parameters target =
      CommonBoundCoalescing.expand (evaluate ∘ rename) problem parameters target := by
  simp only [CommonBoundCoalescing.expand, lower_map, variablePart_map]

theorem models_map (rename : Bound → Other) (evaluate : Other → Common.Ty)
    (problem : Problem n Bound) (values : Fin n → Common.Ty) :
    CommonBoundCoalescing.Models evaluate (mapBounds rename problem) values ↔
      CommonBoundCoalescing.Models (evaluate ∘ rename) problem values := by
  simp only [CommonBoundCoalescing.Models, mapBounds, List.forall_mem_map]
  apply forall_congr'
  intro constraint
  apply forall_congr'
  intro _
  cases constraint <;> rfl

end Yulang.CommonBoundMap
