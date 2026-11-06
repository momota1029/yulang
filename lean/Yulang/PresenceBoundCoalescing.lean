import Yulang.LayerBoundTemplates
import Yulang.PresenceLayers

/-!
# Elimination of flat presence bounds with every parameter left free

The topology is the existing finite worklist topology, but the bounds are
interpreted as arbitrary predicates on data values. In particular they may
contain correlated presence alternatives and arbitrary payload predicates.
Neither bounds nor parameters are approximated by a finite catalogue of values.

For a variable `i`, the expansion is the union of its propagated lower bounds
and `p j ∩ U j` for every predecessor `j`. A finite consistency check is exact
when its supplied bound-inclusion checker is exact. Every parameter assignment
then satisfies the problem, and every independent solution is recovered by
using that solution as the shared parameters.

This is the flat elimination part of the regular presence solver. Constructor
decomposition, open-tail saturation, functions and rows are separate obligations;
an exact inclusion checker for arbitrary predicate bounds is not asserted here.
-/

namespace Yulang.PresenceBoundCoalescing

open LayerBoundTemplates
open PresenceDataTypes (Ty Le)
open SourceDataRuntime (Value)

universe u v
variable {n : Nat} {Bound : Type u}

def Holds (evaluate : Bound → Ty) (value : Fin n → Ty) : Constraint n Bound → Prop
  | .lower bound target => Le (evaluate bound) (value target)
  | .flow source target => Le (value source) (value target)
  | .upper source bound => Le (value source) (evaluate bound)
  | .check source target => Le (evaluate source) (evaluate target)

def Models (evaluate : Bound → Ty) (problem : Problem n Bound) (value : Fin n → Ty) : Prop :=
  ∀ constraint ∈ problem, Holds evaluate value constraint

private theorem mem_successors (problem : Problem n Bound) (source target : Fin n) :
    target ∈ successors problem source ↔ .flow source target ∈ problem := by
  simp only [successors, List.mem_filterMap]
  constructor
  · rintro ⟨constraint, member, found⟩
    cases constraint with
    | flow start finish =>
        change (if start = source then some finish else none) = some target at found
        split at found
        · rename_i equal
          subst start
          have equal : finish = target := Option.some.inj found
          subst finish
          exact member
        · cases found
    | _ => cases found
  · intro member
    exact ⟨.flow source target, member, by simp⟩

private theorem mem_lowerSeeds (problem : Problem n Bound) (bound : Bound) (source : Fin n) :
    (bound, source) ∈ lowerSeeds problem ↔ .lower bound source ∈ problem := by
  simp only [lowerSeeds, List.mem_filterMap]
  constructor
  · rintro ⟨constraint, member, found⟩
    cases constraint with
    | lower actual target =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
        exact member
    | _ => cases found
  · intro member
    exact ⟨.lower bound source, member, rfl⟩

private theorem mem_upperSeeds (problem : Problem n Bound) (source : Fin n) (bound : Bound) :
    (source, bound) ∈ upperSeeds problem ↔ .upper source bound ∈ problem := by
  simp only [upperSeeds, List.mem_filterMap]
  constructor
  · rintro ⟨constraint, member, found⟩
    cases constraint with
    | upper actual target =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
        exact member
    | _ => cases found
  · intro member
    exact ⟨.upper source bound, member, rfl⟩

theorem mem_lowerBounds (problem : Problem n Bound) (target : Fin n) (bound : Bound) :
    bound ∈ lowerBounds problem target ↔
      ∃ source, .lower bound source ∈ problem ∧ Reaches problem source target := by
  simp only [lowerBounds, List.mem_filterMap]
  constructor
  · rintro ⟨⟨actual, source⟩, member, found⟩
    split at found
    · rename_i path
      have equal : actual = bound := Option.some.inj found
      subst actual
      exact ⟨source, (mem_lowerSeeds problem bound source).mp member,
        (reachable_exact problem source target).mp path⟩
    · cases found
  · rintro ⟨source, member, path⟩
    refine ⟨(bound, source), (mem_lowerSeeds problem bound source).mpr member, ?_⟩
    simp only [(reachable_exact problem source target).mpr path, ↓reduceIte]

theorem mem_upperBounds (problem : Problem n Bound) (source : Fin n) (bound : Bound) :
    bound ∈ upperBounds problem source ↔
      ∃ target, .upper target bound ∈ problem ∧ Reaches problem source target := by
  simp only [upperBounds, List.mem_filterMap]
  constructor
  · rintro ⟨⟨target, actual⟩, member, found⟩
    split at found
    · rename_i path
      have equal : actual = bound := Option.some.inj found
      subst actual
      exact ⟨target, (mem_upperSeeds problem target bound).mp member,
        (reachable_exact problem source target).mp path⟩
    · cases found
  · rintro ⟨target, member, path⟩
    refine ⟨(target, bound), (mem_upperSeeds problem target bound).mpr member, ?_⟩
    simp only [(reachable_exact problem source target).mpr path, ↓reduceIte]

def lower (evaluate : Bound → Ty) (problem : Problem n Bound) (target : Fin n) : Ty :=
  fun value => ∃ bound ∈ lowerBounds problem target, evaluate bound value

def upper (evaluate : Bound → Ty) (problem : Problem n Bound) (source : Fin n) : Ty :=
  fun value => ∀ bound ∈ upperBounds problem source, evaluate bound value

/-- This is a shared-parameter expression, not a constrained parameter family. -/
def expand (evaluate : Bound → Ty) (problem : Problem n Bound)
    (parameters : Fin n → Ty) (target : Fin n) : Ty := fun value =>
  lower evaluate problem target value ∨
    ∃ source, Reaches problem source target ∧ parameters source value ∧ upper evaluate problem source value

theorem reaches_inclusion {evaluate : Bound → Ty} {problem : Problem n Bound}
    {value : Fin n → Ty} (model : Models evaluate problem value)
    {source target : Fin n} (path : Reaches problem source target) :
    Le (value source) (value target) := by
  induction path with
  | nil => exact PresenceDataTypes.le_refl _
  | @cons source middle target edge rest ih =>
      exact PresenceDataTypes.le_trans
        (model (.flow source middle) ((mem_successors problem source middle).mp edge)) ih

theorem lower_below {evaluate : Bound → Ty} {problem : Problem n Bound}
    {value : Fin n → Ty} (model : Models evaluate problem value) (target : Fin n) :
    Le (lower evaluate problem target) (value target) := by
  rintro item ⟨bound, member, valid⟩
  obtain ⟨source, seed, path⟩ := (mem_lowerBounds problem target bound).mp member
  exact reaches_inclusion model path item (model (.lower bound source) seed item valid)

theorem upper_above {evaluate : Bound → Ty} {problem : Problem n Bound}
    {value : Fin n → Ty} (model : Models evaluate problem value) (source : Fin n) :
    Le (value source) (upper evaluate problem source) := by
  intro item valid bound member
  obtain ⟨target, seed, path⟩ := (mem_upperBounds problem source bound).mp member
  exact model (.upper target bound) seed item (reaches_inclusion model path item valid)

theorem lower_lower (evaluate : Bound → Ty) (problem : Problem n Bound)
    (bound : Bound) (target : Fin n) (member : .lower bound target ∈ problem) :
    Le (evaluate bound) (lower evaluate problem target) :=
  fun _ valid => ⟨bound, (mem_lowerBounds problem target bound).mpr ⟨target, member, .nil target⟩, valid⟩

theorem lower_flow (evaluate : Bound → Ty) (problem : Problem n Bound)
    (source target : Fin n) (member : .flow source target ∈ problem) :
    Le (lower evaluate problem source) (lower evaluate problem target) := by
  rintro item ⟨bound, lowerMember, valid⟩
  obtain ⟨start, seed, path⟩ := (mem_lowerBounds problem source bound).mp lowerMember
  exact ⟨bound, (mem_lowerBounds problem target bound).mpr
    ⟨start, seed, path.append (.cons ((mem_successors problem source target).mpr member) (.nil target))⟩,
    valid⟩

/-- Existing solutions imply consistency of the computed lower assignment. -/
theorem lower_models_of_models {evaluate : Bound → Ty} {problem : Problem n Bound}
    {value : Fin n → Ty} (model : Models evaluate problem value) :
    Models evaluate problem (lower evaluate problem) := by
  intro constraint member
  cases constraint with
  | lower bound target => exact lower_lower evaluate problem bound target member
  | flow source target => exact lower_flow evaluate problem source target member
  | upper source bound => exact PresenceDataTypes.le_trans (lower_below model source) (model _ member)
  | check source target => exact model _ member

/-- Every freely chosen predicate parameter satisfies the same finite problem.
Consistency is needed only for the fixed bounds, never for the parameters. -/
theorem expand_satisfies {evaluate : Bound → Ty} {problem : Problem n Bound}
    (consistent : Models evaluate problem (lower evaluate problem)) (parameters : Fin n → Ty) :
    Models evaluate problem (expand evaluate problem parameters) := by
  intro constraint member
  cases constraint with
  | lower bound target =>
      exact fun item valid => Or.inl (lower_lower evaluate problem bound target member item valid)
  | flow source target =>
      intro item valid
      rcases valid with lowerValid | ⟨start, path, parameter, upperValid⟩
      · exact Or.inl (lower_flow evaluate problem source target member item lowerValid)
      · exact Or.inr ⟨start,
          path.append (.cons ((mem_successors problem source target).mpr member) (.nil target)),
          parameter, upperValid⟩
  | upper source bound =>
      intro item valid
      rcases valid with lowerValid | ⟨start, path, _, upperValid⟩
      · exact consistent _ member item lowerValid
      · exact upperValid bound ((mem_upperBounds problem start bound).mpr ⟨source, member, path⟩)
  | check source target => exact consistent _ member

/-- Every independent solution is recovered at every original slot. -/
theorem expand_retraction {evaluate : Bound → Ty} {problem : Problem n Bound}
    {value : Fin n → Ty} (model : Models evaluate problem value) (target : Fin n) (item : Value) :
    expand evaluate problem value target item ↔ value target item := by
  constructor
  · intro valid
    rcases valid with lowerValid | ⟨source, path, parameter, _⟩
    · exact lower_below model target item lowerValid
    · exact reaches_inclusion model path item parameter
  · intro valid
    exact Or.inr ⟨target, .nil target, valid, upper_above model target item valid⟩

/-- Extensional recovery permits arbitrary output observations, including
negative occurrences; no monotonicity premise on the output is necessary. -/
theorem expand_retraction_eq {evaluate : Bound → Ty} {problem : Problem n Bound}
    {value : Fin n → Ty} (model : Models evaluate problem value) :
    expand evaluate problem value = value := by
  funext target item
  exact propext (expand_retraction model target item)

def consistent (check : Bound → Bound → Bool) (problem : Problem n Bound) : Bool :=
  problem.all fun
    | .lower _ _ | .flow _ _ => true
    | .upper source bound => (lowerBounds problem source).all fun lowerBound => check lowerBound bound
    | .check source target => check source target

/-- The finite consistency scan uses only comparisons between fixed bounds. -/
theorem consistent_exact (check : Bound → Bound → Bool) (evaluate : Bound → Ty)
    (exactCheck : ∀ left right, check left right = true ↔ Le (evaluate left) (evaluate right))
    (problem : Problem n Bound) :
    consistent check problem = true ↔ Models evaluate problem (lower evaluate problem) := by
  simp only [consistent, List.all_eq_true]
  constructor
  · intro checked constraint member
    cases constraint with
    | lower bound target => exact lower_lower evaluate problem bound target member
    | flow source target => exact lower_flow evaluate problem source target member
    | upper source bound =>
        rintro item ⟨lowerBound, lowerMember, valid⟩
        exact (exactCheck lowerBound bound).mp
          (List.all_eq_true.mp (checked _ member) lowerBound lowerMember) item valid
    | check source target => exact (exactCheck source target).mp (checked _ member)
  · intro model constraint member
    cases constraint with
    | lower | flow => rfl
    | upper source bound =>
        apply List.all_eq_true.mpr
        intro lowerBound lowerMember
        apply (exactCheck lowerBound bound).mpr
        exact fun item valid => model _ member item ⟨lowerBound, lowerMember, valid⟩
    | check source target => exact (exactCheck source target).mpr (model _ member)

theorem consistent_iff_satisfiable (check : Bound → Bound → Bool) (evaluate : Bound → Ty)
    (exactCheck : ∀ left right, check left right = true ↔ Le (evaluate left) (evaluate right))
    (problem : Problem n Bound) :
    consistent check problem = true ↔ ∃ value, Models evaluate problem value := by
  rw [consistent_exact check evaluate exactCheck problem]
  exact ⟨fun model => ⟨_, model⟩, fun ⟨_, model⟩ => lower_models_of_models model⟩

/-! ## Finite presence-layer schemes -/

open PresenceLayers (Layer)
variable {State : Type v}

def joinLayers : List (Layer State) → Layer State
  | [] => .bottom
  | layer :: rest => .union layer (joinLayers rest)

def meetLayers : List (Layer State) → Layer State
  | [] => .top
  | layer :: rest => .inter layer (meetLayers rest)

def coalesce (problem : Problem n (Layer State)) (parameters : Fin n → Layer State)
    (target : Fin n) : Layer State :=
  .union (joinLayers (lowerBounds problem target))
    (joinLayers ((ancestors problem target).map fun source =>
      .inter (parameters source) (meetLayers (upperBounds problem source))))

theorem joinLayers_exact (assignment : State → Ty) (hidden : List Nat)
    (layers : List (Layer State)) (item : Value) :
    (joinLayers layers).meaning assignment hidden item ↔
      ∃ layer ∈ layers, layer.meaning assignment hidden item := by
  induction layers with
  | nil => simp [joinLayers, Layer.meaning, PresenceDataTypes.never]
  | cons layer rest ih =>
      simp [joinLayers, Layer.meaning, PresenceDataTypes.union, ih]

theorem meetLayers_exact (assignment : State → Ty) (hidden : List Nat)
    (layers : List (Layer State)) (item : Value) :
    (meetLayers layers).meaning assignment hidden item ↔
      ∀ layer ∈ layers, layer.meaning assignment hidden item := by
  induction layers with
  | nil => simp [meetLayers, Layer.meaning, PresenceDataTypes.any]
  | cons layer rest ih =>
      simp [meetLayers, Layer.meaning, PresenceDataTypes.inter, ih]

/-- Constructing the finite layer commutes with its independent predicate
meaning for every mask and every payload interpretation. -/
theorem coalesce_exact (assignment : State → Ty) (hidden : List Nat)
    (problem : Problem n (Layer State)) (parameters : Fin n → Layer State)
    (target : Fin n) (item : Value) :
    (coalesce problem parameters target).meaning assignment hidden item ↔
      expand (fun layer => layer.meaning assignment hidden) problem
        (fun index => (parameters index).meaning assignment hidden) target item := by
  simp only [coalesce, Layer.meaning, PresenceDataTypes.union, expand]
  apply or_congr (joinLayers_exact assignment hidden _ item) ?_
  rw [joinLayers_exact]
  constructor
  · rintro ⟨layer, member, valid⟩
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    exact ⟨source, (mem_ancestors problem source target).mp sourceMember, valid.1,
      (meetLayers_exact assignment hidden _ item).mp valid.2⟩
  · rintro ⟨source, path, parameter, upperValid⟩
    exact ⟨_, List.mem_map.mpr ⟨source, (mem_ancestors problem source target).mpr path, rfl⟩,
      parameter, (meetLayers_exact assignment hidden _ item).mpr upperValid⟩

/-- The flat presence coalescer leaves every parameter layer free. -/
theorem coalesce_satisfies (assignment : State → Ty) (hidden : List Nat)
    (problem : Problem n (Layer State)) (parameters : Fin n → Layer State)
    (checked : Models (fun layer => layer.meaning assignment hidden) problem
      (lower (fun layer => layer.meaning assignment hidden) problem)) :
    Models (fun layer => layer.meaning assignment hidden) problem
      (fun index => (coalesce problem parameters index).meaning assignment hidden) := by
  have equal : (fun index => (coalesce problem parameters index).meaning assignment hidden) =
      expand (fun layer => layer.meaning assignment hidden) problem
        (fun index => (parameters index).meaning assignment hidden) := by
    funext index item
    exact propext (coalesce_exact assignment hidden problem parameters index item)
  rw [equal]
  exact expand_satisfies checked _

/-- Layer parameters representing an independent solution recover all slots,
with no positivity assumption on any later observation of those slots. -/
theorem coalesce_retraction (assignment : State → Ty) (hidden : List Nat)
    (problem : Problem n (Layer State)) (parameters : Fin n → Layer State)
    (model : Models (fun layer => layer.meaning assignment hidden) problem
      (fun index => (parameters index).meaning assignment hidden)) (target : Fin n) (item : Value) :
    (coalesce problem parameters target).meaning assignment hidden item ↔
      (parameters target).meaning assignment hidden item :=
  (coalesce_exact assignment hidden problem parameters target item).trans
    (expand_retraction model target item)

end Yulang.PresenceBoundCoalescing
