import Yulang.StructuralDecisions
import Yulang.FiniteWorklist
import Yulang.StructuralRowResolution

/-!
# Executable inference of unknown value-type bounds

A finite problem has unknown value types, ground lower and upper bounds, and
inclusions between unknowns. Ground bounds may be arbitrary types in the
existing structural algebra: arrows, records, variants, unions and intersections
are not replaced by a finite catalogue of possible assignments.

The solver propagates each lower bound along the finite graph of unknowns,
constructs their union at every unknown, and checks the resulting assignment.
The worklist capacity is the number of unknowns, proved sufficient for paths of
every finite length. It is not caller-supplied fuel or a limit on type depth.

The semantic model below is independent of the algorithm. Failure is equivalent
to absence of *any* structural-type assignment, and success returns a least
assignment. This least assignment is not a generalized polymorphic principal
type: constructor-nested unknowns, recursive value types, and let generalization
are separate responsibilities.
-/

namespace Yulang.ValueBounds

open StructuralBase

universe u v

inductive Constraint (n : Nat) (RowType : Type u) where
  | lower (type : Ty RowType) (target : Fin n)
  | flow (source target : Fin n)
  | upper (source : Fin n) (type : Ty RowType)
  | check (source target : Ty RowType)

abbrev Problem (n : Nat) (RowType : Type u) := List (Constraint n RowType)
abbrev Valuation (n : Nat) (RowType : Type u) := Fin n → Ty RowType

variable {n : Nat} {RowType : Type u}

def Constraint.Holds (leRow : RowType → RowType → Prop)
    (value : Valuation n RowType) : Constraint n RowType → Prop
  | .lower type target => Subtype leRow type (value target)
  | .flow source target => Subtype leRow (value source) (value target)
  | .upper source type => Subtype leRow (value source) type
  | .check source target => Subtype leRow source target

def Models (leRow : RowType → RowType → Prop) (problem : Problem n RowType)
    (value : Valuation n RowType) : Prop :=
  ∀ constraint ∈ problem, constraint.Holds leRow value

/-- The forward part of a problem does not include its upper-bound tests. -/
def Constraint.LowerHolds (leRow : RowType → RowType → Prop)
    (value : Valuation n RowType) : Constraint n RowType → Prop
  | .lower type target => Subtype leRow type (value target)
  | .flow source target => Subtype leRow (value source) (value target)
  | .upper _ _ | .check _ _ => True

def LowerModels (leRow : RowType → RowType → Prop) (problem : Problem n RowType)
    (value : Valuation n RowType) : Prop :=
  ∀ constraint ∈ problem, constraint.LowerHolds leRow value

theorem Models.lower {leRow : RowType → RowType → Prop}
    {problem : Problem n RowType} {value : Valuation n RowType}
    (model : Models leRow problem value) : LowerModels leRow problem value := by
  intro constraint member
  cases constraint <;> first | exact model _ member | trivial

/-- Both list scans retain duplicate bounds; duplicates do not affect the
semantic leastness theorem. No equality test on ground types is needed. -/
def seeds (problem : Problem n RowType) : List (Ty RowType × Fin n) :=
  problem.filterMap fun
    | .lower type target => some (type, target)
    | _ => none

def successors (problem : Problem n RowType) (source : Fin n) : List (Fin n) :=
  problem.filterMap fun
    | .flow start target => if start = source then some target else none
    | _ => none

@[simp] theorem mem_seeds (problem : Problem n RowType) (type : Ty RowType)
    (source : Fin n) : (type, source) ∈ seeds problem ↔ .lower type source ∈ problem := by
  simp only [seeds, List.mem_filterMap]
  constructor
  · rintro ⟨constraint, member, found⟩
    cases constraint with
    | lower actual target =>
        have same := Prod.mk.inj (Option.some.inj found)
        obtain ⟨rfl, rfl⟩ := same
        exact member
    | _ => cases found
  · intro member
    exact ⟨.lower type source, member, rfl⟩

@[simp] theorem mem_successors (problem : Problem n RowType) (source target : Fin n) :
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

abbrev Reaches (problem : Problem n RowType) (source target : Fin n) : Prop :=
  FiniteWorklist.Path (successors problem) source target

/-- The executable search receives exactly the finite unknown count. -/
def reachable (problem : Problem n RowType) (source : Fin n) : List (Fin n) :=
  FiniteWorklist.reachable (successors problem) n source

theorem reachable_exact (problem : Problem n RowType) (source target : Fin n) :
    target ∈ reachable problem source ↔ Reaches problem source target := by
  apply FiniteWorklist.reachable_exact (successors problem) n (List.finRange n)
  · intro vertex
    simp
  · simp

/-- The contribution list is computed from the original lower bounds and
actual reachability. A cycle with no incoming lower bound contributes nothing. -/
def lowerTypes (problem : Problem n RowType) (target : Fin n) : List (Ty RowType) :=
  (seeds problem).filterMap fun entry =>
    if target ∈ reachable problem entry.2 then some entry.1 else none

theorem mem_lowerTypes (problem : Problem n RowType) (target : Fin n)
    (type : Ty RowType) :
    type ∈ lowerTypes problem target ↔
      ∃ source, .lower type source ∈ problem ∧ Reaches problem source target := by
  simp only [lowerTypes, List.mem_filterMap]
  constructor
  · rintro ⟨⟨actual, source⟩, member, found⟩
    split at found
    · rename_i path
      have equal : actual = type := Option.some.inj found
      subst actual
      exact ⟨source, (mem_seeds problem type source).mp member,
        (reachable_exact problem source target).mp path⟩
    · cases found
  · rintro ⟨source, member, path⟩
    refine ⟨(type, source), (mem_seeds problem type source).mpr member, ?_⟩
    simp only [(reachable_exact problem source target).mpr path, ↓reduceIte]

/-- The empty join is the existing bottom type, not an invented default type. -/
def joinTypes : List (Ty RowType) → Ty RowType
  | [] => .bottom
  | type :: rest => .union type (joinTypes rest)

theorem joinTypes_le_iff (leRow : RowType → RowType → Prop)
    (types : List (Ty RowType)) (upper : Ty RowType) :
    Subtype leRow (joinTypes types) upper ↔
      ∀ type ∈ types, Subtype leRow type upper := by
  induction types with
  | nil =>
      constructor
      · intro _ _ member
        cases member
      · intro _
        exact .bottom upper
  | cons type rest ih =>
      simp only [joinTypes, union_is_join, ih, List.mem_cons, forall_eq_or_imp]

theorem le_joinTypes (leRow : RowType → RowType → Prop)
    (types : List (Ty RowType)) (type : Ty RowType) (member : type ∈ types) :
    Subtype leRow type (joinTypes types) :=
  (joinTypes_le_iff leRow types (joinTypes types)).mp (.refl _) type member

theorem joinTypes_mono (leRow : RowType → RowType → Prop)
    (left right : List (Ty RowType)) (included : ∀ type ∈ left, type ∈ right) :
    Subtype leRow (joinTypes left) (joinTypes right) :=
  (joinTypes_le_iff leRow left (joinTypes right)).mpr
    (fun type member => le_joinTypes leRow right type (included type member))

/-- This computes a value type at every unknown; no solution is supplied. -/
def least (problem : Problem n RowType) : Valuation n RowType :=
  fun target => joinTypes (lowerTypes problem target)

theorem least_lower (leRow : RowType → RowType → Prop)
    (problem : Problem n RowType) (type : Ty RowType) (target : Fin n)
    (member : .lower type target ∈ problem) : Subtype leRow type (least problem target) := by
  apply le_joinTypes leRow
  exact (mem_lowerTypes problem target type).mpr ⟨target, member, .nil target⟩

theorem least_flow (leRow : RowType → RowType → Prop)
    (problem : Problem n RowType) (source target : Fin n)
    (member : .flow source target ∈ problem) :
    Subtype leRow (least problem source) (least problem target) := by
  apply joinTypes_mono leRow
  intro type contributes
  obtain ⟨start, seed, path⟩ := (mem_lowerTypes problem source type).mp contributes
  apply (mem_lowerTypes problem target type).mpr
  exact ⟨start, seed, path.append (.cons ((mem_successors problem source target).mpr member)
    (.nil target))⟩

theorem least_lowerModels (leRow : RowType → RowType → Prop)
    (problem : Problem n RowType) : LowerModels leRow problem (least problem) := by
  intro constraint member
  cases constraint with
  | lower type target => exact least_lower leRow problem type target member
  | flow source target => exact least_flow leRow problem source target member
  | upper | check => trivial

theorem reaches_subtype {leRow : RowType → RowType → Prop}
    {problem : Problem n RowType} {value : Valuation n RowType}
    (model : LowerModels leRow problem value) {source target : Fin n}
    (path : Reaches problem source target) :
    Subtype leRow (value source) (value target) := by
  induction path with
  | nil => exact .refl _
  | @cons source middle target edge rest ih =>
      exact .trans (model (.flow source middle)
        ((mem_successors problem source middle).mp edge)) ih

/-- Leastness ranges over all structural-type assignments, with no finite
alphabet, depth restriction, or candidate enumeration assumption. -/
theorem least_below {leRow : RowType → RowType → Prop}
    {problem : Problem n RowType} {value : Valuation n RowType}
    (model : LowerModels leRow problem value) (target : Fin n) :
    Subtype leRow (least problem target) (value target) := by
  apply (joinTypes_le_iff leRow _ _).mpr
  intro type contributes
  obtain ⟨source, seed, path⟩ := (mem_lowerTypes problem target type).mp contributes
  exact .trans (model (.lower type source) seed) (reaches_subtype model path)

/-- If the original problem has any model, the constructed least assignment
also passes every upper and ground constraint. -/
theorem least_models_of_models {leRow : RowType → RowType → Prop}
    {problem : Problem n RowType} {value : Valuation n RowType}
    (model : Models leRow problem value) : Models leRow problem (least problem) := by
  intro constraint member
  cases constraint with
  | lower type target => exact least_lower leRow problem type target member
  | flow source target => exact least_flow leRow problem source target member
  | upper source type => exact .trans (least_below model.lower source) (model _ member)
  | check source target => exact model _ member

theorem least_models_iff (leRow : RowType → RowType → Prop)
    (problem : Problem n RowType) :
    Models leRow problem (least problem) ↔ ∃ value, Models leRow problem value :=
  ⟨fun model => ⟨least problem, model⟩,
    fun ⟨_, model⟩ => least_models_of_models model⟩

def Constraint.accepts (typeCheck : Ty RowType → Ty RowType → Bool)
    (value : Valuation n RowType) : Constraint n RowType → Bool
  | .lower type target => typeCheck type (value target)
  | .flow source target => typeCheck (value source) (value target)
  | .upper source type => typeCheck (value source) type
  | .check source target => typeCheck source target

def accepts (typeCheck : Ty RowType → Ty RowType → Bool)
    (problem : Problem n RowType) (value : Valuation n RowType) : Bool :=
  problem.all (fun constraint => constraint.accepts typeCheck value)

theorem accepts_exact (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType) (value : Valuation n RowType) :
    accepts typeCheck problem value = true ↔ Models leRow problem value := by
  simp only [accepts, List.all_eq_true, Models]
  apply forall_congr'
  intro constraint
  apply imp_congr_right
  intro _
  cases constraint <;> exact typeExact _ _

/-- The only decision procedure supplied here compares already constructed
ground types. It does not choose or search any unknown-type assignment. -/
def solve (typeCheck : Ty RowType → Ty RowType → Bool)
    (problem : Problem n RowType) : Option (Valuation n RowType) :=
  let value := least problem
  if accepts typeCheck problem value then some value else none

theorem solve_some_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType) (value : Valuation n RowType) :
    solve typeCheck problem = some value ↔
      value = least problem ∧ Models leRow problem value := by
  simp only [solve]
  split
  · rename_i accepted
    have model := (accepts_exact typeCheck typeExact problem (least problem)).mp accepted
    constructor
    · intro equal
      have same : least problem = value := Option.some.inj equal
      exact ⟨same.symm, same ▸ model⟩
    · rintro ⟨rfl, _⟩
      rfl
  · rename_i rejected
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨rfl, model⟩
      exact False.elim (rejected ((accepts_exact typeCheck typeExact problem _).mpr model))

theorem solve_sound (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    {problem : Problem n RowType} {value : Valuation n RowType}
    (solved : solve typeCheck problem = some value) : Models leRow problem value :=
  ((solve_some_iff typeCheck typeExact problem value).mp solved).2

theorem solve_least (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    {problem : Problem n RowType} {value : Valuation n RowType}
    (solved : solve typeCheck problem = some value)
    {other : Valuation n RowType} (model : Models leRow problem other) (target : Fin n) :
    Subtype leRow (value target) (other target) := by
  rw [((solve_some_iff typeCheck typeExact problem value).mp solved).1]
  exact least_below model.lower target

/-- Failure is exact over unrestricted structural assignments, including
problems containing mutually recursive variable-flow edges. -/
theorem solve_none_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType) :
    solve typeCheck problem = none ↔ ¬ ∃ value, Models leRow problem value := by
  constructor
  · intro failed ⟨value, model⟩
    have solved := (solve_some_iff typeCheck typeExact problem (least problem)).mpr
      ⟨rfl, least_models_of_models model⟩
    rw [failed] at solved
    cases solved
  · intro impossible
    simp only [solve]
    split
    · rename_i accepted
      exact False.elim (impossible ⟨least problem,
        (accepts_exact typeCheck typeExact problem _).mp accepted⟩)
    · rfl

theorem solve_exists_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType) :
    (∃ value, solve typeCheck problem = some value) ↔ ∃ value, Models leRow problem value := by
  constructor
  · rintro ⟨value, solved⟩
    exact ⟨value, solve_sound typeCheck typeExact solved⟩
  · rintro ⟨value, model⟩
    exact ⟨least problem, (solve_some_iff typeCheck typeExact problem _).mpr
      ⟨rfl, least_models_of_models model⟩⟩

/-- A solved problem can be used with a larger observed result type exactly
when the original bounds admit an assignment below that observed type. -/
theorem observed_exact (leRow : RowType → RowType → Prop)
    (problem : Problem n RowType) (target : Fin n) (observed : Ty RowType) :
    (Models leRow problem (least problem) ∧ Subtype leRow (least problem target) observed) ↔
      ∃ value, Models leRow problem value ∧ Subtype leRow (value target) observed := by
  constructor
  · intro result
    exact ⟨least problem, result⟩
  · rintro ⟨value, model, below⟩
    exact ⟨least_models_of_models model, .trans (least_below model.lower target) below⟩


/-! ## Changing the representation of ground bounds -/

variable {OtherRow : Type v}

/-- Mapping a ground type does not add or remove any unknown-flow edge. -/
def Constraint.mapTypes (f : Ty RowType → Ty OtherRow) :
    Constraint n RowType → Constraint n OtherRow
  | .lower type target => .lower (f type) target
  | .flow source target => .flow source target
  | .upper source type => .upper source (f type)
  | .check source target => .check (f source) (f target)

def mapTypes (f : Ty RowType → Ty OtherRow) (problem : Problem n RowType) :
    Problem n OtherRow := problem.map (Constraint.mapTypes f)

theorem seeds_mapTypes (f : Ty RowType → Ty OtherRow) (problem : Problem n RowType) :
    seeds (mapTypes f problem) = (seeds problem).map (fun entry => (f entry.1, entry.2)) := by
  induction problem with
  | nil => rfl
  | cons constraint rest ih =>
      cases constraint <;> simp_all [mapTypes, Constraint.mapTypes, seeds]

theorem successors_mapTypes (f : Ty RowType → Ty OtherRow)
    (problem : Problem n RowType) (source : Fin n) :
    successors (mapTypes f problem) source = successors problem source := by
  unfold successors mapTypes
  rw [List.filterMap_map]
  congr 1
  funext constraint
  cases constraint <;> rfl

theorem reachable_mapTypes (f : Ty RowType → Ty OtherRow)
    (problem : Problem n RowType) (source : Fin n) :
    reachable (mapTypes f problem) source = reachable problem source := by
  unfold reachable
  have same : successors (mapTypes f problem) = successors problem :=
    funext (successors_mapTypes f problem)
  rw [same]

theorem lowerTypes_mapTypes (f : Ty RowType → Ty OtherRow)
    (problem : Problem n RowType) (target : Fin n) :
    lowerTypes (mapTypes f problem) target = (lowerTypes problem target).map f := by
  simp only [lowerTypes, seeds_mapTypes, List.filterMap_map, List.map_filterMap]
  congr 1
  funext entry
  simp only [Function.comp_apply, reachable_mapTypes]
  split <;> rfl

theorem joinTypes_mapTypes (f : Ty RowType → Ty OtherRow)
    (bottom : f .bottom = .bottom)
    (union : ∀ left right, f (.union left right) = .union (f left) (f right))
    (types : List (Ty RowType)) : joinTypes (types.map f) = f (joinTypes types) := by
  induction types with
  | nil => exact bottom.symm
  | cons type rest ih => simp only [List.map_cons, joinTypes, union, ih]

/-- Solving the forward part commutes with any bottom/union-preserving map.
No injectivity or semantic subtyping assumption is needed for this equality. -/
theorem least_mapTypes (f : Ty RowType → Ty OtherRow)
    (bottom : f .bottom = .bottom)
    (union : ∀ left right, f (.union left right) = .union (f left) (f right))
    (problem : Problem n RowType) (target : Fin n) :
    f (least problem target) = least (mapTypes f problem) target := by
  simp only [least, lowerTypes_mapTypes, joinTypes_mapTypes f bottom union]

theorem models_mapTypes_iff (f : Ty RowType → Ty OtherRow)
    (leRow : RowType → RowType → Prop) (leOther : OtherRow → OtherRow → Prop)
    (exact : ∀ left right, Subtype leOther (f left) (f right) ↔ Subtype leRow left right)
    (problem : Problem n RowType) (value : Valuation n RowType) :
    Models leOther (mapTypes f problem) (f ∘ value) ↔ Models leRow problem value := by
  have constraintExact (constraint : Constraint n RowType) :
      (constraint.mapTypes f).Holds leOther (f ∘ value) ↔ constraint.Holds leRow value := by
    cases constraint <;> exact exact _ _
  constructor
  · intro model constraint member
    exact (constraintExact constraint).mp
      (model (constraint.mapTypes f) (List.mem_map.mpr ⟨constraint, member, rfl⟩))
  · intro model mapped member
    change mapped ∈ problem.map (Constraint.mapTypes f) at member
    obtain ⟨constraint, originalMember, rfl⟩ := List.mem_map.mp member
    exact (constraintExact constraint).mpr (model constraint originalMember)

/-- In particular, decoding a row representation commutes with constructing
unknown value types, including both rows nested in arrows. -/
def Constraint.mapRows (f : RowType → OtherRow) : Constraint n RowType → Constraint n OtherRow :=
  Constraint.mapTypes (StructuralRowResolution.mapRows f)

def mapRows (f : RowType → OtherRow) (problem : Problem n RowType) : Problem n OtherRow :=
  problem.map (Constraint.mapRows f)

theorem least_mapRows (f : RowType → OtherRow) (problem : Problem n RowType)
    (target : Fin n) :
    StructuralRowResolution.mapRows f (least problem target) = least (mapRows f problem) target :=
  least_mapTypes (StructuralRowResolution.mapRows f) (by simp only [StructuralRowResolution.mapRows])
    (fun _ _ => by simp only [StructuralRowResolution.mapRows]) problem target

end Yulang.ValueBounds
