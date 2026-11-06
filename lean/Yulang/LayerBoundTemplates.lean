import Yulang.RegularValueTypes
import Yulang.ValueBoundSchemes

/-!
# Value-bound templates over guarded recursive layers

A template separates its finite variable-flow topology from its bounds.
Evaluating those bounds changes neither reachability nor the collection of
lower and upper contributions. A guarded layer can therefore construct the
same shared-parameter expansion that `ValueBoundSchemes` constructs after
each finite observation.

The main equality `expandLayer_eval` is syntactic: evaluation commutes with
the generated unions and intersections. It requires no distributivity of
constructors and no satisfiability or solution hypothesis.
-/

namespace Yulang.LayerBoundTemplates

open StructuralBase RegularValueTypes

universe u v w

inductive Constraint (n : Nat) (Bound : Type u) where
  | lower (bound : Bound) (target : Fin n)
  | flow (source target : Fin n)
  | upper (source : Fin n) (bound : Bound)
  | check (source target : Bound)

abbrev Problem (n : Nat) (Bound : Type u) := List (Constraint n Bound)

variable {n : Nat} {Bound : Type u} {Row : Type v}

def Constraint.instantiateWith (evaluate : Bound → Ty Row) :
    Constraint n Bound → ValueBounds.Constraint n Row
  | .lower bound target => .lower (evaluate bound) target
  | .flow source target => .flow source target
  | .upper source bound => .upper source (evaluate bound)
  | .check source target => .check (evaluate source) (evaluate target)

def instantiateWith (evaluate : Bound → Ty Row) (template : Problem n Bound) : ValueBounds.Problem n Row :=
  template.map (Constraint.instantiateWith evaluate)

def Constraint.map {OtherBound : Type w} (f : Bound → OtherBound) :
    Constraint n Bound → Constraint n OtherBound
  | .lower bound target => .lower (f bound) target
  | .flow source target => .flow source target
  | .upper source bound => .upper source (f bound)
  | .check source target => .check (f source) (f target)

def mapBounds {OtherBound : Type w} (f : Bound → OtherBound) (template : Problem n Bound) :
    Problem n OtherBound := template.map (Constraint.map f)

theorem instantiateWith_mapBounds {OtherBound : Type w} (evaluate : OtherBound → Ty Row)
    (rename : Bound → OtherBound) (template : Problem n Bound) :
    instantiateWith evaluate (mapBounds rename template) = instantiateWith (evaluate ∘ rename) template := by
  simp only [instantiateWith, mapBounds, List.map_map]
  congr 1
  funext constraint
  cases constraint <;> rfl

@[simp] theorem mem_instantiateWith_lower (evaluate : Bound → Ty Row)
    (template : Problem n Bound) (type : Ty Row) (target : Fin n) :
    .lower type target ∈ instantiateWith evaluate template ↔
      ∃ bound, .lower bound target ∈ template ∧ evaluate bound = type := by
  constructor
  · intro member
    obtain ⟨constraint, originalMember, found⟩ := List.mem_map.mp member
    cases constraint with
    | lower bound index =>
        obtain ⟨same, rfl⟩ := ValueBounds.Constraint.lower.inj found
        exact ⟨bound, originalMember, same⟩
    | _ => cases found
  · rintro ⟨bound, member, rfl⟩
    exact List.mem_map.mpr ⟨.lower bound target, member, rfl⟩

@[simp] theorem mem_instantiateWith_flow (evaluate : Bound → Ty Row)
    (template : Problem n Bound) (source target : Fin n) :
    .flow source target ∈ instantiateWith evaluate template ↔ .flow source target ∈ template := by
  constructor
  · intro member
    obtain ⟨constraint, originalMember, found⟩ := List.mem_map.mp member
    cases constraint with
    | flow start finish =>
        obtain ⟨rfl, rfl⟩ := ValueBounds.Constraint.flow.inj found
        exact originalMember
    | _ => cases found
  · intro member
    exact List.mem_map.mpr ⟨.flow source target, member, rfl⟩

@[simp] theorem mem_instantiateWith_upper (evaluate : Bound → Ty Row)
    (template : Problem n Bound) (source : Fin n) (type : Ty Row) :
    .upper source type ∈ instantiateWith evaluate template ↔
      ∃ bound, .upper source bound ∈ template ∧ evaluate bound = type := by
  constructor
  · intro member
    obtain ⟨constraint, originalMember, found⟩ := List.mem_map.mp member
    cases constraint with
    | upper index bound =>
        obtain ⟨rfl, same⟩ := ValueBounds.Constraint.upper.inj found
        exact ⟨bound, originalMember, same⟩
    | _ => cases found
  · rintro ⟨bound, member, rfl⟩
    exact List.mem_map.mpr ⟨.upper source bound, member, rfl⟩

@[simp] theorem mem_instantiateWith_check (evaluate : Bound → Ty Row)
    (template : Problem n Bound) (source target : Ty Row) :
    .check source target ∈ instantiateWith evaluate template ↔
      ∃ left right, .check left right ∈ template ∧ evaluate left = source ∧ evaluate right = target := by
  constructor
  · intro member
    obtain ⟨constraint, originalMember, found⟩ := List.mem_map.mp member
    cases constraint with
    | check left right =>
        obtain ⟨sameLeft, sameRight⟩ := ValueBounds.Constraint.check.inj found
        exact ⟨left, right, originalMember, sameLeft, sameRight⟩
    | _ => cases found
  · rintro ⟨left, right, member, rfl, rfl⟩
    exact List.mem_map.mpr ⟨.check left right, member, rfl⟩

def successors (template : Problem n Bound) (source : Fin n) : List (Fin n) :=
  template.filterMap fun
    | .flow start target => if start = source then some target else none
    | _ => none

abbrev Reaches (template : Problem n Bound) (source target : Fin n) : Prop :=
  FiniteWorklist.Path (successors template) source target

def reachable (template : Problem n Bound) (source : Fin n) : List (Fin n) :=
  FiniteWorklist.reachable (successors template) n source

def lowerSeeds (template : Problem n Bound) : List (Bound × Fin n) :=
  template.filterMap fun
    | .lower bound target => some (bound, target)
    | _ => none

def upperSeeds (template : Problem n Bound) : List (Fin n × Bound) :=
  template.filterMap fun
    | .upper source bound => some (source, bound)
    | _ => none

def lowerBounds (template : Problem n Bound) (target : Fin n) : List Bound :=
  (lowerSeeds template).filterMap fun entry =>
    if target ∈ reachable template entry.2 then some entry.1 else none

def upperBounds (template : Problem n Bound) (source : Fin n) : List Bound :=
  (upperSeeds template).filterMap fun entry =>
    if entry.1 ∈ reachable template source then some entry.2 else none

def ancestors (template : Problem n Bound) (target : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun source => target ∈ reachable template source

theorem reachable_exact (template : Problem n Bound) (source target : Fin n) :
    target ∈ reachable template source ↔ Reaches template source target := by
  apply FiniteWorklist.reachable_exact (successors template) n (List.finRange n)
  · intro vertex
    simp
  · simp

theorem mem_ancestors (template : Problem n Bound) (source target : Fin n) :
    source ∈ ancestors template target ↔ Reaches template source target := by
  simp only [ancestors, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq, reachable_exact]

/-- Grounding the bounds preserves the exact flow graph, not just reachability. -/
theorem successors_instantiateWith (evaluate : Bound → Ty Row)
    (template : Problem n Bound) (source : Fin n) :
    ValueBounds.successors (instantiateWith evaluate template) source = successors template source := by
  unfold ValueBounds.successors instantiateWith successors
  rw [List.filterMap_map]
  congr 1
  funext constraint
  cases constraint <;> rfl

theorem reachable_instantiateWith (evaluate : Bound → Ty Row)
    (template : Problem n Bound) (source : Fin n) :
    ValueBounds.reachable (instantiateWith evaluate template) source = reachable template source := by
  unfold ValueBounds.reachable reachable
  have same : ValueBounds.successors (instantiateWith evaluate template) = successors template :=
    funext (successors_instantiateWith evaluate template)
  rw [same]

theorem reaches_instantiateWith (evaluate : Bound → Ty Row)
    (template : Problem n Bound) (source target : Fin n) :
    ValueBounds.Reaches (instantiateWith evaluate template) source target ↔ Reaches template source target := by
  rw [← ValueBounds.reachable_exact, reachable_instantiateWith, reachable_exact]

theorem lowerSeeds_instantiateWith (evaluate : Bound → Ty Row) (template : Problem n Bound) :
    ValueBounds.seeds (instantiateWith evaluate template) =
      (lowerSeeds template).map (fun entry => (evaluate entry.1, entry.2)) := by
  induction template with
  | nil => rfl
  | cons constraint rest ih =>
      cases constraint <;> simp_all [instantiateWith, Constraint.instantiateWith, ValueBounds.seeds, lowerSeeds]

theorem upperSeeds_instantiateWith (evaluate : Bound → Ty Row) (template : Problem n Bound) :
    ValueUpperBounds.upperSeeds (instantiateWith evaluate template) =
      (upperSeeds template).map (fun entry => (entry.1, evaluate entry.2)) := by
  induction template with
  | nil => rfl
  | cons constraint rest ih =>
      cases constraint <;> simp_all [instantiateWith, Constraint.instantiateWith, ValueUpperBounds.upperSeeds, upperSeeds]

theorem lowerBounds_instantiateWith (evaluate : Bound → Ty Row)
    (template : Problem n Bound) (target : Fin n) :
    ValueBounds.lowerTypes (instantiateWith evaluate template) target =
      (lowerBounds template target).map evaluate := by
  simp only [ValueBounds.lowerTypes, lowerBounds, lowerSeeds_instantiateWith,
    List.filterMap_map, List.map_filterMap]
  congr 1
  funext entry
  simp only [Function.comp_apply, reachable_instantiateWith]
  split <;> rfl

theorem upperBounds_instantiateWith (evaluate : Bound → Ty Row)
    (template : Problem n Bound) (source : Fin n) :
    ValueUpperBounds.upperTypes (instantiateWith evaluate template) source =
      (upperBounds template source).map evaluate := by
  simp only [ValueUpperBounds.upperTypes, upperBounds, upperSeeds_instantiateWith,
    List.filterMap_map, List.map_filterMap]
  congr 1
  funext entry
  simp only [Function.comp_apply, reachable_instantiateWith]
  split <;> rfl

theorem ancestors_instantiateWith (evaluate : Bound → Ty Row)
    (template : Problem n Bound) (target : Fin n) :
    ValueBoundSchemes.ancestors (instantiateWith evaluate template) target = ancestors template target := by
  simp only [ValueBoundSchemes.ancestors, ancestors, reachable_instantiateWith]

/-! ## Guarded layer construction and evaluation -/

variable {State : Type w}

def instantiateProblem (assignment : State → Ty Row) (template : Problem n (Layer Row State)) :
    ValueBounds.Problem n Row := instantiateWith (Layer.eval assignment) template

@[simp] theorem mem_instantiateProblem_lower (assignment : State → Ty Row)
    (template : Problem n (Layer Row State)) (type : Ty Row) (target : Fin n) :
    .lower type target ∈ instantiateProblem assignment template ↔
      ∃ bound, .lower bound target ∈ template ∧ bound.eval assignment = type :=
  mem_instantiateWith_lower _ _ _ _

@[simp] theorem mem_instantiateProblem_flow (assignment : State → Ty Row)
    (template : Problem n (Layer Row State)) (source target : Fin n) :
    .flow source target ∈ instantiateProblem assignment template ↔ .flow source target ∈ template :=
  mem_instantiateWith_flow _ _ _ _

@[simp] theorem mem_instantiateProblem_upper (assignment : State → Ty Row)
    (template : Problem n (Layer Row State)) (source : Fin n) (type : Ty Row) :
    .upper source type ∈ instantiateProblem assignment template ↔
      ∃ bound, .upper source bound ∈ template ∧ bound.eval assignment = type :=
  mem_instantiateWith_upper _ _ _ _

@[simp] theorem mem_instantiateProblem_check (assignment : State → Ty Row)
    (template : Problem n (Layer Row State)) (source target : Ty Row) :
    .check source target ∈ instantiateProblem assignment template ↔
      ∃ left right, .check left right ∈ template ∧ left.eval assignment = source ∧ right.eval assignment = target :=
  mem_instantiateWith_check _ _ _ _

theorem reachable_instantiateProblem (assignment : State → Ty Row)
    (template : Problem n (Layer Row State)) (source : Fin n) :
    ValueBounds.reachable (instantiateProblem assignment template) source = reachable template source :=
  reachable_instantiateWith _ _ _

theorem reaches_instantiateProblem (assignment : State → Ty Row)
    (template : Problem n (Layer Row State)) (source target : Fin n) :
    ValueBounds.Reaches (instantiateProblem assignment template) source target ↔ Reaches template source target :=
  reaches_instantiateWith _ _ _ _

theorem ancestors_instantiateProblem (assignment : State → Ty Row)
    (template : Problem n (Layer Row State)) (target : Fin n) :
    ValueBoundSchemes.ancestors (instantiateProblem assignment template) target = ancestors template target :=
  ancestors_instantiateWith _ _ _

def joinLayers : List (Layer Row State) → Layer Row State
  | [] => .bottom
  | type :: rest => .union type (joinLayers rest)

def meetLayers : List (Layer Row State) → Layer Row State
  | [] => .top
  | type :: rest => .inter type (meetLayers rest)

def lowerLayer (template : Problem n (Layer Row State)) (target : Fin n) : Layer Row State :=
  joinLayers (lowerBounds template target)

def upperLayer (template : Problem n (Layer Row State)) (source : Fin n) : Layer Row State :=
  meetLayers (upperBounds template source)

/-- Finite syntax with shared parameter layers. References inside each bound
remain guarded, because the outer construction adds only finite lattice nodes. -/
def expandLayer (template : Problem n (Layer Row State))
    (parameter : Fin n → Layer Row State) (target : Fin n) : Layer Row State :=
  .union (lowerLayer template target)
    (joinLayers ((ancestors template target).map fun source =>
      .inter (parameter source) (upperLayer template source)))

theorem joinLayers_eval (assignment : State → Ty Row) (types : List (Layer Row State)) :
    (joinLayers types).eval assignment = ValueBounds.joinTypes (types.map (Layer.eval assignment)) := by
  induction types with
  | nil => rfl
  | cons type rest ih => simp only [joinLayers, Layer.eval, List.map, ValueBounds.joinTypes, ih]

theorem meetLayers_eval (assignment : State → Ty Row) (types : List (Layer Row State)) :
    (meetLayers types).eval assignment = ValueUpperBounds.meetTypes (types.map (Layer.eval assignment)) := by
  induction types with
  | nil => rfl
  | cons type rest ih => simp only [meetLayers, Layer.eval, List.map, ValueUpperBounds.meetTypes, ih]

theorem lowerLayer_eval (assignment : State → Ty Row)
    (template : Problem n (Layer Row State)) (target : Fin n) :
    (lowerLayer template target).eval assignment = ValueBounds.least (instantiateProblem assignment template) target := by
  simp only [lowerLayer, joinLayers_eval, ValueBounds.least, instantiateProblem, lowerBounds_instantiateWith]

theorem upperLayer_eval (assignment : State → Ty Row)
    (template : Problem n (Layer Row State)) (source : Fin n) :
    (upperLayer template source).eval assignment = ValueUpperBounds.greatest (instantiateProblem assignment template) source := by
  simp only [upperLayer, meetLayers_eval, ValueUpperBounds.greatest, instantiateProblem, upperBounds_instantiateWith]

/-- Constructing the recursive layer and then observing it is exactly the
existing flat shared-parameter expansion of the observed bounds. -/
theorem expandLayer_eval (assignment : State → Ty Row)
    (template : Problem n (Layer Row State)) (parameter : Fin n → Layer Row State) (target : Fin n) :
    (expandLayer template parameter target).eval assignment =
      ValueBoundSchemes.expand (instantiateProblem assignment template)
        (fun index => (parameter index).eval assignment) target := by
  simp only [expandLayer, Layer.eval, lowerLayer_eval, joinLayers_eval, List.map_map,
    Function.comp_def, upperLayer_eval, ValueBoundSchemes.expand, ValueBoundSchemes.variablePart,
    instantiateProblem, ancestors_instantiateWith]

end Yulang.LayerBoundTemplates
