import Yulang.Horn

/-!
# Exact reachability on a finite dependency graph

The graph is a finite interface, with a finite adjacency list at every vertex.
`closure` is executable: it reuses the finite Horn reference solver's model
intersection. `Reach` is an independent inductive path judgement. Their exact
correspondence does not assume a path-length cutoff, acyclicity, or successful
resolution. Cycles alone cannot create a reachable fact.

This reference implementation enumerates Boolean valuations and is exponential.
It is shared by evaluation-dependency checks and finite ground cast lookup; it
does not establish that a source-level polymorphic cast graph is finite.
-/

namespace Yulang.FiniteReachability

abbrev Adj (n : Nat) := Fin n → List (Fin n)

inductive Reach (adj : Adj n) (seeds : List (Fin n)) : Fin n → Prop where
  | seed : vertex ∈ seeds → Reach adj seeds vertex
  | step : Reach adj seeds source → target ∈ adj source → Reach adj seeds target

def constraints (adj : Adj n) (seeds : List (Fin n)) : Horn.Problem n :=
  seeds.map Horn.Clause.seed ++
    (List.finRange n).flatMap (fun source => (adj source).map (Horn.Clause.include source))

def closure (adj : Adj n) (seeds : List (Fin n)) : Fin n → Bool :=
  Horn.intersection (Horn.allModels (constraints adj seeds))

@[simp] theorem models_seed (vertex : Fin n) (value : Horn.Valuation n) :
    Horn.ModelsClause (Horn.Clause.seed vertex) value ↔ value vertex = true := by
  simp [Horn.ModelsClause, Horn.Clause.seed]

@[simp] theorem models_include (source target : Fin n) (value : Horn.Valuation n) :
    Horn.ModelsClause (Horn.Clause.include source target) value ↔
      (value source = true → value target = true) := by
  simp [Horn.ModelsClause, Horn.Clause.include]

theorem models_iff (adj : Adj n) (seeds : List (Fin n)) (value : Horn.Valuation n) :
    Horn.Models (constraints adj seeds) value ↔
      (∀ vertex ∈ seeds, value vertex = true) ∧
      (∀ source target, target ∈ adj source → value source = true → value target = true) := by
  constructor
  · intro model
    constructor
    · intro vertex present
      apply (models_seed vertex value).mp
      exact model _ (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨vertex, present, rfl⟩)))
    · intro source target edge
      apply (models_include source target value).mp
      apply model
      apply List.mem_append.mpr
      apply Or.inr
      apply List.mem_flatMap.mpr
      exact ⟨source, by simp, List.mem_map.mpr ⟨target, edge, rfl⟩⟩
  · rintro ⟨seeded, closed⟩ clause member
    rcases List.mem_append.mp member with initial | edge
    · obtain ⟨vertex, present, rfl⟩ := List.mem_map.mp initial
      exact (models_seed vertex value).mpr (seeded vertex present)
    · obtain ⟨source, _, member⟩ := List.mem_flatMap.mp edge
      obtain ⟨target, adjacent, rfl⟩ := List.mem_map.mp member
      exact (models_include source target value).mpr (closed source target adjacent)

theorem allModels_nonempty (adj : Adj n) (seeds : List (Fin n)) :
    Horn.allModels (constraints adj seeds) ≠ [] := by
  have allTrue : Horn.Models (constraints adj seeds) (fun _ => true) :=
    (models_iff adj seeds _).mpr ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  have present := (Horn.mem_allModels (constraints adj seeds) (fun _ => true)).mpr allTrue
  intro empty
  simp [empty] at present

theorem closure_least (adj : Adj n) (seeds : List (Fin n)) :
    Horn.IsLeastModel (constraints adj seeds) (closure adj seeds) := by
  constructor
  · exact Horn.intersection_models _ _ (allModels_nonempty adj seeds)
      (fun value member => (Horn.mem_allModels _ value).mp member)
  · intro value model
    exact Horn.intersection_below _ value ((Horn.mem_allModels _ value).mpr model)

/-- A fact is generated exactly when a finite inductive path reaches it. -/
theorem closure_exact (adj : Adj n) (seeds : List (Fin n)) (vertex : Fin n) :
    closure adj seeds vertex = true ↔ Reach adj seeds vertex := by
  constructor
  · intro included
    classical
    let pathValue : Horn.Valuation n := fun target => decide (Reach adj seeds target)
    have pathModel : Horn.Models (constraints adj seeds) pathValue := by
      apply (models_iff adj seeds pathValue).mpr
      constructor
      · intro target member
        exact decide_eq_true (Reach.seed member)
      · intro source target edge prior
        exact decide_eq_true (Reach.step (of_decide_eq_true prior) edge)
    exact of_decide_eq_true ((closure_least adj seeds).2 pathValue pathModel vertex included)
  · intro path
    have model := (models_iff adj seeds _).mp (closure_least adj seeds).1
    induction path with
    | seed member => exact model.1 _ member
    | step _ edge ih => exact model.2 _ _ edge ih

theorem Reach.mono {adj other : Adj n} {seeds initial : List (Fin n)}
    (seedSubset : ∀ vertex, vertex ∈ seeds → vertex ∈ initial)
    (edgeSubset : ∀ source target, target ∈ adj source → target ∈ other source)
    {vertex : Fin n} (path : Reach adj seeds vertex) : Reach other initial vertex := by
  induction path with
  | seed member => exact .seed (seedSubset _ member)
  | step _ edge ih => exact .step ih (edgeSubset _ _ edge)

theorem Reach.append {adj : Adj n} {seeds : List (Fin n)} {middle target : Fin n}
    (first : Reach adj seeds middle) (second : Reach adj [middle] target) :
    Reach adj seeds target := by
  induction second with
  | seed member =>
      have same := List.mem_singleton.mp member
      subst same
      exact first
  | step _ edge ih => exact .step ih edge

theorem Reach.no_seed {adj : Adj n} {vertex : Fin n} : ¬ Reach adj [] vertex := by
  intro path
  induction path with
  | seed member => cases member
  | step _ _ ih => exact ih

@[simp] theorem closure_empty (adj : Adj n) (vertex : Fin n) :
    closure adj [] vertex = false := by
  cases found : closure adj [] vertex with
  | false => rfl
  | true => exact False.elim (Reach.no_seed ((closure_exact adj [] vertex).mp found))

/-- Adjacency order, seed order, and duplicate entries have no semantic effect. -/
theorem closure_congr {adj other : Adj n} {seeds initial : List (Fin n)}
    (seedEquiv : ∀ vertex, vertex ∈ seeds ↔ vertex ∈ initial)
    (edgeEquiv : ∀ source target, target ∈ adj source ↔ target ∈ other source) :
    closure adj seeds = closure other initial := by
  funext vertex
  have same : closure adj seeds vertex = true ↔ closure other initial vertex = true := by
    rw [closure_exact, closure_exact]
    exact ⟨Reach.mono (fun x => (seedEquiv x).mp) (fun x y => (edgeEquiv x y).mp),
      Reach.mono (fun x => (seedEquiv x).mpr) (fun x y => (edgeEquiv x y).mpr)⟩
  cases left : closure adj seeds vertex <;> cases right : closure other initial vertex <;>
    simp_all

end Yulang.FiniteReachability
