import Yulang.CastGraph

/-!
# Executable witnesses for finite cast reachability

Routes retain every edge, permitting a compiler to sequence declaration bodies
without extracting computational data from a proof in `Prop`. Search removes
a vertex from the remaining finite list at each step. There is no caller
supplied fuel and no acyclicity premise.
-/

namespace Yulang.CommonCastRoutes

open FiniteReachability

variable {n : Nat}

inductive Edges (adj : Adj n) : Fin n → List (Fin n) → Fin n → Prop where
  | nil : Edges adj source [] source
  | cons : next ∈ adj source → Edges adj next tail target →
      Edges adj source (next :: tail) target

structure Route (adj : Adj n) (source target : Fin n) where
  steps : List (Fin n)
  valid : Edges adj source steps target

def Route.identity (adj : Adj n) (source : Fin n) : Route adj source source :=
  ⟨[], .nil⟩

theorem Edges.append {adj : Adj n} {source middle target : Fin n}
    {first last : List (Fin n)} (before : Edges adj source first middle)
    (after : Edges adj middle last target) : Edges adj source (first ++ last) target := by
  induction before with
  | nil => exact after
  | cons edge _ ih => exact .cons edge (ih after)

def Route.extend {adj : Adj n} {source middle target : Fin n}
    (route : Route adj source middle) (edge : target ∈ adj middle) : Route adj source target :=
  ⟨route.steps ++ [target], route.valid.append (.cons edge .nil)⟩

theorem Edges.reachable {adj : Adj n} {source target : Fin n} {steps : List (Fin n)}
    (edges : Edges adj source steps target) : Reach adj [source] target := by
  induction edges with
  | nil => exact .seed (by simp)
  | cons edge _ ih => exact Reach.append (.step (.seed (by simp)) edge) ih

abbrev Table (adj : Adj n) (source : Fin n) :=
  (target : Fin n) → Option (Route adj source target)

structure Candidate (adj : Adj n) (source : Fin n) (remaining : List (Fin n)) where
  vertex : Fin n
  route : Route adj source vertex
  present : vertex ∈ remaining

def candidates (adj : Adj n) (source : Fin n) (remaining : List (Fin n))
    (table : Table adj source) : List (Candidate adj source remaining) :=
  (List.finRange n).flatMap fun origin =>
    match table origin with
    | none => []
    | some route => (adj origin).attach.filterMap fun next =>
        if h : next.val ∈ remaining then
          some ⟨next.val, route.extend next.property, h⟩
        else none

def install {adj : Adj n} {source : Fin n} (table : Table adj source)
    (vertex : Fin n) (route : Route adj source vertex) : Table adj source :=
  fun target => if same : target = vertex then some (same ▸ route) else table target

@[simp] theorem install_same {adj : Adj n} {source : Fin n}
    (table : Table adj source) (vertex : Fin n) (route : Route adj source vertex) :
    (install table vertex route vertex).isSome = true := by simp [install]

theorem install_preserves {adj : Adj n} {source : Fin n}
    (table : Table adj source) (vertex : Fin n) (route : Route adj source vertex)
    (target : Fin n) (present : (table target).isSome = true) :
    (install table vertex route target).isSome = true := by
  by_cases same : target = vertex <;> simp [install, same, present]

def grow (adj : Adj n) (source : Fin n) (remaining : List (Fin n))
    (table : Table adj source) : Table adj source :=
  match (candidates adj source remaining table).head? with
  | none => table
  | some next => grow adj source (remaining.erase next.vertex)
      (install table next.vertex next.route)
termination_by remaining.length
decreasing_by
  rw [List.length_erase_of_mem next.present]
  have positive : 0 < remaining.length := List.length_pos_iff.mpr (by
    intro empty
    simpa [empty] using next.present)
  omega

theorem candidates_nonempty (adj : Adj n) (source : Fin n)
    (remaining : List (Fin n)) (table : Table adj source)
    {origin target : Fin n} (known : (table origin).isSome = true)
    (edge : target ∈ adj origin) (pending : target ∈ remaining) :
    candidates adj source remaining table ≠ [] := by
  obtain ⟨route, found⟩ := Option.isSome_iff_exists.mp known
  have member : (⟨target, route.extend edge, pending⟩ : Candidate adj source remaining) ∈
      candidates adj source remaining table := by
    apply List.mem_flatMap.mpr
    refine ⟨origin, List.mem_finRange _, ?_⟩
    simp only [found]
    apply List.mem_filterMap.mpr
    refine ⟨⟨target, edge⟩, by simp, ?_⟩
    simp [pending]
  intro empty
  simp [empty] at member

theorem grow_preserves (adj : Adj n) (source : Fin n)
    (remaining : List (Fin n)) (table : Table adj source)
    (target : Fin n) (known : (table target).isSome = true) :
    (grow adj source remaining table target).isSome = true := by
  cases found : (candidates adj source remaining table).head? with
  | none => simpa only [grow, found] using known
  | some next =>
      rw [grow, found]
      exact grow_preserves adj source _ _ target
        (install_preserves table _ _ target known)
termination_by remaining.length
decreasing_by
  rw [List.length_erase_of_mem next.present]
  have positive : 0 < remaining.length := List.length_pos_iff.mpr (by
    intro empty
    simpa [empty] using next.present)
  omega

theorem grow_complete (adj : Adj n) (source : Fin n)
    (remaining : List (Fin n)) (table : Table adj source)
    (seeded : (table source).isSome = true)
    (covers : ∀ target, (table target).isSome = false → target ∈ remaining)
    (target : Fin n) (reachable : Reach adj [source] target) :
    (grow adj source remaining table target).isSome = true := by
  cases exhausted : (candidates adj source remaining table).head? with
  | none =>
    rw [grow, exhausted]
    have empty := List.head?_eq_none_iff.mp exhausted
    induction reachable with
    | seed member =>
        have equal := List.mem_singleton.mp member
        subst equal
        exact seeded
    | @step origin target _ edge ih =>
        cases found : (table target).isSome with
        | true => rfl
        | false =>
            exact False.elim (candidates_nonempty adj source remaining table ih edge
              (covers target found) empty)
  | some next =>
    rw [grow, exhausted]
    apply grow_complete adj source _ _
      (install_preserves table _ _ source seeded) ?_ target reachable
    intro missing absent
    have different : missing ≠ next.vertex := by
      intro same
      subst missing
      simp at absent
    apply (List.mem_erase_of_ne different).mpr
    apply covers
    simpa [install, different] using absent
termination_by remaining.length
decreasing_by
  rw [List.length_erase_of_mem next.present]
  have positive : 0 < remaining.length := List.length_pos_iff.mpr (by
    intro empty
    simpa [empty] using next.present)
  omega

def search (adj : Adj n) (source target : Fin n) : Option (Route adj source target) :=
  grow adj source (List.finRange n)
    (install (fun _ => none) source (Route.identity adj source)) target

/-- Every finite graph, every pair of vertices, including cyclic graphs.
The returned object contains executable data rather than a path proposition. -/
theorem search_exact (adj : Adj n) (source target : Fin n) :
    (search adj source target).isSome = true ↔ Reach adj [source] target := by
  constructor
  · intro found
    obtain ⟨route, _⟩ := Option.isSome_iff_exists.mp found
    exact route.valid.reachable
  · intro reached
    apply grow_complete adj source (List.finRange n) _ (by simp) _ target reached
    intro missing _
    exact List.mem_finRange missing

theorem search_eq_none_iff (adj : Adj n) (source target : Fin n) :
    search adj source target = none ↔ ¬ Reach adj [source] target := by
  have exactness := search_exact adj source target
  cases found : search adj source target <;> simp_all

theorem search_agrees_with_closure (adj : Adj n) (source target : Fin n) :
    (search adj source target).isSome = closure adj [source] target := by
  have same := (search_exact adj source target).trans (closure_exact adj [source] target).symm
  cases first : (search adj source target).isSome <;>
    cases last : closure adj [source] target <;> simp_all

end Yulang.CommonCastRoutes
