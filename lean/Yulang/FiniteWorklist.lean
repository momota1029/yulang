import Std

/-!
# Exact finite reachability by a worklist

Only successors of configurations reached from the initial configuration are
generated. A newly visited configuration consumes one unit of the finite-state
capacity; duplicate pending entries are discarded without consuming capacity.
An empty pending list stops the search immediately. The capacity is justified
by a complete finite universe in the correctness theorem, and is not a cutoff
on path length. The universe is used only in proofs, not by the executable
search. No matrix of edges or unrelated state pairs is constructed.
-/

namespace Yulang.FiniteWorklist

variable {Vertex : Type}

inductive Path (successors : Vertex → List Vertex) : Vertex → Vertex → Prop where
  | nil (vertex : Vertex) : Path successors vertex vertex
  | cons : middle ∈ successors source → Path successors middle target →
      Path successors source target

theorem Path.append {successors : Vertex → List Vertex} {first middle last : Vertex}
    (left : Path successors first middle) (right : Path successors middle last) :
    Path successors first last := by
  induction left with
  | nil => exact right
  | cons edge rest ih => exact .cons edge (ih right)

theorem closed_path (successors : Vertex → List Vertex) (seen : List Vertex)
    (closed : ∀ source ∈ seen, ∀ target ∈ successors source, target ∈ seen)
    {first last : Vertex} (path : Path successors first last) (initial : first ∈ seen) :
    last ∈ seen := by
  induction path with
  | nil => exact initial
  | cons edge rest ih => exact ih (closed _ initial _ edge)

/-- Discard pending duplicates before handing the next fresh configuration
to the continuation. This recursion is structural on the pending list. -/
def scan [DecidableEq Vertex] (successors : Vertex → List Vertex)
    (resume : List Vertex → List Vertex → List Vertex) (seen : List Vertex) :
    List Vertex → List Vertex
  | [] => seen
  | current :: rest =>
      if current ∈ seen then scan successors resume seen rest
      else resume (current :: seen) (successors current ++ rest)

/-- Each recursive call consumes one fresh configuration. Separating the
structural pending scan also makes kernel reduction execute the algorithm. -/
def explore [DecidableEq Vertex] (successors : Vertex → List Vertex) :
    Nat → List Vertex → List Vertex → List Vertex
  | 0, seen, _ => seen
  | capacity + 1, seen, pending => scan successors (explore successors capacity) seen pending

theorem explore_cons [DecidableEq Vertex] (successors : Vertex → List Vertex)
    (capacity : Nat) (seen : List Vertex) (current : Vertex) (rest : List Vertex) :
    explore successors (capacity + 1) seen (current :: rest) =
      if current ∈ seen then explore successors (capacity + 1) seen rest
      else explore successors capacity (current :: seen) (successors current ++ rest) := rfl

structure Invariant (successors : Vertex → List Vertex) (initial : Vertex)
    (seen pending : List Vertex) : Prop where
  distinct : seen.Nodup
  seen_sound : ∀ vertex ∈ seen, Path successors initial vertex
  pending_sound : ∀ vertex ∈ pending, Path successors initial vertex
  initial_present : initial ∈ seen ∨ initial ∈ pending
  frontier : ∀ source ∈ seen, ∀ target ∈ successors source,
    target ∈ seen ∨ target ∈ pending

theorem Invariant.skip {successors : Vertex → List Vertex} {initial current : Vertex}
    {seen rest : List Vertex} (invariant : Invariant successors initial seen (current :: rest))
    (known : current ∈ seen) : Invariant successors initial seen rest := by
  have move (vertex : Vertex) (member : vertex ∈ seen ∨ vertex ∈ current :: rest) :
      vertex ∈ seen ∨ vertex ∈ rest := by
    rcases member with present | pending
    · exact Or.inl present
    · rcases List.mem_cons.mp pending with rfl | remaining
      · exact Or.inl known
      · exact Or.inr remaining
  exact ⟨invariant.distinct, invariant.seen_sound,
    fun vertex member => invariant.pending_sound vertex (List.mem_cons_of_mem _ member),
    move initial invariant.initial_present,
    fun source member target edge => move target (invariant.frontier source member target edge)⟩

theorem Invariant.visit {successors : Vertex → List Vertex} {initial current : Vertex}
    {seen rest : List Vertex} (invariant : Invariant successors initial seen (current :: rest))
    (fresh : current ∉ seen) :
    Invariant successors initial (current :: seen) (successors current ++ rest) := by
  have currentPath := invariant.pending_sound current List.mem_cons_self
  have move (vertex : Vertex) (member : vertex ∈ seen ∨ vertex ∈ current :: rest) :
      vertex ∈ current :: seen ∨ vertex ∈ successors current ++ rest := by
    rcases member with present | pending
    · exact Or.inl (List.mem_cons_of_mem _ present)
    · rcases List.mem_cons.mp pending with rfl | remaining
      · exact Or.inl List.mem_cons_self
      · exact Or.inr (List.mem_append_right _ remaining)
  refine ⟨List.nodup_cons.mpr ⟨fresh, invariant.distinct⟩, ?_, ?_,
    move initial invariant.initial_present, ?_⟩
  · intro vertex member
    rcases List.mem_cons.mp member with rfl | earlier
    · exact currentPath
    · exact invariant.seen_sound vertex earlier
  · intro vertex member
    rcases List.mem_append.mp member with next | remaining
    · exact currentPath.append (.cons next (.nil vertex))
    · exact invariant.pending_sound vertex (List.mem_cons_of_mem _ remaining)
  · intro source member target edge
    rcases List.mem_cons.mp member with rfl | earlier
    · exact Or.inr (List.mem_append_left _ edge)
    · exact move target (invariant.frontier source earlier target edge)

/-- At capacity, every possible configuration has already been visited.
Otherwise adjoining a missing configuration contradicts the finite bound. -/
theorem saturated [DecidableEq Vertex] (vertices seen : List Vertex) (complete : ∀ vertex, vertex ∈ vertices)
    (distinct : seen.Nodup) (full : vertices.length ≤ seen.length) (vertex : Vertex) :
    vertex ∈ seen := by
  by_cases present : vertex ∈ seen
  · exact present
  · have enlarged : (vertex :: seen).Nodup := List.nodup_cons.mpr ⟨present, distinct⟩
    have bound := enlarged.length_le_of_subset (fun candidate _ => complete candidate)
    simp only [List.length_cons] at bound
    omega

/-- The worklist invariant accounts for every edge from an already processed
configuration. Exhausting the justified capacity therefore loses no path. -/
theorem explore_exact [DecidableEq Vertex] (successors : Vertex → List Vertex) (vertices : List Vertex)
    (complete : ∀ vertex, vertex ∈ vertices) (initial : Vertex)
    (capacity : Nat) (seen pending : List Vertex)
    (invariant : Invariant successors initial seen pending)
    (enough : vertices.length ≤ seen.length + capacity) (target : Vertex) :
    target ∈ explore successors capacity seen pending ↔ Path successors initial target := by
  induction capacity generalizing seen pending with
  | zero =>
      simp only [explore]
      exact ⟨invariant.seen_sound target, fun _ =>
        saturated vertices seen complete invariant.distinct (by simpa using enough) target⟩
  | succ capacity capacityIH =>
      induction pending generalizing seen with
      | nil =>
          simp only [explore, scan]
          have start : initial ∈ seen := invariant.initial_present.resolve_right (by simp)
          have closed : ∀ source ∈ seen, ∀ target ∈ successors source, target ∈ seen :=
            fun source member target edge =>
              (invariant.frontier source member target edge).resolve_right (by simp)
          exact ⟨invariant.seen_sound target, fun path => closed_path successors seen closed path start⟩
      | cons current rest pendingIH =>
          by_cases known : current ∈ seen
          · simp only [explore_cons, known, ↓reduceIte]
            exact pendingIH seen (invariant.skip known) enough
          · simp only [explore_cons, known, ↓reduceIte]
            apply capacityIH (current :: seen) (successors current ++ rest) (invariant.visit known)
            simp only [List.length_cons]
            omega

def reachable [DecidableEq Vertex] (successors : Vertex → List Vertex) (capacity : Nat) (initial : Vertex) : List Vertex :=
  explore successors capacity [] [initial]

/-- A complete finite universe certifies the capacity. It does not occur in
the executable arguments, and the result covers paths of every finite length. -/
theorem reachable_exact [DecidableEq Vertex] (successors : Vertex → List Vertex) (capacity : Nat)
    (vertices : List Vertex) (complete : ∀ vertex, vertex ∈ vertices)
    (enough : vertices.length ≤ capacity) (initial target : Vertex) :
    target ∈ reachable successors capacity initial ↔ Path successors initial target := by
  apply explore_exact successors vertices complete initial capacity [] [initial]
  · refine ⟨by simp, by simp, ?_, by simp, by simp⟩
    intro vertex member
    have same : vertex = initial := List.mem_singleton.mp member
    subst vertex
    exact .nil initial
  · simpa using enough

end Yulang.FiniteWorklist
