import Yulang.SemilinearWeights

/-!
# Finite unguarded integer-weighted graphs have constructive semilinear images

State elimination builds a regular expression for all paths between two
vertices. Its correctness is proved against the independent `Path` relation,
without a path-length bound. Compiling that expression uses the constructive
semilinear closure theorems. All integer coordinates and signs are preserved.

There are no guards here: an edge is always enabled at its source vertex.
Applying this result to recursive rows therefore requires proving that their
normalized exclusion sets are empty. No containment decision procedure is
asserted by the finite representation theorem.
-/

namespace Yulang.WeightedPaths

open SemilinearWeights

variable {n : Nat} {Vertex : Type}

structure Edge (n : Nat) (Vertex : Type) where
  source : Vertex
  target : Vertex
  weight : Weight n

abbrev Graph (n : Nat) (Vertex : Type) := List (Edge n Vertex)

inductive Path (graph : Graph n Vertex) : Vertex → Vertex → Weight n → Prop where
  | nil (vertex : Vertex) : Path graph vertex vertex zero
  | cons {edge : Edge n Vertex} {target : Vertex} {rest : Weight n} :
      edge ∈ graph → Path graph edge.target target rest →
        Path graph edge.source target (add edge.weight rest)

theorem Path.single {graph : Graph n Vertex} {edge : Edge n Vertex}
    (member : edge ∈ graph) : Path graph edge.source edge.target edge.weight := by
  simpa using Path.cons member (Path.nil edge.target)

theorem Path.append {graph : Graph n Vertex} {first middle last : Vertex} {left right : Weight n}
    (firstPath : Path graph first middle left) (secondPath : Path graph middle last right) :
    Path graph first last (add left right) := by
  induction firstPath with
  | nil => simpa using secondPath
  | cons member path ih => simpa only [add_assoc] using Path.cons member (ih secondPath)

abbrev Relation (n : Nat) (Vertex : Type) := Vertex → Vertex → WeightSet n

def TransAt (relation : Relation n Vertex) (middle : Vertex) : Prop :=
  ∀ first last left right, relation first middle left → relation middle last right →
    relation first last (add left right)

/-- The new paths may pass through the pivot any finite number of times. -/
def Extend (relation : Relation n Vertex) (pivot : Vertex) : Relation n Vertex :=
  fun first last weight => relation first last weight ∨
    ∃ initial loops suffix,
      relation first pivot initial ∧ Star (relation pivot pivot) loops ∧
        relation pivot last suffix ∧ add initial (add loops suffix) = weight

theorem extend_keeps (relation : Relation n Vertex) (pivot : Vertex) {first last : Vertex}
    {weight : Weight n} (member : relation first last weight) :
    Extend relation pivot first last weight := Or.inl member

theorem extend_to_pivot (relation : Relation n Vertex) (pivot first : Vertex) (weight : Weight n)
    (member : Extend relation pivot first pivot weight) :
    ∃ initial loops, relation first pivot initial ∧ Star (relation pivot pivot) loops ∧
      add initial loops = weight := by
  rcases member with direct | ⟨initial, loops, suffix, first, repeated, last, rfl⟩
  · exact ⟨weight, zero, direct, .nil, add_zero _⟩
  · exact ⟨initial, add loops suffix, first, repeated.append (Star.single last), rfl⟩

theorem extend_from_pivot (relation : Relation n Vertex) (pivot last : Vertex) (weight : Weight n)
    (member : Extend relation pivot pivot last weight) :
    ∃ loops suffix, Star (relation pivot pivot) loops ∧ relation pivot last suffix ∧
      add loops suffix = weight := by
  rcases member with direct | ⟨initial, loops, suffix, first, repeated, last, rfl⟩
  · exact ⟨zero, weight, .nil, direct, zero_add _⟩
  · exact ⟨add initial loops, suffix, Star.cons first repeated, last, add_assoc _ _ _⟩

theorem extend_trans_pivot (relation : Relation n Vertex) (pivot : Vertex) :
    TransAt (Extend relation pivot) pivot := by
  intro first last left right firstPath secondPath
  obtain ⟨initial, firstLoops, first, repeatedFirst, rfl⟩ :=
    extend_to_pivot relation pivot first left firstPath
  obtain ⟨secondLoops, suffix, repeatedSecond, last, rfl⟩ :=
    extend_from_pivot relation pivot last right secondPath
  refine Or.inr ⟨initial, add firstLoops secondLoops, suffix, first,
    repeatedFirst.append repeatedSecond, last, ?_⟩
  simp only [add_assoc]

/-- Closing a new pivot preserves transitivity through every previously
closed vertex. The intermediate crossing joins two old legs at that vertex. -/
theorem extend_trans_old (relation : Relation n Vertex) (pivot middle : Vertex)
    (transitive : TransAt relation middle) : TransAt (Extend relation pivot) middle := by
  intro first last left right firstPath secondPath
  rcases firstPath with firstDirect | ⟨firstLeg, firstLoops, firstEnd, firstStart, firstRepeat, firstFinish, rfl⟩
  · rcases secondPath with secondDirect | ⟨secondLeg, secondLoops, secondEnd, secondStart, secondRepeat, secondFinish, rfl⟩
    · exact Or.inl (transitive _ _ _ _ firstDirect secondDirect)
    · refine Or.inr ⟨add left secondLeg, secondLoops, secondEnd,
        transitive _ _ _ _ firstDirect secondStart, secondRepeat, secondFinish, ?_⟩
      simp only [add_assoc]
  · rcases secondPath with secondDirect | ⟨secondLeg, secondLoops, secondEnd, secondStart, secondRepeat, secondFinish, rfl⟩
    · refine Or.inr ⟨firstLeg, firstLoops, add firstEnd right,
        firstStart, firstRepeat, transitive _ _ _ _ firstFinish secondDirect, ?_⟩
      simp only [add_assoc]
    · have crossing : relation pivot pivot (add firstEnd secondLeg) :=
        transitive _ _ _ _ firstFinish secondStart
      refine Or.inr ⟨firstLeg, add firstLoops (add (add firstEnd secondLeg) secondLoops),
        secondEnd, firstStart, firstRepeat.append (Star.cons crossing secondRepeat), secondFinish, ?_⟩
      simp only [add_assoc]

theorem star_path {graph : Graph n Vertex} {relation : Relation n Vertex} (vertex : Vertex)
    (sound : ∀ weight, relation vertex vertex weight → Path graph vertex vertex weight)
    {weight : Weight n} (member : Star (relation vertex vertex) weight) :
    Path graph vertex vertex weight := by
  induction member with
  | nil => exact .nil _
  | cons first rest ih => exact (sound _ first).append ih

theorem extend_sound {graph : Graph n Vertex} {relation : Relation n Vertex}
    (sound : ∀ first last weight, relation first last weight → Path graph first last weight)
    (pivot first last : Vertex) (weight : Weight n)
    (member : Extend relation pivot first last weight) : Path graph first last weight := by
  rcases member with direct | ⟨initial, loops, suffix, firstPath, repeated, lastPath, rfl⟩
  · exact sound _ _ _ direct
  · exact (sound _ _ _ firstPath).append
      ((star_path pivot (sound pivot pivot) repeated).append (sound _ _ _ lastPath))

def direct [DecidableEq Vertex] (graph : Graph n Vertex) (first last : Vertex) : Regex n :=
  graph.foldr (fun edge rest =>
    if edge.source = first ∧ edge.target = last then .union (.atom edge.weight) rest else rest)
    (if first = last then .epsilon else .empty)

theorem direct_exact [DecidableEq Vertex] (graph : Graph n Vertex) (first last : Vertex)
    (weight : Weight n) :
    (direct graph first last).Meaning weight ↔
      (first = last ∧ zero = weight) ∨
        ∃ edge ∈ graph, edge.source = first ∧ edge.target = last ∧ edge.weight = weight := by
  induction graph with
  | nil => by_cases same : first = last <;> simp [direct, same, Regex.Meaning]
  | cons edge rest ih =>
      by_cases connects : edge.source = first ∧ edge.target = last
      · simp only [direct, List.foldr_cons, connects]
        change (edge.weight = weight ∨ (direct rest first last).Meaning weight) ↔ _
        rw [ih]
        simp only [List.mem_cons]
        constructor
        · rintro (equal | nilPath | ⟨selected, present, source, target, equal⟩)
          · exact Or.inr ⟨edge, Or.inl rfl, connects.1, connects.2, equal⟩
          · exact Or.inl nilPath
          · exact Or.inr ⟨selected, Or.inr present, source, target, equal⟩
        · rintro (nilPath | ⟨selected, present, source, target, equal⟩)
          · exact Or.inr (Or.inl nilPath)
          · rcases present with rfl | present
            · exact Or.inl equal
            · exact Or.inr (Or.inr ⟨selected, present, source, target, equal⟩)
      · simp only [direct, List.foldr_cons, connects, ↓reduceIte]
        change (direct rest first last).Meaning weight ↔ _
        rw [ih]
        constructor
        · rintro (nilPath | ⟨selected, present, source, target, equal⟩)
          · exact Or.inl nilPath
          · exact Or.inr ⟨selected, List.mem_cons_of_mem _ present, source, target, equal⟩
        · rintro (nilPath | ⟨selected, present, source, target, equal⟩)
          · exact Or.inl nilPath
          · rcases List.mem_cons.mp present with rfl | present
            · exact False.elim (connects ⟨source, target⟩)
            · exact Or.inr ⟨selected, present, source, target, equal⟩

def eliminate (matrix : Vertex → Vertex → Regex n) (pivot : Vertex) : Vertex → Vertex → Regex n :=
  fun first last => .union (matrix first last)
    (.seq (matrix first pivot) (.seq (.star (matrix pivot pivot)) (matrix pivot last)))

theorem eliminate_exact (matrix : Vertex → Vertex → Regex n) (pivot first last : Vertex)
    (weight : Weight n) :
    (eliminate matrix pivot first last).Meaning weight ↔
      Extend (fun first last => (matrix first last).Meaning) pivot first last weight := by
  simp only [eliminate, Regex.Meaning, Join, SemilinearWeights.Sum, Extend]
  constructor
  · rintro (direct | ⟨initial, rest, firstPath, ⟨loops, suffix, repeated, lastPath, rfl⟩, total⟩)
    · exact Or.inl direct
    · exact Or.inr ⟨initial, loops, suffix, firstPath, repeated, lastPath, total⟩
  · rintro (direct | ⟨initial, loops, suffix, firstPath, repeated, lastPath, total⟩)
    · exact Or.inl direct
    · exact Or.inr ⟨initial, add loops suffix, firstPath, ⟨loops, suffix, repeated, lastPath, rfl⟩, total⟩

def close : List Vertex → (Vertex → Vertex → Regex n) → (Vertex → Vertex → Regex n)
  | [], matrix => matrix
  | pivot :: rest, matrix => eliminate (close rest matrix) pivot

theorem close_keeps (vertices : List Vertex) (matrix : Vertex → Vertex → Regex n)
    (first last : Vertex) (weight : Weight n) (member : (matrix first last).Meaning weight) :
    (close vertices matrix first last).Meaning weight := by
  induction vertices with
  | nil => exact member
  | cons pivot rest ih => exact (eliminate_exact _ _ _ _ _).mpr (Or.inl ih)

theorem close_trans (vertices : List Vertex) (matrix : Vertex → Vertex → Regex n)
    (middle : Vertex) (present : middle ∈ vertices) :
    TransAt (fun first last => (close vertices matrix first last).Meaning) middle := by
  induction vertices with
  | nil => simp at present
  | cons pivot rest ih =>
      have same : (fun first last => (close (pivot :: rest) matrix first last).Meaning) =
          Extend (fun first last => (close rest matrix first last).Meaning) pivot := by
        funext first last weight
        exact propext (eliminate_exact _ _ _ _ _)
      rw [same]
      rcases List.mem_cons.mp present with rfl | present
      · exact extend_trans_pivot _ _
      · exact extend_trans_old _ _ _ (ih present)

theorem close_sound {graph : Graph n Vertex} (vertices : List Vertex)
    (matrix : Vertex → Vertex → Regex n)
    (sound : ∀ first last weight, (matrix first last).Meaning weight → Path graph first last weight)
    (first last : Vertex) (weight : Weight n) :
    (close vertices matrix first last).Meaning weight → Path graph first last weight := by
  induction vertices generalizing first last weight with
  | nil => exact sound first last weight
  | cons pivot rest ih =>
      intro member
      exact extend_sound ih pivot first last weight ((eliminate_exact _ _ _ _ _).mp member)

theorem direct_sound [DecidableEq Vertex] (graph : Graph n Vertex)
    (first last : Vertex) (weight : Weight n) :
    (direct graph first last).Meaning weight → Path graph first last weight := by
  intro member
  rcases (direct_exact graph first last weight).mp member with ⟨rfl, rfl⟩ |
    ⟨edge, present, rfl, rfl, rfl⟩
  · exact .nil _
  · exact Path.single present

theorem close_complete_targets [DecidableEq Vertex] (vertices : List Vertex)
    (graph : Graph n Vertex) (complete : ∀ edge ∈ graph, edge.target ∈ vertices)
    (first last : Vertex) (weight : Weight n) (path : Path graph first last weight) :
    (close vertices (direct graph) first last).Meaning weight := by
  induction path with
  | nil vertex =>
      exact close_keeps vertices (direct graph) vertex vertex zero
        ((direct_exact _ _ _ _).mpr (Or.inl ⟨rfl, rfl⟩))
  | @cons edge target rest member path ih =>
      have step : (close vertices (direct graph) edge.source edge.target).Meaning edge.weight :=
        close_keeps vertices (direct graph) _ _ _
          ((direct_exact _ _ _ _).mpr (Or.inr ⟨edge, member, rfl, rfl, rfl⟩))
      exact close_trans vertices (direct graph) edge.target (complete edge member) _ _ _ _ step ih

theorem close_complete [DecidableEq Vertex] (vertices : List Vertex)
    (complete : ∀ vertex, vertex ∈ vertices) (graph : Graph n Vertex)
    (first last : Vertex) (weight : Weight n) (path : Path graph first last weight) :
    (close vertices (direct graph) first last).Meaning weight :=
  close_complete_targets vertices graph (fun edge _ => complete edge.target) first last weight path

def solve [DecidableEq Vertex] (vertices : List Vertex) (graph : Graph n Vertex)
    (first last : Vertex) : Semi n := (close vertices (direct graph) first last).compile

/-- The executable finite representation describes every finite graph path,
and only such paths. Completeness of the vertex enumeration is the sole
finiteness premise; no bound on path length or integer weights occurs. -/
theorem solve_exact [DecidableEq Vertex] (vertices : List Vertex)
    (complete : ∀ vertex, vertex ∈ vertices) (graph : Graph n Vertex)
    (first last : Vertex) (weight : Weight n) :
    Meaning (solve vertices graph first last) weight ↔ Path graph first last weight := by
  rw [solve, Regex.compile_exact]
  exact ⟨close_sound vertices (direct graph) (direct_sound graph) first last weight,
    close_complete vertices complete graph first last weight⟩

theorem solve_targets_exact [DecidableEq Vertex] (vertices : List Vertex)
    (graph : Graph n Vertex) (complete : ∀ edge ∈ graph, edge.target ∈ vertices)
    (first last : Vertex) (weight : Weight n) :
    Meaning (solve vertices graph first last) weight ↔ Path graph first last weight := by
  rw [solve, Regex.compile_exact]
  exact ⟨close_sound vertices (direct graph) (direct_sound graph) first last weight,
    close_complete_targets vertices graph complete first last weight⟩

/-- The input graph itself supplies the finite support. Even if the type of
vertex identifiers is infinite, every intermediate vertex is an edge target.
Eliminate each distinct target once: repeated elimination preserves meaning
but can expand even a single seeded cycle into millions of linear components. -/
def solveFinite [DecidableEq Vertex] (graph : Graph n Vertex) (first last : Vertex) : Semi n :=
  solve (graph.map Edge.target).eraseDups graph first last

theorem solveFinite_exact [DecidableEq Vertex] (graph : Graph n Vertex)
    (first last : Vertex) (weight : Weight n) :
    Meaning (solveFinite graph first last) weight ↔ Path graph first last weight :=
  solve_targets_exact (graph.map Edge.target).eraseDups graph
    (fun edge member => List.mem_eraseDups.mpr (List.mem_map.mpr ⟨edge, member, rfl⟩)) first last weight

end Yulang.WeightedPaths
