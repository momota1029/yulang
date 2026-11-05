import Std

/-!
# Materialized finite Boolean reachability

Floyd elimination constructs the reflexive transitive closure of an arbitrary
finite directed graph. Every intermediate matrix is materialized as a vector
of vectors; the algorithm neither enumerates Boolean models nor chooses a
path-length cutoff. Its correctness refers to an independent finite-path
judgment. This reference matrix implementation uses cubic many Boolean cells
updates and quadratic matrix space.
-/

namespace Yulang.FiniteBooleanReachability

abbrev Matrix (n : Nat) := Vector (Vector Bool n) n

def tabulate (relation : Fin n → Fin n → Bool) : Matrix n :=
  Vector.ofFn fun source => Vector.ofFn fun target => relation source target

def entry (matrix : Matrix n) (source target : Fin n) : Bool :=
  matrix[source.val][target.val]

@[simp] theorem entry_tabulate (relation : Fin n → Fin n → Bool) (source target : Fin n) :
    entry (tabulate relation) source target = relation source target := by
  simp [entry, tabulate]

inductive Path (edge : Fin n → Fin n → Bool) : Fin n → Fin n → Prop where
  | nil (vertex : Fin n) : Path edge vertex vertex
  | cons : edge source middle = true → Path edge middle target → Path edge source target

theorem Path.append {edge : Fin n → Fin n → Bool} {first middle last : Fin n}
    (left : Path edge first middle) (right : Path edge middle last) : Path edge first last := by
  induction left with
  | nil => exact right
  | cons step path ih => exact .cons step (ih right)

def TransAt (matrix : Matrix n) (middle : Fin n) : Prop :=
  ∀ source target, entry matrix source middle = true → entry matrix middle target = true →
    entry matrix source target = true

def extend (matrix : Matrix n) (pivot : Fin n) : Matrix n :=
  tabulate fun source target =>
    entry matrix source target || (entry matrix source pivot && entry matrix pivot target)

@[simp] theorem extend_exact (matrix : Matrix n) (pivot source target : Fin n) :
    entry (extend matrix pivot) source target = true ↔
      entry matrix source target = true ∨
        (entry matrix source pivot = true ∧ entry matrix pivot target = true) := by
  simp [extend]

theorem extend_trans_pivot (matrix : Matrix n) (pivot : Fin n) :
    TransAt (extend matrix pivot) pivot := by
  intro source target left right
  rw [extend_exact] at left right ⊢
  exact Or.inr ⟨left.elim id And.left, right.elim id And.right⟩

theorem extend_trans_old (matrix : Matrix n) (pivot middle : Fin n)
    (closed : TransAt matrix middle) : TransAt (extend matrix pivot) middle := by
  intro source target left right
  rw [extend_exact] at left right ⊢
  rcases left with directLeft | ⟨before, after⟩
  · rcases right with directRight | ⟨before, after⟩
    · exact Or.inl (closed source target directLeft directRight)
    · exact Or.inr ⟨closed source pivot directLeft before, after⟩
  · rcases right with directRight | ⟨before', after'⟩
    · exact Or.inr ⟨before, closed pivot target after directRight⟩
    · exact Or.inr ⟨before, after'⟩

def close : List (Fin n) → Matrix n → Matrix n
  | [], matrix => matrix
  | pivot :: rest, matrix => extend (close rest matrix) pivot

theorem close_keeps (vertices : List (Fin n)) (matrix : Matrix n) (source target : Fin n)
    (present : entry matrix source target = true) : entry (close vertices matrix) source target = true := by
  induction vertices with
  | nil => exact present
  | cons pivot rest ih => exact (extend_exact _ _ _ _).mpr (Or.inl ih)

theorem close_trans (vertices : List (Fin n)) (matrix : Matrix n)
    (middle : Fin n) (present : middle ∈ vertices) : TransAt (close vertices matrix) middle := by
  induction vertices with
  | nil => simp at present
  | cons pivot rest ih =>
      rcases List.mem_cons.mp present with rfl | member
      · exact extend_trans_pivot _ _
      · exact extend_trans_old _ _ _ (ih member)

theorem close_sound (vertices : List (Fin n)) (matrix : Matrix n)
    (edge : Fin n → Fin n → Bool)
    (sound : ∀ source target, entry matrix source target = true → Path edge source target)
    (source target : Fin n) : entry (close vertices matrix) source target = true → Path edge source target := by
  induction vertices generalizing source target with
  | nil => exact sound source target
  | cons pivot rest ih =>
      intro reached
      rcases (extend_exact _ _ _ _).mp reached with direct | ⟨before, after⟩
      · exact ih _ _ direct
      · exact (ih _ _ before).append (ih _ _ after)

def initial (edge : Fin n → Fin n → Bool) : Matrix n :=
  tabulate fun source target => decide (source = target) || edge source target

@[simp] theorem initial_exact (edge : Fin n → Fin n → Bool) (source target : Fin n) :
    entry (initial edge) source target = true ↔ source = target ∨ edge source target = true := by
  simp [initial]

def closure (edge : Fin n → Fin n → Bool) : Matrix n :=
  close (List.finRange n) (initial edge)

theorem closure_exact (edge : Fin n → Fin n → Bool) (source target : Fin n) :
    entry (closure edge) source target = true ↔ Path edge source target := by
  constructor
  · apply close_sound
    intro source target reached
    rcases (initial_exact _ _ _).mp reached with rfl | single
    · exact .nil _
    · exact .cons single (.nil _)
  · intro path
    induction path with
    | nil vertex =>
        exact close_keeps _ _ _ _ ((initial_exact _ _ _).mpr (Or.inl rfl))
    | @cons source middle target step rest ih =>
        have first : entry (closure edge) source middle = true :=
          close_keeps _ _ _ _ ((initial_exact _ _ _).mpr (Or.inr step))
        exact close_trans _ _ middle (by simp) source target first ih

end Yulang.FiniteBooleanReachability
