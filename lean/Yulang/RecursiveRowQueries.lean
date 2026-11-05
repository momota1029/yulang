import Yulang.RecursiveRows

/-!
# Fresh output slots for arbitrary recursive row expressions

A finite family of queries is added as fresh output-only slots. Original
constraints refer only to original slots, and each query reads only original
slots. The extended least solution therefore preserves every original row and
gives each fresh slot exactly its query evaluated in the original least model.

No finite-support assumption or row-solving oracle enters this construction.
An open original slot is empty in the least model; arbitrary other models may
assign additional effects to it. Query exactness concerns the least model and
the facts forced by every model, not all later scheme instantiations.
-/

namespace Yulang.RecursiveRowQueries

open RowInference (RowExpr)
open RecursiveRows (Rule Problem Environment Models Below IsLeastModel Derives algebra)

variable {n k : Nat} {Key Slot Query : Type}

def liftExpr (row : RowExpr Key (Fin n) Slot) : RowExpr Key (Fin n) (Slot ⊕ Query) :=
  row.subst (fun slot => .var (.inl slot))

theorem eval_liftExpr (row : RowExpr Key (Fin n) Slot)
    (rows : Environment n Key (Slot ⊕ Query)) :
    (liftExpr row).eval (algebra n Key) rows =
      row.eval (algebra n Key) (fun slot => rows (.inl slot)) :=
  RowExpr.eval_subst _ _ _ _

def liftRule (rule : Rule n Key Slot) : Rule n Key (Slot ⊕ Query) :=
  ⟨.inl rule.target, liftExpr rule.lower⟩

def queryRule (queries : Fin k → RowExpr Key (Fin n) Slot) (index : Fin k) :
    Rule n Key (Slot ⊕ Fin k) :=
  ⟨.inr index, liftExpr (queries index)⟩

def extend (problem : Problem n Key Slot) (queries : Fin k → RowExpr Key (Fin n) Slot) :
    Problem n Key (Slot ⊕ Fin k) :=
  problem.map liftRule ++ (List.finRange k).map (queryRule queries)

def extendRows (queries : Fin k → RowExpr Key (Fin n) Slot)
    (rows : Environment n Key Slot) : Environment n Key (Slot ⊕ Fin k)
  | .inl slot => rows slot
  | .inr index => (queries index).eval (algebra n Key) rows

/-- The fresh constraints add only lower bounds at their output slots. -/
theorem models_exact (problem : Problem n Key Slot)
    (queries : Fin k → RowExpr Key (Fin n) Slot)
    (rows : Environment n Key (Slot ⊕ Fin k)) :
    Models (extend problem queries) rows ↔
      Models problem (fun slot => rows (.inl slot)) ∧
      ∀ index occurrence,
        (queries index).eval (algebra n Key) (fun slot => rows (.inl slot)) occurrence →
          rows (.inr index) occurrence := by
  constructor
  · intro model
    constructor
    · intro rule declared occurrence fact
      apply model (liftRule rule)
        (List.mem_append_left _ (List.mem_map.mpr ⟨rule, declared, rfl⟩)) occurrence
      exact (congrFun (eval_liftExpr rule.lower rows) occurrence).mpr fact
    · intro index occurrence fact
      apply model (queryRule queries index)
        (List.mem_append_right _ (List.mem_map.mpr
          ⟨index, List.mem_finRange index, rfl⟩)) occurrence
      exact (congrFun (eval_liftExpr (queries index) rows) occurrence).mpr fact
  · rintro ⟨original, output⟩ rule declared occurrence fact
    rcases List.mem_append.mp declared with declared | declared
    · obtain ⟨source, member, rfl⟩ := List.mem_map.mp declared
      exact original source member occurrence
        ((congrFun (eval_liftExpr source.lower rows) occurrence).mp fact)
    · obtain ⟨index, _, rfl⟩ := List.mem_map.mp declared
      exact output index occurrence
        ((congrFun (eval_liftExpr (queries index) rows) occurrence).mp fact)

theorem restrict_models (problem : Problem n Key Slot)
    (queries : Fin k → RowExpr Key (Fin n) Slot)
    (rows : Environment n Key (Slot ⊕ Fin k))
    (model : Models (extend problem queries) rows) :
    Models problem (fun slot => rows (.inl slot)) :=
  ((models_exact problem queries rows).mp model).1

theorem extend_models (problem : Problem n Key Slot)
    (queries : Fin k → RowExpr Key (Fin n) Slot)
    (rows : Environment n Key Slot) (model : Models problem rows) :
    Models (extend problem queries) (extendRows queries rows) := by
  exact (models_exact problem queries (extendRows queries rows)).mpr
    ⟨model, fun _ _ fact => fact⟩

/-- Evaluation at the old least model supplies the least possible fresh rows,
while every old row retains its original least value. -/
theorem extension_least (problem : Problem n Key Slot)
    (queries : Fin k → RowExpr Key (Fin n) Slot) :
    IsLeastModel (extend problem queries) (extendRows queries (Derives problem)) := by
  constructor
  · exact extend_models problem queries _ (RecursiveRows.least_models problem)
  · intro rows model slot occurrence fact
    have conditions := (models_exact problem queries rows).mp model
    have below := RecursiveRows.least_below problem _ conditions.1
    cases slot with
    | inl original => exact below original occurrence fact
    | inr index =>
        exact conditions.2 index occurrence
          (RecursiveRows.eval_mono (queries index) _ _ below occurrence fact)

theorem original_exact (problem : Problem n Key Slot)
    (queries : Fin k → RowExpr Key (Fin n) Slot) (slot : Slot)
    (occurrence : Directed.Occurrence n Key) :
    Derives (extend problem queries) (.inl slot) occurrence ↔
      Derives problem slot occurrence :=
  (RecursiveRows.least_unique _ _ (extension_least problem queries) (.inl slot) occurrence).symm

theorem query_exact (problem : Problem n Key Slot)
    (queries : Fin k → RowExpr Key (Fin n) Slot) (index : Fin k)
    (occurrence : Directed.Occurrence n Key) :
    Derives (extend problem queries) (.inr index) occurrence ↔
      (queries index).eval (algebra n Key) (Derives problem) occurrence :=
  (RecursiveRows.least_unique _ _ (extension_least problem queries) (.inr index) occurrence).symm

/-- Queries describe forced expression facts. The theorem does not replace an
arbitrary model by its least submodel when later instantiating a scheme. -/
theorem query_iff_forced (problem : Problem n Key Slot)
    (queries : Fin k → RowExpr Key (Fin n) Slot) (index : Fin k)
    (occurrence : Directed.Occurrence n Key) :
    Derives (extend problem queries) (.inr index) occurrence ↔
      ∀ rows, Models problem rows → (queries index).eval (algebra n Key) rows occurrence := by
  rw [query_exact]
  constructor
  · intro fact rows model
    exact RecursiveRows.eval_mono (queries index) _ _
      (RecursiveRows.least_below problem rows model) occurrence fact
  · intro forced
    exact forced (Derives problem) (RecursiveRows.least_models problem)

end Yulang.RecursiveRowQueries
