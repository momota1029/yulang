import Yulang.ValueBounds
import Yulang.SemilinearRowQuotient

/-!
# Concrete value-bound solvers, including arbitrary semantic row witnesses

The signed entry point supplies its own exact ground comparison. The semilinear
entry point accepts finite codes for possibly infinite latent rows, constructs
unknown value types, and decides satisfiability in the original set-row algebra.
Its negative answer excludes every finite structural value-type assignment over
arbitrary set rows, not just assignments representable by semilinear codes.

The finite object is the graph of unknowns and supplied bounds. Neither the
space of possible value types nor the signed weights is bounded or enumerated.
-/

namespace Yulang.ValueBoundSolvers

open StructuralBase ValueBounds

variable {m : Nat} {R : Type u} {S : Type v}

theorem accepts_mapped_exact (decode : Ty R → Ty S)
    (typeCheck : Ty R → Ty R → Bool) (leRow : S → S → Prop)
    (exact : ∀ left right, typeCheck left right = true ↔
      Subtype leRow (decode left) (decode right))
    (problem : Problem m R) (value : Valuation m R) :
    accepts typeCheck problem value = true ↔
      Models leRow (mapTypes decode problem) (decode ∘ value) := by
  simp only [accepts, List.all_eq_true, Models, mapTypes, List.forall_mem_map]
  apply forall_congr'
  intro constraint
  apply imp_congr_right
  intro _
  cases constraint <;> exact exact _ _

theorem solve_mapped_some_iff (decode : Ty R → Ty S)
    (typeCheck : Ty R → Ty R → Bool) (leRow : S → S → Prop)
    (exact : ∀ left right, typeCheck left right = true ↔
      Subtype leRow (decode left) (decode right))
    (problem : Problem m R) (value : Valuation m R) :
    solve typeCheck problem = some value ↔
      value = least problem ∧ Models leRow (mapTypes decode problem) (decode ∘ value) := by
  simp only [solve]
  split
  · rename_i accepted
    have model := (accepts_mapped_exact decode typeCheck leRow exact problem _).mp accepted
    constructor
    · intro same
      have same : least problem = value := Option.some.inj same
      exact ⟨same.symm, same ▸ model⟩
    · rintro ⟨rfl, _⟩
      rfl
  · rename_i rejected
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨rfl, model⟩
      exact False.elim (rejected
        ((accepts_mapped_exact decode typeCheck leRow exact problem _).mpr model))

/-- Completeness needs no assumption that an arbitrary semantic solution can
be encoded. Only the solver's least assignment must commute with decoding. -/
theorem solve_mapped_none_iff (decode : Ty R → Ty S)
    (bottom : decode .bottom = .bottom)
    (union : ∀ left right, decode (.union left right) = .union (decode left) (decode right))
    (typeCheck : Ty R → Ty R → Bool) (leRow : S → S → Prop)
    (exact : ∀ left right, typeCheck left right = true ↔
      Subtype leRow (decode left) (decode right))
    (problem : Problem m R) :
    solve typeCheck problem = none ↔
      ¬ ∃ value : Valuation m S, Models leRow (mapTypes decode problem) value := by
  have same : decode ∘ least problem = least (mapTypes decode problem) :=
    funext (least_mapTypes decode bottom union problem)
  constructor
  · intro failed ⟨value, model⟩
    have leastModel : Models leRow (mapTypes decode problem) (decode ∘ least problem) := by
      rw [same]
      exact least_models_of_models model
    have succeeded := (solve_mapped_some_iff decode typeCheck leRow exact problem _).mpr
      ⟨rfl, leastModel⟩
    rw [failed] at succeeded
    cases succeeded
  · intro absent
    cases returned : solve typeCheck problem with
    | none => rfl
    | some value =>
        exact False.elim (absent ⟨decode ∘ value,
          ((solve_mapped_some_iff decode typeCheck leRow exact problem value).mp returned).2⟩)

theorem solve_mapped_least (decode : Ty R → Ty S)
    (bottom : decode .bottom = .bottom)
    (union : ∀ left right, decode (.union left right) = .union (decode left) (decode right))
    (typeCheck : Ty R → Ty R → Bool) (leRow : S → S → Prop)
    (exact : ∀ left right, typeCheck left right = true ↔
      Subtype leRow (decode left) (decode right))
    {problem : Problem m R} {value : Valuation m R}
    (solved : solve typeCheck problem = some value)
    {other : Valuation m S} (model : Models leRow (mapTypes decode problem) other)
    (target : Fin m) : Subtype leRow (decode (value target)) (other target) := by
  rw [((solve_mapped_some_iff decode typeCheck leRow exact problem value).mp solved).1,
    least_mapTypes decode bottom union]
  exact least_below model.lower target

/-! ## Finite signed rows -/

def solveSigned [DecidableEq Key] (problem : Problem m (Directed.Row n Key)) :
    Option (Valuation m (Directed.Row n Key)) := solve StructuralDecisions.checkSigned problem

theorem solveSigned_some_iff [DecidableEq Key]
    (problem : Problem m (Directed.Row n Key)) (value : Valuation m (Directed.Row n Key)) :
    solveSigned problem = some value ↔
      value = least problem ∧ Models SignedStructural.RowLe problem value :=
  solve_some_iff StructuralDecisions.checkSigned StructuralDecisions.checkSigned_exact problem value

theorem solveSigned_none_iff [DecidableEq Key] (problem : Problem m (Directed.Row n Key)) :
    solveSigned problem = none ↔ ¬ ∃ value, Models SignedStructural.RowLe problem value :=
  solve_none_iff StructuralDecisions.checkSigned StructuralDecisions.checkSigned_exact problem

/-! ## Infinite rows, given by finite semilinear presentations -/

def decodeType [DecidableEq Key] (type : SemilinearRowAlgebra.GroundType n Key) :
    Ty (RecursiveRows.SetRow n Key) :=
  StructuralRowResolution.mapRows SemilinearRowAlgebra.decode type

def semanticProblem [DecidableEq Key] (problem : Problem m (SemilinearRowAlgebra.Row n Key)) :
    Problem m (RecursiveRows.SetRow n Key) := mapTypes decodeType problem

def solveSemilinear [DecidableEq Key] (problem : Problem m (SemilinearRowAlgebra.Row n Key)) :
    Option (Valuation m (SemilinearRowAlgebra.Row n Key)) :=
  solve SemilinearRowQuotient.compareCodes problem

theorem solveSemilinear_some_iff [DecidableEq Key]
    (problem : Problem m (SemilinearRowAlgebra.Row n Key))
    (value : Valuation m (SemilinearRowAlgebra.Row n Key)) :
    solveSemilinear problem = some value ↔
      value = least problem ∧
        Models (RecursiveRows.algebra n Key).le (semanticProblem problem) (decodeType ∘ value) :=
  solve_mapped_some_iff decodeType SemilinearRowQuotient.compareCodes _
    SemilinearRowQuotient.compareCodes_exact problem value

/-- The quantified witness may contain any set row, even a non-semilinear one. -/
theorem solveSemilinear_none_iff [DecidableEq Key]
    (problem : Problem m (SemilinearRowAlgebra.Row n Key)) :
    solveSemilinear problem = none ↔
      ¬ ∃ value : Valuation m (RecursiveRows.SetRow n Key),
        Models (RecursiveRows.algebra n Key).le (semanticProblem problem) value :=
  solve_mapped_none_iff decodeType rfl (fun _ _ => rfl)
    SemilinearRowQuotient.compareCodes _ SemilinearRowQuotient.compareCodes_exact problem

theorem solveSemilinear_least [DecidableEq Key]
    {problem : Problem m (SemilinearRowAlgebra.Row n Key)}
    {value : Valuation m (SemilinearRowAlgebra.Row n Key)}
    (solved : solveSemilinear problem = some value)
    {other : Valuation m (RecursiveRows.SetRow n Key)}
    (model : Models (RecursiveRows.algebra n Key).le (semanticProblem problem) other)
    (target : Fin m) :
    Subtype (RecursiveRows.algebra n Key).le (decodeType (value target)) (other target) :=
  solve_mapped_least decodeType rfl (fun _ _ => rfl)
    SemilinearRowQuotient.compareCodes _ SemilinearRowQuotient.compareCodes_exact solved model target

end Yulang.ValueBoundSolvers
