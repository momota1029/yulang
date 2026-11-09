import Yulang.CommonRoleRecursivePaths

/-! Model-exact finite decomposition of actual pair, arrow and same-tag variant
constraints. Other constructors and rows remain residual; this is not a complete
ordinary solver. Internal payload variables are exposed without allocating slots. -/
namespace Yulang.CommonRoleStructuralDecomposition
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)

def expandFuel : Nat → TyTerm α → TyTerm α → List (Atom α)
  | 0, l, r => [.tyLe l r]
  | k+1, l, r => match l, r with
    | .pair a b, .pair c d => expandFuel k a c ++ expandFuel k b d
    | .arrow a ea b eb, .arrow c ec d ed =>
        expandFuel k c a ++ [.rowLe ec ea] ++ expandFuel k b d ++ [.rowLe eb ed]
    | .variant i a, .variant j b =>
        if i = j then expandFuel k a b else [.tyLe (.variant i a) (.variant j b)]
    | l, r => [.tyLe l r]

private theorem singleton_exact (a : α → Comp Common.model) (x : Atom α) :
    All Common.model a [x] ↔ x.Holds Common.model a := by simp [All]

theorem expandFuel_exact (k : Nat) (l r : TyTerm α) (a : α → Comp Common.model) :
    All Common.model a (expandFuel k l r) ↔ (Atom.tyLe l r).Holds Common.model a := by
  induction k generalizing l r with
  | zero => exact singleton_exact a _
  | succ k ih =>
    simp only [expandFuel]
    split
    · simp only [PresenceNormalForm.all_append, ih]
      exact (Common.common_pair_iff ..).symm
    · simp only [PresenceNormalForm.all_append, singleton_exact, ih]
      simp only [Atom.Holds, TyTerm.eval]
      constructor
      · rintro ⟨⟨⟨ha,hea⟩,hb⟩,heb⟩
        exact (Common.common_arrow_iff ..).mpr ⟨ha,hea,hb,heb⟩
      · intro h
        obtain ⟨ha,hea,hb,heb⟩ := (Common.common_arrow_iff ..).mp h
        exact ⟨⟨⟨ha,hea⟩,hb⟩,heb⟩
    · split
      · rename_i eq; subst eq
        rw [ih]
        exact (Common.common_variant_iff ..).symm
      · exact singleton_exact a _
    · exact singleton_exact a _

def expand (l r : TyTerm α) : List (Atom α) :=
  expandFuel (CommonRoleRecursiveConflicts.weight l + CommonRoleRecursiveConflicts.weight r) l r

theorem expand_exact (l r : TyTerm α) (a : α → Comp Common.model) :
    All Common.model a (expand l r) ↔ (Atom.tyLe l r).Holds Common.model a :=
  expandFuel_exact _ l r a

def atom : Atom α → List (Atom α)
  | .tyLe l r => expand l r
  | .rowLe l r => [.rowLe l r]

theorem atom_exact (x : Atom α) (a : α → Comp Common.model) :
    All Common.model a (atom x) ↔ x.Holds Common.model a := by
  cases x with
  | tyLe l r => exact expand_exact l r a
  | rowLe l r => exact singleton_exact a _

def normalize (atoms : List (Atom α)) : List (Atom α) := atoms.flatMap atom

theorem normalize_exact (atoms : List (Atom α)) (a : α → Comp Common.model) :
    All Common.model a (normalize atoms) ↔ All Common.model a atoms := by
  induction atoms with
  | nil => simp [normalize]
  | cons x xs ih =>
    change All Common.model a (atom x ++ normalize xs) ↔ _
    rw [PresenceNormalForm.all_append, atom_exact, ih]
    simp [All]

/-- Constraints on a variable hidden in a pair become ordinary endpoint atoms. -/
theorem pair_variable_exposed (i : α) :
    normalize [.tyLe (.pair (.base .int) (.var i)) (.pair (.base .int) (.base .bool))] =
      [.tyLe (.base .int) (.base .int), .tyLe (.var i) (.base .bool)] := by
  rfl

/-- A constraint on that exposed variable can now participate in the existing checker. -/
def payloadProblem : List (Atom (Fin 1)) :=
  [.tyLe (.pair (.base .int) (.var 0)) (.pair (.base .int) (.base .bool)),
   .tyLe (.base .int) (.var 0)]

theorem payload_old_check_false : CommonRoleRecursivePaths.check payloadProblem = false := by
  decide

theorem payload_checked : CommonRoleRecursivePaths.check (normalize payloadProblem) = true := by
  decide

theorem payload_no_model (a : Fin 1 → Comp Common.model) :
    ¬ All Common.model a payloadProblem := by
  intro h
  exact CommonRoleRecursivePaths.checked_no_model_all _ payload_checked a
    ((normalize_exact _ a).mpr h)

end Yulang.CommonRoleStructuralDecomposition
