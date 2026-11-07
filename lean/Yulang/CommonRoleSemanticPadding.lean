import Yulang.CheckedRoles
import Yulang.CommonBoundCoalescing

/-!
# Raw Paterson checks and semantically redundant union heads

The finite binary-tree patterns here contain variables, unit and pair. An
actual `Roles.Impl` is formed by repeating its source pattern under union.
This increases the raw size and occurrence counts checked by `checkImpl`.
The subsequent Common interpretation treats that union by the existing demand
semantics, where repeating a type does not change its meaning.

This exposes a reduction mechanism, not yet an impossibility theorem for A2.
It does not replace raw declaration validation by validation after normalization.
-/

namespace Yulang.CommonRoleSemanticPadding

inductive Pattern where
  | var : Nat → Pattern
  | nil : Pattern
  | pair : Pattern → Pattern → Pattern
  deriving DecidableEq, Repr

def Pattern.weight : Pattern → Nat
  | .var _ | .nil => 1
  | .pair first last => 1 + first.weight + last.weight

def Pattern.occurrences (name : Nat) : Pattern → Nat
  | .var index => if name = index then 1 else 0
  | .nil => 0
  | .pair first last => first.occurrences name + last.occurrences name

/-- IDs 0/1/2 denote unit/pair/union in the interpreter below. -/
def Pattern.toTerm : Pattern → Roles.Term
  | .var index => .var index
  | .nil => .app 0 []
  | .pair first last => .app 1 [first.toTerm, last.toTerm]

def padded : Nat → Roles.Term → Roles.Term
  | 0, source => source
  | count + 1, source => .app 2 [source, padded count source]

def declaration (source target : Pattern) (identity : Nat) : Roles.Impl :=
  ⟨0, [padded (target.weight + 1) source.toTerm], [⟨0, [target.toTerm]⟩], identity⟩

def RangeRestricted (source target : Pattern) : Prop :=
  ∀ name, source.occurrences name = 0 → target.occurrences name = 0

def Pattern.eval (assignment : Nat → Common.Ty) : Pattern → Common.Ty
  | .var name => assignment name
  | .nil => .base .unit
  | .pair first last => Common.pair (first.eval assignment) (last.eval assignment)

/-- A fixed constructor interpretation, not an arbitrary decoder. Unknown
constructor IDs and malformed arities are rejected. -/
def interpret (assignment : Nat → Common.Ty) : Roles.Term → Option Common.Ty
  | .var name => some (assignment name)
  | .app 0 [] => some (.base .unit)
  | .app 1 [first, last] => do
      return Common.pair (← interpret assignment first) (← interpret assignment last)
  | .app 2 [first, last] => do
      return .union (← interpret assignment first) (← interpret assignment last)
  | .app _ _ => none

/-- Every range-restricted binary-tree rewrite is admitted by the *existing*
raw checker after finite union padding. Target duplication is unrestricted. -/
theorem padded_declaration_accepted (source target : Pattern) (identity : Nat)
    (closed : RangeRestricted source target) :
    CheckedRoles.checkImpl (declaration source target identity) = true := by
  have sizes (pattern : Pattern) : pattern.toTerm.size = pattern.weight := by
    induction pattern <;> simp_all [Pattern.toTerm, Pattern.weight, Roles.Term.size,
      Roles.argsSize, Nat.add_assoc]
  have occurrences (pattern : Pattern) (name : Nat) :
      pattern.toTerm.occurrences name = pattern.occurrences name := by
    induction pattern <;> simp_all [Pattern.toTerm, Pattern.occurrences,
      Roles.Term.occurrences, Roles.argsOccurrences]
  have bounded (pattern : Pattern) (name : Nat) :
      pattern.occurrences name ≤ pattern.weight := by
    induction pattern with
    | var index => simp [Pattern.occurrences, Pattern.weight]; split <;> omega
    | nil => simp [Pattern.occurrences, Pattern.weight]
    | pair first last ihf ihl => simp only [Pattern.occurrences, Pattern.weight]; omega
  have sizePadding (count : Nat) (term : Roles.Term) :
      (padded count term).size = (count + 1) * term.size + count := by
    induction count with
    | zero => simp [padded]
    | succ count ih =>
        simp only [padded, Roles.Term.size, Roles.argsSize, Nat.add_zero, ih]
        simp only [Nat.add_mul, Nat.one_mul]
        omega
  have occurrencePadding (count : Nat) (term : Roles.Term) (name : Nat) :
      (padded count term).occurrences name = (count + 1) * term.occurrences name := by
    induction count with
    | zero => simp [padded]
    | succ count ih =>
        simp only [padded, Roles.Term.occurrences, Roles.argsOccurrences, Nat.add_zero, ih]
        simp only [Nat.add_mul, Nat.one_mul]
        omega
  apply (CheckedRoles.checkImpl_exact _).mpr
  intro child member
  have childSame : child = ⟨0, [target.toTerm]⟩ := by simpa [declaration] using member
  subst child
  constructor
  · simp only [declaration, Roles.argsSize, Nat.add_zero, sizePadding, sizes]
    omega
  · intro name
    simp only [declaration, Roles.argsOccurrences, Nat.add_zero, occurrencePadding, occurrences]
    by_cases absent : source.occurrences name = 0
    · simp [absent, closed name absent]
    · have positive : 1 ≤ source.occurrences name := by omega
      have large := Nat.mul_le_mul_left (target.weight + 1 + 1) positive
      have bound := bounded target name
      omega

/-- Every amount of raw padding preserves the independently interpreted
Common head for all assignments, including arbitrary regular types and rows. -/
theorem padded_head_exact (count : Nat) (source : Pattern) (assignment : Nat → Common.Ty) :
    ∃ head, interpret assignment (padded count source.toTerm) = some head ∧
      Common.Equivalent head (source.eval assignment) := by
  have ordinary : interpret assignment source.toTerm = some (source.eval assignment) := by
    induction source <;> simp_all [Pattern.toTerm, Pattern.eval, interpret]
  induction count with
  | zero => exact ⟨source.eval assignment, ordinary, Common.equivalent_refl _⟩
  | succ count ih =>
      obtain ⟨head, evaluated, same⟩ := ih
      refine ⟨.union (source.eval assignment) head, ?_, ?_⟩
      · simp [padded, interpret, ordinary, evaluated]
      · exact ⟨(Common.common_union_is_join _ _ _).mpr ⟨Common.subtype_refl _, same.1⟩,
          CommonBoundCoalescing.le_union_left _ _⟩

end Yulang.CommonRoleSemanticPadding
