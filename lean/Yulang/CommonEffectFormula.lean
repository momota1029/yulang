import Yulang.CommonEffectRequestGeneration

/-!
# Finite signed formulas with captured schemes and type binders

Renaming/substitution are capture avoiding under computation and local value
binders. Neither a semantic predicate nor a Typing judgment is an atom.
-/
namespace Yulang.CommonEffectFormula
open Core.PresenceGeneration
open CommonEffectRequestGeneration (Computation Permission RowExpr localEnv)

variable {scopes : Nat}

def RowExpr.subst (substitution : α → RowExpr scopes β) : RowExpr scopes α → RowExpr scopes β
  | .var name => substitution name
  | .empty => .empty
  | .head key => .head key
  | .union first last => .union (subst substitution first) (subst substitution last)
  | .protect scope permission row => .protect scope permission (subst substitution row)
  | .release scope permission row => .release scope permission (subst substitution row)
  | .residual keys row => .residual keys (subst substitution row)

def rowSubst (substitution : α → CompTerm β) : RowExpr scopes α → RowExpr scopes β :=
  RowExpr.subst (fun name => RowExpr.fromPresence (substitution name).row)

theorem rowSubst_eval (assignment : β → Computation) (substitution : α → CompTerm β)
    (row : RowExpr scopes α) :
    (rowSubst substitution row).eval assignment = row.eval (fun name => (substitution name).eval Common.model assignment) := by
  induction row <;> simp_all [rowSubst, RowExpr.subst, RowExpr.eval, CompTerm.eval]
  all_goals rfl

/-- Local types have value kind and are injected with empty rows. -/
def liftTypes (substitution : α → CompTerm β) : α ⊕ Fin count → CompTerm (β ⊕ Fin count)
  | .inl name => (substitution name).rename Sum.inl
  | .inr name => CompTerm.pure (.var (.inr name))

theorem liftTypes_eval (assignment : β → Computation) (substitution : α → CompTerm β)
    (locals : Fin count → Common.Ty) :
    (fun name => (liftTypes substitution name).eval Common.model (localEnv assignment locals)) =
      localEnv (fun name => (substitution name).eval Common.model assignment) locals := by
  funext name
  cases name with
  | inl name => simp [liftTypes, CompTerm.eval_rename, localEnv]
  | inr name => rfl

inductive Formula (scopes : Nat) : Type → Type 1 where
  | core : Core.PresenceGeneration.Formula α → Formula scopes α
  | rowLe : RowExpr scopes α → RowExpr scopes α → Formula scopes α
  | and : Formula scopes α → Formula scopes α → Formula scopes α
  | or : Formula scopes α → Formula scopes α → Formula scopes α
  | existsSlot : Formula scopes (Option α) → Formula scopes α
  | existsTypes : (count : Nat) → Formula scopes (α ⊕ Fin count) → Formula scopes α
  | forallTypes : (count : Nat) → Formula scopes (α ⊕ Fin count) → Formula scopes α

def Formula.Holds : {α : Type} → (α → Computation) → Formula scopes α → Prop
  | _, assignment, .core body => body.Holds Common.model assignment
  | _, assignment, .rowLe first last => Common.rowLe (first.eval assignment) (last.eval assignment)
  | _, assignment, .and first last => first.Holds assignment ∧ last.Holds assignment
  | _, assignment, .or first last => first.Holds assignment ∨ last.Holds assignment
  | _, assignment, .existsSlot body => ∃ value, body.Holds (extend assignment value)
  | _, assignment, .existsTypes _ body => ∃ locals, body.Holds (localEnv assignment locals)
  | _, assignment, .forallTypes _ body => ∀ locals, body.Holds (localEnv assignment locals)

def Formula.subst (substitution : α → CompTerm β) : Formula scopes α → Formula scopes β
  | .core body => .core (body.subst substitution)
  | .rowLe first last => .rowLe (rowSubst substitution first) (rowSubst substitution last)
  | .and first last => .and (first.subst substitution) (last.subst substitution)
  | .or first last => .or (first.subst substitution) (last.subst substitution)
  | .existsSlot body => .existsSlot (body.subst (liftSubst substitution))
  | .existsTypes count body => .existsTypes count (body.subst (liftTypes substitution))
  | .forallTypes count body => .forallTypes count (body.subst (liftTypes substitution))

@[simp] theorem Formula.holds_subst (assignment : β → Computation) (substitution : α → CompTerm β)
    (formula : Formula scopes α) :
    (formula.subst substitution).Holds assignment ↔
      formula.Holds (fun name => (substitution name).eval Common.model assignment) := by
  induction formula generalizing β with
  | core body => exact Core.PresenceGeneration.Formula.holds_subst _ _ _ _
  | rowLe first last => simp only [subst, Holds, rowSubst_eval]
  | and first last firstIH lastIH => simp only [subst, Holds, firstIH, lastIH]
  | or first last firstIH lastIH => simp only [subst, Holds, firstIH, lastIH]
  | existsSlot body ih =>
    simp only [subst, Holds, ih]
    apply exists_congr
    intro value
    have same : (fun name => (liftSubst substitution name).eval Common.model (extend assignment value)) =
        extend (fun name => (substitution name).eval Common.model assignment) value := by
      funext name
      cases name <;> simp [liftSubst]
    rw [same]
  | existsTypes count body ih =>
    simp only [subst, Holds, ih, liftTypes_eval]
  | forallTypes count body ih =>
    simp only [subst, Holds, ih, liftTypes_eval]

def Formula.rename (names : α → β) (formula : Formula scopes α) : Formula scopes β :=
  formula.subst (fun name => CompTerm.var (names name))

@[simp] theorem Formula.holds_rename (assignment : β → Computation) (names : α → β)
    (formula : Formula scopes α) :
    (formula.rename names).Holds assignment ↔ formula.Holds (assignment ∘ names) := by
  simp only [rename, holds_subst, CompTerm.eval_var]
  rfl

abbrev Scheme (scopes : Nat) (α : Type) := Formula scopes (Option α)
abbrev SchemeEnv (scopes : Nat) (α : Type) := List (Scheme scopes α)

def Scheme.instantiate (scheme : Scheme scopes α) (out : CompTerm α) : Formula scopes α :=
  scheme.subst (fun | none => out | some name => CompTerm.var name)

@[simp] theorem Scheme.instantiate_exact (scheme : Scheme scopes α) (out : CompTerm α)
    (assignment : α → Computation) :
    (scheme.instantiate out).Holds assignment ↔ scheme.Holds (extend assignment (out.eval Common.model assignment)) := by
  simp only [instantiate, Formula.holds_subst]
  have same : (fun name => ((fun | none => out | some name => CompTerm.var name) name).eval Common.model assignment) =
      extend assignment (out.eval Common.model assignment) := by
    funext name
    cases name <;> rfl
  exact (congrArg (fun env => scheme.Holds env) same).to_iff

/-- The old finite request/handler constraints embed without semantic leaves. -/
def ofConstraint : CommonEffectRequestGeneration.Constraint scopes α → Formula scopes α
  | .core body => .core body
  | .rowLe first last => .rowLe first last
  | .and first last => .and (ofConstraint first) (ofConstraint last)
  | .existsSlot body => .existsSlot (ofConstraint body)
  | .existsTypes count body => .existsTypes count (ofConstraint body)
  | .forallTypes count body => .forallTypes count (ofConstraint body)

@[simp] theorem ofConstraint_exact (assignment : α → Computation)
    (constraint : CommonEffectRequestGeneration.Constraint scopes α) :
    (ofConstraint constraint).Holds assignment ↔ constraint.Holds assignment := by
  induction constraint <;> simp_all only [ofConstraint, Formula.Holds,
    CommonEffectRequestGeneration.Constraint.Holds]
end Yulang.CommonEffectFormula
