import Yulang.CommonEffectFormula

/-!
Finite quantifiers with independently sorted value and effect-row locals.
The captured assignment is retained literally, including every captured row.
Row locals are injected with an irrelevant unit value; the finite kind check
rejects reading this value in a value position. There are no semantic atoms.

This extends the syntax locally without changing the public Core or the
pre-existing value-only formula. Solving its universal binders is a separate
obligation; interpreting them does not supply a solver success condition.
-/
namespace Yulang.CommonEffectKindedFormula
open Core.PresenceGeneration
open CommonEffectRequestGeneration (Computation)

abbrev Names (types rows : Nat) := Fin types ⊕ Fin rows

structure Locals (types rows : Nat) where
  values : Fin types → Common.Ty
  effects : Fin rows → Common.Row

def localEnv (assignment : α → Computation) (locals : Locals types rows) :
    α ⊕ Names types rows → Computation
  | .inl name => assignment name
  | .inr (.inl name) => (locals.values name, Common.rowEmpty)
  | .inr (.inr name) => (.base .unit, locals.effects name)

@[simp] theorem localEnv_comp_inl (assignment : α → Computation) (locals : Locals types rows) :
    localEnv assignment locals ∘ Sum.inl = assignment := rfl

theorem localEnv_names (names : α → β) (assignment : β → Computation)
    (locals : Locals types rows) :
    localEnv assignment locals ∘ Sum.map names id = localEnv (assignment ∘ names) locals := by
  funext name
  cases name with
  | inl name => rfl
  | inr name => cases name <;> rfl

def rowWellKinded : RowTerm (α ⊕ Names types rows) → Bool
  | .var (.inl _) | .var (.inr (.inr _)) | .empty => true
  | .var (.inr (.inl _)) => false
  | .join first last => rowWellKinded first && rowWellKinded last

def typeWellKinded : TyTerm (α ⊕ Names types rows) → Bool
  | .var (.inr (.inr _)) => false
  | .var (.inl _) | .var (.inr (.inl _)) | .base _ | .bottom | .top |
      .emptyRecord | .exactEmpty => true
  | .union first last | .inter first last | .pair first last | .record _ first last |
      .recordDefault _ first last => typeWellKinded first && typeWellKinded last
  | .required _ value | .variant _ value => typeWellKinded value
  | .arrow input incoming output outgoing =>
      typeWellKinded input && rowWellKinded incoming && typeWellKinded output && rowWellKinded outgoing

def localEnvWith (assignment : α → Computation) (locals : Locals types rows)
    (placeholders : Fin rows → Common.Ty) : α ⊕ Names types rows → Computation
  | .inl name => assignment name
  | .inr (.inl name) => (locals.values name, Common.rowEmpty)
  | .inr (.inr name) => (placeholders name, locals.effects name)

theorem row_placeholder_irrelevant (assignment : α → Computation) (locals : Locals types rows)
    (placeholders : Fin rows → Common.Ty) (row : RowTerm (α ⊕ Names types rows)) :
    row.eval Common.model (localEnvWith assignment locals placeholders) =
      row.eval Common.model (localEnv assignment locals) := by
  induction row with
  | var name =>
    cases name with
    | inl name => rfl
    | inr name => cases name <;> rfl
  | empty => rfl
  | join first last ihFirst ihLast => simp only [RowTerm.eval, ihFirst, ihLast]

/-- A well-kinded term cannot observe the arbitrary value placeholder of a
row local, even through a nested arrow, default, mask-free record or union. -/
theorem type_placeholder_irrelevant (assignment : α → Computation) (locals : Locals types rows)
    (placeholders : Fin rows → Common.Ty) (value : TyTerm (α ⊕ Names types rows))
    (kinded : typeWellKinded value = true) :
    value.eval Common.model (localEnvWith assignment locals placeholders) =
      value.eval Common.model (localEnv assignment locals) := by
  induction value with
  | var name =>
    cases name with
    | inl name => rfl
    | inr name =>
      cases name with
      | inl name => rfl
      | inr name => simp [typeWellKinded] at kinded
  | _ => simp_all only [typeWellKinded, Bool.and_eq_true, TyTerm.eval, row_placeholder_irrelevant]

inductive Formula (scopes : Nat) : Type → Type 1 where
  | old : CommonEffectFormula.Formula scopes α → Formula scopes α
  | and : Formula scopes α → Formula scopes α → Formula scopes α
  | or : Formula scopes α → Formula scopes α → Formula scopes α
  | existsSlot : Formula scopes (Option α) → Formula scopes α
  | existsLocals : (types rows : Nat) → Formula scopes (α ⊕ Names types rows) → Formula scopes α
  | forallLocals : (types rows : Nat) → Formula scopes (α ⊕ Names types rows) → Formula scopes α

def Formula.Holds : {α : Type} → (α → Computation) → Formula scopes α → Prop
  | _, assignment, .old body => body.Holds assignment
  | _, assignment, .and first last => first.Holds assignment ∧ last.Holds assignment
  | _, assignment, .or first last => first.Holds assignment ∨ last.Holds assignment
  | _, assignment, .existsSlot body => ∃ value, body.Holds (extend assignment value)
  | _, assignment, .existsLocals _ _ body => ∃ locals, body.Holds (localEnv assignment locals)
  | _, assignment, .forallLocals _ _ body => ∀ locals, body.Holds (localEnv assignment locals)

def liftLocals (substitution : α → CompTerm β) :
    α ⊕ Names types rows → CompTerm (β ⊕ Names types rows)
  | .inl name => (substitution name).rename Sum.inl
  | .inr (.inl name) => CompTerm.pure (.var (.inr (.inl name)))
  | .inr (.inr name) => ⟨.base .unit, .var (.inr (.inr name))⟩

theorem liftLocals_eval (assignment : β → Computation) (substitution : α → CompTerm β)
    (locals : Locals types rows) :
    (fun name => (liftLocals substitution name).eval Common.model (localEnv assignment locals)) =
      localEnv (fun name => (substitution name).eval Common.model assignment) locals := by
  funext name
  cases name with
  | inl name => simp only [liftLocals, CompTerm.eval_rename, localEnv_comp_inl]; rfl
  | inr name => cases name <;> rfl

def Formula.subst (substitution : α → CompTerm β) : Formula scopes α → Formula scopes β
  | .old body => .old (body.subst substitution)
  | .and first last => .and (first.subst substitution) (last.subst substitution)
  | .or first last => .or (first.subst substitution) (last.subst substitution)
  | .existsSlot body => .existsSlot (body.subst (liftSubst substitution))
  | .existsLocals types rows body => .existsLocals types rows (body.subst (liftLocals substitution))
  | .forallLocals types rows body => .forallLocals types rows (body.subst (liftLocals substitution))

@[simp] theorem Formula.holds_subst (assignment : β → Computation) (substitution : α → CompTerm β)
    (formula : Formula scopes α) :
    (formula.subst substitution).Holds assignment ↔
      formula.Holds (fun name => (substitution name).eval Common.model assignment) := by
  induction formula generalizing β with
  | old body => exact CommonEffectFormula.Formula.holds_subst _ _ _
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
  | existsLocals types rows body ih => simp only [subst, Holds, ih, liftLocals_eval]
  | forallLocals types rows body ih => simp only [subst, Holds, ih, liftLocals_eval]

def Formula.rename (names : α → β) (formula : Formula scopes α) : Formula scopes β :=
  formula.subst (fun name => CompTerm.var (names name))

@[simp] theorem Formula.holds_rename (assignment : β → Computation) (names : α → β)
    (formula : Formula scopes α) :
    (formula.rename names).Holds assignment ↔ formula.Holds (assignment ∘ names) := by
  simp only [rename, holds_subst, CompTerm.eval_var]
  rfl

/-- A syntactic embedding, preserving every pre-existing type-only binder. -/
def ofOld : CommonEffectFormula.Formula scopes α → Formula scopes α := .old

theorem ofOld_exact (formula : CommonEffectFormula.Formula scopes α) (assignment : α → Computation) :
    (ofOld formula).Holds assignment ↔ formula.Holds assignment := Iff.rfl

/-- Value-only assignments are exactly the old local environments after the
finite name embedding. No row parameter is introduced when rows=0. -/
theorem value_only_env (assignment : α → Computation) (values : Fin types → Common.Ty) :
    localEnv assignment (Locals.mk values Fin.elim0) ∘ Sum.map id Sum.inl =
      CommonEffectRequestGeneration.localEnv assignment values := by
  funext name
  cases name <;> rfl

theorem value_locals_env (assignment : α → Computation) (locals : Locals types 0) :
    localEnv assignment locals ∘ Sum.map id Sum.inl =
      CommonEffectRequestGeneration.localEnv assignment locals.values := by
  funext name
  cases name <;> rfl

theorem value_only_exists_exact (body : CommonEffectFormula.Formula scopes (α ⊕ Fin types))
    (assignment : α → Computation) :
    (Formula.existsLocals types 0 (.old (body.rename (Sum.map id Sum.inl)))).Holds assignment ↔
      (CommonEffectFormula.Formula.existsTypes types body).Holds assignment := by
  simp only [Formula.Holds, CommonEffectFormula.Formula.holds_rename, value_locals_env,
    CommonEffectFormula.Formula.Holds]
  exact ⟨fun ⟨locals, accepted⟩ => ⟨locals.values, accepted⟩,
    fun ⟨values, accepted⟩ => ⟨⟨values, Fin.elim0⟩, accepted⟩⟩

theorem value_only_forall_exact (body : CommonEffectFormula.Formula scopes (α ⊕ Fin types))
    (assignment : α → Computation) :
    (Formula.forallLocals types 0 (.old (body.rename (Sum.map id Sum.inl)))).Holds assignment ↔
      (CommonEffectFormula.Formula.forallTypes types body).Holds assignment := by
  simp only [Formula.Holds, CommonEffectFormula.Formula.holds_rename, value_locals_env,
    CommonEffectFormula.Formula.Holds]
  exact ⟨fun accepted values => accepted ⟨values, Fin.elim0⟩,
    fun accepted locals => accepted locals.values⟩

end Yulang.CommonEffectKindedFormula
