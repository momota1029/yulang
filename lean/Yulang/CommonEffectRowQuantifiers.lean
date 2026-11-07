import Yulang.CommonEffectFormula

/-! Complete removal of local value-type quantifiers from the row-only finite
formula language. This includes nested computation existentials and signed
row actions. It does not split coupled value/row formulas into independent
parts or eliminate type comparisons from universal handlers. -/
namespace Yulang.CommonEffectRowQuantifiers
open Core.PresenceGeneration (Comp CompTerm RowTerm extend)
open CommonEffectRequestGeneration (Computation RowExpr localEnv)
open CommonEffectFormula

variable {scopes : Nat}

def coreRowOnly : Core.PresenceGeneration.Formula α → Bool
  | .top | .bot | .rowLe _ _ => true
  | .tyLe _ _ => false
  | .and first last | .or first last => coreRowOnly first && coreRowOnly last
  | .existsSlot body => coreRowOnly body

def rowOnly : Formula scopes α → Bool
  | .core body => coreRowOnly body
  | .rowLe _ _ => true
  | .and first last | .or first last => rowOnly first && rowOnly last
  | .existsSlot body => rowOnly body
  | .existsTypes _ body | .forallTypes _ body => rowOnly body

theorem rowTerm_congr (row : RowTerm α) (first last : α → Computation)
    (same : ∀ name, (first name).2 = (last name).2) :
    row.eval Common.model first = row.eval Common.model last := by
  induction row <;> simp_all [RowTerm.eval]

theorem rowExpr_congr (row : RowExpr scopes α) (first last : α → Computation)
    (same : ∀ name, (first name).2 = (last name).2) : row.eval first = row.eval last := by
  induction row <;> simp_all [RowExpr.eval]
  all_goals rfl

theorem extend_rows (first last : α → Computation) (value : Computation)
    (same : ∀ name, (first name).2 = (last name).2) :
    ∀ name, (extend first value name).2 = (extend last value name).2 := by
  intro name
  cases name with
  | none => rfl
  | some name => exact same name

theorem local_rows (first last : α → Computation) (types : Fin count → Common.Ty)
    (same : ∀ name, (first name).2 = (last name).2) :
    ∀ name, (localEnv first types name).2 = (localEnv last types name).2 := by
  intro name
  cases name with
  | inl name => exact same name
  | inr => rfl

theorem core_congr (formula : Core.PresenceGeneration.Formula α) (first last : α → Computation)
    (same : ∀ name, (first name).2 = (last name).2) (only : coreRowOnly formula = true) :
    formula.Holds Common.model first ↔ formula.Holds Common.model last := by
  induction formula with
  | top | bot => rfl
  | tyLe => cases only
  | rowLe a b =>
    simp only [Core.PresenceGeneration.Formula.Holds, rowTerm_congr a first last same, rowTerm_congr b first last same]
  | and a b iha ihb =>
    have both := Bool.and_eq_true_iff.mp only
    exact and_congr (iha first last same both.1) (ihb first last same both.2)
  | or a b iha ihb =>
    have both := Bool.and_eq_true_iff.mp only
    exact or_congr (iha first last same both.1) (ihb first last same both.2)
  | existsSlot body ih =>
    apply exists_congr
    intro value
    exact ih _ _ (extend_rows first last value same) only

theorem holds_congr (formula : Formula scopes α) (first last : α → Computation)
    (same : ∀ name, (first name).2 = (last name).2) (only : rowOnly formula = true) :
    formula.Holds first ↔ formula.Holds last := by
  induction formula with
  | core body => exact core_congr body first last same only
  | rowLe a b => simp only [Formula.Holds, rowExpr_congr a first last same, rowExpr_congr b first last same]
  | and a b iha ihb =>
    have both := Bool.and_eq_true_iff.mp only
    exact and_congr (iha first last same both.1) (ihb first last same both.2)
  | or a b iha ihb =>
    have both := Bool.and_eq_true_iff.mp only
    exact or_congr (iha first last same both.1) (ihb first last same both.2)
  | existsSlot body ih =>
    apply exists_congr
    intro value
    exact ih _ _ (extend_rows first last value same) only
  | existsTypes count body ih =>
    apply exists_congr
    intro types
    exact ih _ _ (local_rows first last types same) only
  | forallTypes count body ih =>
    apply forall_congr'
    intro types
    exact ih _ _ (local_rows first last types same) only

/-- Substitute finite syntax for all locals. Its row is empty regardless of
which value types are chosen in the original universal interpretation. -/
def project : α ⊕ Fin count → CompTerm α
  | .inl name => CompTerm.var name
  | .inr _ => CompTerm.pure .top

theorem project_eval (assignment : α → Computation) :
    (fun name : α ⊕ Fin count => (project name).eval Common.model assignment) =
      localEnv assignment (fun _ => .top) := by
  funext name
  cases name <;> rfl

theorem type_assignment_irrelevant (formula : Formula scopes (α ⊕ Fin count))
    (only : rowOnly formula = true) (assignment : α → Computation)
    (types : Fin count → Common.Ty) :
    formula.Holds (localEnv assignment types) ↔ formula.Holds (localEnv assignment (fun _ => .top)) := by
  apply holds_congr formula _ _ _ only
  intro name
  cases name <;> rfl

def eliminate : Formula scopes α → Formula scopes α
  | .core body => .core body
  | .rowLe first last => .rowLe first last
  | .and first last => .and (eliminate first) (eliminate last)
  | .or first last => .or (eliminate first) (eliminate last)
  | .existsSlot body => .existsSlot (eliminate body)
  | .existsTypes _ body => (eliminate body).subst project
  | .forallTypes _ body => (eliminate body).subst project

/-- Every row-only formula, every ambient assignment, arbitrary rows and all
nested binders. Local quantification is discharged by this computation. -/
theorem eliminate_exact (formula : Formula scopes α) (assignment : α → Computation)
    (only : rowOnly formula = true) : (eliminate formula).Holds assignment ↔ formula.Holds assignment := by
  induction formula with
  | core | rowLe => rfl
  | and a b iha ihb =>
    have both := Bool.and_eq_true_iff.mp only
    exact and_congr (iha assignment both.1) (ihb assignment both.2)
  | or a b iha ihb =>
    have both := Bool.and_eq_true_iff.mp only
    exact or_congr (iha assignment both.1) (ihb assignment both.2)
  | existsSlot body ih =>
    apply exists_congr
    intro value
    exact ih _ only
  | existsTypes count body ih =>
    simp only [eliminate, Formula.holds_subst, project_eval, ih _ only, Formula.Holds]
    constructor
    · intro holds
      exact ⟨fun _ => .top, holds⟩
    · rintro ⟨types, holds⟩
      exact (type_assignment_irrelevant body only assignment types).mp holds
  | forallTypes count body ih =>
    simp only [eliminate, Formula.holds_subst, project_eval, ih _ only, Formula.Holds]
    exact ⟨fun holds types => (type_assignment_irrelevant body only assignment types).mpr holds,
      fun all => all (fun _ => .top)⟩
/-- Core formulas contain no local type binders; their computation binders
are deliberately retained by the elimination. -/
def typeBinders : Formula scopes α → Nat
  | .core _ | .rowLe _ _ => 0
  | .and first last | .or first last => typeBinders first + typeBinders last
  | .existsSlot body => typeBinders body
  | .existsTypes _ body | .forallTypes _ body => typeBinders body + 1

theorem typeBinders_subst (formula : Formula scopes α) (substitution : α → CompTerm β) :
    typeBinders (formula.subst substitution) = typeBinders formula := by
  induction formula generalizing β <;> simp_all [Formula.subst, typeBinders]

/-- The computed output has no hidden forallTypes or existsTypes. -/
theorem eliminate_no_type_binders (formula : Formula scopes α) : typeBinders (eliminate formula) = 0 := by
  induction formula <;> simp_all [eliminate, typeBinders, typeBinders_subst]
end Yulang.CommonEffectRowQuantifiers
