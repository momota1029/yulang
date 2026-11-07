import Yulang.CommonNominalGuardedRowSolver
import Yulang.CorePresenceGenerationExact

/-!
# Finite regular field templates with shared invariant arguments

A resolved field template is a finite mixed constructor graph with a node or
parameter root. Every field in a declaration can refer to the same type and row
parameter vector, including several different parameters within one field.
Fixed fields are the parameter-free special case. This syntax does not choose
declaration lookup, implicit cast policy or weak-parameter finalization.
-/

namespace Yulang.CommonNominalFieldTemplates

open CommonNominalCarrier
open Core.PresenceGeneration (Comp TyTerm RowTerm extend)

structure Template (types rows : Nat) where
  nodes : Nat
  body : Fin nodes → CommonNominalSyntax.Layer (RowTerm (Fin rows)) (Fin nodes ⊕ Fin types)
  root : Fin nodes ⊕ Fin types

def Template.eval (template : Template types rows) (arguments : Fin types → Ty)
    (rowArguments : Fin rows → Row) : Ty :=
  match template.root with
  | .inl node => CommonNominalGuardedClosure.instantiate
      (fun index => CommonNominalGuardedRowSolver.rowsLayer rowArguments (template.body index)) arguments node
  | .inr parameter => arguments parameter

def Template.parameter (index : Fin types) : Template types rows :=
  ⟨0, Fin.elim0, .inr index⟩

@[simp] theorem parameter_eval (index : Fin types) (arguments : Fin types → Ty)
    (rowArguments : Fin rows → Row) :
    (Template.parameter index).eval arguments rowArguments = arguments index := rfl

/-- Finite symbolic applications retain every shared parameter occurrence.
The regular graph itself is syntax, not a residual model proof. -/
inductive Term (α : Type) where
  | ordinary : TyTerm α → Term α
  | template {types rows : Nat} : Template types rows →
      (Fin types → TyTerm α) → (Fin rows → RowTerm α) → Term α

def Term.eval (assignment : α → Comp model) : Term α → Ty
  | .ordinary type => type.eval model assignment
  | .template fieldTemplate arguments rows =>
      fieldTemplate.eval (fun index => (arguments index).eval model assignment)
        (fun index => (rows index).eval model assignment)

def Term.rename (rename : α → β) : Term α → Term β
  | .ordinary type => .ordinary (type.rename rename)
  | .template fieldTemplate arguments rows => .template fieldTemplate
      (fun index => (arguments index).rename rename) (fun index => (rows index).rename rename)

@[simp] theorem Term.eval_rename (assignment : β → Comp model) (rename : α → β) (term : Term α) :
    (term.rename rename).eval assignment = term.eval (assignment ∘ rename) := by
  cases term <;> simp only [Term.rename, Term.eval, TyTerm.eval_rename, RowTerm.eval_rename] <;> rfl

inductive Formula : Type → Type 1 where
  | ordinary : Core.PresenceGeneration.Formula α → Formula α
  | tyLe : Term α → Term α → Formula α
  | and : Formula α → Formula α → Formula α
  | or : Formula α → Formula α → Formula α
  | existsSlot : Formula (Option α) → Formula α

def Formula.Models : {α : Type} → (α → Comp model) → Formula α → Prop
  | _, assignment, .ordinary formula => formula.Holds model assignment
  | _, assignment, .tyLe first last => CommonNominalCarrier.Subtype (first.eval assignment) (last.eval assignment)
  | _, assignment, .and first last => first.Models assignment ∧ last.Models assignment
  | _, assignment, .or first last => first.Models assignment ∨ last.Models assignment
  | _, assignment, .existsSlot body => ∃ fresh, body.Models (extend assignment fresh)

def Formula.rename (rename : α → β) : Formula α → Formula β
  | .ordinary formula => .ordinary (formula.rename rename)
  | .tyLe first last => .tyLe (first.rename rename) (last.rename rename)
  | .and first last => .and (first.rename rename) (last.rename rename)
  | .or first last => .or (first.rename rename) (last.rename rename)
  | .existsSlot body => .existsSlot (body.rename (Option.map rename))

@[simp] theorem Formula.models_rename (assignment : β → Comp model) (rename : α → β) (formula : Formula α) :
    (formula.rename rename).Models assignment ↔ formula.Models (assignment ∘ rename) := by
  induction formula generalizing β with
  | ordinary formula => exact Core.PresenceGeneration.Formula.holds_rename model formula rename assignment
  | tyLe first last => simp only [Formula.rename, Models, Term.eval_rename]
  | and first last ihf ihl => simp only [Formula.rename, Models, ihf, ihl]
  | or first last ihf ihl => simp only [Formula.rename, Models, ihf, ihl]
  | existsSlot body ih =>
      simp only [Formula.rename, Models, ih]
      apply exists_congr
      intro fresh
      have same : extend assignment fresh ∘ Option.map rename = extend (assignment ∘ rename) fresh := by
        funext index
        cases index <;> rfl
      rw [same]

def Formula.all (formulas : List (Formula α)) : Formula α :=
  formulas.foldr .and (.ordinary .top)

def Formula.any (formulas : List (Formula α)) : Formula α :=
  formulas.foldr .or (.ordinary .bot)

@[simp] theorem Formula.models_all (assignment : α → Comp model) (formulas : List (Formula α)) :
    (Formula.all formulas).Models assignment ↔ ∀ formula ∈ formulas, formula.Models assignment := by
  induction formulas <;> simp_all [Formula.all, Formula.Models, Core.PresenceGeneration.Formula.Holds]

@[simp] theorem Formula.models_any (assignment : α → Comp model) (formulas : List (Formula α)) :
    (Formula.any formulas).Models assignment ↔ ∃ formula ∈ formulas, formula.Models assignment := by
  induction formulas <;> simp_all [Formula.any, Formula.Models, Core.PresenceGeneration.Formula.Holds]

def Formula.tyEq (first last : Term α) : Formula α := .and (.tyLe first last) (.tyLe last first)

@[simp] theorem Formula.models_tyEq (assignment : α → Comp model) (first last : Term α) :
    (Formula.tyEq first last).Models assignment ↔ Equivalent (first.eval assignment) (last.eval assignment) := Iff.rfl

end Yulang.CommonNominalFieldTemplates
