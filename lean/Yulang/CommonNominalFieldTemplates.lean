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

inductive TemplateRow (rows : Nat) where
  | var : Fin rows → TemplateRow rows
  | empty : TemplateRow rows
  | heads : List Common.Occurrence → TemplateRow rows
  | join : TemplateRow rows → TemplateRow rows → TemplateRow rows

def TemplateRow.eval (arguments : Fin rows → Row) : TemplateRow rows → Row
  | .var index => arguments index
  | .empty => Common.rowEmpty
  | .heads occurrences => fun occurrence => occurrence ∈ occurrences
  | .join first last => Common.rowJoin (first.eval arguments) (last.eval arguments)

/-- Signed literal heads remain concrete finite syntax; arbitrary row
parameters remain arbitrary occurrence sets. -/
@[simp] theorem TemplateRow.heads_eval (arguments : Fin rows → Row)
    (occurrences : List Common.Occurrence) (occurrence : Common.Occurrence) :
    (TemplateRow.heads occurrences).eval arguments occurrence ↔ occurrence ∈ occurrences := Iff.rfl

def rowsLayer (rows : Fin count → Row) :
    CommonNominalSyntax.Layer (TemplateRow count) Index → CommonNominalSyntax.Layer Row Index
  | .base scalar => .base scalar
  | .float => .float
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (rowsLayer rows first) (rowsLayer rows last)
  | .inter first last => .inter (rowsLayer rows first) (rowsLayer rows last)
  | .pair first last => .pair first last
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label payload rest => .record label payload (rowsLayer rows rest)
  | .recordDefault label source fallback => .recordDefault label (rowsLayer rows source) fallback
  | .variant label payload => .variant label payload
  | .arrow input incoming output outgoing => .arrow input (incoming.eval rows) output (outgoing.eval rows)
  | .mask hidden source => .mask hidden (rowsLayer rows source)
  | .nominal name arguments => .nominal name (arguments.map (Sum.map id (TemplateRow.eval rows)))

/-- Whole shared parameters may occur in positive same-depth positions,
including union/intersection, record tails, masks and default sources.
Internal graph references occur only at the original guarded payload sites. -/
inductive Body (nodes types rows : Nat) where
  | parameter : Fin types → Body nodes types rows
  | base : Inference.Base → Body nodes types rows
  | float : Body nodes types rows
  | bottom : Body nodes types rows
  | top : Body nodes types rows
  | union : Body nodes types rows → Body nodes types rows → Body nodes types rows
  | inter : Body nodes types rows → Body nodes types rows → Body nodes types rows
  | pair : (Fin nodes ⊕ Fin types) → (Fin nodes ⊕ Fin types) → Body nodes types rows
  | emptyRecord : Body nodes types rows
  | exactEmpty : Body nodes types rows
  | record : Nat → (Fin nodes ⊕ Fin types) → Body nodes types rows → Body nodes types rows
  | recordDefault : Nat → Body nodes types rows → (Fin nodes ⊕ Fin types) → Body nodes types rows
  | variant : Nat → (Fin nodes ⊕ Fin types) → Body nodes types rows
  | arrow : (Fin nodes ⊕ Fin types) → TemplateRow rows → (Fin nodes ⊕ Fin types) → TemplateRow rows → Body nodes types rows
  | mask : List Nat → Body nodes types rows → Body nodes types rows
  | nominal : Nat → List ((Fin nodes ⊕ Fin types) ⊕ TemplateRow rows) → Body nodes types rows

def reference (arguments : Fin types → Ty) : Fin nodes ⊕ Fin types → Fin nodes ⊕ CommonNominalSyntax.State Row :=
  Sum.map id (fun index => CommonNominalSyntax.State.node (arguments index))

def Body.instantiate (arguments : Fin types → Ty) (rows : Fin rowCount → Row) :
    Body nodes types rowCount → CommonNominalSyntax.Layer Row (Fin nodes ⊕ CommonNominalSyntax.State Row)
  | .parameter index => (arguments index).map Sum.inr
  | .base scalar => .base scalar
  | .float => .float
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (first.instantiate arguments rows) (last.instantiate arguments rows)
  | .inter first last => .inter (first.instantiate arguments rows) (last.instantiate arguments rows)
  | .pair first last => .pair (reference arguments first) (reference arguments last)
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label payload tail => .record label (reference arguments payload) (tail.instantiate arguments rows)
  | .recordDefault label source fallback => .recordDefault label (source.instantiate arguments rows) (reference arguments fallback)
  | .variant label payload => .variant label (reference arguments payload)
  | .arrow input incoming output outgoing => .arrow (reference arguments input) (incoming.eval rows)
      (reference arguments output) (outgoing.eval rows)
  | .mask hidden source => .mask hidden (source.instantiate arguments rows)
  | .nominal name arguments' => .nominal name (arguments'.map (Sum.map (reference arguments) (TemplateRow.eval rows)))

def Body.ofLayer : CommonNominalSyntax.Layer (TemplateRow rows) (Fin nodes ⊕ Fin types) → Body nodes types rows
  | .base scalar => .base scalar
  | .float => .float
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (ofLayer first) (ofLayer last)
  | .inter first last => .inter (ofLayer first) (ofLayer last)
  | .pair first last => .pair first last
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label payload tail => .record label payload (ofLayer tail)
  | .recordDefault label source fallback => .recordDefault label (ofLayer source) fallback
  | .variant label payload => .variant label payload
  | .arrow input incoming output outgoing => .arrow input incoming output outgoing
  | .mask hidden source => .mask hidden (ofLayer source)
  | .nominal name arguments => .nominal name arguments

theorem of_layer_instantiate (arguments : Fin types → Ty) (rows : Fin rowCount → Row)
    (layer : CommonNominalSyntax.Layer (TemplateRow rowCount) (Fin nodes ⊕ Fin types)) :
    (Body.ofLayer layer).instantiate arguments rows = (rowsLayer rows layer).map (reference arguments) := by
  induction layer <;> simp_all [Body.ofLayer, Body.instantiate, rowsLayer, CommonNominalSyntax.Layer.map]

structure Template (types rows : Nat) where
  nodes : Nat
  body : Fin nodes → Body nodes types rows
  root : Fin nodes ⊕ Fin types

def Template.eval (template : Template types rows) (arguments : Fin types → Ty)
    (rowArguments : Fin rows → Row) : Ty :=
  match template.root with
  | .inl node => CommonNominalSyntax.graph Row (CommonNominalSyntax.closeBlock
      (fun index => (template.body index).instantiate arguments rowArguments) node)
  | .inr parameter => arguments parameter

def Template.parameter (index : Fin types) : Template types rows :=
  ⟨0, Fin.elim0, .inr index⟩

@[simp] theorem parameter_eval (index : Fin types) (arguments : Fin types → Ty)
    (rowArguments : Fin rows → Row) :
    (Template.parameter index).eval arguments rowArguments = arguments index := rfl

def Template.ofLayers (body : Fin nodeCount → CommonNominalSyntax.Layer (TemplateRow rows) (Fin nodeCount ⊕ Fin types))
    (root : Fin nodeCount ⊕ Fin types) : Template types rows :=
  ⟨nodeCount, fun index => Body.ofLayer (body index), root⟩

/-- The earlier layer-only template grammar embeds with exactly its original
regular interpretation; whole-parameter support adds no observation delay. -/
theorem old_layer_template_eval (body : Fin nodes → CommonNominalSyntax.Layer (TemplateRow rows) (Fin nodes ⊕ Fin types))
    (root : Fin nodes ⊕ Fin types) (arguments : Fin types → Ty) (rowArguments : Fin rows → Row) :
    (Template.ofLayers body root).eval arguments rowArguments =
      match root with
      | .inl index => CommonNominalGuardedClosure.instantiate (fun index => rowsLayer rowArguments (body index)) arguments index
      | .inr parameter => arguments parameter := by
  cases root with
  | inr parameter => rfl
  | inl index =>
      simp only [Template.ofLayers, Template.eval, of_layer_instantiate, reference,
        CommonNominalGuardedClosure.instantiate, CommonNominalGuardedClosure.node]
      rfl

def Template.unionParameters (first last : Fin types) : Template types rows :=
  ⟨1, fun _ => .union (.parameter first) (.parameter last), .inl 0⟩

theorem union_parameters_eval (first last : Fin types) (arguments : Fin types → Ty) (rowArguments : Fin rows → Row) :
    (Template.unionParameters first last).eval arguments rowArguments = .union (arguments first) (arguments last) := by
  simp [Template.unionParameters, Template.eval, Body.instantiate, CommonNominalSyntax.graph_closeBlock,
    CommonNominalSyntax.Layer.map, CommonNominalSyntax.Layer.map_comp, CommonNominalSyntax.blockRef, Function.comp_def]
  exact ⟨CommonNominalSyntax.Layer.map_id _, CommonNominalSyntax.Layer.map_id _⟩

def Template.maskedParameter (hidden : List Nat) (index : Fin types) : Template types rows :=
  ⟨1, fun _ => .mask hidden (.parameter index), .inl 0⟩

theorem masked_parameter_eval (hidden : List Nat) (index : Fin types) (arguments : Fin types → Ty) (rowArguments : Fin rows → Row) :
    (Template.maskedParameter hidden index).eval arguments rowArguments = .mask hidden (arguments index) := by
  simp [Template.maskedParameter, Template.eval, Body.instantiate, CommonNominalSyntax.graph_closeBlock,
    CommonNominalSyntax.Layer.map, CommonNominalSyntax.Layer.map_comp, CommonNominalSyntax.blockRef, Function.comp_def]
  exact CommonNominalSyntax.Layer.map_id _

def Template.defaultParameters (label : Nat) (source fallback : Fin types) : Template types rows :=
  ⟨1, fun _ => .recordDefault label (.parameter source) (.inr fallback), .inl 0⟩

theorem default_parameters_eval (label : Nat) (source fallback : Fin types) (arguments : Fin types → Ty)
    (rowArguments : Fin rows → Row) :
    (Template.defaultParameters label source fallback).eval arguments rowArguments =
      recordDefault label (arguments source) (arguments fallback) := by
  simp [Template.defaultParameters, Template.eval, Body.instantiate, CommonNominalSyntax.graph_closeBlock,
    CommonNominalSyntax.Layer.map, CommonNominalSyntax.Layer.map_comp, CommonNominalSyntax.blockRef, reference,
    recordDefault, Function.comp_def]
  exact CommonNominalSyntax.Layer.map_id _

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
