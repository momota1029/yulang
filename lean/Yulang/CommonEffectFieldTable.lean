import Yulang.CommonEffectFieldInstances

/-!
Finite resolved field tables retain each field's own value and row binders.
Construction checks all original field bodies, rejecting a length mismatch,
and retains the local binders for fresh projection at each occurrence. Field
positions and names are already resolved. This is a pure-construction bridge,
not nominal subtyping, runtime representation, or source name resolution.
-/
namespace Yulang.CommonEffectFieldTable
open Core.PresenceGeneration (Comp CompTerm)
open CommonEffectRequestGeneration (Computation Declarations)
open CommonEffectKindedFormula
open CommonEffectKindedGeneration
open CommonEffectRecursiveSource
open CommonEffectRecursiveGeneration (ContextRel)

variable {scopes : Nat}

structure Field (α : Type) where
  name : Nat
  scheme : FieldScheme α

structure Declaration (α : Type) where
  name : Nat
  fields : List (Field α)

def FieldTyping (signatures : List SemanticSignature) (bindings : List (Binding scopes))
    (assignment : α → Computation) (field : Field α) (body : Expr scopes) : Prop :=
  field.scheme.wellKinded = true ∧
    ∀ locals : Locals field.scheme.types field.scheme.rows,
      Typing signatures bindings body
        (Comp.pure Common.model (field.scheme.body.eval Common.model (localEnv assignment locals)))

def FieldsTyping (signatures : List SemanticSignature) (bindings : List (Binding scopes))
    (assignment : α → Computation) : List (Field α) → List (Expr scopes) → Prop
  | [], [] => True
  | field :: fields, body :: bodies =>
      FieldTyping signatures bindings assignment field body ∧
        FieldsTyping signatures bindings assignment fields bodies
  | _, _ => False

/-- The source bodies are in their resolved field order; none are dropped. -/
def constructFields (declarations : Declarations α)
    (environment : CommonEffectFormula.SchemeEnv scopes α) :
    List (Field α) → List (Expr scopes) → Formula scopes α
  | [], [] => .old (.core .top)
  | field :: fields, body :: bodies =>
      .and (constructCheckedField declarations environment field.scheme body)
        (constructFields declarations environment fields bodies)
  | _, _ => .old (.core .bot)

/-- Every field has independently sorted rigid locals. The captured table,
assignment and environment are the same for the whole construction. -/
theorem construct_fields_exact (signatures : List SemanticSignature) (declarations : Declarations α)
    (environment : CommonEffectFormula.SchemeEnv scopes α) (bindings : List (Binding scopes))
    (assignment : α → Computation) (related : ContextRel signatures declarations assignment environment bindings)
    (fields : List (Field α)) (bodies : List (Expr scopes)) :
    (constructFields declarations environment fields bodies).Holds assignment ↔
      FieldsTyping signatures bindings assignment fields bodies := by
  induction fields generalizing bodies with
  | nil =>
    cases bodies <;> rfl
  | cons field fields ih =>
    cases bodies with
    | nil => rfl
    | cons body bodies =>
      exact and_congr
        (construct_checked_field_exact signatures declarations environment bindings assignment related field.scheme body)
        (ih bodies)

/-- A field position is resolved before this rule. Its scheme is opened anew
by useCheckedField; no instantiation is stored back into the declaration. -/
def project (declaration : Declaration α) (index : Nat) (out : CompTerm α) : Formula scopes α :=
  match declaration.fields[index]? with
  | none => .old (.core .bot)
  | some field => useCheckedField field.scheme out

def ProjectionTyping (assignment : α → Computation) (declaration : Declaration α)
    (index : Nat) (out : Computation) : Prop :=
  ∃ field, declaration.fields[index]? = some field ∧
    field.scheme.wellKinded = true ∧ FieldUse assignment field.scheme out

/-- Exact checked elimination for a field of any local arity and either kind,
including a missing-position rejection. The ambient assignment stays fixed. -/
theorem project_exact (assignment : α → Computation) (declaration : Declaration α)
    (index : Nat) (out : CompTerm α) :
    (project (scopes := scopes) declaration index out).Holds assignment ↔
      ProjectionTyping assignment declaration index (out.eval Common.model assignment) := by
  cases found : declaration.fields[index]? with
  | none =>
    simp [project, ProjectionTyping, found, Formula.Holds,
      CommonEffectFormula.Formula.Holds, Core.PresenceGeneration.Formula.Holds]
  | some field =>
    simpa only [project, ProjectionTyping, found, Option.some.injEq, exists_eq_left', true_and] using
      use_checked_field_exact (scopes := scopes) assignment field.scheme out

end Yulang.CommonEffectFieldTable
