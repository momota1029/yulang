import Yulang.CommonEffectKindedFormula
import Yulang.CommonEffectRecursiveExact

/-!
Sorted rigid construction and fresh instantiation of finite signatures over
the recursive effect source. Fixed captures are never rebound by either rule.
This is the shared binder bridge for operation-local and field-local types /
rows. It does not add rank-2 struct subtyping, inference, or role rules.
-/
namespace Yulang.CommonEffectKindedGeneration
open Core.PresenceGeneration (Comp CompTerm TyTerm RowTerm)
open CommonEffectRequestGeneration (Computation Declarations)
open CommonEffectKindedFormula
open CommonEffectRecursiveSource
open CommonEffectRecursiveGeneration (ContextRel)
open CommonEffectDeclarationInterpretation (renameAll)

variable {scopes : Nat}

def generateLocal (declarations : Declarations α) (environment : CommonEffectFormula.SchemeEnv scopes α)
    (body : Expr scopes) (out : CompTerm (α ⊕ Names types rows)) :
    CommonEffectFormula.Formula scopes (α ⊕ Names types rows) :=
  CommonEffectRecursiveGeneration.generate (renameAll Sum.inl declarations)
    (environment.rename Sum.inl) body out

theorem generate_local_exact (signatures : List SemanticSignature) (declarations : Declarations α)
    (environment : CommonEffectFormula.SchemeEnv scopes α) (bindings : List (Binding scopes))
    (assignment : α → Computation) (related : ContextRel signatures declarations assignment environment bindings)
    (body : Expr scopes) (out : CompTerm (α ⊕ Names types rows)) (locals : Locals types rows) :
    (generateLocal declarations environment body out).Holds (localEnv assignment locals) ↔
      Typing signatures bindings body (out.eval Common.model (localEnv assignment locals)) := by
  exact CommonEffectRecursiveExact.generate_recursive_effect_exact signatures body
    (environment.rename Sum.inl) bindings (localEnv assignment locals) out
    (related.rename Sum.inl _ rfl)

def generateRigid (declarations : Declarations α) (environment : CommonEffectFormula.SchemeEnv scopes α)
    (body : Expr scopes) (out : CompTerm (α ⊕ Names types rows)) : Formula scopes α :=
  .forallLocals types rows (.old (generateLocal declarations environment body out))

def generateInstance (declarations : Declarations α) (environment : CommonEffectFormula.SchemeEnv scopes α)
    (body : Expr scopes) (out : CompTerm (α ⊕ Names types rows)) : Formula scopes α :=
  .existsLocals types rows (.old (generateLocal declarations environment body out))

theorem generate_rigid_exact (signatures : List SemanticSignature) (declarations : Declarations α)
    (environment : CommonEffectFormula.SchemeEnv scopes α) (bindings : List (Binding scopes))
    (assignment : α → Computation) (related : ContextRel signatures declarations assignment environment bindings)
    (body : Expr scopes) (out : CompTerm (α ⊕ Names types rows)) :
    (generateRigid declarations environment body out).Holds assignment ↔
      ∀ locals : Locals types rows,
        Typing signatures bindings body (out.eval Common.model (localEnv assignment locals)) := by
  exact forall_congr' (generate_local_exact signatures declarations environment bindings assignment related body out)

theorem generate_instance_exact (signatures : List SemanticSignature) (declarations : Declarations α)
    (environment : CommonEffectFormula.SchemeEnv scopes α) (bindings : List (Binding scopes))
    (assignment : α → Computation) (related : ContextRel signatures declarations assignment environment bindings)
    (body : Expr scopes) (out : CompTerm (α ⊕ Names types rows)) :
    (generateInstance declarations environment body out).Holds assignment ↔
      ∃ locals : Locals types rows,
        Typing signatures bindings body (out.eval Common.model (localEnv assignment locals)) := by
  exact exists_congr (generate_local_exact signatures declarations environment bindings assignment related body out)

structure FieldScheme (α : Type) where
  types : Nat
  rows : Nat
  body : TyTerm (α ⊕ Names types rows)

def FieldScheme.wellKinded (field : FieldScheme α) : Bool := typeWellKinded field.body

/-- Raw syntax helper. Source admission uses constructCheckedField below. -/
def constructField (declarations : Declarations α) (environment : CommonEffectFormula.SchemeEnv scopes α)
    (field : FieldScheme α) (body : Expr scopes) : Formula scopes α :=
  generateRigid declarations environment body (CompTerm.pure field.body)

/-- Rigid field construction keeps the source expression and environment
fixed for every independently sorted local type and row assignment. -/
theorem construct_field_exact (signatures : List SemanticSignature) (declarations : Declarations α)
    (environment : CommonEffectFormula.SchemeEnv scopes α) (bindings : List (Binding scopes))
    (assignment : α → Computation) (related : ContextRel signatures declarations assignment environment bindings)
    (field : FieldScheme α) (body : Expr scopes) :
    (constructField declarations environment field body).Holds assignment ↔
      ∀ locals : Locals field.types field.rows,
        Typing signatures bindings body
          (Comp.pure Common.model (field.body.eval Common.model (localEnv assignment locals))) := by
  exact generate_rigid_exact signatures declarations environment bindings assignment related body _

/-- Raw syntax helper. Source admission uses useCheckedField below. -/
def useField (field : FieldScheme α) (out : CompTerm α) : Formula scopes α :=
  .existsLocals field.types field.rows (.old
    (CommonEffectFormula.Formula.compLe (CompTerm.pure field.body) (out.rename Sum.inl)))

/-- The independently stated elimination rule chooses fresh value and row
instances. It does not assume a whole-polymorphic-value subtype relation. -/
inductive FieldUse (assignment : α → Computation) (field : FieldScheme α) (out : Computation) : Prop where
  | intro (locals : Locals field.types field.rows) :
      Comp.le Common.model
        (Comp.pure Common.model (field.body.eval Common.model (localEnv assignment locals))) out →
      FieldUse assignment field out

theorem use_field_exact (assignment : α → Computation) (field : FieldScheme α) (out : CompTerm α) :
    (useField (scopes := scopes) field out).Holds assignment ↔
      FieldUse assignment field (out.eval Common.model assignment) := by
  simp only [useField, Formula.Holds, CommonEffectFormula.Formula.holds_compLe,
    CompTerm.eval_rename, localEnv_comp_inl]
  constructor
  · rintro ⟨locals, accepted⟩
    exact .intro locals accepted
  · intro typed
    cases typed with
    | intro locals accepted => exact ⟨locals, accepted⟩

def constructCheckedField (declarations : Declarations α) (environment : CommonEffectFormula.SchemeEnv scopes α)
    (field : FieldScheme α) (body : Expr scopes) : Formula scopes α :=
  if field.wellKinded then constructField declarations environment field body else .old (.core .bot)

def useCheckedField (field : FieldScheme α) (out : CompTerm α) : Formula scopes α :=
  if field.wellKinded then useField field out else .old (.core .bot)

theorem construct_checked_field_exact (signatures : List SemanticSignature) (declarations : Declarations α)
    (environment : CommonEffectFormula.SchemeEnv scopes α) (bindings : List (Binding scopes))
    (assignment : α → Computation) (related : ContextRel signatures declarations assignment environment bindings)
    (field : FieldScheme α) (body : Expr scopes) :
    (constructCheckedField declarations environment field body).Holds assignment ↔
      field.wellKinded = true ∧ ∀ locals : Locals field.types field.rows,
        Typing signatures bindings body
          (Comp.pure Common.model (field.body.eval Common.model (localEnv assignment locals))) := by
  cases kinded : field.wellKinded <;>
    simp only [constructCheckedField, kinded, Bool.false_eq_true, ↓reduceIte,
      Formula.Holds, CommonEffectFormula.Formula.Holds, Core.PresenceGeneration.Formula.Holds,
      false_and, true_and]
  exact construct_field_exact signatures declarations environment bindings assignment related field body

theorem use_checked_field_exact (assignment : α → Computation) (field : FieldScheme α) (out : CompTerm α) :
    (useCheckedField (scopes := scopes) field out).Holds assignment ↔
      field.wellKinded = true ∧ FieldUse assignment field (out.eval Common.model assignment) := by
  cases kinded : field.wellKinded <;>
    simp only [useCheckedField, kinded, Bool.false_eq_true, ↓reduceIte,
      Formula.Holds, CommonEffectFormula.Formula.Holds, Core.PresenceGeneration.Formula.Holds,
      false_and, true_and]
  exact use_field_exact assignment field out

end Yulang.CommonEffectKindedGeneration
