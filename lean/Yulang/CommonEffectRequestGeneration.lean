import Yulang.CommonSignedResidual
import Yulang.CorePresenceGenerationExact

/-!
# Finite declared requests over the common presence judgment

Operation bodies are finite presence type terms. Operation-local variables
range over arbitrary Common values, with no local row variables. A request
freshly quantifies those locals and its payload row; captured value/row slots
remain shared. The payload uses the existing presence generator, including
exact emptiness and strict defaults, and is checked by its independent typing
judgment. No typing predicate, semantic signature function or solver is stored
in a formula.

This is the compositional request rule, not the recursive Common effect source
generator or a solved effect family. Payloads are arbitrary `Inference.Expr`
terms and may use captured polymorphic bindings, but contain no nested effect
constructors. Handler permission discovery and role-qualified declarations are
separate obligations.
-/

namespace Yulang.CommonEffectRequestGeneration

open Core.PresenceGeneration

abbrev Computation := Comp Common.model

/-- A finite permission description; `all` also covers keys introduced by a
future instantiation of an arbitrary Common row parameter. -/
inductive Permission where
  | all
  | only : List Nat → Permission
  deriving DecidableEq, Repr

def Permission.allows : Permission → Nat → Bool
  | .all, _ => true
  | .only keys, key => keys.contains key

/-- Signed row syntax with finite masks, rather than arbitrary functions in
the generated syntax. Free row variables still denote arbitrary Common rows. -/
inductive RowExpr (scopes : Nat) (α : Type) where
  | var : α → RowExpr scopes α
  | empty : RowExpr scopes α
  | head : Nat → RowExpr scopes α
  | union : RowExpr scopes α → RowExpr scopes α → RowExpr scopes α
  | protect : Fin scopes → Permission → RowExpr scopes α → RowExpr scopes α
  | release : Fin scopes → Permission → RowExpr scopes α → RowExpr scopes α
  | residual : List Nat → RowExpr scopes α → RowExpr scopes α

def RowExpr.eval (assignment : α → Computation) : RowExpr scopes α → Common.Row
  | .var index => (assignment index).2
  | .empty => Common.rowEmpty
  | .head key => (CommonSignedRows.commonAlgebra scopes).head key
  | .union first last => Common.rowJoin (first.eval assignment) (last.eval assignment)
  | .protect scope permission source =>
      CommonSignedRows.commonProtect scope.val permission.allows (source.eval assignment)
  | .release scope permission source =>
      CommonSignedRows.commonRelease scope.val permission.allows (source.eval assignment)
  | .residual handled source => CommonSignedRows.commonResidual handled (source.eval assignment)

def RowExpr.fromPresence : RowTerm α → RowExpr scopes α
  | .var index => .var index
  | .empty => .empty
  | .join first last => .union (fromPresence first) (fromPresence last)

@[simp] theorem RowExpr.eval_fromPresence (assignment : α → Computation) (row : RowTerm α) :
    (RowExpr.fromPresence (scopes := scopes) row).eval assignment = row.eval Common.model assignment := by
  induction row <;> simp_all [fromPresence, eval, RowTerm.eval, Common.model]

def RowExpr.heads (keys : List Nat) : RowExpr scopes α :=
  keys.foldr (fun key rest => .union (.head key) rest) .empty

@[simp] theorem RowExpr.eval_heads (assignment : α → Computation) (keys : List Nat) :
    (RowExpr.heads (scopes := scopes) keys).eval assignment =
      RowInference.keysRow (CommonSignedRows.commonAlgebra scopes) keys := by
  induction keys <;> simp_all [heads, eval, RowInference.keysRow, CommonSignedRows.commonAlgebra]

/-- Local type instantiation never chooses a fresh row for a local. -/
def localEnv (assignment : α → Computation) (locals : Fin count → Common.Ty) :
    α ⊕ Fin count → Computation :=
  Sum.elim assignment (fun index => Comp.pure Common.model (locals index))

@[simp] theorem localEnv_comp_inl (assignment : α → Computation)
    (locals : Fin count → Common.Ty) : localEnv assignment locals ∘ Sum.inl = assignment := rfl

/-- Only finite syntax is stored, including every type quantifier body. -/
inductive Constraint (scopes : Nat) : Type → Type 1 where
  | core : Formula α → Constraint scopes α
  | rowLe : RowExpr scopes α → RowExpr scopes α → Constraint scopes α
  | and : Constraint scopes α → Constraint scopes α → Constraint scopes α
  | existsSlot : Constraint scopes (Option α) → Constraint scopes α
  | existsTypes : (count : Nat) → Constraint scopes (α ⊕ Fin count) → Constraint scopes α
  | forallTypes : (count : Nat) → Constraint scopes (α ⊕ Fin count) → Constraint scopes α

def Constraint.Holds : {α : Type} → (α → Computation) → Constraint scopes α → Prop
  | _, assignment, .core formula => formula.Holds Common.model assignment
  | _, assignment, .rowLe first last => Common.rowLe (first.eval assignment) (last.eval assignment)
  | _, assignment, .and first last => first.Holds assignment ∧ last.Holds assignment
  | _, assignment, .existsSlot body => ∃ value, body.Holds (extend assignment value)
  | _, assignment, .existsTypes _ body => ∃ locals, body.Holds (localEnv assignment locals)
  | _, assignment, .forallTypes _ body => ∀ locals, body.Holds (localEnv assignment locals)

/-- Resolved keys and additive extra heads contain no operation-local type
variables. Captured slots and local value slots are distinct in both bodies. -/
structure Declaration (α : Type) where
  locals : Nat
  key : Nat
  extra : List Nat := []
  input : TyTerm (α ⊕ Fin locals)
  output : TyTerm (α ⊕ Fin locals)

/-- Local variables have value kind. They cannot be read in a row position. -/
def rowWellKinded : RowTerm (α ⊕ Fin count) → Bool
  | .var (.inl _) | .empty => true
  | .var (.inr _) => false
  | .join first last => rowWellKinded first && rowWellKinded last

def typeWellKinded : TyTerm (α ⊕ Fin count) → Bool
  | .var _ | .base _ | .bottom | .top | .emptyRecord | .exactEmpty => true
  | .union first last | .inter first last | .pair first last | .record _ first last |
      .recordDefault _ first last => typeWellKinded first && typeWellKinded last
  | .required _ value | .variant _ value => typeWellKinded value
  | .arrow input incoming output outgoing =>
      typeWellKinded input && rowWellKinded incoming && typeWellKinded output && rowWellKinded outgoing

def Declaration.wellKinded (declaration : Declaration α) : Bool :=
  typeWellKinded declaration.input && typeWellKinded declaration.output

/-- Finite declarations are selected by their resolved table position. This
checks type/row kinds, not names, visibility, role obligations or permission. -/
abbrev Declarations (α : Type) := List (Declaration α)

def Declarations.wellKinded (declarations : Declarations α) : Bool :=
  declarations.all Declaration.wellKinded

/-- The independent call rule uses actual finite declaration syntax only to
interpret its input/output. It does not mention generated constraints. -/
inductive RequestTyping (scopes : Nat) (assignment : α → Computation)
    (declaration : Declaration α) (environment : List (Binding Common.model))
    (payload : Inference.Expr) (out : Computation) : Prop where
  | intro (locals : Fin declaration.locals → Common.Ty) (payloadRow : Common.Row) :
      Typing Common.model environment payload
        (declaration.input.eval Common.model (localEnv assignment locals), payloadRow) →
      Common.Subtype (declaration.output.eval Common.model (localEnv assignment locals)) out.1 →
      Common.rowLe
        (Common.rowJoin payloadRow (Common.rowJoin
          ((CommonSignedRows.commonAlgebra scopes).head declaration.key)
          (RowInference.keysRow (CommonSignedRows.commonAlgebra scopes) declaration.extra))) out.2 →
      RequestTyping scopes assignment declaration environment payload out

def requestBody (environment : SchemeEnv α) (key : Nat) (extra : List Nat)
    (input output : TyTerm α) (payload : Inference.Expr) (out : CompTerm α) : Constraint scopes α :=
  .existsSlot (.and
    (.core (generate environment.lift payload ⟨input.rename some, .var none⟩))
    (.and (.core (.tyLe (output.rename some) (out.ty.rename some)))
      (.rowLe (.union (.var none) (.union (.head key) (RowExpr.heads extra)))
        (RowExpr.fromPresence (out.row.rename some)))))

def generateRequest (environment : SchemeEnv α) (declaration : Declaration α)
    (payload : Inference.Expr) (out : CompTerm α) : Constraint scopes α :=
  .existsTypes declaration.locals (requestBody (environment.rename Sum.inl) declaration.key
    declaration.extra declaration.input declaration.output payload (out.rename Sum.inl))

private theorem requestBody_exact (environment : SchemeEnv α)
    (bindings : List (Binding Common.model)) (assignment : α → Computation)
    (related : EnvRel Common.model assignment environment bindings)
    (key : Nat) (extra : List Nat) (input output : TyTerm α)
    (payload : Inference.Expr) (out : CompTerm α) :
    (requestBody (scopes := scopes) environment key extra input output payload out).Holds assignment ↔
      ∃ payloadRow, Typing Common.model bindings payload (input.eval Common.model assignment, payloadRow) ∧
        Common.Subtype (output.eval Common.model assignment) (out.eval Common.model assignment).1 ∧
        Common.rowLe (Common.rowJoin payloadRow (Common.rowJoin
          ((CommonSignedRows.commonAlgebra scopes).head key)
          (RowInference.keysRow (CommonSignedRows.commonAlgebra scopes) extra)))
            (out.eval Common.model assignment).2 := by
  have payloadExact (value : Computation) :
      (generate environment.lift payload ⟨input.rename some, .var none⟩).Holds
        Common.model (extend assignment value) ↔
      Typing Common.model bindings payload (input.eval Common.model assignment, value.2) := by
    simpa [CompTerm.eval, TyTerm.eval, RowTerm.eval] using
      generate_models_iff_typing Common.model payload environment.lift bindings (extend assignment value)
        ⟨input.rename some, .var none⟩ (related.lift value)
  simp only [requestBody, Constraint.Holds, payloadExact, Formula.Holds,
    TyTerm.eval_rename, extend_comp_some, RowExpr.eval, RowExpr.eval_heads,
    RowExpr.eval_fromPresence, RowTerm.eval_rename]
  constructor
  · rintro ⟨value, typed, valueBound, rowBound⟩
    exact ⟨value.2, typed, valueBound, rowBound⟩
  · rintro ⟨row, typed, valueBound, rowBound⟩
    exact ⟨(.base .unit, row), typed, valueBound, rowBound⟩

/-- Every finite declaration, related environment, arbitrary Common ambient
assignment, payload and symbolic result. No success or well-kindedness premise
is needed for this semantic correspondence. The checked entry below performs
the independent finite kind validation. -/
theorem generate_request_exact (environment : SchemeEnv α)
    (bindings : List (Binding Common.model)) (assignment : α → Computation)
    (related : EnvRel Common.model assignment environment bindings)
    (declaration : Declaration α) (payload : Inference.Expr) (out : CompTerm α) :
    (generateRequest (scopes := scopes) environment declaration payload out).Holds assignment ↔
      RequestTyping scopes assignment declaration bindings payload (out.eval Common.model assignment) := by
  change (∃ locals, (requestBody _ _ _ _ _ _ _).Holds (localEnv assignment locals)) ↔ _
  constructor
  · rintro ⟨locals, accepted⟩
    have exactBody := (requestBody_exact (environment.rename Sum.inl) bindings (localEnv assignment locals)
      (related.rename Sum.inl _ rfl) declaration.key declaration.extra declaration.input declaration.output
      payload (out.rename Sum.inl)).mp accepted
    simp only [CompTerm.eval_rename, localEnv_comp_inl] at exactBody
    obtain ⟨payloadRow, typed, valueBound, rowBound⟩ := exactBody
    exact .intro locals payloadRow typed valueBound rowBound
  · intro typed
    cases typed with
    | intro locals payloadRow payloadTyped valueBound rowBound =>
        refine ⟨locals, (requestBody_exact (environment.rename Sum.inl) bindings (localEnv assignment locals)
          (related.rename Sum.inl _ rfl) declaration.key declaration.extra declaration.input declaration.output
          payload (out.rename Sum.inl)).mpr ?_⟩
        simpa only [CompTerm.eval_rename, localEnv_comp_inl] using
          (show ∃ payloadRow, Typing Common.model bindings payload
            (declaration.input.eval Common.model (localEnv assignment locals), payloadRow) ∧
            Common.Subtype (declaration.output.eval Common.model (localEnv assignment locals))
              (out.eval Common.model assignment).1 ∧
            Common.rowLe (Common.rowJoin payloadRow (Common.rowJoin
              ((CommonSignedRows.commonAlgebra scopes).head declaration.key)
              (RowInference.keysRow (CommonSignedRows.commonAlgebra scopes) declaration.extra)))
              (out.eval Common.model assignment).2 from
            ⟨payloadRow, payloadTyped, valueBound, rowBound⟩)

inductive DeclaredRequestTyping (scopes : Nat) (assignment : α → Computation)
    (declarations : Declarations α) (environment : List (Binding Common.model))
    (operation : Nat) (payload : Inference.Expr) (out : Computation) : Prop where
  | intro (declaration : Declaration α) :
      declarations[operation]? = some declaration →
      RequestTyping scopes assignment declaration environment payload out →
      DeclaredRequestTyping scopes assignment declarations environment operation payload out

/-- Actual finite lookup rejects a missing resolved operation identifier. -/
def generateDeclared (environment : SchemeEnv α) (declarations : Declarations α)
    (operation : Nat) (payload : Inference.Expr) (out : CompTerm α) : Constraint scopes α :=
  match declarations[operation]? with
  | none => .core .bot
  | some declaration => generateRequest environment declaration payload out

/-- Exactness includes unsuccessful lookup, and quantifies the whole finite
table rather than an externally supplied semantic signature. -/
theorem generate_declared_request_exact (environment : SchemeEnv α)
    (bindings : List (Binding Common.model)) (assignment : α → Computation)
    (related : EnvRel Common.model assignment environment bindings)
    (declarations : Declarations α) (operation : Nat) (payload : Inference.Expr) (out : CompTerm α) :
    (generateDeclared (scopes := scopes) environment declarations operation payload out).Holds assignment ↔
      DeclaredRequestTyping scopes assignment declarations bindings operation payload
        (out.eval Common.model assignment) := by
  cases found : declarations[operation]? with
  | none =>
      constructor
      · simp [generateDeclared, found, Constraint.Holds, Formula.Holds]
      · intro typed
        cases typed with
        | intro declaration present _ => simp [found] at present
  | some declaration =>
      simp only [generateDeclared, found, generate_request_exact environment bindings assignment related]
      constructor
      · exact .intro declaration found
      · intro typed
        cases typed with
        | intro actual present accepted =>
            have same : actual = declaration := Option.some.inj (present.symm.trans found)
            simpa only [same] using accepted

/-- This entry checks the finite value/row kind discipline before generation.
It deliberately does not stand for the remaining declaration visibility,
role-obligation or handler-permission validation. -/
def checkAndGenerate (environment : SchemeEnv α) (declarations : Declarations α)
    (operation : Nat) (payload : Inference.Expr) (out : CompTerm α) : Constraint scopes α :=
  if declarations.wellKinded then generateDeclared environment declarations operation payload out else .core .bot

theorem checked_request_exact (environment : SchemeEnv α)
    (bindings : List (Binding Common.model)) (assignment : α → Computation)
    (related : EnvRel Common.model assignment environment bindings)
    (declarations : Declarations α) (operation : Nat) (payload : Inference.Expr) (out : CompTerm α) :
    (checkAndGenerate (scopes := scopes) environment declarations operation payload out).Holds assignment ↔
      declarations.wellKinded = true ∧
      DeclaredRequestTyping scopes assignment declarations bindings operation payload
        (out.eval Common.model assignment) := by
  simp only [checkAndGenerate]
  split <;> rename_i valid
  · simpa only [valid, true_and] using
      generate_declared_request_exact (scopes := scopes) environment bindings assignment related
        declarations operation payload out
  · simp [Constraint.Holds, Formula.Holds, valid]

end Yulang.CommonEffectRequestGeneration
