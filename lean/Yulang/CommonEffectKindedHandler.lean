import Yulang.CommonEffectKindedGeneration

/-!
Finite mixed-kind operation signatures with universal handler arms. All three
bodies use the actual recursive effect generator with its captured table.
This compositional bridge does not replace that table's value-local entries
by mixed-kind entries, or solve universal constraints.
-/
namespace Yulang.CommonEffectKindedHandler
open Core.PresenceGeneration (Comp CompTerm TyTerm RowTerm extend extend_none extend_some extend_comp_some)
open CommonEffectRequestGeneration (Computation Declarations Permission)
open CommonEffectKindedFormula
open CommonEffectRecursiveSource
open CommonEffectRecursiveGeneration (ContextRel generate handlerChecks handlerChecks_holds)
open CommonEffectDeclarationInterpretation (renameAll)
open CommonEffectPresence (fresh₀ fresh₁ lift₂ env₂)

variable {scopes : Nat}

structure Declaration (α : Type) where
  types : Nat
  rows : Nat
  key : Nat
  extra : List Nat := []
  input : TyTerm (α ⊕ Names types rows)
  output : TyTerm (α ⊕ Names types rows)

def Declaration.wellKinded (declaration : Declaration α) : Bool :=
  typeWellKinded declaration.input && typeWellKinded declaration.output

def armBody (declarations : Declarations α) (environment : CommonEffectFormula.SchemeEnv scopes α)
    (key : Nat) (payload response : TyTerm α) (input returned out : CompTerm α)
    (body : Expr scopes) : CommonEffectFormula.Formula scopes α :=
  .existsSlot (handlerChecks key input returned out
    (generate (renameAll some declarations)
      (CommonEffectFormula.Scheme.mono (CompTerm.pure (payload.rename some)) ::
       CommonEffectFormula.Scheme.mono (CompTerm.pure (CompTerm.arrow
         (CompTerm.pure (response.rename some)) (input.rename some))) :: environment.lift)
      body (CompTerm.var none)))

theorem arm_body_exact (signatures : List SemanticSignature) (declarations : Declarations α)
    (environment : CommonEffectFormula.SchemeEnv scopes α) (bindings : List (Binding scopes))
    (assignment : α → Computation) (related : ContextRel signatures declarations assignment environment bindings)
    (key : Nat) (payload response : TyTerm α) (input returned out : CompTerm α) (body : Expr scopes) :
    (armBody declarations environment key payload response input returned out body).Holds assignment ↔
      ∃ operated : Computation,
        Typing signatures
          (.mono (Comp.pure Common.model (payload.eval Common.model assignment)) ::
           .mono (Comp.pure Common.model (Comp.arrow Common.model
             (Comp.pure Common.model (response.eval Common.model assignment)) (input.eval Common.model assignment))) ::
           bindings) body operated ∧
        Common.Subtype (.union (returned.eval Common.model assignment).1 operated.1) (out.eval Common.model assignment).1 ∧
        Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual [key] (input.eval Common.model assignment).2)
          (Common.rowJoin (returned.eval Common.model assignment).2 operated.2)) (out.eval Common.model assignment).2 := by
  change (∃ operated, (handlerChecks _ _ _ _ _).Holds (extend assignment operated)) ↔ _
  apply exists_congr
  intro operated
  rw [handlerChecks_holds]
  have typed := CommonEffectRecursiveExact.generate_recursive_effect_exact signatures body
    (CommonEffectFormula.Scheme.mono (CompTerm.pure (payload.rename some)) ::
     CommonEffectFormula.Scheme.mono (CompTerm.pure (CompTerm.arrow
       (CompTerm.pure (response.rename some)) (input.rename some))) :: environment.lift)
    _ (extend assignment operated) (CompTerm.var none)
    (((related.lift operated).mono
      (CompTerm.pure (CompTerm.arrow (CompTerm.pure (response.rename some)) (input.rename some)))).mono
      (CompTerm.pure (payload.rename some)))
  simp only [CompTerm.eval_var, extend_none] at typed
  rw [typed]
  simp only [CompTerm.eval, CompTerm.pure, CompTerm.arrow, CompTerm.rename, TyTerm.eval, RowTerm.eval,
    TyTerm.eval_rename, RowTerm.eval_rename, extend_comp_some]
  rfl

/-- Original Γ/input/returned/result are outside both local sorts. The
continuation returns to the original input, including its original row. -/
inductive HandlerTyping (signatures : List SemanticSignature) (assignment : α → Computation)
    (declaration : Declaration α) (permission : Permission) (environment : List (Binding scopes))
    (action onReturn onOperation : Expr scopes) (out : Computation) : Prop where
  | intro (input returned : Computation) :
      permission.allows declaration.key = true →
      Typing signatures environment action input →
      Typing signatures (.mono (Comp.pure Common.model input.1) :: environment) onReturn returned →
      (∀ locals : Locals declaration.types declaration.rows, ∃ operated : Computation,
        Typing signatures
          (.mono (Comp.pure Common.model (declaration.input.eval Common.model (localEnv assignment locals))) ::
           .mono (Comp.pure Common.model (Comp.arrow Common.model
             (Comp.pure Common.model (declaration.output.eval Common.model (localEnv assignment locals))) input)) ::
           environment) onOperation operated ∧
        Common.Subtype (.union returned.1 operated.1) out.1 ∧
        Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual [declaration.key] input.2)
          (Common.rowJoin returned.2 operated.2)) out.2) →
      HandlerTyping signatures assignment declaration permission environment action onReturn onOperation out

/-- Raw finite syntax helper; generateCheckedHandler validates local kinds. -/
def generateHandler (declarations : Declarations α) (environment : CommonEffectFormula.SchemeEnv scopes α)
    (declaration : Declaration α) (permission : Permission)
    (action onReturn onOperation : Expr scopes) (out : CompTerm α) : Formula scopes α :=
  if permission.allows declaration.key then
    .existsSlot (.existsSlot (.and
      (.old (generate (renameAll some (renameAll some declarations)) (env₂ environment) action fresh₀))
      (.and (.old (generate (renameAll some (renameAll some declarations))
          (CommonEffectFormula.Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ environment) onReturn fresh₁))
        (.forallLocals declaration.types declaration.rows (.old
          (armBody (renameAll Sum.inl (renameAll some (renameAll some declarations)))
            ((env₂ environment).rename Sum.inl) declaration.key
            (declaration.input.rename (Sum.map (fun name => some (some name)) id))
            (declaration.output.rename (Sum.map (fun name => some (some name)) id))
            (fresh₀.rename Sum.inl) (fresh₁.rename Sum.inl) ((lift₂ out).rename Sum.inl) onOperation))))))
  else .old (.core .bot)

private theorem ambient_local (assignment : α → Computation) (input returned : Computation)
    (locals : Locals types rows) :
    localEnv (extend (extend assignment input) returned) locals ∘
        Sum.map (fun name => some (some name)) id = localEnv assignment locals := by
  funext name
  cases name with
  | inl name => rfl
  | inr name => cases name <;> rfl

theorem generate_handler_exact (signatures : List SemanticSignature) (declarations : Declarations α)
    (environment : CommonEffectFormula.SchemeEnv scopes α) (bindings : List (Binding scopes))
    (assignment : α → Computation) (related : ContextRel signatures declarations assignment environment bindings)
    (declaration : Declaration α) (permission : Permission)
    (action onReturn onOperation : Expr scopes) (out : CompTerm α) :
    (generateHandler declarations environment declaration permission action onReturn onOperation out).Holds assignment ↔
      HandlerTyping signatures assignment declaration permission bindings action onReturn onOperation
        (out.eval Common.model assignment) := by
  have actionExact (a b : Computation) :
      (generate (renameAll some (renameAll some declarations)) (env₂ environment) action fresh₀).Holds
          (extend (extend assignment a) b) ↔ Typing signatures bindings action a := by
    simpa only [env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some] using
      CommonEffectRecursiveExact.generate_recursive_effect_exact signatures action (env₂ environment)
        bindings (extend (extend assignment a) b) fresh₀ ((related.lift a).lift b)
  have returnExact (a b : Computation) :
      (generate (renameAll some (renameAll some declarations))
        (CommonEffectFormula.Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ environment) onReturn fresh₁).Holds
          (extend (extend assignment a) b) ↔
        Typing signatures (.mono (Comp.pure Common.model a.1) :: bindings) onReturn b := by
    simpa [env₂, fresh₀, fresh₁, CompTerm.eval, CompTerm.pure, TyTerm.eval,
      CompTerm.var, RowTerm.eval, Comp.pure] using
      CommonEffectRecursiveExact.generate_recursive_effect_exact signatures onReturn _ _
        (extend (extend assignment a) b) fresh₁ (((related.lift a).lift b).mono (CompTerm.pure fresh₀.ty))
  have armExact (a b : Computation) (locals : Locals declaration.types declaration.rows) :=
    arm_body_exact signatures (renameAll Sum.inl (renameAll some (renameAll some declarations)))
      ((env₂ environment).rename Sum.inl) bindings (localEnv (extend (extend assignment a) b) locals)
      (((related.lift a).lift b).rename Sum.inl _ rfl) declaration.key
      (declaration.input.rename (Sum.map (fun name => some (some name)) id))
      (declaration.output.rename (Sum.map (fun name => some (some name)) id))
      (fresh₀.rename Sum.inl) (fresh₁.rename Sum.inl) ((lift₂ out).rename Sum.inl) onOperation
  simp only [TyTerm.eval_rename, CompTerm.eval_rename, ambient_local, localEnv_comp_inl] at armExact
  simp only [fresh₀, fresh₁, lift₂, CompTerm.eval_rename, CompTerm.eval_var,
    extend_some, extend_none] at armExact
  cases allowed : permission.allows declaration.key with
  | false =>
    simp only [generateHandler, allowed, Bool.false_eq_true, ↓reduceIte, Formula.Holds,
      CommonEffectFormula.Formula.Holds, Core.PresenceGeneration.Formula.Holds]
    constructor
    · exact False.elim
    · intro typed
      cases typed with
      | intro _ _ permitted _ _ _ => simp [allowed] at permitted
  | true =>
    simp only [generateHandler, allowed, ↓reduceIte, Formula.Holds, actionExact, returnExact]
    constructor
    · rintro ⟨input, returned, actionTyped, returnTyped, arms⟩
      exact .intro input returned allowed actionTyped returnTyped
        (fun locals => (armExact input returned locals).mp (arms locals))
    · intro typed
      cases typed with
      | intro input returned _ actionTyped returnTyped arms =>
        exact ⟨input, returned, actionTyped, returnTyped,
          fun locals => (armExact input returned locals).mpr (arms locals)⟩

def generateCheckedHandler (declarations : Declarations α) (environment : CommonEffectFormula.SchemeEnv scopes α)
    (declaration : Declaration α) (permission : Permission)
    (action onReturn onOperation : Expr scopes) (out : CompTerm α) : Formula scopes α :=
  if declaration.wellKinded then
    generateHandler declarations environment declaration permission action onReturn onOperation out
  else .old (.core .bot)

theorem generate_checked_handler_exact (signatures : List SemanticSignature) (declarations : Declarations α)
    (environment : CommonEffectFormula.SchemeEnv scopes α) (bindings : List (Binding scopes))
    (assignment : α → Computation) (related : ContextRel signatures declarations assignment environment bindings)
    (declaration : Declaration α) (permission : Permission)
    (action onReturn onOperation : Expr scopes) (out : CompTerm α) :
    (generateCheckedHandler declarations environment declaration permission action onReturn onOperation out).Holds assignment ↔
      declaration.wellKinded = true ∧ HandlerTyping signatures assignment declaration permission bindings
        action onReturn onOperation (out.eval Common.model assignment) := by
  cases kinded : declaration.wellKinded <;>
    simp only [generateCheckedHandler, kinded, Bool.false_eq_true, ↓reduceIte,
      Formula.Holds, CommonEffectFormula.Formula.Holds, Core.PresenceGeneration.Formula.Holds,
      false_and, true_and]
  exact generate_handler_exact signatures declarations environment bindings assignment related
    declaration permission action onReturn onOperation out

end Yulang.CommonEffectKindedHandler
