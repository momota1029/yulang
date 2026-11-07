import Yulang.CommonEffectRequestGeneration

/-! Finite universal single-handler composition over the presence source.
This is not recursive effect generation or an effect solver. -/
namespace Yulang.CommonEffectHandlerGeneration
open Core.PresenceGeneration
open CommonEffectRequestGeneration

/-- Outer computations, context and final result precede local types. -/
inductive HandlerTyping (scopes : Nat) (assignment : α → Computation)
    (declaration : Declaration α) (permission : Permission)
    (environment : List (Binding Common.model))
    (action onReturn onOperation : Inference.Expr) (out : Computation) : Prop where
  | intro (input returned : Computation) :
      permission.allows declaration.key = true →
      Typing Common.model environment action input →
      Typing Common.model (.mono (Comp.pure Common.model input.1) :: environment) onReturn returned →
      (∀ locals : Fin declaration.locals → Common.Ty, ∃ operated : Computation,
        Typing Common.model
          (.mono (Comp.pure Common.model
            (declaration.input.eval Common.model (localEnv assignment locals))) ::
           .mono (Comp.pure Common.model (Comp.arrow Common.model
             (Comp.pure Common.model (declaration.output.eval Common.model (localEnv assignment locals)))
             input)) :: environment) onOperation operated ∧
        Common.Subtype (.union returned.1 operated.1) out.1 ∧
        Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual [declaration.key] input.2)
          (Common.rowJoin returned.2 operated.2)) out.2) →
      HandlerTyping scopes assignment declaration permission environment action onReturn onOperation out

/-- The arm result is allocated inside the universal type binder. -/
def armBody (environment : SchemeEnv α) (key : Nat) (payload response : TyTerm α)
    (input returned out : CompTerm α) (body : Inference.Expr) : Constraint scopes α :=
  .existsSlot (.and
    (.core (generate
      (Scheme.mono (CompTerm.pure (payload.rename some)) ::
       Scheme.mono (CompTerm.pure (CompTerm.arrow
         (CompTerm.pure (response.rename some)) (input.rename some))) :: environment.lift)
      body (CompTerm.var none)))
    (.and (.core (.tyLe (.union (returned.ty.rename some) (.var none)) (out.ty.rename some)))
      (.rowLe (.union (.residual [key] (RowExpr.fromPresence (input.row.rename some)))
        (.union (RowExpr.fromPresence (returned.row.rename some)) (.var none)))
        (RowExpr.fromPresence (out.row.rename some)))))

theorem armBody_exact (environment : SchemeEnv α) (bindings : List (Binding Common.model))
    (assignment : α → Computation) (related : EnvRel Common.model assignment environment bindings)
    (key : Nat) (payload response : TyTerm α) (input returned out : CompTerm α)
    (body : Inference.Expr) :
    (armBody (scopes := scopes) environment key payload response input returned out body).Holds assignment ↔
      ∃ operated : Computation,
        Typing Common.model
          (.mono (Comp.pure Common.model (payload.eval Common.model assignment)) ::
           .mono (Comp.pure Common.model (Comp.arrow Common.model
             (Comp.pure Common.model (response.eval Common.model assignment)) (input.eval Common.model assignment))) ::
           bindings) body operated ∧
        Common.Subtype (.union (returned.eval Common.model assignment).1 operated.1)
          (out.eval Common.model assignment).1 ∧
        Common.rowLe
          (Common.rowJoin (CommonSignedRows.commonResidual [key] (input.eval Common.model assignment).2)
            (Common.rowJoin (returned.eval Common.model assignment).2 operated.2))
          (out.eval Common.model assignment).2 := by
  have exactBody (operated : Computation) :=
    generate_models_iff_typing Common.model body
      (Scheme.mono (CompTerm.pure (payload.rename some)) ::
       Scheme.mono (CompTerm.pure (CompTerm.arrow
         (CompTerm.pure (response.rename some)) (input.rename some))) :: environment.lift)
      _ (extend assignment operated) (CompTerm.var none)
      (((related.lift operated).mono
        (CompTerm.pure (CompTerm.arrow (CompTerm.pure (response.rename some)) (input.rename some)))).mono
        (CompTerm.pure (payload.rename some)))
  simp only [armBody, Constraint.Holds]
  apply exists_congr
  intro operated
  rw [exactBody operated]
  simp only [CompTerm.arrow, CompTerm.rename, CompTerm.var,
    CompTerm.eval, TyTerm.eval, RowTerm.eval, RowExpr.eval, Formula.Holds]
  simp only [TyTerm.eval_rename, RowTerm.eval_rename, RowExpr.eval_fromPresence,
    extend_none, extend_comp_some]
  simp only [CompTerm.pure, TyTerm.eval, RowTerm.eval, TyTerm.eval_rename,
    RowTerm.eval_rename, extend_comp_some]
  rfl

/-- Allocate input/return outside forall, and operated inside forall. -/
def generateHandler (environment : SchemeEnv α) (declaration : Declaration α)
    (permission : Permission) (action onReturn onOperation : Inference.Expr)
    (out : CompTerm α) : Constraint scopes α :=
  if permission.allows declaration.key then
    .existsSlot (.existsSlot (.and
      (.core (generate (env₂ environment) action fresh₀))
      (.and (.core (generate (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ environment) onReturn fresh₁))
        (.forallTypes declaration.locals
          (armBody ((env₂ environment).rename Sum.inl) declaration.key
            (declaration.input.rename (Sum.map (fun x => some (some x)) id))
            (declaration.output.rename (Sum.map (fun x => some (some x)) id))
            (fresh₀.rename Sum.inl) (fresh₁.rename Sum.inl) ((lift₂ out).rename Sum.inl) onOperation)))))
  else .core .bot

private theorem ambient_local (assignment : α → Computation) (a b : Computation)
    (locals : Fin count → Common.Ty) :
    localEnv (extend (extend assignment a) b) locals ∘
        Sum.map (fun x => some (some x)) id = localEnv assignment locals := by
  funext index
  cases index <;> rfl

/-- Every finite signature, arbitrary captured environments/assignment/result.
The finite mask is explicit; this does not claim source permission discovery. -/
theorem generate_handler_exact (environment : SchemeEnv α) (bindings : List (Binding Common.model))
    (assignment : α → Computation) (related : EnvRel Common.model assignment environment bindings)
    (declaration : Declaration α) (permission : Permission)
    (action onReturn onOperation : Inference.Expr) (out : CompTerm α) :
    (generateHandler (scopes := scopes) environment declaration permission action onReturn onOperation out).Holds assignment ↔
      HandlerTyping scopes assignment declaration permission bindings action onReturn onOperation
        (out.eval Common.model assignment) := by
  have actionExact (a b : Computation) :
      (generate (env₂ environment) action fresh₀).Holds Common.model (extend (extend assignment a) b) ↔
        Typing Common.model bindings action a := by
    simpa only [env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some] using
      generate_models_iff_typing Common.model action (env₂ environment) bindings
        (extend (extend assignment a) b) fresh₀ ((related.lift a).lift b)
  have returnExact (a b : Computation) :
      (generate (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ environment) onReturn fresh₁).Holds
          Common.model (extend (extend assignment a) b) ↔
        Typing Common.model (.mono (Comp.pure Common.model a.1) :: bindings) onReturn b := by
    simpa [env₂, fresh₀, fresh₁, CompTerm.eval, CompTerm.pure, TyTerm.eval,
      CompTerm.var, RowTerm.eval, Comp.pure] using
      generate_models_iff_typing Common.model onReturn _ _ (extend (extend assignment a) b) fresh₁
        (((related.lift a).lift b).mono (CompTerm.pure fresh₀.ty))
  have armExact (a b : Computation) (locals : Fin declaration.locals → Common.Ty) :=
    armBody_exact (scopes := scopes) ((env₂ environment).rename Sum.inl) bindings
      (localEnv (extend (extend assignment a) b) locals)
      (((related.lift a).lift b).rename Sum.inl _ rfl) declaration.key
      (declaration.input.rename (Sum.map (fun x => some (some x)) id))
      (declaration.output.rename (Sum.map (fun x => some (some x)) id))
      (fresh₀.rename Sum.inl) (fresh₁.rename Sum.inl) ((lift₂ out).rename Sum.inl) onOperation
  simp only [TyTerm.eval_rename, CompTerm.eval_rename, ambient_local, localEnv_comp_inl] at armExact
  simp only [fresh₀, fresh₁, lift₂, CompTerm.eval_rename, CompTerm.eval_var, localEnv,
    extend_some, extend_none] at armExact
  cases allowed : permission.allows declaration.key with
  | false =>
    simp only [generateHandler, allowed, Bool.false_eq_true, ↓reduceIte,
      Constraint.Holds, Formula.Holds]
    constructor
    · exact False.elim
    · intro typed
      cases typed with
      | intro _ _ permitted _ _ _ => simp [allowed] at permitted
  | true =>
    simp only [generateHandler, allowed, ↓reduceIte, Constraint.Holds, actionExact, returnExact]
    constructor
    · rintro ⟨input, returned, actionTyped, returnTyped, arms⟩
      exact .intro input returned allowed actionTyped returnTyped
        (fun locals => (armExact input returned locals).mp (arms locals))
    · intro typed
      cases typed with
      | intro input returned _ actionTyped returnTyped arms =>
        exact ⟨input, returned, actionTyped, returnTyped,
          fun locals => (armExact input returned locals).mpr (arms locals)⟩
end Yulang.CommonEffectHandlerGeneration
