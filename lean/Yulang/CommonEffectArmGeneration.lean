import Yulang.CommonEffectUniversalArms

/-! Actual finite generation of heterogeneous universal operation arms over
presence source bodies. This is a compositional layer, not recursive source
inference or universal-constraint elimination by the solver. -/
namespace Yulang.CommonEffectArmGeneration
open Core.PresenceGeneration
open CommonEffectRequestGeneration
open CommonEffectUniversalArms (universalArms universalArms_exact)

/-- The result slot is bound by universalArms inside the local type binder. -/
def armResultBody (environment : SchemeEnv α) (payload response : TyTerm α)
    (input out : CompTerm α) (body : Inference.Expr) : Constraint scopes (Option α) :=
  .and (.core (generate
      (Scheme.mono (CompTerm.pure (payload.rename some)) ::
       Scheme.mono (CompTerm.pure (CompTerm.arrow
         (CompTerm.pure (response.rename some)) (input.rename some))) :: environment.lift)
      body (CompTerm.var none)))
    (.core (Formula.compLe (CompTerm.var none) (out.rename some)))

theorem armResultBody_exact (environment : SchemeEnv α) (bindings : List (Binding Common.model))
    (assignment : α → Computation) (related : EnvRel Common.model assignment environment bindings)
    (payload response : TyTerm α) (input out : CompTerm α) (body : Inference.Expr) (operated : Computation) :
    (armResultBody (scopes := scopes) environment payload response input out body).Holds (extend assignment operated) ↔
      Typing Common.model
        (.mono (Comp.pure Common.model (payload.eval Common.model assignment)) ::
         .mono (Comp.pure Common.model (Comp.arrow Common.model
           (Comp.pure Common.model (response.eval Common.model assignment)) (input.eval Common.model assignment))) ::
         bindings) body operated ∧ Comp.le Common.model operated (out.eval Common.model assignment) := by
  have typed := generate_models_iff_typing Common.model body
    (Scheme.mono (CompTerm.pure (payload.rename some)) ::
     Scheme.mono (CompTerm.pure (CompTerm.arrow
       (CompTerm.pure (response.rename some)) (input.rename some))) :: environment.lift)
    _ (extend assignment operated) (CompTerm.var none)
    (((related.lift operated).mono
      (CompTerm.pure (CompTerm.arrow (CompTerm.pure (response.rename some)) (input.rename some)))).mono
      (CompTerm.pure (payload.rename some)))
  simp only [armResultBody, Constraint.Holds, typed, Formula.holds_compLe,
    CompTerm.eval_rename, extend_comp_some, CompTerm.eval_var, extend_none]
  simp only [CompTerm.pure, CompTerm.arrow, CompTerm.rename, CompTerm.eval,
    TyTerm.eval, RowTerm.eval]
  simp only [TyTerm.eval_rename, RowTerm.eval_rename, extend_comp_some]
  rfl

def generateArms (environment : SchemeEnv α) (declarations : Fin count → Declaration α)
    (input out : CompTerm α) (bodies : Fin count → Inference.Expr) : CommonEffectFormula.Formula scopes α :=
  universalArms (fun i => (declarations i).locals) (fun i =>
    CommonEffectFormula.ofConstraint (armResultBody (environment.rename Sum.inl)
      (declarations i).input (declarations i).output (input.rename Sum.inl) (out.rename Sum.inl) (bodies i)))

/-- Finite declarations and source bodies, all related captured environments,
all ambient assignments, and all symbolic input/output terms. Captured rows
and the shallow continuation's original input are fixed outside joint locals. -/
theorem generate_arms_exact (environment : SchemeEnv α) (bindings : List (Binding Common.model))
    (assignment : α → Computation) (related : EnvRel Common.model assignment environment bindings)
    (declarations : Fin count → Declaration α) (input out : CompTerm α)
    (bodies : Fin count → Inference.Expr) :
    (generateArms (scopes := scopes) environment declarations input out bodies).Holds assignment ↔
      ∀ locals : (i : Fin count) → Fin (declarations i).locals → Common.Ty,
        ∃ operated : Fin count → Computation, ∀ i,
          Typing Common.model
            (.mono (Comp.pure Common.model ((declarations i).input.eval Common.model (localEnv assignment (locals i)))) ::
             .mono (Comp.pure Common.model (Comp.arrow Common.model
               (Comp.pure Common.model ((declarations i).output.eval Common.model (localEnv assignment (locals i))))
               (input.eval Common.model assignment))) :: bindings) (bodies i) (operated i) ∧
          Comp.le Common.model (operated i) (out.eval Common.model assignment) := by
  have each (i : Fin count) (locals : Fin (declarations i).locals → Common.Ty) (operated : Computation) :=
    armResultBody_exact (scopes := scopes) (environment.rename Sum.inl) bindings (localEnv assignment locals)
      (related.rename Sum.inl _ rfl) (declarations i).input (declarations i).output
      (input.rename Sum.inl) (out.rename Sum.inl) (bodies i) operated
  simp only [CompTerm.eval_rename, localEnv_comp_inl] at each
  simp only [generateArms, universalArms_exact]
  constructor
  · intro held locals
    obtain ⟨operated, valid⟩ := held locals
    refine ⟨operated, fun i => (each i (locals i) (operated i)).mp ?_⟩
    exact (CommonEffectFormula.ofConstraint_exact _ _).mp (valid i)
  · intro typed locals
    obtain ⟨operated, valid⟩ := typed locals
    refine ⟨operated, fun i => (CommonEffectFormula.ofConstraint_exact _ _).mpr ?_⟩
    exact (each i (locals i) (operated i)).mpr (valid i)

/-- Empty-arm cases retain the returned value and residual/returned row bounds.
This equivalence justifies keeping those bounds outside all universal arms. -/
theorem aggregate_bounds_iff (handled : List Nat) (input returned out : Computation)
    (operated : Fin count → Computation) :
    (Common.Subtype
      ((List.finRange count).foldr (fun i rest => .union (operated i).1 rest) returned.1) out.1 ∧
     Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual handled input.2)
       (Common.rowJoin returned.2
         ((List.finRange count).foldr (fun i rest => Common.rowJoin (operated i).2 rest) Common.rowEmpty))) out.2) ↔
      Common.Subtype returned.1 out.1 ∧
      Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual handled input.2) returned.2) out.2 ∧
      ∀ i, Comp.le Common.model (operated i) out := by
  change Common.Ty × Common.Row at input returned out
  change Fin count → Common.Ty × Common.Row at operated
  rw [CommonEffectUniversalArms.fold_types_le_iff (List.finRange count) (fun i => (operated i).1) returned.1 out.1,
    Common.rowJoin_le_iff, Common.rowJoin_le_iff,
    CommonEffectUniversalArms.fold_rows_le_iff (List.finRange count) (fun i => (operated i).2) out.2]
  simp only [List.mem_finRange, true_implies]
  constructor
  · rintro ⟨⟨returnedValue, armValues⟩, residual, returnedRow, armRows⟩
    exact ⟨returnedValue, (Common.rowJoin_le_iff _ _ _).mpr ⟨residual, returnedRow⟩,
      fun i => ⟨armValues i, armRows i⟩⟩
  · rintro ⟨returnedValue, baseRows, arms⟩
    have base := (Common.rowJoin_le_iff _ _ _).mp baseRows
    exact ⟨⟨returnedValue, fun i => (arms i).1⟩, base.1, base.2, fun i => (arms i).2⟩
end Yulang.CommonEffectArmGeneration
