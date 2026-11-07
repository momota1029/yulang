import Yulang.CommonEffectRecursiveGeneration

/-! Finite generation exactness for the recursive single-effect nucleus.
The independent source has all presence constructors and recursively nested
requests, finite boundaries and single universal handlers. This is not the
full multi/partial/visibility B3 theorem. -/
namespace Yulang.CommonEffectRecursiveExact
open Core.PresenceGeneration (Comp CompTerm TyTerm RowTerm extend extend_none extend_some extend_comp_some
  exists_comp_row exists_comp_ty)
open CommonEffectRequestGeneration (Declarations Declaration Computation RowExpr localEnv localEnv_comp_inl)
open CommonEffectFormula
open CommonEffectPresence (fresh₀ fresh₁ fresh₀₃ fresh₁₃ fresh₂₃ lift₂ lift₃ env₂ env₃)
open CommonEffectDeclarationInterpretation (renameAll interpret interpretAll lookup_interpretAll)
open CommonEffectRecursiveSource
open CommonEffectRecursiveGeneration

variable {scopes : Nat}

private theorem local_names (assignment : α → Computation) (a b : Computation)
    (locals : Fin count → Common.Ty) :
    localEnv (extend (extend assignment a) b) locals ∘ Sum.map (fun name => some (some name)) id =
      localEnv assignment locals := by
  funext name
  cases name <;> rfl

private theorem arrow_eval (first last : CompTerm α) (assignment : α → Computation) :
    (CompTerm.arrow first last).eval Common.model assignment =
      Comp.arrow Common.model (first.eval Common.model assignment) (last.eval Common.model assignment) := rfl

/-- Exactness of the generated constraint scheme. Both directions quantify
over all semantic types and rows; neither assumes that a solver succeeds.
The environment hypothesis only relates input schemes to input bindings. -/
theorem generate_recursive_single_exact (signatures : List SemanticSignature) (e : Expr scopes)
    {declarations : Declarations α}
    (sΓ : SchemeEnv scopes α) (Γ : List (Binding scopes)) (ρ : α → Comp Common.model)
    (out : CompTerm α) (henv : ContextRel signatures declarations ρ sΓ Γ) :
    (generate declarations sΓ e out).Holds ρ ↔ Typing signatures Γ e (out.eval Common.model ρ) := by
  induction e generalizing α declarations sΓ Γ ρ out with
  | var n =>
      exact (lookup_exact sΓ n out ρ).trans
        ((henv.environment n _).trans (Typing.var_iff signatures Γ n _).symm)
  | lit b => simp [generate, CompTerm.eval, CompTerm.pure, TyTerm.eval, RowTerm.eval, Comp.pure]
  | lam body ih =>
      have hb (a b : Comp Common.model) :
          (generate (decl₂ declarations) (Scheme.mono fresh₀ :: env₂ sΓ) body fresh₁).Holds (extend (extend ρ a) b) ↔
          Typing signatures (.mono a :: Γ) body b := by
        simpa only [decl₂, decl₃, fresh₀, fresh₁, env₂, CompTerm.eval_var, extend_some, extend_none]
          using ih _ _ _ fresh₁ (((henv.lift a).lift b).mono fresh₀)
      simp only [generate, Formula.Holds, Typing.lam_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      rw [hb]
      simp [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds, Comp.le, Comp.arrow, Comp.pure,
        CompTerm.eval, CompTerm.arrow, CompTerm.pure, fresh₀, fresh₁, lift₂,
        CompTerm.rename, TyTerm.eval, RowTerm.eval, CompTerm.var, Function.comp_def]
  | app f x ihf ihx =>
      have hf (a b d : Comp Common.model) :
          (generate (decl₃ declarations) (env₃ sΓ) f ⟨CompTerm.arrow fresh₀₃ fresh₁₃, fresh₂₃.row⟩).Holds
            (extend (extend (extend ρ a) b) d) ↔ Typing signatures Γ f (Comp.arrow Common.model a b, d.2) := by
        simpa only [decl₂, decl₃, env₃, fresh₀₃, fresh₁₃, fresh₂₃, CompTerm.eval, CompTerm.arrow,
          CompTerm.var, TyTerm.eval, RowTerm.eval, extend_none, extend_some, Comp.arrow]
          using ihf _ _ _ ⟨CompTerm.arrow fresh₀₃ fresh₁₃, fresh₂₃.row⟩ (((henv.lift a).lift b).lift d)
      have hx (a b d : Comp Common.model) :
          (generate (decl₃ declarations) (env₃ sΓ) x fresh₀₃).Holds (extend (extend (extend ρ a) b) d) ↔
          Typing signatures Γ x a := by
        simpa only [decl₂, decl₃, env₃, fresh₀₃, CompTerm.eval_var, extend_some, extend_none]
          using ihx _ _ _ fresh₀₃ (((henv.lift a).lift b).lift d)
      simp only [generate, Formula.Holds, Typing.app_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      simp only [hf, hx]
      simp only [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds]
      simp only [lift₃, CompTerm.rename, CompTerm.eval, CompTerm.var, fresh₁₃,
        fresh₂₃, TyTerm.eval, RowTerm.eval, TyTerm.eval_rename, RowTerm.eval_rename,
        extend_none, extend_some, Function.comp_def]
      exact exists_comp_row Common.model (fun r => Typing signatures Γ f (Comp.arrow Common.model a b, r) ∧
        Typing signatures Γ x a ∧ Comp.le Common.model (b.1, Common.model.join r b.2) (out.eval Common.model ρ))
  | letE v body ihv ihb =>
      let mono : Formula scopes α := .existsSlot (.existsSlot (
        .and (generate (decl₂ declarations) (env₂ sΓ) v fresh₀)
          (.and (generate (decl₂ declarations) (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ sΓ) body fresh₁)
            (Formula.compLe ⟨fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out)))))
      have hmono : mono.Holds ρ ↔ ∃ a b,
          Typing signatures Γ v a ∧ Typing signatures (.mono (Comp.pure Common.model a.1) :: Γ) body b ∧
          Comp.le Common.model (b.1, Common.model.join a.2 b.2) (out.eval Common.model ρ) := by
        have ha (a b : Comp Common.model) :
            (generate (decl₂ declarations) (env₂ sΓ) v fresh₀).Holds (extend (extend ρ a) b) ↔ Typing signatures Γ v a := by
          simpa only [decl₂, decl₃, env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
            using ihv _ _ _ fresh₀ ((henv.lift a).lift b)
        have hb (a b : Comp Common.model) :
            (generate (decl₂ declarations) (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ sΓ) body fresh₁).Holds
              (extend (extend ρ a) b) ↔ Typing signatures (.mono (Comp.pure Common.model a.1) :: Γ) body b := by
          simpa [decl₂, decl₃, env₂, fresh₀, fresh₁, CompTerm.pure, Comp.pure,
            CompTerm.var, CompTerm.eval, TyTerm.eval, RowTerm.eval]
            using ihb _ _ _ fresh₁ (((henv.lift a).lift b).mono (CompTerm.pure fresh₀.ty))
        simp only [mono, Formula.Holds, ]
        apply exists_congr; intro a
        apply exists_congr; intro b
        rw [ha, hb]
        simp [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
          CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
      cases hv : v.isValue with
      | true =>
          let scheme : Scheme scopes α := .and
            (generate (renameAll some declarations) sΓ.lift v (CompTerm.pure (.var none))) (.rowLe .empty (.var none))
          have hvalue (c : Comp Common.model) :
              (generate (renameAll some declarations) sΓ.lift v (CompTerm.pure (.var none))).Holds (extend ρ c) ↔
              Typing signatures Γ v (Comp.pure Common.model c.1) := by
            simpa only [decl₂, decl₃, CompTerm.eval_pure, TyTerm.eval, extend_none]
              using ihv _ _ _ (CompTerm.pure (.var none)) (henv.lift c)
          have hscheme : ∀ c, scheme.Holds (extend ρ c) ↔ BindingTyping signatures (.poly v Γ) c := by
            intro c
            simp only [scheme, Formula.Holds, CommonEffectRequestGeneration.RowExpr.eval, hvalue, extend_none,
              BindingTyping.poly_iff]
            rfl
          have hbody := ihb (scheme :: sΓ) (.poly v Γ :: Γ) ρ out (henv.cons hscheme)
          simp only [generate, hv]
          change (((∃ c, (generate (renameAll some declarations) sΓ.lift v (CompTerm.pure (.var none))).Holds (extend ρ c)) ∧
            (generate declarations (scheme :: sΓ) body out).Holds ρ) ∨ mono.Holds ρ) ↔ _
          rw [Typing.letValue_iff signatures Γ v body (out.eval Common.model ρ) hv]
          apply or_congr
          · simp only [hvalue]
            rw [hbody]
            exact and_congr (exists_comp_ty Common.model (fun a => Typing signatures Γ v (Comp.pure Common.model a))) Iff.rfl
          · exact hmono
      | false =>
          simp only [generate, hv]
          change mono.Holds ρ ↔ _
          exact hmono.trans (Typing.letComputed_iff signatures Γ v body (out.eval Common.model ρ) hv).symm
  | branch g y n ihg ihy ihn =>
      have hg (a b d : Comp Common.model) :
          (generate (decl₃ declarations) (env₃ sΓ) g ⟨.base .bool, fresh₀₃.row⟩).Holds
            (extend (extend (extend ρ a) b) d) ↔ Typing signatures Γ g (Common.model.base .bool, a.2) := by
        simpa only [decl₂, decl₃, env₃, fresh₀₃, CompTerm.eval, CompTerm.var, TyTerm.eval, RowTerm.eval,
          extend_none, extend_some] using ihg _ _ _ ⟨.base .bool, fresh₀₃.row⟩ (((henv.lift a).lift b).lift d)
      have hy (a b d : Comp Common.model) :
          (generate (decl₃ declarations) (env₃ sΓ) y fresh₁₃).Holds (extend (extend (extend ρ a) b) d) ↔
          Typing signatures Γ y b := by
        simpa only [decl₂, decl₃, env₃, fresh₁₃, CompTerm.eval_var, extend_none, extend_some]
          using ihy _ _ _ fresh₁₃ (((henv.lift a).lift b).lift d)
      have hn (a b d : Comp Common.model) :
          (generate (decl₃ declarations) (env₃ sΓ) n fresh₂₃).Holds (extend (extend (extend ρ a) b) d) ↔
          Typing signatures Γ n d := by
        simpa only [decl₂, decl₃, env₃, fresh₂₃, CompTerm.eval_var, extend_none]
          using ihn _ _ _ fresh₂₃ (((henv.lift a).lift b).lift d)
      simp only [generate, Formula.Holds, Typing.branch_iff]
      simp only [hg, hy, hn]
      simp only [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds]
      simp only [lift₃, CompTerm.rename, CompTerm.eval, CompTerm.var, fresh₀₃, fresh₁₃,
        fresh₂₃, TyTerm.eval, RowTerm.eval, TyTerm.eval_rename, RowTerm.eval_rename,
        extend_none, extend_some, Function.comp_def]
      exact exists_comp_row Common.model (fun r => ∃ a b, Typing signatures Γ g (Common.model.base .bool, r) ∧
        Typing signatures Γ y a ∧ Typing signatures Γ n b ∧
        Comp.le Common.model (Common.model.union a.1 b.1, Common.model.join r (Common.model.join a.2 b.2)) (out.eval Common.model ρ))
  | pair x y ihx ihy =>
      have hx (a b : Comp Common.model) :
          (generate (decl₂ declarations) (env₂ sΓ) x fresh₀).Holds (extend (extend ρ a) b) ↔ Typing signatures Γ x a := by
        simpa only [decl₂, decl₃, env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
          using ihx _ _ _ fresh₀ ((henv.lift a).lift b)
      have hy (a b : Comp Common.model) :
          (generate (decl₂ declarations) (env₂ sΓ) y fresh₁).Holds (extend (extend ρ a) b) ↔ Typing signatures Γ y b := by
        simpa only [decl₂, decl₃, env₂, fresh₁, CompTerm.eval_var, extend_none]
          using ihy _ _ _ fresh₁ ((henv.lift a).lift b)
      simp only [generate, Formula.Holds, Typing.pair_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      rw [hx, hy]
      simp [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
        CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
  | fst x ih =>
      have hx (a b : Comp Common.model) :
          (generate (decl₂ declarations) (env₂ sΓ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩).Holds
            (extend (extend ρ a) b) ↔ Typing signatures Γ x (Common.model.pair a.1 b.1, a.2) := by
        simpa only [decl₂, decl₃, env₂, fresh₀, fresh₁, CompTerm.eval, CompTerm.var, TyTerm.eval, RowTerm.eval,
          extend_none, extend_some] using ih _ _ _ ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩ ((henv.lift a).lift b)
      simp only [generate, Formula.Holds, Typing.fst_iff]
      simp only [hx]
      simp only [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds]
      simp only [lift₂, CompTerm.rename, CompTerm.eval, CompTerm.var, fresh₀,
        TyTerm.eval, RowTerm.eval, TyTerm.eval_rename, RowTerm.eval_rename,
        extend_none, extend_some, Function.comp_def]
      constructor
      · rintro ⟨a, b, hx, hc⟩; exact ⟨a.1, b.1, a.2, hx, hc⟩
      · rintro ⟨a, b, er, hx, hc⟩; exact ⟨(a, er), (b, Common.model.empty), hx, hc⟩
  | snd x ih =>
      have hx (a b : Comp Common.model) :
          (generate (decl₂ declarations) (env₂ sΓ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩).Holds
            (extend (extend ρ a) b) ↔ Typing signatures Γ x (Common.model.pair a.1 b.1, a.2) := by
        simpa only [decl₂, decl₃, env₂, fresh₀, fresh₁, CompTerm.eval, CompTerm.var, TyTerm.eval, RowTerm.eval,
          extend_none, extend_some] using ih _ _ _ ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩ ((henv.lift a).lift b)
      simp only [generate, Formula.Holds, Typing.snd_iff]
      simp only [hx]
      simp only [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds]
      simp only [lift₂, CompTerm.rename, CompTerm.eval, CompTerm.var, fresh₀, fresh₁,
        TyTerm.eval, RowTerm.eval, TyTerm.eval_rename, RowTerm.eval_rename,
        extend_none, extend_some, Function.comp_def]
      constructor
      · rintro ⟨a, b, hx, hc⟩; exact ⟨a.1, b.1, a.2, hx, hc⟩
      · rintro ⟨a, b, er, hx, hc⟩; exact ⟨(a, er), (b, Common.model.empty), hx, hc⟩
  | emptyRecord => simp [generate, CompTerm.eval, CompTerm.pure, TyTerm.eval, RowTerm.eval, Comp.pure]
  | record l x r ihx ihr =>
      have hx (a b : Comp Common.model) :
          (generate (decl₂ declarations) (env₂ sΓ) x fresh₀).Holds (extend (extend ρ a) b) ↔ Typing signatures Γ x a := by
        simpa only [decl₂, decl₃, env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
          using ihx _ _ _ fresh₀ ((henv.lift a).lift b)
      have hr (a b : Comp Common.model) :
          (generate (decl₂ declarations) (env₂ sΓ) r fresh₁).Holds (extend (extend ρ a) b) ↔ Typing signatures Γ r b := by
        simpa only [decl₂, decl₃, env₂, fresh₁, CompTerm.eval_var, extend_none]
          using ihr _ _ _ fresh₁ ((henv.lift a).lift b)
      simp only [generate, Formula.Holds, Formula.tyLe, Core.PresenceGeneration.Formula.Holds, Typing.record_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      rw [hx, hr]
      simp [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
        CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
  | recordDefault l source fallback ihs ihf =>
      have hs (a b : Comp Common.model) :
          (generate (decl₂ declarations) (env₂ sΓ) source fresh₀).Holds (extend (extend ρ a) b) ↔
            Typing signatures Γ source a := by
        simpa only [decl₂, decl₃, env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
          using ihs _ _ _ fresh₀ ((henv.lift a).lift b)
      have hf (a b : Comp Common.model) :
          (generate (decl₂ declarations) (env₂ sΓ) fallback fresh₁).Holds (extend (extend ρ a) b) ↔
            Typing signatures Γ fallback b := by
        simpa only [decl₂, decl₃, env₂, fresh₁, CompTerm.eval_var, extend_none]
          using ihf _ _ _ fresh₁ ((henv.lift a).lift b)
      simp only [generate, Formula.Holds, Formula.tyLe, Core.PresenceGeneration.Formula.Holds, Typing.recordDefault_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      rw [hs, hf]
      simp [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
        CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
  | field l x ih =>
      have hx (a : Comp Common.model) :
          (generate (renameAll some declarations) sΓ.lift x ⟨.required l (.var none), .var none⟩).Holds
            (extend ρ a) ↔ Typing signatures Γ x (Common.model.required l a.1, a.2) := by
        simpa only [decl₂, decl₃, CompTerm.eval, TyTerm.eval, RowTerm.eval, extend_none]
          using ih _ _ _ ⟨.required l (.var none), .var none⟩ (henv.lift a)
      simp only [generate, Formula.Holds, Typing.field_iff]
      simp only [hx]
      simp [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
        CompTerm.rename, TyTerm.eval, RowTerm.eval, Function.comp_def, Prod.exists]
  | variant l x ih =>
      have hx (a : Comp Common.model) :
          (generate (renameAll some declarations) sΓ.lift x (CompTerm.var none)).Holds (extend ρ a) ↔ Typing signatures Γ x a := by
        simpa only [decl₂, decl₃, CompTerm.eval_var, extend_none] using ih _ _ _ (CompTerm.var none) (henv.lift a)
      simp only [generate, Formula.Holds, Typing.variant_iff]
      apply exists_congr; intro a
      rw [hx]
      simp [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds, Comp.le, CompTerm.eval,
        CompTerm.rename, TyTerm.eval, RowTerm.eval, Function.comp_def]

  | request operation payload ih =>
    cases found : declarations[operation]? with
    | none =>
      have absent : signatures[operation]? = none := by
        rw [← henv.declarations, lookup_interpretAll, found]
        rfl
      simp [generate, found, Formula.Holds, Core.PresenceGeneration.Formula.Holds,
        Typing.request_iff, absent]
    | some declaration =>
      have resolved : signatures[operation]? = some (interpret ρ declaration) := by
        rw [← henv.declarations, lookup_interpretAll, found]
        rfl
      have payloadExact (locals : Fin declaration.locals → Common.Ty) (value : Computation) :
          (generate (renameAll some (renameAll Sum.inl declarations)) (sΓ.rename Sum.inl).lift payload
            ⟨declaration.input.rename some, .var none⟩).Holds (extend (localEnv ρ locals) value) ↔
          Typing signatures Γ payload (declaration.input.eval Common.model (localEnv ρ locals), value.2) := by
        simpa only [decl₂, decl₃, CompTerm.eval, TyTerm.eval_rename, RowTerm.eval, extend_comp_some, extend_none] using
          ih _ _ _ ⟨declaration.input.rename some, .var none⟩
            ((henv.rename Sum.inl (localEnv ρ locals) rfl).lift value)
      have finiteShape :
          (generate declarations sΓ (.request operation payload) out).Holds ρ ↔
            ∃ locals : Fin declaration.locals → Common.Ty, ∃ value : Computation,
              Typing signatures Γ payload (declaration.input.eval Common.model (localEnv ρ locals), value.2) ∧
              Common.Subtype (declaration.output.eval Common.model (localEnv ρ locals)) (out.eval Common.model ρ).1 ∧
              Common.rowLe (Common.rowJoin value.2 (Common.rowJoin
                ((CommonSignedRows.commonAlgebra scopes).head declaration.key)
                (RowInference.keysRow (CommonSignedRows.commonAlgebra scopes) declaration.extra))) (out.eval Common.model ρ).2 := by
        simp only [generate, found, Formula.Holds, payloadExact, Formula.tyLe,
          Core.PresenceGeneration.Formula.Holds, TyTerm.eval_rename, extend_comp_some,
          CompTerm.rename, localEnv_comp_inl, RowExpr.eval, RowExpr.eval_heads,
          RowExpr.eval_fromPresence, RowTerm.eval_rename, extend_none]
        rfl
      rw [finiteShape]
      constructor
      · rintro ⟨locals, value, payloadTyped, valueBound, rowBound⟩
        exact .request (signature := interpret ρ declaration) (locals := locals) resolved payloadTyped valueBound rowBound
      · intro typed
        obtain ⟨actual, actualFound, locals, row, payloadTyped, valueBound, rowBound⟩ :=
          (Typing.request_iff signatures Γ operation payload (out.eval Common.model ρ)).mp typed
        have same : actual = interpret ρ declaration := Option.some.inj (actualFound.symm.trans resolved)
        subst actual
        exact ⟨locals, (.base .unit, row), payloadTyped, valueBound, rowBound⟩
  | boundary boundary body ih =>
    have bodyExact (input : Computation) :
        (generate (renameAll some declarations) sΓ.lift body (CompTerm.var none)).Holds (extend ρ input) ↔
          Typing signatures Γ body input := by
      simpa only [decl₂, decl₃, CompTerm.eval_var, extend_none] using
        ih _ _ _ (CompTerm.var none) (henv.lift input)
    rw [Typing.boundary_iff]
    simp only [generate, Formula.Holds, bodyExact, Formula.tyLe,
      Core.PresenceGeneration.Formula.Holds, TyTerm.eval, TyTerm.eval_rename,
      extend_none, extend_comp_some, boundaryRow_eval, RowExpr.eval, RowExpr.eval_fromPresence,
      RowTerm.eval_rename]
    rfl
  | handler permission operation action onReturn onOperation iha ihr iho =>
    cases found : declarations[operation]? with
    | none =>
      have absent : signatures[operation]? = none := by
        rw [← henv.declarations, lookup_interpretAll, found]
        rfl
      simp [generate, found, Formula.Holds, Core.PresenceGeneration.Formula.Holds,
        Typing.handler_iff, absent]
    | some declaration =>
      have resolved : signatures[operation]? = some (interpret ρ declaration) := by
        rw [← henv.declarations, lookup_interpretAll, found]
        rfl
      have actionExact (a b : Computation) :
          (generate (decl₂ declarations) (env₂ sΓ) action fresh₀).Holds (extend (extend ρ a) b) ↔
            Typing signatures Γ action a := by
        simpa only [decl₂, decl₃, env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some] using
          iha _ _ _ fresh₀ ((henv.lift a).lift b)
      have returnExact (a b : Computation) :
          (generate (decl₂ declarations) (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ sΓ) onReturn fresh₁).Holds
            (extend (extend ρ a) b) ↔
            Typing signatures (.mono (Comp.pure Common.model a.1) :: Γ) onReturn b := by
        simpa [decl₂, decl₃, env₂, fresh₀, fresh₁, CompTerm.eval, CompTerm.pure, CompTerm.var, TyTerm.eval, RowTerm.eval, Comp.pure] using
          ihr _ _ _ fresh₁ (((henv.lift a).lift b).mono (CompTerm.pure fresh₀.ty))
      have armTyped (a b : Computation) (locals : Fin declaration.locals → Common.Ty) (operated : Computation) :=
        iho _ _ _ (CompTerm.var none)
          ((((((henv.lift a).lift b).rename Sum.inl (localEnv (extend (extend ρ a) b) locals) rfl).mono
            (CompTerm.pure (CompTerm.arrow
              (CompTerm.pure (declaration.output.rename (Sum.map (fun name => some (some name)) id)))
              (fresh₀.rename Sum.inl)))).mono
            (CompTerm.pure (declaration.input.rename (Sum.map (fun name => some (some name)) id)))).lift operated)
      simp only [CompTerm.eval_var, extend_none, CompTerm.eval_pure, arrow_eval,
        TyTerm.eval_rename, local_names, CompTerm.eval_rename, localEnv_comp_inl,
        fresh₀, CompTerm.eval_var, extend_some] at armTyped
      cases allowed : permission.allows declaration.key with
      | false =>
        simp [generate, found, allowed, Formula.Holds, Core.PresenceGeneration.Formula.Holds,
          Typing.handler_iff, resolved, interpret]
      | true =>
        have finiteShape :
            (generate declarations sΓ (.handler permission operation action onReturn onOperation) out).Holds ρ ↔
              ∃ input returned,
                Typing signatures Γ action input ∧
                Typing signatures (.mono (Comp.pure Common.model input.1) :: Γ) onReturn returned ∧
                ∀ locals : Fin declaration.locals → Common.Ty, ∃ operated : Computation,
                  Typing signatures
                    (.mono (Comp.pure Common.model (declaration.input.eval Common.model (localEnv ρ locals))) ::
                     .mono (Comp.pure Common.model (Comp.arrow Common.model
                       (Comp.pure Common.model (declaration.output.eval Common.model (localEnv ρ locals))) input)) :: Γ)
                    onOperation operated ∧
                  Common.Subtype (.union returned.1 operated.1) (out.eval Common.model ρ).1 ∧
                  Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual [declaration.key] input.2)
                    (Common.rowJoin returned.2 operated.2)) (out.eval Common.model ρ).2 := by
          simp only [generate, found, allowed, ↓reduceIte, Formula.Holds, handlerChecks_holds]
          simp only [actionExact, returnExact]
          simp only [decl₂, env₂, fresh₀, fresh₁]
          simp only [armTyped]
          simp only [CompTerm.eval_rename, localEnv_comp_inl, lift₂, CompTerm.eval_var,
            extend_none, extend_some]
          rfl
        rw [finiteShape, Typing.handler_iff]
        simp [resolved, interpret, allowed]
end Yulang.CommonEffectRecursiveExact
