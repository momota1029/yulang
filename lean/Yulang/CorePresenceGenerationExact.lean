import Yulang.CorePresenceGeneration

/-!
# Model-parametric exactness of presence constraint generation

Every source expression, input environment, captured value/row assignment and
output term is quantified. The sole environment hypothesis says that input
symbolic schemes and independent bindings have the same instances. Solver
success, fuel, saturation, and a successful input derivation are not premises.

The concrete regular presence model and its solver remain separate obligations;
this module does not claim the full `presence_generate_exact` M1 contract for a
model that has not yet been constructed.
-/

namespace Yulang.Core.PresenceGeneration

open Inference (Expr Base)

/-- Exactness of the generated constraint scheme. Both directions quantify
over all semantic types and rows; neither assumes that a solver succeeds.
The environment hypothesis only relates input schemes to input bindings. -/
theorem generate_models_iff_typing (m : Model) (e : Expr)
    (sΓ : SchemeEnv α) (Γ : List (Binding m)) (ρ : α → Comp m)
    (out : CompTerm α) (henv : EnvRel m ρ sΓ Γ) :
    (generate sΓ e out).Holds m ρ ↔ Typing m Γ e (out.eval m ρ) := by
  induction e generalizing α sΓ Γ ρ out with
  | var n => simpa [generate] using henv n (out.eval m ρ)
  | lit b => simp [generate, CompTerm.eval, CompTerm.pure, TyTerm.eval, RowTerm.eval, Comp.pure]
  | lam body ih =>
      have hb (a b : Comp m) :
          (generate (Scheme.mono fresh₀ :: env₂ sΓ) body fresh₁).Holds m (extend (extend ρ a) b) ↔
          Typing m (.mono a :: Γ) body b := by
        simpa only [fresh₀, fresh₁, env₂, CompTerm.eval_var, extend_some, extend_none]
          using ih _ _ _ fresh₁ (((henv.lift a).lift b).mono fresh₀)
      simp only [generate, Formula.Holds, Typing.lam_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      rw [hb]
      simp [Formula.compLe, Formula.Holds, Comp.le, Comp.arrow, Comp.pure,
        CompTerm.eval, CompTerm.arrow, CompTerm.pure, fresh₀, fresh₁, lift₂,
        CompTerm.rename, TyTerm.eval, RowTerm.eval, CompTerm.var, Function.comp_def]
  | app f x ihf ihx =>
      have hf (a b d : Comp m) :
          (generate (env₃ sΓ) f ⟨CompTerm.arrow fresh₀₃ fresh₁₃, fresh₂₃.row⟩).Holds m
            (extend (extend (extend ρ a) b) d) ↔ Typing m Γ f (Comp.arrow m a b, d.2) := by
        simpa only [env₃, fresh₀₃, fresh₁₃, fresh₂₃, CompTerm.eval, CompTerm.arrow,
          CompTerm.var, TyTerm.eval, RowTerm.eval, extend_none, extend_some, Comp.arrow]
          using ihf _ _ _ ⟨CompTerm.arrow fresh₀₃ fresh₁₃, fresh₂₃.row⟩ (((henv.lift a).lift b).lift d)
      have hx (a b d : Comp m) :
          (generate (env₃ sΓ) x fresh₀₃).Holds m (extend (extend (extend ρ a) b) d) ↔
          Typing m Γ x a := by
        simpa only [env₃, fresh₀₃, CompTerm.eval_var, extend_some, extend_none]
          using ihx _ _ _ fresh₀₃ (((henv.lift a).lift b).lift d)
      simp only [generate, Formula.Holds, Typing.app_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      simp only [hf, hx]
      simp only [Formula.compLe, Formula.Holds]
      simp only [lift₃, CompTerm.rename, CompTerm.eval, CompTerm.var, fresh₁₃,
        fresh₂₃, TyTerm.eval, RowTerm.eval, TyTerm.eval_rename, RowTerm.eval_rename,
        extend_none, extend_some, Function.comp_def]
      exact exists_comp_row m (fun r => Typing m Γ f (Comp.arrow m a b, r) ∧
        Typing m Γ x a ∧ Comp.le m (b.1, m.join r b.2) (out.eval m ρ))
  | letE v body ihv ihb =>
      let mono : Formula α := .existsSlot (.existsSlot (
        .and (generate (env₂ sΓ) v fresh₀)
          (.and (generate (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ sΓ) body fresh₁)
            (Formula.compLe ⟨fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out)))))
      have hmono : mono.Holds m ρ ↔ ∃ a b,
          Typing m Γ v a ∧ Typing m (.mono (Comp.pure m a.1) :: Γ) body b ∧
          Comp.le m (b.1, m.join a.2 b.2) (out.eval m ρ) := by
        have ha (a b : Comp m) :
            (generate (env₂ sΓ) v fresh₀).Holds m (extend (extend ρ a) b) ↔ Typing m Γ v a := by
          simpa only [env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
            using ihv _ _ _ fresh₀ ((henv.lift a).lift b)
        have hb (a b : Comp m) :
            (generate (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ sΓ) body fresh₁).Holds m
              (extend (extend ρ a) b) ↔ Typing m (.mono (Comp.pure m a.1) :: Γ) body b := by
          simpa [env₂, fresh₀, fresh₁, CompTerm.pure, Comp.pure,
            CompTerm.var, CompTerm.eval, TyTerm.eval, RowTerm.eval]
            using ihb _ _ _ fresh₁ (((henv.lift a).lift b).mono (CompTerm.pure fresh₀.ty))
        simp only [mono, Formula.Holds]
        apply exists_congr; intro a
        apply exists_congr; intro b
        rw [ha, hb]
        simp [Formula.compLe, Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
          CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
      cases hv : v.isValue with
      | true =>
          let scheme : Scheme α := .and
            (generate sΓ.lift v (CompTerm.pure (.var none))) (.rowLe .empty (.var none))
          have hvalue (c : Comp m) :
              (generate sΓ.lift v (CompTerm.pure (.var none))).Holds m (extend ρ c) ↔
              Typing m Γ v (Comp.pure m c.1) := by
            simpa only [CompTerm.eval_pure, TyTerm.eval, extend_none]
              using ihv _ _ _ (CompTerm.pure (.var none)) (henv.lift c)
          have hscheme : ∀ c, scheme.Holds m (extend ρ c) ↔ BindingTyping m (.poly v Γ) c := by
            intro c
            simp only [scheme, Formula.Holds, hvalue, RowTerm.eval, extend_none,
              BindingTyping.poly_iff]
          have hbody := ihb (scheme :: sΓ) (.poly v Γ :: Γ) ρ out (henv.cons hscheme)
          simp only [generate, hv]
          change (((∃ c, (generate sΓ.lift v (CompTerm.pure (.var none))).Holds m (extend ρ c)) ∧
            (generate (scheme :: sΓ) body out).Holds m ρ) ∨ mono.Holds m ρ) ↔ _
          rw [Typing.letValue_iff m Γ v body (out.eval m ρ) hv]
          apply or_congr
          · simp only [hvalue]
            rw [hbody]
            exact and_congr (exists_comp_ty m (fun a => Typing m Γ v (Comp.pure m a))) Iff.rfl
          · exact hmono
      | false =>
          simp only [generate, hv]
          change mono.Holds m ρ ↔ _
          exact hmono.trans (Typing.letComputed_iff m Γ v body (out.eval m ρ) hv).symm
  | branch g y n ihg ihy ihn =>
      have hg (a b d : Comp m) :
          (generate (env₃ sΓ) g ⟨.base .bool, fresh₀₃.row⟩).Holds m
            (extend (extend (extend ρ a) b) d) ↔ Typing m Γ g (m.base .bool, a.2) := by
        simpa only [env₃, fresh₀₃, CompTerm.eval, CompTerm.var, TyTerm.eval, RowTerm.eval,
          extend_none, extend_some] using ihg _ _ _ ⟨.base .bool, fresh₀₃.row⟩ (((henv.lift a).lift b).lift d)
      have hy (a b d : Comp m) :
          (generate (env₃ sΓ) y fresh₁₃).Holds m (extend (extend (extend ρ a) b) d) ↔
          Typing m Γ y b := by
        simpa only [env₃, fresh₁₃, CompTerm.eval_var, extend_none, extend_some]
          using ihy _ _ _ fresh₁₃ (((henv.lift a).lift b).lift d)
      have hn (a b d : Comp m) :
          (generate (env₃ sΓ) n fresh₂₃).Holds m (extend (extend (extend ρ a) b) d) ↔
          Typing m Γ n d := by
        simpa only [env₃, fresh₂₃, CompTerm.eval_var, extend_none]
          using ihn _ _ _ fresh₂₃ (((henv.lift a).lift b).lift d)
      simp only [generate, Formula.Holds, Typing.branch_iff]
      simp only [hg, hy, hn]
      simp only [Formula.compLe, Formula.Holds]
      simp only [lift₃, CompTerm.rename, CompTerm.eval, CompTerm.var, fresh₀₃, fresh₁₃,
        fresh₂₃, TyTerm.eval, RowTerm.eval, TyTerm.eval_rename, RowTerm.eval_rename,
        extend_none, extend_some, Function.comp_def]
      exact exists_comp_row m (fun r => ∃ a b, Typing m Γ g (m.base .bool, r) ∧
        Typing m Γ y a ∧ Typing m Γ n b ∧
        Comp.le m (m.union a.1 b.1, m.join r (m.join a.2 b.2)) (out.eval m ρ))
  | pair x y ihx ihy =>
      have hx (a b : Comp m) :
          (generate (env₂ sΓ) x fresh₀).Holds m (extend (extend ρ a) b) ↔ Typing m Γ x a := by
        simpa only [env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
          using ihx _ _ _ fresh₀ ((henv.lift a).lift b)
      have hy (a b : Comp m) :
          (generate (env₂ sΓ) y fresh₁).Holds m (extend (extend ρ a) b) ↔ Typing m Γ y b := by
        simpa only [env₂, fresh₁, CompTerm.eval_var, extend_none]
          using ihy _ _ _ fresh₁ ((henv.lift a).lift b)
      simp only [generate, Formula.Holds, Typing.pair_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      rw [hx, hy]
      simp [Formula.compLe, Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
        CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
  | fst x ih =>
      have hx (a b : Comp m) :
          (generate (env₂ sΓ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩).Holds m
            (extend (extend ρ a) b) ↔ Typing m Γ x (m.pair a.1 b.1, a.2) := by
        simpa only [env₂, fresh₀, fresh₁, CompTerm.eval, CompTerm.var, TyTerm.eval, RowTerm.eval,
          extend_none, extend_some] using ih _ _ _ ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩ ((henv.lift a).lift b)
      simp only [generate, Formula.Holds, Typing.fst_iff]
      simp only [hx]
      simp only [Formula.compLe, Formula.Holds]
      simp only [lift₂, CompTerm.rename, CompTerm.eval, CompTerm.var, fresh₀,
        TyTerm.eval, RowTerm.eval, TyTerm.eval_rename, RowTerm.eval_rename,
        extend_none, extend_some, Function.comp_def]
      constructor
      · rintro ⟨a, b, hx, hc⟩; exact ⟨a.1, b.1, a.2, hx, hc⟩
      · rintro ⟨a, b, er, hx, hc⟩; exact ⟨(a, er), (b, m.empty), hx, hc⟩
  | snd x ih =>
      have hx (a b : Comp m) :
          (generate (env₂ sΓ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩).Holds m
            (extend (extend ρ a) b) ↔ Typing m Γ x (m.pair a.1 b.1, a.2) := by
        simpa only [env₂, fresh₀, fresh₁, CompTerm.eval, CompTerm.var, TyTerm.eval, RowTerm.eval,
          extend_none, extend_some] using ih _ _ _ ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩ ((henv.lift a).lift b)
      simp only [generate, Formula.Holds, Typing.snd_iff]
      simp only [hx]
      simp only [Formula.compLe, Formula.Holds]
      simp only [lift₂, CompTerm.rename, CompTerm.eval, CompTerm.var, fresh₀, fresh₁,
        TyTerm.eval, RowTerm.eval, TyTerm.eval_rename, RowTerm.eval_rename,
        extend_none, extend_some, Function.comp_def]
      constructor
      · rintro ⟨a, b, hx, hc⟩; exact ⟨a.1, b.1, a.2, hx, hc⟩
      · rintro ⟨a, b, er, hx, hc⟩; exact ⟨(a, er), (b, m.empty), hx, hc⟩
  | emptyRecord => simp [generate, CompTerm.eval, CompTerm.pure, TyTerm.eval, RowTerm.eval, Comp.pure]
  | record l x r ihx ihr =>
      have hx (a b : Comp m) :
          (generate (env₂ sΓ) x fresh₀).Holds m (extend (extend ρ a) b) ↔ Typing m Γ x a := by
        simpa only [env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
          using ihx _ _ _ fresh₀ ((henv.lift a).lift b)
      have hr (a b : Comp m) :
          (generate (env₂ sΓ) r fresh₁).Holds m (extend (extend ρ a) b) ↔ Typing m Γ r b := by
        simpa only [env₂, fresh₁, CompTerm.eval_var, extend_none]
          using ihr _ _ _ fresh₁ ((henv.lift a).lift b)
      simp only [generate, Formula.Holds, Typing.record_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      rw [hx, hr]
      simp [Formula.compLe, Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
        CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
  | recordDefault l source fallback ihs ihf =>
      have hs (a b : Comp m) :
          (generate (env₂ sΓ) source fresh₀).Holds m (extend (extend ρ a) b) ↔
            Typing m Γ source a := by
        simpa only [env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
          using ihs _ _ _ fresh₀ ((henv.lift a).lift b)
      have hf (a b : Comp m) :
          (generate (env₂ sΓ) fallback fresh₁).Holds m (extend (extend ρ a) b) ↔
            Typing m Γ fallback b := by
        simpa only [env₂, fresh₁, CompTerm.eval_var, extend_none]
          using ihf _ _ _ fresh₁ ((henv.lift a).lift b)
      simp only [generate, Formula.Holds, Typing.recordDefault_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      rw [hs, hf]
      simp [Formula.compLe, Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
        CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
  | field l x ih =>
      have hx (a : Comp m) :
          (generate sΓ.lift x ⟨.required l (.var none), .var none⟩).Holds m
            (extend ρ a) ↔ Typing m Γ x (m.required l a.1, a.2) := by
        simpa only [CompTerm.eval, TyTerm.eval, RowTerm.eval, extend_none]
          using ih _ _ _ ⟨.required l (.var none), .var none⟩ (henv.lift a)
      simp only [generate, Formula.Holds, Typing.field_iff]
      simp only [hx]
      simp [Formula.compLe, Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
        CompTerm.rename, TyTerm.eval, RowTerm.eval, Function.comp_def, Prod.exists]
  | variant l x ih =>
      have hx (a : Comp m) :
          (generate sΓ.lift x (CompTerm.var none)).Holds m (extend ρ a) ↔ Typing m Γ x a := by
        simpa only [CompTerm.eval_var, extend_none] using ih _ _ _ (CompTerm.var none) (henv.lift a)
      simp only [generate, Formula.Holds, Typing.variant_iff]
      apply exists_congr; intro a
      rw [hx]
      simp [Formula.compLe, Formula.Holds, Comp.le, CompTerm.eval,
        CompTerm.rename, TyTerm.eval, RowTerm.eval, Function.comp_def]

/-- Constraint-scheme entry point; existential constraints are retained.
Its one bound slot is the inferred result;
the existing free slots of `Γ` remain parameters, not generalized variables. -/
def principal (Γ : SchemeEnv α) (e : Expr) : Scheme α :=
  generate Γ.lift e (CompTerm.var none)

/-- The principal scheme represents all and only the declarative typings. -/
theorem principal_exact (m : Model) (e : Expr) (sΓ : SchemeEnv α)
    (Γ : List (Binding m)) (ρ : α → Comp m) (henv : EnvRel m ρ sΓ Γ) (c : Comp m) :
    (principal sΓ e).Holds m (extend ρ c) ↔ Typing m Γ e c := by
  simpa only [principal, CompTerm.eval_var, extend_none]
    using generate_models_iff_typing m e sΓ.lift Γ (extend ρ c) (CompTerm.var none) (henv.lift c)

theorem principal_sound (m : Model) (e : Expr) (sΓ : SchemeEnv α)
    (Γ : List (Binding m)) (ρ : α → Comp m) (henv : EnvRel m ρ sΓ Γ) (c : Comp m)
    (h : (principal sΓ e).Holds m (extend ρ c)) : Typing m Γ e c :=
  (principal_exact m e sΓ Γ ρ henv c).mp h

theorem principal_complete (m : Model) (e : Expr) (sΓ : SchemeEnv α)
    (Γ : List (Binding m)) (ρ : α → Comp m) (henv : EnvRel m ρ sΓ Γ) (c : Comp m)
    (h : Typing m Γ e c) : (principal sΓ e).Holds m (extend ρ c) :=
  (principal_exact m e sΓ Γ ρ henv c).mpr h

/-- Every sound candidate scheme is an instance-set subset of the generated
scheme. This is principality of constraints, not a solved normal-form theorem. -/
theorem principal_most_general (m : Model) (e : Expr) (sΓ : SchemeEnv α)
    (Γ : List (Binding m)) (ρ : α → Comp m) (henv : EnvRel m ρ sΓ Γ)
    (candidate : Scheme α)
    (hsound : ∀ c, candidate.Holds m (extend ρ c) → Typing m Γ e c) :
    ∀ c, candidate.Holds m (extend ρ c) → (principal sΓ e).Holds m (extend ρ c) := by
  intro c hc
  exact principal_complete m e sΓ Γ ρ henv c (hsound c hc)

theorem generate_unbound (Γ : SchemeEnv α) (n : Nat) (out : CompTerm α)
    (h : Γ[n]? = none) : generate Γ (.var n) out = .bot := by
  simp [generate, Scheme.lookup, h]

theorem unbound_not_typable (m : Model) (Γ : List (Binding m)) (n : Nat) (c : Comp m)
    (h : Γ[n]? = none) : ¬ Typing m Γ (.var n) c := by
  simp [Typing.var_iff, BindingLookup, h]

/-- Formula size counts logical nodes. Type-term sizes are separate; there is
no performance claim that scheme instantiation is constant time. -/
def Formula.nodes : Formula α → Nat
  | .top | .bot | .tyLe _ _ | .rowLe _ _ => 1
  | .and p q | .or p q => 1 + p.nodes + q.nodes
  | .existsSlot p => 1 + p.nodes

theorem Formula.nodes_pos (p : Formula α) : 0 < p.nodes := by
  cases p <;> simp [nodes] <;> omega

theorem Formula.nodes_rename (p : Formula α) (f : α → β) :
    (p.rename f).nodes = p.nodes := by
  induction p generalizing β <;> simp_all [rename, nodes]

theorem Formula.nodes_subst (p : Formula α) (f : α → CompTerm β) :
    (p.subst f).nodes = p.nodes := by
  induction p generalizing β <;> simp_all [subst, nodes]

theorem Scheme.instantiation_nodes (s : Scheme α) (c : CompTerm α) :
    (s.instantiate c).nodes = s.nodes := by
  simp [instantiate, Formula.nodes_subst]

/-- Strictness is independent of the source's presence information: even a
source that already contains the selected field cannot hide an unbound fallback.
Every model, label, source expression, unbound index and result is quantified. -/
theorem unbound_default_fallback (m : Model) (label : Nat) (source : Expr)
    (index : Nat) (c : Comp m) :
    ¬ Typing m [] (.recordDefault label source (.var index)) c := by
  intro typed
  obtain ⟨a, b, _, fallback, _, _⟩ := (Typing.recordDefault_iff m [] label source (.var index) c).mp typed
  exact unbound_not_typable m [] index b (by simp) fallback

/-- The formula generator enforces the same strictness, for every arbitrary
assignment of free type/row slots and every symbolic output. -/
theorem generate_unbound_default_fallback (m : Model) (label : Nat) (source : Expr)
    (index : Nat) (ρ : α → Comp m) (out : CompTerm α) :
    ¬ (generate [] (.recordDefault label source (.var index)) out).Holds m ρ := by
  intro held
  have typed := (generate_models_iff_typing m (.recordDefault label source (.var index))
    [] [] ρ out (EnvRel.nil m ρ)).mp held
  exact unbound_default_fallback m label source index (out.eval m ρ) typed

end Yulang.Core.PresenceGeneration
