import Yulang.CommonEffectFormula

/-! Ordinary presence generation with the extended finite effect-scheme
vocabulary. Input schemes may contain signed rows and universal local types.
The source here is still Inference.Expr; recursive effect constructors are
not introduced by this module. -/
namespace Yulang.CommonEffectFormula
open Core.PresenceGeneration
open CommonEffectRequestGeneration (Computation)

variable {scopes : Nat}

def Formula.tyLe (first last : TyTerm α) : Formula scopes α := .core (.tyLe first last)
def Formula.compLe (first last : CompTerm α) : Formula scopes α := .core (.compLe first last)

@[simp] theorem Formula.holds_compLe (first last : CompTerm α) (assignment : α → Computation) :
    (Formula.compLe (scopes := scopes) first last).Holds assignment ↔
      Comp.le Common.model (first.eval Common.model assignment) (last.eval Common.model assignment) := Iff.rfl

@[simp] theorem Formula.holds_tyLe (first last : TyTerm α) (assignment : α → Computation) :
    (Formula.tyLe (scopes := scopes) first last).Holds assignment ↔
      Common.Subtype (first.eval Common.model assignment) (last.eval Common.model assignment) := Iff.rfl

def Scheme.mono (input : CompTerm α) : Scheme scopes α :=
  Formula.compLe (input.rename some) (CompTerm.var none)

def SchemeEnv.rename (environment : SchemeEnv scopes α) (names : α → β) : SchemeEnv scopes β :=
  environment.map (Formula.rename (Option.map names))

def SchemeEnv.lift (environment : SchemeEnv scopes α) : SchemeEnv scopes (Option α) :=
  environment.rename some

def Scheme.lookup (environment : SchemeEnv scopes α) (index : Nat) (out : CompTerm α) : Formula scopes α :=
  match environment[index]? with
  | none => .core .bot
  | some scheme => scheme.instantiate out

@[simp] theorem Scheme.holds_mono (input : CompTerm α) (assignment : α → Computation) (out : Computation) :
    (Scheme.mono (scopes := scopes) input).Holds (extend assignment out) ↔
      Comp.le Common.model (input.eval Common.model assignment) out := by
  simp [mono]
end Yulang.CommonEffectFormula

namespace Yulang.CommonEffectPresence
open Core.PresenceGeneration (Comp CompTerm TyTerm RowTerm Binding BindingTyping BindingLookup Typing
  extend extend_none extend_some extend_comp_some exists_comp_row exists_comp_ty)
open CommonEffectRequestGeneration (Computation)
open CommonEffectFormula
open Inference (Expr)

variable {scopes : Nat}

/-- Two fresh slots. Their names and all prior free names remain distinct. -/
def fresh₀ : CompTerm (Option (Option α)) := CompTerm.var (some none)
def fresh₁ : CompTerm (Option (Option α)) := CompTerm.var none
def lift₂ (a : CompTerm α) := a.rename (fun x => some (some x))
def env₂ (Γ : SchemeEnv scopes α) := Γ.lift.lift

/-- Three fresh slots, in allocation order. -/
def fresh₀₃ : CompTerm (Option (Option (Option α))) := CompTerm.var (some (some none))
def fresh₁₃ : CompTerm (Option (Option (Option α))) := CompTerm.var (some none)
def fresh₂₃ : CompTerm (Option (Option (Option α))) := CompTerm.var none
def lift₃ (a : CompTerm α) := a.rename (fun x => some (some (some x)))
def env₃ (Γ : SchemeEnv scopes α) := Γ.lift.lift.lift

/-- Constraint generation is structurally recursive on the input expression.
Stored schemes contain formulas, so instantiating them does not recurse on a
previously seen expression. No fuel, oracle, or satisfiability assumption occurs. -/
def generate (Γ : SchemeEnv scopes α) : Expr → CompTerm α → Formula scopes α
  | .var n, out => Scheme.lookup Γ n out
  | .lit b, out => Formula.compLe (CompTerm.pure (.base b)) out
  | .lam body, out =>
      .existsSlot (.existsSlot (
        .and (generate (Scheme.mono fresh₀ :: env₂ Γ) body fresh₁)
          (Formula.compLe (CompTerm.pure (CompTerm.arrow fresh₀ fresh₁)) (lift₂ out))))
  | .app f x, out =>
      .existsSlot (.existsSlot (.existsSlot (
        .and (generate (env₃ Γ) f ⟨CompTerm.arrow fresh₀₃ fresh₁₃, fresh₂₃.row⟩)
          (.and (generate (env₃ Γ) x fresh₀₃)
            (Formula.compLe ⟨fresh₁₃.ty, .join fresh₂₃.row fresh₁₃.row⟩ (lift₃ out))))))
  | .letE v body, out =>
      let monomorphic := .existsSlot (.existsSlot (
        .and (generate (env₂ Γ) v fresh₀)
          (.and (generate (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ Γ) body fresh₁)
            (Formula.compLe ⟨fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out)))))
      if v.isValue then
        let scheme : Scheme scopes α :=
          .and (generate Γ.lift v (CompTerm.pure (.var none)))
            (.rowLe .empty (.var none))
        .or (.and (.existsSlot (generate Γ.lift v (CompTerm.pure (.var none))))
          (generate (scheme :: Γ) body out)) monomorphic
      else
        monomorphic
  | .branch g y n, out =>
      .existsSlot (.existsSlot (.existsSlot (
        .and (generate (env₃ Γ) g ⟨.base .bool, fresh₀₃.row⟩)
          (.and (generate (env₃ Γ) y fresh₁₃)
            (.and (generate (env₃ Γ) n fresh₂₃)
              (Formula.compLe ⟨.union fresh₁₃.ty fresh₂₃.ty,
                .join fresh₀₃.row (.join fresh₁₃.row fresh₂₃.row)⟩ (lift₃ out)))))))
  | .pair x y, out =>
      .existsSlot (.existsSlot (
        .and (generate (env₂ Γ) x fresh₀)
          (.and (generate (env₂ Γ) y fresh₁)
            (Formula.compLe ⟨.pair fresh₀.ty fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out)))))
  | .fst x, out =>
      .existsSlot (.existsSlot (
        .and (generate (env₂ Γ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩)
          (Formula.compLe ⟨fresh₀.ty, fresh₀.row⟩ (lift₂ out))))
  | .snd x, out =>
      .existsSlot (.existsSlot (
        .and (generate (env₂ Γ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩)
          (Formula.compLe ⟨fresh₁.ty, fresh₀.row⟩ (lift₂ out))))
  | .emptyRecord, out => Formula.compLe (CompTerm.pure .exactEmpty) out
  | .record l x rest, out =>
      .existsSlot (.existsSlot (
        .and (generate (env₂ Γ) x fresh₀)
          (.and (generate (env₂ Γ) rest fresh₁)
            (.and (.tyLe fresh₁.ty .emptyRecord)
              (Formula.compLe ⟨.record l fresh₀.ty fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out))))))
  | .recordDefault l source fallback, out =>
      .existsSlot (.existsSlot (
        .and (generate (env₂ Γ) source fresh₀)
          (.and (generate (env₂ Γ) fallback fresh₁)
            (.and (.tyLe fresh₀.ty .emptyRecord)
              (Formula.compLe ⟨.recordDefault l fresh₀.ty fresh₁.ty,
                .join fresh₀.row fresh₁.row⟩ (lift₂ out))))))
  | .field l x, out =>
      .existsSlot (
        .and (generate Γ.lift x ⟨.required l (.var none), .var none⟩)
          (Formula.compLe (CompTerm.var none) (out.rename some)))
  | .variant l x, out =>
      .existsSlot (
        .and (generate Γ.lift x (CompTerm.var none))
          (Formula.compLe ⟨.variant l (.var none), .var none⟩ (out.rename some)))

def SchemeLookup (assignment : α → Computation) (environment : SchemeEnv scopes α) (index : Nat) (out : Computation) : Prop :=
  match environment[index]? with
  | none => False
  | some scheme => scheme.Holds (extend assignment out)

def EnvRel (assignment : α → Computation) (environment : SchemeEnv scopes α)
    (bindings : List (Binding Common.model)) : Prop :=
  ∀ index out, SchemeLookup assignment environment index out ↔
    Core.PresenceGeneration.BindingLookup Common.model bindings index out

@[simp] theorem lookup_exact (environment : SchemeEnv scopes α) (index : Nat) (out : CompTerm α)
    (assignment : α → Computation) :
    (Scheme.lookup environment index out).Holds assignment ↔ SchemeLookup assignment environment index (out.eval Common.model assignment) := by
  unfold Scheme.lookup SchemeLookup
  split <;> simp [CommonEffectFormula.Formula.Holds, Core.PresenceGeneration.Formula.Holds]
theorem EnvRel.nil (ρ : α → Comp Common.model) : EnvRel (scopes := scopes) ρ [] [] := by
  intro n c
  simp [SchemeLookup, BindingLookup]

theorem EnvRel.cons {ρ : α → Comp Common.model} {sΓ : SchemeEnv scopes α}
    {Γ : List (Binding Common.model)} {s : Scheme scopes α} {b : Binding Common.model} (h : EnvRel ρ sΓ Γ)
    (head : ∀ c, s.Holds (extend ρ c) ↔ BindingTyping Common.model b c) :
    EnvRel ρ (s :: sΓ) (b :: Γ) := by
  intro n c
  cases n with
  | zero => simpa [SchemeLookup, BindingLookup] using head c
  | succ n => simpa [SchemeLookup, BindingLookup] using h n c

theorem EnvRel.mono {ρ : α → Comp Common.model} {sΓ : SchemeEnv scopes α}
    {Γ : List (Binding Common.model)} (h : EnvRel ρ sΓ Γ) (a : CompTerm α) :
    EnvRel ρ (Scheme.mono a :: sΓ) (.mono (a.eval Common.model ρ) :: Γ) := by
  apply h.cons
  intro c
  simp

theorem EnvRel.rename {ρ : α → Comp Common.model} {sΓ : SchemeEnv scopes α}
    {Γ : List (Binding Common.model)} (h : EnvRel ρ sΓ Γ) (f : α → β) (η : β → Comp Common.model)
    (he : η ∘ f = ρ) : EnvRel η (sΓ.rename f) Γ := by
  intro n c
  have hn := h n c
  unfold SchemeLookup at hn ⊢
  simp only [SchemeEnv.rename, List.getElem?_map]
  cases hs : sΓ[n]? with
  | none => simpa [hs] using hn
  | some s =>
      simp only [Option.map_some, Formula.holds_rename]
      have he' : extend η c ∘ Option.map f = extend ρ c := by
        funext x
        cases x with
        | none => rfl
        | some x => exact congrFun he x
      simpa only [he', hs] using hn

theorem EnvRel.lift {ρ : α → Comp Common.model} {sΓ : SchemeEnv scopes α}
    {Γ : List (Binding Common.model)} (h : EnvRel ρ sΓ Γ) (a : Comp Common.model) :
    EnvRel (extend ρ a) sΓ.lift Γ := by
  intro n c
  have hn := h n c
  unfold SchemeLookup at hn ⊢
  simp only [SchemeEnv.lift, SchemeEnv.rename, List.getElem?_map]
  cases hs : sΓ[n]? with
  | none => simpa [hs] using hn
  | some s =>
      simp only [Option.map_some, Formula.holds_rename]
      have he : extend (extend ρ a) c ∘ Option.map some = extend ρ c := by
        funext x
        cases x <;> rfl
      simpa only [he, hs] using hn

/-- Exactness of the generated constraint scheme. Both directions quantify
over all semantic types and rows; neither assumes that a solver succeeds.
The environment hypothesis only relates input schemes to input bindings. -/
theorem generate_presence_exact (e : Expr)
    (sΓ : SchemeEnv scopes α) (Γ : List (Binding Common.model)) (ρ : α → Comp Common.model)
    (out : CompTerm α) (henv : EnvRel ρ sΓ Γ) :
    (generate sΓ e out).Holds ρ ↔ Typing Common.model Γ e (out.eval Common.model ρ) := by
  induction e generalizing α sΓ Γ ρ out with
  | var n => simpa [generate] using henv n (out.eval Common.model ρ)
  | lit b => simp [generate, CompTerm.eval, CompTerm.pure, TyTerm.eval, RowTerm.eval, Comp.pure]
  | lam body ih =>
      have hb (a b : Comp Common.model) :
          (generate (Scheme.mono fresh₀ :: env₂ sΓ) body fresh₁).Holds (extend (extend ρ a) b) ↔
          Typing Common.model (.mono a :: Γ) body b := by
        simpa only [fresh₀, fresh₁, env₂, CompTerm.eval_var, extend_some, extend_none]
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
          (generate (env₃ sΓ) f ⟨CompTerm.arrow fresh₀₃ fresh₁₃, fresh₂₃.row⟩).Holds
            (extend (extend (extend ρ a) b) d) ↔ Typing Common.model Γ f (Comp.arrow Common.model a b, d.2) := by
        simpa only [env₃, fresh₀₃, fresh₁₃, fresh₂₃, CompTerm.eval, CompTerm.arrow,
          CompTerm.var, TyTerm.eval, RowTerm.eval, extend_none, extend_some, Comp.arrow]
          using ihf _ _ _ ⟨CompTerm.arrow fresh₀₃ fresh₁₃, fresh₂₃.row⟩ (((henv.lift a).lift b).lift d)
      have hx (a b d : Comp Common.model) :
          (generate (env₃ sΓ) x fresh₀₃).Holds (extend (extend (extend ρ a) b) d) ↔
          Typing Common.model Γ x a := by
        simpa only [env₃, fresh₀₃, CompTerm.eval_var, extend_some, extend_none]
          using ihx _ _ _ fresh₀₃ (((henv.lift a).lift b).lift d)
      simp only [generate, Formula.Holds, Typing.app_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      simp only [hf, hx]
      simp only [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds]
      simp only [lift₃, CompTerm.rename, CompTerm.eval, CompTerm.var, fresh₁₃,
        fresh₂₃, TyTerm.eval, RowTerm.eval, TyTerm.eval_rename, RowTerm.eval_rename,
        extend_none, extend_some, Function.comp_def]
      exact exists_comp_row Common.model (fun r => Typing Common.model Γ f (Comp.arrow Common.model a b, r) ∧
        Typing Common.model Γ x a ∧ Comp.le Common.model (b.1, Common.model.join r b.2) (out.eval Common.model ρ))
  | letE v body ihv ihb =>
      let mono : Formula scopes α := .existsSlot (.existsSlot (
        .and (generate (env₂ sΓ) v fresh₀)
          (.and (generate (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ sΓ) body fresh₁)
            (Formula.compLe ⟨fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out)))))
      have hmono : mono.Holds ρ ↔ ∃ a b,
          Typing Common.model Γ v a ∧ Typing Common.model (.mono (Comp.pure Common.model a.1) :: Γ) body b ∧
          Comp.le Common.model (b.1, Common.model.join a.2 b.2) (out.eval Common.model ρ) := by
        have ha (a b : Comp Common.model) :
            (generate (env₂ sΓ) v fresh₀).Holds (extend (extend ρ a) b) ↔ Typing Common.model Γ v a := by
          simpa only [env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
            using ihv _ _ _ fresh₀ ((henv.lift a).lift b)
        have hb (a b : Comp Common.model) :
            (generate (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ sΓ) body fresh₁).Holds
              (extend (extend ρ a) b) ↔ Typing Common.model (.mono (Comp.pure Common.model a.1) :: Γ) body b := by
          simpa [env₂, fresh₀, fresh₁, CompTerm.pure, Comp.pure,
            CompTerm.var, CompTerm.eval, TyTerm.eval, RowTerm.eval]
            using ihb _ _ _ fresh₁ (((henv.lift a).lift b).mono (CompTerm.pure fresh₀.ty))
        simp only [mono, Formula.Holds,         apply exists_congr; intro a
        apply exists_congr; intro b
        rw [ha, hb]
        simp [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
          CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
      cases hv : v.isValue with
      | true =>
          let scheme : Scheme scopes α := .and
            (generate sΓ.lift v (CompTerm.pure (.var none))) (.rowLe .empty (.var none))
          have hvalue (c : Comp Common.model) :
              (generate sΓ.lift v (CompTerm.pure (.var none))).Holds (extend ρ c) ↔
              Typing Common.model Γ v (Comp.pure Common.model c.1) := by
            simpa only [CompTerm.eval_pure, TyTerm.eval, extend_none]
              using ihv _ _ _ (CompTerm.pure (.var none)) (henv.lift c)
          have hscheme : ∀ c, scheme.Holds (extend ρ c) ↔ BindingTyping Common.model (.poly v Γ) c := by
            intro c
            simp only [scheme, Formula.Holds, CommonEffectRequestGeneration.RowExpr.eval, hvalue, extend_none,
              BindingTyping.poly_iff]
            rfl
          have hbody := ihb (scheme :: sΓ) (.poly v Γ :: Γ) ρ out (henv.cons hscheme)
          simp only [generate, hv]
          change (((∃ c, (generate sΓ.lift v (CompTerm.pure (.var none))).Holds (extend ρ c)) ∧
            (generate (scheme :: sΓ) body out).Holds ρ) ∨ mono.Holds ρ) ↔ _
          rw [Typing.letValue_iff Common.model Γ v body (out.eval Common.model ρ) hv]
          apply or_congr
          · simp only [hvalue]
            rw [hbody]
            exact and_congr (exists_comp_ty Common.model (fun a => Typing Common.model Γ v (Comp.pure Common.model a))) Iff.rfl
          · exact hmono
      | false =>
          simp only [generate, hv]
          change mono.Holds ρ ↔ _
          exact hmono.trans (Typing.letComputed_iff Common.model Γ v body (out.eval Common.model ρ) hv).symm
  | branch g y n ihg ihy ihn =>
      have hg (a b d : Comp Common.model) :
          (generate (env₃ sΓ) g ⟨.base .bool, fresh₀₃.row⟩).Holds
            (extend (extend (extend ρ a) b) d) ↔ Typing Common.model Γ g (Common.model.base .bool, a.2) := by
        simpa only [env₃, fresh₀₃, CompTerm.eval, CompTerm.var, TyTerm.eval, RowTerm.eval,
          extend_none, extend_some] using ihg _ _ _ ⟨.base .bool, fresh₀₃.row⟩ (((henv.lift a).lift b).lift d)
      have hy (a b d : Comp Common.model) :
          (generate (env₃ sΓ) y fresh₁₃).Holds (extend (extend (extend ρ a) b) d) ↔
          Typing Common.model Γ y b := by
        simpa only [env₃, fresh₁₃, CompTerm.eval_var, extend_none, extend_some]
          using ihy _ _ _ fresh₁₃ (((henv.lift a).lift b).lift d)
      have hn (a b d : Comp Common.model) :
          (generate (env₃ sΓ) n fresh₂₃).Holds (extend (extend (extend ρ a) b) d) ↔
          Typing Common.model Γ n d := by
        simpa only [env₃, fresh₂₃, CompTerm.eval_var, extend_none]
          using ihn _ _ _ fresh₂₃ (((henv.lift a).lift b).lift d)
      simp only [generate, Formula.Holds, Typing.branch_iff]
      simp only [hg, hy, hn]
      simp only [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds]
      simp only [lift₃, CompTerm.rename, CompTerm.eval, CompTerm.var, fresh₀₃, fresh₁₃,
        fresh₂₃, TyTerm.eval, RowTerm.eval, TyTerm.eval_rename, RowTerm.eval_rename,
        extend_none, extend_some, Function.comp_def]
      exact exists_comp_row Common.model (fun r => ∃ a b, Typing Common.model Γ g (Common.model.base .bool, r) ∧
        Typing Common.model Γ y a ∧ Typing Common.model Γ n b ∧
        Comp.le Common.model (Common.model.union a.1 b.1, Common.model.join r (Common.model.join a.2 b.2)) (out.eval Common.model ρ))
  | pair x y ihx ihy =>
      have hx (a b : Comp Common.model) :
          (generate (env₂ sΓ) x fresh₀).Holds (extend (extend ρ a) b) ↔ Typing Common.model Γ x a := by
        simpa only [env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
          using ihx _ _ _ fresh₀ ((henv.lift a).lift b)
      have hy (a b : Comp Common.model) :
          (generate (env₂ sΓ) y fresh₁).Holds (extend (extend ρ a) b) ↔ Typing Common.model Γ y b := by
        simpa only [env₂, fresh₁, CompTerm.eval_var, extend_none]
          using ihy _ _ _ fresh₁ ((henv.lift a).lift b)
      simp only [generate, Formula.Holds, Typing.pair_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      rw [hx, hy]
      simp [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
        CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
  | fst x ih =>
      have hx (a b : Comp Common.model) :
          (generate (env₂ sΓ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩).Holds
            (extend (extend ρ a) b) ↔ Typing Common.model Γ x (Common.model.pair a.1 b.1, a.2) := by
        simpa only [env₂, fresh₀, fresh₁, CompTerm.eval, CompTerm.var, TyTerm.eval, RowTerm.eval,
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
          (generate (env₂ sΓ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩).Holds
            (extend (extend ρ a) b) ↔ Typing Common.model Γ x (Common.model.pair a.1 b.1, a.2) := by
        simpa only [env₂, fresh₀, fresh₁, CompTerm.eval, CompTerm.var, TyTerm.eval, RowTerm.eval,
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
          (generate (env₂ sΓ) x fresh₀).Holds (extend (extend ρ a) b) ↔ Typing Common.model Γ x a := by
        simpa only [env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
          using ihx _ _ _ fresh₀ ((henv.lift a).lift b)
      have hr (a b : Comp Common.model) :
          (generate (env₂ sΓ) r fresh₁).Holds (extend (extend ρ a) b) ↔ Typing Common.model Γ r b := by
        simpa only [env₂, fresh₁, CompTerm.eval_var, extend_none]
          using ihr _ _ _ fresh₁ ((henv.lift a).lift b)
      simp only [generate, Formula.Holds, Formula.tyLe, Core.PresenceGeneration.Formula.Holds, Typing.record_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      rw [hx, hr]
      simp [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
        CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
  | recordDefault l source fallback ihs ihf =>
      have hs (a b : Comp Common.model) :
          (generate (env₂ sΓ) source fresh₀).Holds (extend (extend ρ a) b) ↔
            Typing Common.model Γ source a := by
        simpa only [env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
          using ihs _ _ _ fresh₀ ((henv.lift a).lift b)
      have hf (a b : Comp Common.model) :
          (generate (env₂ sΓ) fallback fresh₁).Holds (extend (extend ρ a) b) ↔
            Typing Common.model Γ fallback b := by
        simpa only [env₂, fresh₁, CompTerm.eval_var, extend_none]
          using ihf _ _ _ fresh₁ ((henv.lift a).lift b)
      simp only [generate, Formula.Holds, Formula.tyLe, Core.PresenceGeneration.Formula.Holds, Typing.recordDefault_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      rw [hs, hf]
      simp [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
        CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
  | field l x ih =>
      have hx (a : Comp Common.model) :
          (generate sΓ.lift x ⟨.required l (.var none), .var none⟩).Holds
            (extend ρ a) ↔ Typing Common.model Γ x (Common.model.required l a.1, a.2) := by
        simpa only [CompTerm.eval, TyTerm.eval, RowTerm.eval, extend_none]
          using ih _ _ _ ⟨.required l (.var none), .var none⟩ (henv.lift a)
      simp only [generate, Formula.Holds, Typing.field_iff]
      simp only [hx]
      simp [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
        CompTerm.rename, TyTerm.eval, RowTerm.eval, Function.comp_def, Prod.exists]
  | variant l x ih =>
      have hx (a : Comp Common.model) :
          (generate sΓ.lift x (CompTerm.var none)).Holds (extend ρ a) ↔ Typing Common.model Γ x a := by
        simpa only [CompTerm.eval_var, extend_none] using ih _ _ _ (CompTerm.var none) (henv.lift a)
      simp only [generate, Formula.Holds, Typing.variant_iff]
      apply exists_congr; intro a
      rw [hx]
      simp [Formula.compLe, Core.PresenceGeneration.Formula.compLe, Formula.Holds, Core.PresenceGeneration.Formula.Holds, Comp.le, CompTerm.eval,
        CompTerm.rename, TyTerm.eval, RowTerm.eval, Function.comp_def]


end Yulang.CommonEffectPresence
