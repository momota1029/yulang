import Yulang.CorePresenceGenerationModel

/-!
# Independent presence typing and first-order constraint generation

The rules extend the value-restricted source calculus to strict record defaults.
They quantify over the extended model in `CorePresenceGenerationModel`; they do
not define typing by generated constraints. Captured polymorphic bindings keep
their original environment, and both let alternatives of the legacy calculus
remain available. Every `Inference.Expr` constructor is covered by `generate`.

This is a formula generator, not an instance-extracting regular solver.
-/

namespace Yulang.Core.PresenceGeneration

open Inference (Expr Base)

inductive Formula : Type → Type 1 where
  | top : Formula α
  | bot : Formula α
  | and : Formula α → Formula α → Formula α
  | or : Formula α → Formula α → Formula α
  | tyLe : TyTerm α → TyTerm α → Formula α
  | rowLe : RowTerm α → RowTerm α → Formula α
  | existsSlot : Formula (Option α) → Formula α

def Formula.compLe (a b : CompTerm α) : Formula α :=
  .and (.tyLe a.ty b.ty) (.rowLe a.row b.row)

def Formula.Holds (m : Model) : {α : Type} → (α → Comp m) → Formula α → Prop
  | _, _, .top => True
  | _, _, .bot => False
  | _, ρ, .and p q => p.Holds m ρ ∧ q.Holds m ρ
  | _, ρ, .or p q => p.Holds m ρ ∨ q.Holds m ρ
  | _, ρ, .tyLe a b => m.subTy (a.eval m ρ) (b.eval m ρ)
  | _, ρ, .rowLe a b => m.subRow (a.eval m ρ) (b.eval m ρ)
  | _, ρ, .existsSlot p => ∃ c, p.Holds m (extend ρ c)

def Formula.rename (f : α → β) : Formula α → Formula β
  | .top => .top
  | .bot => .bot
  | .and p q => .and (p.rename f) (q.rename f)
  | .or p q => .or (p.rename f) (q.rename f)
  | .tyLe a b => .tyLe (a.rename f) (b.rename f)
  | .rowLe a b => .rowLe (a.rename f) (b.rename f)
  | .existsSlot p => .existsSlot (p.rename (Option.map f))

def liftSubst (f : α → CompTerm β) : Option α → CompTerm (Option β)
  | none => CompTerm.var none
  | some a => (f a).rename some

def Formula.subst (f : α → CompTerm β) : Formula α → Formula β
  | .top => .top
  | .bot => .bot
  | .and p q => .and (p.subst f) (q.subst f)
  | .or p q => .or (p.subst f) (q.subst f)
  | .tyLe a b => .tyLe (a.subst f) (b.subst f)
  | .rowLe a b => .rowLe (a.subst f) (b.subst f)
  | .existsSlot p => .existsSlot (p.subst (liftSubst f))

@[simp] theorem Formula.holds_compLe (m : Model) (ρ : α → Comp m)
    (a b : CompTerm α) :
    (Formula.compLe a b).Holds m ρ ↔ Comp.le m (a.eval m ρ) (b.eval m ρ) := Iff.rfl

@[simp] theorem Formula.holds_rename (m : Model) (p : Formula α)
    (f : α → β) (ρ : β → Comp m) :
    (p.rename f).Holds m ρ ↔ p.Holds m (ρ ∘ f) := by
  induction p generalizing β with
  | top => rfl
  | bot => rfl
  | and p q ihp ihq => simp [rename, Holds, ihp, ihq]
  | or p q ihp ihq => simp [rename, Holds, ihp, ihq]
  | tyLe a b => simp [rename, Holds]
  | rowLe a b => simp [rename, Holds]
  | existsSlot p ih =>
      simp only [rename, Holds, ih]
      apply exists_congr
      intro c
      have h : extend ρ c ∘ Option.map f = extend (ρ ∘ f) c := by
        funext x
        cases x <;> rfl
      rw [h]

@[simp] theorem Formula.holds_subst (m : Model) (p : Formula α)
    (f : α → CompTerm β) (ρ : β → Comp m) :
    (p.subst f).Holds m ρ ↔ p.Holds m (fun x => (f x).eval m ρ) := by
  induction p generalizing β with
  | top => rfl
  | bot => rfl
  | and p q ihp ihq => simp [subst, Holds, ihp, ihq]
  | or p q ihp ihq => simp [subst, Holds, ihp, ihq]
  | tyLe a b => simp [subst, Holds]
  | rowLe a b => simp [subst, Holds]
  | existsSlot p ih =>
      simp only [subst, Holds, ih]
      apply exists_congr
      intro c
      have h : (fun x => (liftSubst f x).eval m (extend ρ c)) =
          extend (fun x => (f x).eval m ρ) c := by
        funext x
        cases x <;> simp [liftSubst]
      rw [h]

abbrev Scheme (α : Type) := Formula (Option α)
abbrev SchemeEnv (α : Type) := List (Scheme α)

def Scheme.instantiate (s : Scheme α) (c : CompTerm α) : Formula α :=
  s.subst (fun | none => c | some a => CompTerm.var a)

def Scheme.mono (a : CompTerm α) : Scheme α :=
  Formula.compLe (a.rename some) (CompTerm.var none)

/-- Rename captured slots, preserving the scheme's result slot. -/
def SchemeEnv.rename (Γ : SchemeEnv α) (f : α → β) : SchemeEnv β :=
  Γ.map (Formula.rename (Option.map f))

def SchemeEnv.lift (Γ : SchemeEnv α) : SchemeEnv (Option α) :=
  Γ.map (Formula.rename (Option.map some))

def Scheme.lookup (Γ : SchemeEnv α) (n : Nat) (c : CompTerm α) : Formula α :=
  match Γ[n]? with
  | none => .bot
  | some s => s.instantiate c

@[simp] theorem Scheme.holds_instantiate (m : Model) (ρ : α → Comp m)
    (s : Scheme α) (c : CompTerm α) :
    (s.instantiate c).Holds m ρ ↔ s.Holds m (extend ρ (c.eval m ρ)) := by
  simp only [instantiate, Formula.holds_subst]
  have h : (fun x => ((fun | none => c | some a => CompTerm.var a) x).eval m ρ) =
      extend ρ (c.eval m ρ) := by
    funext x
    cases x <;> rfl
  exact (congrArg (fun η => s.Holds m η) h).to_iff

@[simp] theorem Scheme.holds_mono (m : Model) (ρ : α → Comp m)
    (a : CompTerm α) (c : Comp m) :
    (Scheme.mono a).Holds m (extend ρ c) ↔ Comp.le m (a.eval m ρ) c := by
  simp [mono]

inductive Binding (m : Model) where
  | mono : Comp m → Binding m
  | poly : Expr → List (Binding m) → Binding m
  /-- An independently prescribed signature quantifies value types only.
  Inferred row assignments and the lexical environment are captured by
  `instantiate`; no fresh row assignment is supplied at a call. -/
  | signature (n : Nat) (instantiate : (Fin n → m.Ty) → Comp m) : Binding m

mutual
  inductive Typing (m : Model) : List (Binding m) → Expr → Comp m → Prop where
    | var : Γ[n]? = some b → BindingTyping m b c → Typing m Γ (.var n) c
    | lit : Comp.le m (Comp.pure m (m.base b)) c → Typing m Γ (.lit b) c
    | lam : Typing m (.mono a :: Γ) body b →
        Comp.le m (Comp.pure m (Comp.arrow m a b)) c → Typing m Γ (.lam body) c
    | app : Typing m Γ f (Comp.arrow m a b, ef) → Typing m Γ x a →
        Comp.le m (b.1, m.join ef b.2) c → Typing m Γ (.app f x) c
    | letValue : v.isValue = true → Typing m Γ v (Comp.pure m a) →
        Typing m (.poly v Γ :: Γ) body c → Typing m Γ (.letE v body) c
    | letComputed : Typing m Γ v a →
        Typing m (.mono (Comp.pure m a.1) :: Γ) body b →
        Comp.le m (b.1, m.join a.2 b.2) c → Typing m Γ (.letE v body) c
    | branch : Typing m Γ condition (m.base .bool, eg) →
        Typing m Γ yes a → Typing m Γ no b →
        Comp.le m (m.union a.1 b.1, m.join eg (m.join a.2 b.2)) c →
        Typing m Γ (.branch condition yes no) c
    | pair : Typing m Γ x a → Typing m Γ y b →
        Comp.le m (m.pair a.1 b.1, m.join a.2 b.2) c → Typing m Γ (.pair x y) c
    | fst : Typing m Γ x (m.pair a b, er) →
        Comp.le m (a, er) c → Typing m Γ (.fst x) c
    | snd : Typing m Γ x (m.pair a b, er) →
        Comp.le m (b, er) c → Typing m Γ (.snd x) c
    | emptyRecord : Comp.le m (Comp.pure m m.exactEmpty) c →
        Typing m Γ .emptyRecord c
    | record : Typing m Γ x a → Typing m Γ rest b → m.subTy b.1 m.emptyRecord →
        Comp.le m (m.record l a.1 b.1, m.join a.2 b.2) c →
        Typing m Γ (.record l x rest) c
    /-- Both operands are checked; the base and fallback rows are joined even
    when the base already supplies the field. -/
    | recordDefault : Typing m Γ source a → Typing m Γ fallback b →
        m.subTy a.1 m.emptyRecord →
        Comp.le m (m.recordDefault l a.1 b.1, m.join a.2 b.2) c →
        Typing m Γ (.recordDefault l source fallback) c
    | field : Typing m Γ x (m.required l a, er) →
        Comp.le m (a, er) c → Typing m Γ (.field l x) c
    | variant : Typing m Γ x a →
        Comp.le m (m.variant l a.1, a.2) c → Typing m Γ (.variant l x) c

  inductive BindingTyping (m : Model) : Binding m → Comp m → Prop where
    | mono : Comp.le m a c → BindingTyping m (.mono a) c
    | poly : Typing m Γ v (Comp.pure m c.1) → m.subRow m.empty c.2 →
        BindingTyping m (.poly v Γ) c
    | signature {n : Nat} {instantiate : (Fin n → m.Ty) → Comp m} {ι : Fin n → m.Ty} :
        Comp.le m (instantiate ι) c →
        BindingTyping m (.signature n instantiate) c
end

/-- Two fresh slots. Their names and all prior free names remain distinct. -/
def fresh₀ : CompTerm (Option (Option α)) := CompTerm.var (some none)
def fresh₁ : CompTerm (Option (Option α)) := CompTerm.var none
def lift₂ (a : CompTerm α) := a.rename (fun x => some (some x))
def env₂ (Γ : SchemeEnv α) := Γ.lift.lift

/-- Three fresh slots, in allocation order. -/
def fresh₀₃ : CompTerm (Option (Option (Option α))) := CompTerm.var (some (some none))
def fresh₁₃ : CompTerm (Option (Option (Option α))) := CompTerm.var (some none)
def fresh₂₃ : CompTerm (Option (Option (Option α))) := CompTerm.var none
def lift₃ (a : CompTerm α) := a.rename (fun x => some (some (some x)))
def env₃ (Γ : SchemeEnv α) := Γ.lift.lift.lift

/-- Constraint generation is structurally recursive on the input expression.
Stored schemes contain formulas, so instantiating them does not recurse on a
previously seen expression. No fuel, oracle, or satisfiability assumption occurs. -/
def generate (Γ : SchemeEnv α) : Expr → CompTerm α → Formula α
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
        let scheme : Scheme α :=
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

def SchemeLookup (m : Model) (ρ : α → Comp m) (Γ : SchemeEnv α)
    (n : Nat) (c : Comp m) : Prop :=
  match Γ[n]? with
  | none => False
  | some s => s.Holds m (extend ρ c)

def BindingLookup (m : Model) (Γ : List (Binding m)) (n : Nat) (c : Comp m) : Prop :=
  ∃ b, Γ[n]? = some b ∧ BindingTyping m b c

/-- A symbolic context represents exactly the same instances as its independent
declarative context. This relation is preserved by fresh allocation. -/
def EnvRel (m : Model) (ρ : α → Comp m) (sΓ : SchemeEnv α)
    (Γ : List (Binding m)) : Prop :=
  ∀ n c, SchemeLookup m ρ sΓ n c ↔ BindingLookup m Γ n c

@[simp] theorem Scheme.holds_lookup (m : Model) (ρ : α → Comp m)
    (Γ : SchemeEnv α) (n : Nat) (c : CompTerm α) :
    (Scheme.lookup Γ n c).Holds m ρ ↔ SchemeLookup m ρ Γ n (c.eval m ρ) := by
  unfold lookup SchemeLookup
  split <;> simp [Formula.Holds]

@[simp] theorem BindingTyping.mono_iff (m : Model) (a c : Comp m) :
    BindingTyping m (.mono a) c ↔ Comp.le m a c := by
  constructor
  · intro h; cases h with | mono h => exact h
  · exact BindingTyping.mono

@[simp] theorem BindingTyping.poly_iff (m : Model) (Γ : List (Binding m))
    (v : Expr) (c : Comp m) :
    BindingTyping m (.poly v Γ) c ↔
      Typing m Γ v (Comp.pure m c.1) ∧ m.subRow m.empty c.2 := by
  constructor
  · intro h; cases h with | poly hv he => exact ⟨hv, he⟩
  · rintro ⟨hv, he⟩; exact BindingTyping.poly hv he

@[simp] theorem BindingTyping.signature_iff (m : Model) (n : Nat)
    (instantiate : (Fin n → m.Ty) → Comp m) (c : Comp m) :
    BindingTyping m (.signature n instantiate) c ↔ ∃ ι, Comp.le m (instantiate ι) c := by
  constructor
  · intro h; cases h with | signature hc => exact ⟨_, hc⟩
  · rintro ⟨ι, hc⟩; exact BindingTyping.signature hc

theorem EnvRel.nil (m : Model) (ρ : α → Comp m) : EnvRel m ρ [] [] := by
  intro n c
  simp [SchemeLookup, BindingLookup]

theorem EnvRel.cons {m : Model} {ρ : α → Comp m} {sΓ : SchemeEnv α}
    {Γ : List (Binding m)} {s : Scheme α} {b : Binding m} (h : EnvRel m ρ sΓ Γ)
    (head : ∀ c, s.Holds m (extend ρ c) ↔ BindingTyping m b c) :
    EnvRel m ρ (s :: sΓ) (b :: Γ) := by
  intro n c
  cases n with
  | zero => simpa [SchemeLookup, BindingLookup] using head c
  | succ n => simpa [SchemeLookup, BindingLookup] using h n c

theorem EnvRel.mono {m : Model} {ρ : α → Comp m} {sΓ : SchemeEnv α}
    {Γ : List (Binding m)} (h : EnvRel m ρ sΓ Γ) (a : CompTerm α) :
    EnvRel m ρ (Scheme.mono a :: sΓ) (.mono (a.eval m ρ) :: Γ) := by
  apply h.cons
  intro c
  simp

theorem EnvRel.rename {m : Model} {ρ : α → Comp m} {sΓ : SchemeEnv α}
    {Γ : List (Binding m)} (h : EnvRel m ρ sΓ Γ) (f : α → β) (η : β → Comp m)
    (he : η ∘ f = ρ) : EnvRel m η (sΓ.rename f) Γ := by
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

theorem EnvRel.lift {m : Model} {ρ : α → Comp m} {sΓ : SchemeEnv α}
    {Γ : List (Binding m)} (h : EnvRel m ρ sΓ Γ) (a : Comp m) :
    EnvRel m (extend ρ a) sΓ.lift Γ := by
  intro n c
  have hn := h n c
  unfold SchemeLookup at hn ⊢
  simp only [SchemeEnv.lift, List.getElem?_map]
  cases hs : sΓ[n]? with
  | none => simpa [hs] using hn
  | some s =>
      simp only [Option.map_some, Formula.holds_rename]
      have he : extend (extend ρ a) c ∘ Option.map some = extend ρ c := by
        funext x
        cases x <;> rfl
      simpa only [he, hs] using hn

@[simp] theorem Typing.var_iff (m : Model) (Γ : List (Binding m)) (n : Nat) (c : Comp m) :
    Typing m Γ (.var n) c ↔ BindingLookup m Γ n c := by
  constructor
  · intro h
    cases h with | var hget hb => exact ⟨_, hget, hb⟩
  · rintro ⟨b, hget, hb⟩
    exact Typing.var hget hb

/-- Strict default extension retains the full constructor result and both rows. -/
@[simp] theorem Typing.recordDefault_iff (m : Model) (Γ : List (Binding m))
    (l : Nat) (source fallback : Expr) (c : Comp m) :
    Typing m Γ (.recordDefault l source fallback) c ↔ ∃ a b,
      Typing m Γ source a ∧ Typing m Γ fallback b ∧ m.subTy a.1 m.emptyRecord ∧
      Comp.le m (m.recordDefault l a.1 b.1, m.join a.2 b.2) c := by
  constructor
  · intro h; cases h with | recordDefault ha hb hs hc => exact ⟨_, _, ha, hb, hs, hc⟩
  · rintro ⟨a, b, ha, hb, hs, hc⟩; exact Typing.recordDefault ha hb hs hc

@[simp] theorem Typing.lit_iff (m : Model) (Γ : List (Binding m)) (b : Base) (c : Comp m) :
    Typing m Γ (.lit b) c ↔ Comp.le m (Comp.pure m (m.base b)) c := by
  constructor
  · intro h; cases h with | lit h => exact h
  · exact Typing.lit

@[simp] theorem Typing.lam_iff (m : Model) (Γ : List (Binding m)) (body : Expr) (c : Comp m) :
    Typing m Γ (.lam body) c ↔ ∃ a b,
      Typing m (.mono a :: Γ) body b ∧
      Comp.le m (Comp.pure m (Comp.arrow m a b)) c := by
  constructor
  · intro h; cases h with | lam hb hc => exact ⟨_, _, hb, hc⟩
  · rintro ⟨a, b, hb, hc⟩; exact Typing.lam hb hc

@[simp] theorem Typing.app_iff (m : Model) (Γ : List (Binding m)) (f x : Expr) (c : Comp m) :
    Typing m Γ (.app f x) c ↔ ∃ a b ef,
      Typing m Γ f (Comp.arrow m a b, ef) ∧ Typing m Γ x a ∧
      Comp.le m (b.1, m.join ef b.2) c := by
  constructor
  · intro h; cases h with | app hf hx hc => exact ⟨_, _, _, hf, hx, hc⟩
  · rintro ⟨a, b, ef, hf, hx, hc⟩; exact Typing.app hf hx hc

theorem Typing.letValue_iff (m : Model) (Γ : List (Binding m)) (v body : Expr) (c : Comp m)
    (hv : v.isValue = true) :
    Typing m Γ (.letE v body) c ↔
      ((∃ a, Typing m Γ v (Comp.pure m a)) ∧ Typing m (.poly v Γ :: Γ) body c) ∨
      ∃ a b, Typing m Γ v a ∧ Typing m (.mono (Comp.pure m a.1) :: Γ) body b ∧
        Comp.le m (b.1, m.join a.2 b.2) c := by
  constructor
  · intro h
    cases h with
    | letValue _ ha hb => exact Or.inl ⟨⟨_, ha⟩, hb⟩
    | letComputed ha hb hc => exact Or.inr ⟨_, _, ha, hb, hc⟩
  · intro h
    rcases h with ⟨⟨a, ha⟩, hb⟩ | ⟨a, b, ha, hb, hc⟩
    · exact Typing.letValue hv ha hb
    · exact Typing.letComputed ha hb hc

theorem Typing.letComputed_iff (m : Model) (Γ : List (Binding m)) (v body : Expr) (c : Comp m)
    (hv : v.isValue = false) :
    Typing m Γ (.letE v body) c ↔ ∃ a b,
      Typing m Γ v a ∧ Typing m (.mono (Comp.pure m a.1) :: Γ) body b ∧
      Comp.le m (b.1, m.join a.2 b.2) c := by
  constructor
  · intro h
    cases h with
    | letValue hn _ _ => simp [hv] at hn
    | letComputed ha hb hc => exact ⟨_, _, ha, hb, hc⟩
  · rintro ⟨a, b, ha, hb, hc⟩
    exact Typing.letComputed ha hb hc

@[simp] theorem Typing.branch_iff (m : Model) (Γ : List (Binding m)) (g y n : Expr) (c : Comp m) :
    Typing m Γ (.branch g y n) c ↔ ∃ eg a b,
      Typing m Γ g (m.base .bool, eg) ∧ Typing m Γ y a ∧ Typing m Γ n b ∧
      Comp.le m (m.union a.1 b.1, m.join eg (m.join a.2 b.2)) c := by
  constructor
  · intro h; cases h with | branch hg hy hn hc => exact ⟨_, _, _, hg, hy, hn, hc⟩
  · rintro ⟨eg, a, b, hg, hy, hn, hc⟩; exact Typing.branch hg hy hn hc

@[simp] theorem Typing.pair_iff (m : Model) (Γ : List (Binding m)) (x y : Expr) (c : Comp m) :
    Typing m Γ (.pair x y) c ↔ ∃ a b,
      Typing m Γ x a ∧ Typing m Γ y b ∧
      Comp.le m (m.pair a.1 b.1, m.join a.2 b.2) c := by
  constructor
  · intro h; cases h with | pair hx hy hc => exact ⟨_, _, hx, hy, hc⟩
  · rintro ⟨a, b, hx, hy, hc⟩; exact Typing.pair hx hy hc

@[simp] theorem Typing.fst_iff (m : Model) (Γ : List (Binding m)) (x : Expr) (c : Comp m) :
    Typing m Γ (.fst x) c ↔ ∃ a b er,
      Typing m Γ x (m.pair a b, er) ∧ Comp.le m (a, er) c := by
  constructor
  · intro h; cases h with | fst hx hc => exact ⟨_, _, _, hx, hc⟩
  · rintro ⟨a, b, er, hx, hc⟩; exact Typing.fst hx hc

@[simp] theorem Typing.snd_iff (m : Model) (Γ : List (Binding m)) (x : Expr) (c : Comp m) :
    Typing m Γ (.snd x) c ↔ ∃ a b er,
      Typing m Γ x (m.pair a b, er) ∧ Comp.le m (b, er) c := by
  constructor
  · intro h; cases h with | snd hx hc => exact ⟨_, _, _, hx, hc⟩
  · rintro ⟨a, b, er, hx, hc⟩; exact Typing.snd hx hc

@[simp] theorem Typing.emptyRecord_iff (m : Model) (Γ : List (Binding m)) (c : Comp m) :
    Typing m Γ .emptyRecord c ↔ Comp.le m (Comp.pure m m.exactEmpty) c := by
  constructor
  · intro h; cases h with | emptyRecord h => exact h
  · exact Typing.emptyRecord

@[simp] theorem Typing.record_iff (m : Model) (Γ : List (Binding m))
    (l : Nat) (x r : Expr) (c : Comp m) :
    Typing m Γ (.record l x r) c ↔ ∃ a b,
      Typing m Γ x a ∧ Typing m Γ r b ∧ m.subTy b.1 m.emptyRecord ∧
      Comp.le m (m.record l a.1 b.1, m.join a.2 b.2) c := by
  constructor
  · intro h; cases h with | record hx hr hs hc => exact ⟨_, _, hx, hr, hs, hc⟩
  · rintro ⟨a, b, hx, hr, hs, hc⟩; exact Typing.record hx hr hs hc

@[simp] theorem Typing.field_iff (m : Model) (Γ : List (Binding m))
    (l : Nat) (x : Expr) (c : Comp m) :
    Typing m Γ (.field l x) c ↔ ∃ a er,
      Typing m Γ x (m.required l a, er) ∧ Comp.le m (a, er) c := by
  constructor
  · intro h; cases h with | field hx hc => exact ⟨_, _, hx, hc⟩
  · rintro ⟨a, er, hx, hc⟩; exact Typing.field hx hc

@[simp] theorem Typing.variant_iff (m : Model) (Γ : List (Binding m))
    (l : Nat) (x : Expr) (c : Comp m) :
    Typing m Γ (.variant l x) c ↔ ∃ a,
      Typing m Γ x a ∧ Comp.le m (m.variant l a.1, a.2) c := by
  constructor
  · intro h; cases h with | variant hx hc => exact ⟨_, hx, hc⟩
  · rintro ⟨a, hx, hc⟩; exact Typing.variant hx hc

theorem exists_comp_row (m : Model) (p : m.Row → Prop) :
    (∃ c : Comp m, p c.2) ↔ ∃ r, p r := by
  constructor
  · rintro ⟨c, h⟩; exact ⟨c.2, h⟩
  · rintro ⟨r, h⟩; exact ⟨(m.base .unit, r), h⟩

theorem exists_comp_ty (m : Model) (p : m.Ty → Prop) :
    (∃ c : Comp m, p c.1) ↔ ∃ a, p a := by
  constructor
  · rintro ⟨c, h⟩; exact ⟨c.1, h⟩
  · rintro ⟨a, h⟩; exact ⟨(a, m.empty), h⟩

end Yulang.Core.PresenceGeneration
