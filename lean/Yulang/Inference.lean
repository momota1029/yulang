import Yulang.Types

/-!
# Executable, value-restricted principal constraint generation

`generate` produces a finite first-order formula, not a satisfiability answer.
Its binders are intrinsically scoped: `none` is fresh and `some x` preserves an
existing variable. A scheme is a formula with one result slot. Instantiation
substitutes that slot while preserving the captured environment.

The independent declarative judgement below never mentions `generate` or
`Formula`. Application passes a computation, rather than eagerly adding the
argument row to the result. The input and output rows of its arrow are distinct.
Effect operations, handlers, recursive bindings, methods and casts belong to
additional layers; this file does not claim their operational safety.
-/

namespace Yulang.Inference

inductive Formula : Type → Type 1 where
  | top : Formula α
  | bot : Formula α
  | and : Formula α → Formula α → Formula α
  | tyLe : TyTerm α → TyTerm α → Formula α
  | rowLe : RowTerm α → RowTerm α → Formula α
  | existsSlot : Formula (Option α) → Formula α

def Formula.compLe (a b : CompTerm α) : Formula α :=
  .and (.tyLe a.ty b.ty) (.rowLe a.row b.row)

def Formula.Holds (m : Model) : {α : Type} → (α → Comp m) → Formula α → Prop
  | _, _, .top => True
  | _, _, .bot => False
  | _, ρ, .and p q => p.Holds m ρ ∧ q.Holds m ρ
  | _, ρ, .tyLe a b => m.subTy (a.eval m ρ) (b.eval m ρ)
  | _, ρ, .rowLe a b => m.subRow (a.eval m ρ) (b.eval m ρ)
  | _, ρ, .existsSlot p => ∃ c, p.Holds m (extend ρ c)

def Formula.rename (f : α → β) : Formula α → Formula β
  | .top => .top
  | .bot => .bot
  | .and p q => .and (p.rename f) (q.rename f)
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

inductive Expr where
  | var : Nat → Expr
  | lit : Base → Expr
  | lam : Expr → Expr
  | app : Expr → Expr → Expr
  | letE : Expr → Expr → Expr
  | branch : Expr → Expr → Expr → Expr
  | pair : Expr → Expr → Expr
  | fst : Expr → Expr
  | snd : Expr → Expr
  | emptyRecord : Expr
  | record : Nat → Expr → Expr → Expr
  | field : Nat → Expr → Expr
  | variant : Nat → Expr → Expr
  deriving Repr, DecidableEq

/-- The core's nonexpansive syntax. A variable is generalizable only if its
scheme also permits a pure typing; a computation argument is not made pure. -/
def Expr.isValue : Expr → Bool
  | .var _ | .lit _ | .lam _ | .emptyRecord => true
  | .pair a b | .record _ a b => a.isValue && b.isValue
  | .variant _ a => a.isValue
  | _ => false

/-- A polymorphic binding remembers the lexical environment. It does not
capture the caller's future instantiations or generalize their variables. -/
inductive Binding (m : Model) where
  | mono : Comp m → Binding m
  | poly : Expr → List (Binding m) → Binding m

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
    | letComputed : v.isValue = false → Typing m Γ v a →
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
    | emptyRecord : Comp.le m (Comp.pure m m.emptyRecord) c →
        Typing m Γ .emptyRecord c
    | record : Typing m Γ x a → Typing m Γ rest b →
        Comp.le m (m.record l a.1 b.1, m.join a.2 b.2) c →
        Typing m Γ (.record l x rest) c
    | field : Typing m Γ x (m.record l a m.emptyRecord, er) →
        Comp.le m (a, er) c → Typing m Γ (.field l x) c
    | variant : Typing m Γ x a →
        Comp.le m (m.variant l a.1, a.2) c → Typing m Γ (.variant l x) c

  inductive BindingTyping (m : Model) : Binding m → Comp m → Prop where
    | mono : Comp.le m a c → BindingTyping m (.mono a) c
    | poly : Typing m Γ v (Comp.pure m c.1) → m.subRow m.empty c.2 →
        BindingTyping m (.poly v Γ) c
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
      if v.isValue then
        let scheme : Scheme α :=
          .and (generate Γ.lift v (CompTerm.pure (.var none)))
            (.rowLe .empty (.var none))
        .and (.existsSlot (generate Γ.lift v (CompTerm.pure (.var none))))
          (generate (scheme :: Γ) body out)
      else
        .existsSlot (.existsSlot (
          .and (generate (env₂ Γ) v fresh₀)
            (.and (generate (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ Γ) body fresh₁)
              (Formula.compLe ⟨fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out)))))
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
  | .emptyRecord, out => Formula.compLe (CompTerm.pure .emptyRecord) out
  | .record l x rest, out =>
      .existsSlot (.existsSlot (
        .and (generate (env₂ Γ) x fresh₀)
          (.and (generate (env₂ Γ) rest fresh₁)
            (Formula.compLe ⟨.record l fresh₀.ty fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out)))))
  | .field l x, out =>
      .existsSlot (
        .and (generate Γ.lift x ⟨.record l (.var none) .emptyRecord, .var none⟩)
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
      (∃ a, Typing m Γ v (Comp.pure m a)) ∧ Typing m (.poly v Γ :: Γ) body c := by
  constructor
  · intro h
    cases h with
    | letValue _ ha hb => exact ⟨⟨_, ha⟩, hb⟩
    | letComputed hn _ _ _ => simp [hv] at hn
  · rintro ⟨⟨a, ha⟩, hb⟩
    exact Typing.letValue hv ha hb

theorem Typing.letComputed_iff (m : Model) (Γ : List (Binding m)) (v body : Expr) (c : Comp m)
    (hv : v.isValue = false) :
    Typing m Γ (.letE v body) c ↔ ∃ a b,
      Typing m Γ v a ∧ Typing m (.mono (Comp.pure m a.1) :: Γ) body b ∧
      Comp.le m (b.1, m.join a.2 b.2) c := by
  constructor
  · intro h
    cases h with
    | letValue hn _ _ => simp [hv] at hn
    | letComputed _ ha hb hc => exact ⟨_, _, ha, hb, hc⟩
  · rintro ⟨a, b, ha, hb, hc⟩
    exact Typing.letComputed hv ha hb hc

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
    Typing m Γ .emptyRecord c ↔ Comp.le m (Comp.pure m m.emptyRecord) c := by
  constructor
  · intro h; cases h with | emptyRecord h => exact h
  · exact Typing.emptyRecord

@[simp] theorem Typing.record_iff (m : Model) (Γ : List (Binding m))
    (l : Nat) (x r : Expr) (c : Comp m) :
    Typing m Γ (.record l x r) c ↔ ∃ a b,
      Typing m Γ x a ∧ Typing m Γ r b ∧
      Comp.le m (m.record l a.1 b.1, m.join a.2 b.2) c := by
  constructor
  · intro h; cases h with | record hx hr hc => exact ⟨_, _, hx, hr, hc⟩
  · rintro ⟨a, b, hx, hr, hc⟩; exact Typing.record hx hr hc

@[simp] theorem Typing.field_iff (m : Model) (Γ : List (Binding m))
    (l : Nat) (x : Expr) (c : Comp m) :
    Typing m Γ (.field l x) c ↔ ∃ a er,
      Typing m Γ x (m.record l a m.emptyRecord, er) ∧ Comp.le m (a, er) c := by
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
          change ((∃ c, (generate sΓ.lift v (CompTerm.pure (.var none))).Holds m (extend ρ c)) ∧
            (generate (scheme :: sΓ) body out).Holds m ρ) ↔ _
          simp only [hvalue]
          rw [hbody, Typing.letValue_iff m Γ v body (out.eval m ρ) hv]
          exact and_congr (exists_comp_ty m (fun a => Typing m Γ v (Comp.pure m a))) Iff.rfl
      | false =>
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
          simp only [generate, hv]
          rw [Typing.letComputed_iff m Γ v body (out.eval m ρ) hv]
          apply exists_congr; intro a
          apply exists_congr; intro b
          simp only [Formula.Holds]
          rw [ha, hb]
          simp [Formula.compLe, Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
            CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
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
  | field l x ih =>
      have hx (a : Comp m) :
          (generate sΓ.lift x ⟨.record l (.var none) .emptyRecord, .var none⟩).Holds m
            (extend ρ a) ↔ Typing m Γ x (m.record l a.1 m.emptyRecord, a.2) := by
        simpa only [CompTerm.eval, TyTerm.eval, RowTerm.eval, extend_none]
          using ih _ _ _ ⟨.record l (.var none) .emptyRecord, .var none⟩ (henv.lift a)
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

/-- Public inference entry point. Its one bound slot is the inferred result;
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
  | .and p q => 1 + p.nodes + q.nodes
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

end Yulang.Inference
