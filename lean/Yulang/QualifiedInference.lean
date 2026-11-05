import Yulang.RoleConstraints
import Yulang.EffectInference

/-!
# Inference with deferred role predicates and abstract dictionaries

Resolved method references generate their declared role obligations without
calling a resolver. This core keeps the existing computation-argument rules,
structural forms, and monomorphic sequencing. Qualified generalization is the
separate checked-interface rule below: it checks a pure RHS under abstract
dictionaries and stores a scheme for use-time instantiation. Source method
search and the choice of an interface from unsolved structural constraints are
not part of this theorem.
-/

namespace Yulang.QualifiedInference

open Inference RoleConstraints
open EffectInference (localEnv localEnv_comp_inl localEnv_map)

structure MethodDecl where
  locals : Nat
  requirements : List (Goal (Fin locals))
  value : TyTerm (Fin locals)

abbrev MethodTable := Nat → MethodDecl

def typeEnv (m : Model) (ι : Fin n → m.Ty) : Fin n → Comp m := Comp.pure m ∘ ι

/-- Ordinary let schemes quantify value types and rows independently. This is
distinct from operation-local type parameters, whose row component is empty. -/
def slotEnv (ρ : α → Comp m) (ι : Fin n → Comp m) : α ⊕ Fin n → Comp m :=
  Sum.elim ρ ι

@[simp] theorem slotEnv_comp_inl (ρ : α → Comp m) (ι : Fin n → Comp m) :
    slotEnv ρ ι ∘ Sum.inl = ρ := rfl

@[simp] theorem slotEnv_map (ρ : β → Comp m) (ι : Fin n → Comp m) (f : α → β) :
    slotEnv ρ ι ∘ Sum.map f id = slotEnv (ρ ∘ f) ι := by
  funext x; cases x <;> rfl

inductive Formula : Type → Type 1 where
  | top : Formula α
  | bot : Formula α
  | and : Formula α → Formula α → Formula α
  | or : Formula α → Formula α → Formula α
  | tyLe : TyTerm α → TyTerm α → Formula α
  | rowLe : RowTerm α → RowTerm α → Formula α
  | role : Goal α → Formula α
  | existsSlot : Formula (Option α) → Formula α
  | existsTypes : (n : Nat) → Formula (α ⊕ Fin n) → Formula α
  | forallTypes : (n : Nat) → Formula (α ⊕ Fin n) → Formula α
  | existsSlots : (n : Nat) → Formula (α ⊕ Fin n) → Formula α
  | forallSlots : (n : Nat) → Formula (α ⊕ Fin n) → Formula α
  | given : List (Goal α) → Formula α → Formula α

def Formula.compLe (a b : CompTerm α) : Formula α :=
  .and (.tyLe a.ty b.ty) (.rowLe a.row b.row)

def Formula.roles (goals : List (Goal α)) : Formula α :=
  goals.foldr (fun goal rest => .and (.role goal) rest) .top

def Formula.Holds (m : Model) (theory : Theory m) :
    {α : Type} → (α → Comp m) → Formula α → Prop
  | _, _, .top => True
  | _, _, .bot => False
  | _, ρ, .and p q => p.Holds m theory ρ ∧ q.Holds m theory ρ
  | _, ρ, .or p q => p.Holds m theory ρ ∨ q.Holds m theory ρ
  | _, ρ, .tyLe a b => m.subTy (a.eval m ρ) (b.eval m ρ)
  | _, ρ, .rowLe a b => m.subRow (a.eval m ρ) (b.eval m ρ)
  | _, ρ, .role goal => theory (goal.eval m ρ)
  | _, ρ, .existsSlot p => ∃ c, p.Holds m theory (extend ρ c)
  | _, ρ, .existsTypes n p => ∃ ι : Fin n → m.Ty, p.Holds m theory (localEnv m ρ ι)
  | _, ρ, .forallTypes n p => ∀ ι : Fin n → m.Ty, p.Holds m theory (localEnv m ρ ι)
  | _, ρ, .existsSlots n p => ∃ ι : Fin n → Comp m, p.Holds m theory (slotEnv ρ ι)
  | _, ρ, .forallSlots n p => ∀ ι : Fin n → Comp m, p.Holds m theory (slotEnv ρ ι)
  | _, ρ, .given goals p => p.Holds m
      (WithEvidence theory (goals.map (Goal.eval m ρ))) ρ

def Formula.rename (f : α → β) : Formula α → Formula β
  | .top => .top
  | .bot => .bot
  | .and p q => .and (p.rename f) (q.rename f)
  | .or p q => .or (p.rename f) (q.rename f)
  | .tyLe a b => .tyLe (a.rename f) (b.rename f)
  | .rowLe a b => .rowLe (a.rename f) (b.rename f)
  | .role goal => .role (goal.rename f)
  | .existsSlot p => .existsSlot (p.rename (Option.map f))
  | .existsTypes n p => .existsTypes n (p.rename (Sum.map f id))
  | .forallTypes n p => .forallTypes n (p.rename (Sum.map f id))
  | .existsSlots n p => .existsSlots n (p.rename (Sum.map f id))
  | .forallSlots n p => .forallSlots n (p.rename (Sum.map f id))
  | .given goals p => .given (goals.map (Goal.rename f)) (p.rename f)

def liftTypeSubst (f : α → CompTerm β) : α ⊕ Fin n → CompTerm (β ⊕ Fin n)
  | .inl a => (f a).rename Sum.inl
  | .inr i => CompTerm.var (.inr i)

def Formula.subst (f : α → CompTerm β) : Formula α → Formula β
  | .top => .top
  | .bot => .bot
  | .and p q => .and (p.subst f) (q.subst f)
  | .or p q => .or (p.subst f) (q.subst f)
  | .tyLe a b => .tyLe (a.subst f) (b.subst f)
  | .rowLe a b => .rowLe (a.subst f) (b.subst f)
  | .role goal => .role (goal.subst f)
  | .existsSlot p => .existsSlot (p.subst (Inference.liftSubst f))
  | .existsTypes n p => .existsTypes n (p.subst (liftTypeSubst f))
  | .forallTypes n p => .forallTypes n (p.subst (liftTypeSubst f))
  | .existsSlots n p => .existsSlots n (p.subst (liftTypeSubst f))
  | .forallSlots n p => .forallSlots n (p.subst (liftTypeSubst f))
  | .given goals p => .given (goals.map (Goal.subst f)) (p.subst f)

@[simp] theorem Formula.holds_compLe (m : Model) (theory : Theory m) (ρ : α → Comp m)
    (a b : CompTerm α) :
    (Formula.compLe a b).Holds m theory ρ ↔ Comp.le m (a.eval m ρ) (b.eval m ρ) := Iff.rfl

@[simp] theorem Formula.holds_roles (m : Model) (theory : Theory m) (ρ : α → Comp m)
    (goals : List (Goal α)) :
    (Formula.roles goals).Holds m theory ρ ↔
      Satisfies theory (goals.map (Goal.eval m ρ)) := by
  induction goals <;> simp_all [roles, Holds, Satisfies]

@[simp] theorem Formula.holds_rename (m : Model) (theory : Theory m) (p : Formula α)
    (f : α → β) (ρ : β → Comp m) :
    (p.rename f).Holds m theory ρ ↔ p.Holds m theory (ρ ∘ f) := by
  induction p generalizing β theory with
  | top => rfl
  | bot => rfl
  | and p q ihp ihq => simp [rename, Holds, ihp, ihq]
  | or p q ihp ihq => simp [rename, Holds, ihp, ihq]
  | tyLe a b => simp [rename, Holds]
  | rowLe a b => simp [rename, Holds]
  | role goal => simp [rename, Holds]
  | existsSlot p ih =>
      simp only [rename, Holds, ih]
      apply exists_congr
      intro c
      have h : extend ρ c ∘ Option.map f = extend (ρ ∘ f) c := by
        funext x; cases x <;> rfl
      rw [h]
  | existsTypes n p ih => simp [rename, Holds, ih, localEnv_map]
  | forallTypes n p ih => simp [rename, Holds, ih, localEnv_map]
  | existsSlots n p ih => simp [rename, Holds, ih, slotEnv_map]
  | forallSlots n p ih => simp [rename, Holds, ih, slotEnv_map]
  | given goals p ih => simp [rename, Holds, ih, List.map_map, Function.comp_def]

theorem eval_liftTypeSubst (m : Model) (ρ : β → Comp m)
    (f : α → CompTerm β) (ι : Fin n → m.Ty) :
    (fun x => (liftTypeSubst f x).eval m (localEnv m ρ ι)) =
      localEnv m (fun x => (f x).eval m ρ) ι := by
  funext x; cases x <;> simp [liftTypeSubst, localEnv]

theorem eval_liftSlotSubst (m : Model) (ρ : β → Comp m)
    (f : α → CompTerm β) (ι : Fin n → Comp m) :
    (fun x => (liftTypeSubst f x).eval m (slotEnv ρ ι)) =
      slotEnv (fun x => (f x).eval m ρ) ι := by
  funext x; cases x <;> simp [liftTypeSubst, slotEnv]

@[simp] theorem Formula.holds_subst (m : Model) (theory : Theory m) (p : Formula α)
    (f : α → CompTerm β) (ρ : β → Comp m) :
    (p.subst f).Holds m theory ρ ↔ p.Holds m theory (fun x => (f x).eval m ρ) := by
  induction p generalizing β theory with
  | top => rfl
  | bot => rfl
  | and p q ihp ihq => simp [subst, Holds, ihp, ihq]
  | or p q ihp ihq => simp [subst, Holds, ihp, ihq]
  | tyLe a b => simp [subst, Holds]
  | rowLe a b => simp [subst, Holds]
  | role goal => simp [subst, Holds]
  | existsSlot p ih =>
      simp only [subst, Holds, ih]
      apply exists_congr
      intro c
      have h : (fun x => (Inference.liftSubst f x).eval m (extend ρ c)) =
          extend (fun x => (f x).eval m ρ) c := by
        funext x; cases x <;> simp [Inference.liftSubst]
      rw [h]
  | existsTypes n p ih => simp [subst, Holds, ih, eval_liftTypeSubst]
  | forallTypes n p ih => simp [subst, Holds, ih, eval_liftTypeSubst]
  | existsSlots n p ih => simp [subst, Holds, ih, eval_liftSlotSubst]
  | forallSlots n p ih => simp [subst, Holds, ih, eval_liftSlotSubst]
  | given goals p ih => simp [subst, Holds, ih, List.map_map, Function.comp_def]

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

@[simp] theorem Scheme.holds_instantiate (m : Model) (theory : Theory m) (ρ : α → Comp m)
    (s : Scheme α) (c : CompTerm α) :
    (s.instantiate c).Holds m theory ρ ↔ s.Holds m theory (extend ρ (c.eval m ρ)) := by
  simp only [instantiate, Formula.holds_subst]
  have h : (fun x => ((fun | none => c | some a => CompTerm.var a) x).eval m ρ) =
      extend ρ (c.eval m ρ) := by
    funext x
    cases x <;> rfl
  exact (congrArg (fun η => s.Holds m theory η) h).to_iff

@[simp] theorem Scheme.holds_mono (m : Model) (theory : Theory m) (ρ : α → Comp m)
    (a : CompTerm α) (c : Comp m) :
    (Scheme.mono a).Holds m theory (extend ρ c) ↔ Comp.le m (a.eval m ρ) c := by
  simp [mono]

inductive Expr where
  | var : Nat → Expr
  | method : Nat → Expr
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

/-- Only a pure, nonexpansive RHS may use the qualified-let rule. -/
def Expr.isValue : Expr → Bool
  | .var _ | .method _ | .lit _ | .lam _ | .emptyRecord => true
  | .pair a b | .record _ a b => a.isValue && b.isValue
  | .variant _ a => a.isValue
  | _ => false

/-- Signatures retain their captured environment through these semantic
functions; only finite local type/row slots are independently instantiated. -/
inductive Binding (m : Model) where
  | mono : Comp m → Binding m
  | qualified : (n : Nat) → ((Fin n → Comp m) → List (Predicate m.Ty)) →
      ((Fin n → Comp m) → Comp m) → Binding m

inductive BindingTyping (m : Model) (theory : Theory m) : Binding m → Comp m → Prop where
  | mono : Comp.le m a c → BindingTyping m theory (.mono a) c
  | qualified (ι : Fin n → Comp m) : Satisfies theory (requirements ι) →
      Comp.le m (result ι) c → BindingTyping m theory (.qualified n requirements result) c

inductive Typing (m : Model) (methods : MethodTable) (theory : Theory m) : List (Binding m) → Expr → Comp m → Prop where
  | var : Γ[n]? = some b → BindingTyping m theory b c → Typing m methods theory Γ (.var n) c
  | method (ι : Fin (methods name).locals → m.Ty) :
      Satisfies theory ((methods name).requirements.map (Goal.eval m (typeEnv m ι))) →
      Comp.le m (Comp.pure m ((methods name).value.eval m (typeEnv m ι))) c →
      Typing m methods theory Γ (.method name) c
  | lit : Comp.le m (Comp.pure m (m.base b)) c → Typing m methods theory Γ (.lit b) c
  | lam : Typing m methods theory (.mono a :: Γ) body b →
      Comp.le m (Comp.pure m (Comp.arrow m a b)) c → Typing m methods theory Γ (.lam body) c
  | app : Typing m methods theory Γ f (Comp.arrow m a b, ef) → Typing m methods theory Γ x a →
      Comp.le m (b.1, m.join ef b.2) c → Typing m methods theory Γ (.app f x) c
  | letComputed : Typing m methods theory Γ v a →
      Typing m methods theory (.mono (Comp.pure m a.1) :: Γ) body b →
      Comp.le m (b.1, m.join a.2 b.2) c → Typing m methods theory Γ (.letE v body) c
  | branch : Typing m methods theory Γ condition (m.base .bool, eg) →
      Typing m methods theory Γ yes a → Typing m methods theory Γ no b →
      Comp.le m (m.union a.1 b.1, m.join eg (m.join a.2 b.2)) c →
      Typing m methods theory Γ (.branch condition yes no) c
  | pair : Typing m methods theory Γ x a → Typing m methods theory Γ y b →
      Comp.le m (m.pair a.1 b.1, m.join a.2 b.2) c → Typing m methods theory Γ (.pair x y) c
  | fst : Typing m methods theory Γ x (m.pair a b, er) →
      Comp.le m (a, er) c → Typing m methods theory Γ (.fst x) c
  | snd : Typing m methods theory Γ x (m.pair a b, er) →
      Comp.le m (b, er) c → Typing m methods theory Γ (.snd x) c
  | emptyRecord : Comp.le m (Comp.pure m m.emptyRecord) c →
      Typing m methods theory Γ .emptyRecord c
  | record : Typing m methods theory Γ x a → Typing m methods theory Γ rest b → m.subTy b.1 m.emptyRecord →
      Comp.le m (m.record l a.1 b.1, m.join a.2 b.2) c →
      Typing m methods theory Γ (.record l x rest) c
  | field : Typing m methods theory Γ x (m.record l a m.emptyRecord, er) →
      Comp.le m (a, er) c → Typing m methods theory Γ (.field l x) c
  | variant : Typing m methods theory Γ x a →
      Comp.le m (m.variant l a.1, a.2) c → Typing m methods theory Γ (.variant l x) c


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
def generate (methods : MethodTable) (Γ : SchemeEnv α) : Expr → CompTerm α → Formula α
  | .var n, out => Scheme.lookup Γ n out
  | .method name, out =>
      .existsTypes (methods name).locals
        (.and (Formula.roles ((methods name).requirements.map (Goal.rename Sum.inr)))
          (Formula.compLe (CompTerm.pure ((methods name).value.rename Sum.inr))
            (out.rename Sum.inl)))
  | .lit b, out => Formula.compLe (CompTerm.pure (.base b)) out
  | .lam body, out =>
      .existsSlot (.existsSlot (
        .and (generate methods (Scheme.mono fresh₀ :: env₂ Γ) body fresh₁)
          (Formula.compLe (CompTerm.pure (CompTerm.arrow fresh₀ fresh₁)) (lift₂ out))))
  | .app f x, out =>
      .existsSlot (.existsSlot (.existsSlot (
        .and (generate methods (env₃ Γ) f ⟨CompTerm.arrow fresh₀₃ fresh₁₃, fresh₂₃.row⟩)
          (.and (generate methods (env₃ Γ) x fresh₀₃)
            (Formula.compLe ⟨fresh₁₃.ty, .join fresh₂₃.row fresh₁₃.row⟩ (lift₃ out))))))
  | .letE v body, out =>
      .existsSlot (.existsSlot (
        .and (generate methods (env₂ Γ) v fresh₀)
          (.and (generate methods (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ Γ) body fresh₁)
            (Formula.compLe ⟨fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out)))))
  | .branch g y n, out =>
      .existsSlot (.existsSlot (.existsSlot (
        .and (generate methods (env₃ Γ) g ⟨.base .bool, fresh₀₃.row⟩)
          (.and (generate methods (env₃ Γ) y fresh₁₃)
            (.and (generate methods (env₃ Γ) n fresh₂₃)
              (Formula.compLe ⟨.union fresh₁₃.ty fresh₂₃.ty,
                .join fresh₀₃.row (.join fresh₁₃.row fresh₂₃.row)⟩ (lift₃ out)))))))
  | .pair x y, out =>
      .existsSlot (.existsSlot (
        .and (generate methods (env₂ Γ) x fresh₀)
          (.and (generate methods (env₂ Γ) y fresh₁)
            (Formula.compLe ⟨.pair fresh₀.ty fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out)))))
  | .fst x, out =>
      .existsSlot (.existsSlot (
        .and (generate methods (env₂ Γ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩)
          (Formula.compLe ⟨fresh₀.ty, fresh₀.row⟩ (lift₂ out))))
  | .snd x, out =>
      .existsSlot (.existsSlot (
        .and (generate methods (env₂ Γ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩)
          (Formula.compLe ⟨fresh₁.ty, fresh₀.row⟩ (lift₂ out))))
  | .emptyRecord, out => Formula.compLe (CompTerm.pure .emptyRecord) out
  | .record l x rest, out =>
      .existsSlot (.existsSlot (
        .and (generate methods (env₂ Γ) x fresh₀)
          (.and (generate methods (env₂ Γ) rest fresh₁)
            (.and (.tyLe fresh₁.ty .emptyRecord)
              (Formula.compLe ⟨.record l fresh₀.ty fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out))))))
  | .field l x, out =>
      .existsSlot (
        .and (generate methods Γ.lift x ⟨.record l (.var none) .emptyRecord, .var none⟩)
          (Formula.compLe (CompTerm.var none) (out.rename some)))
  | .variant l x, out =>
      .existsSlot (
        .and (generate methods Γ.lift x (CompTerm.var none))
          (Formula.compLe ⟨.variant l (.var none), .var none⟩ (out.rename some)))

def SchemeLookup (m : Model) (theory : Theory m) (ρ : α → Comp m) (Γ : SchemeEnv α)
    (n : Nat) (c : Comp m) : Prop :=
  match Γ[n]? with
  | none => False
  | some s => s.Holds m theory (extend ρ c)

def BindingLookup (m : Model) (theory : Theory m) (Γ : List (Binding m)) (n : Nat) (c : Comp m) : Prop :=
  ∃ b, Γ[n]? = some b ∧ BindingTyping m theory b c

/-- A symbolic context represents exactly the same instances as its independent
declarative context. This relation is preserved by fresh allocation. -/
def EnvRel (m : Model) (theory : Theory m) (ρ : α → Comp m) (sΓ : SchemeEnv α)
    (Γ : List (Binding m)) : Prop :=
  ∀ n c, SchemeLookup m theory ρ sΓ n c ↔ BindingLookup m theory Γ n c

@[simp] theorem Scheme.holds_lookup (m : Model) (theory : Theory m) (ρ : α → Comp m)
    (Γ : SchemeEnv α) (n : Nat) (c : CompTerm α) :
    (Scheme.lookup Γ n c).Holds m theory ρ ↔ SchemeLookup m theory ρ Γ n (c.eval m ρ) := by
  unfold lookup SchemeLookup
  split <;> simp [Formula.Holds]

@[simp] theorem BindingTyping.mono_iff (m : Model) (theory : Theory m) (a c : Comp m) :
    BindingTyping m theory (.mono a) c ↔ Comp.le m a c := by
  constructor
  · intro h; cases h with | mono h => exact h
  · exact BindingTyping.mono

theorem EnvRel.nil (m : Model) (theory : Theory m) (ρ : α → Comp m) : EnvRel m theory ρ [] [] := by
  intro n c
  simp [SchemeLookup, BindingLookup]

theorem EnvRel.cons {m : Model} {theory : Theory m} {ρ : α → Comp m} {sΓ : SchemeEnv α}
    {Γ : List (Binding m)} {s : Scheme α} {b : Binding m} (h : EnvRel m theory ρ sΓ Γ)
    (head : ∀ c, s.Holds m theory (extend ρ c) ↔ BindingTyping m theory b c) :
    EnvRel m theory ρ (s :: sΓ) (b :: Γ) := by
  intro n c
  cases n with
  | zero => simpa [SchemeLookup, BindingLookup] using head c
  | succ n => simpa [SchemeLookup, BindingLookup] using h n c

theorem EnvRel.mono {m : Model} {theory : Theory m} {ρ : α → Comp m} {sΓ : SchemeEnv α}
    {Γ : List (Binding m)} (h : EnvRel m theory ρ sΓ Γ) (a : CompTerm α) :
    EnvRel m theory ρ (Scheme.mono a :: sΓ) (.mono (a.eval m ρ) :: Γ) := by
  apply h.cons
  intro c
  simp

theorem EnvRel.rename {m : Model} {theory : Theory m} {ρ : α → Comp m} {sΓ : SchemeEnv α}
    {Γ : List (Binding m)} (h : EnvRel m theory ρ sΓ Γ) (f : α → β) (η : β → Comp m)
    (he : η ∘ f = ρ) : EnvRel m theory η (sΓ.rename f) Γ := by
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

theorem EnvRel.lift {m : Model} {theory : Theory m} {ρ : α → Comp m} {sΓ : SchemeEnv α}
    {Γ : List (Binding m)} (h : EnvRel m theory ρ sΓ Γ) (a : Comp m) :
    EnvRel m theory (extend ρ a) sΓ.lift Γ := by
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

@[simp] theorem Typing.var_iff (m : Model) (methods : MethodTable) (theory : Theory m) (Γ : List (Binding m)) (n : Nat) (c : Comp m) :
    Typing m methods theory Γ (.var n) c ↔ BindingLookup m theory Γ n c := by
  constructor
  · intro h
    cases h with | var hget hb => exact ⟨_, hget, hb⟩
  · rintro ⟨b, hget, hb⟩
    exact Typing.var hget hb

@[simp] theorem Typing.lit_iff (m : Model) (methods : MethodTable) (theory : Theory m) (Γ : List (Binding m)) (b : Base) (c : Comp m) :
    Typing m methods theory Γ (.lit b) c ↔ Comp.le m (Comp.pure m (m.base b)) c := by
  constructor
  · intro h; cases h with | lit h => exact h
  · exact Typing.lit

@[simp] theorem Typing.lam_iff (m : Model) (methods : MethodTable) (theory : Theory m) (Γ : List (Binding m)) (body : Expr) (c : Comp m) :
    Typing m methods theory Γ (.lam body) c ↔ ∃ a b,
      Typing m methods theory (.mono a :: Γ) body b ∧
      Comp.le m (Comp.pure m (Comp.arrow m a b)) c := by
  constructor
  · intro h; cases h with | lam hb hc => exact ⟨_, _, hb, hc⟩
  · rintro ⟨a, b, hb, hc⟩; exact Typing.lam hb hc

@[simp] theorem Typing.app_iff (m : Model) (methods : MethodTable) (theory : Theory m) (Γ : List (Binding m)) (f x : Expr) (c : Comp m) :
    Typing m methods theory Γ (.app f x) c ↔ ∃ a b ef,
      Typing m methods theory Γ f (Comp.arrow m a b, ef) ∧ Typing m methods theory Γ x a ∧
      Comp.le m (b.1, m.join ef b.2) c := by
  constructor
  · intro h; cases h with | app hf hx hc => exact ⟨_, _, _, hf, hx, hc⟩
  · rintro ⟨a, b, ef, hf, hx, hc⟩; exact Typing.app hf hx hc

@[simp] theorem Typing.letComputed_iff (m : Model) (methods : MethodTable) (theory : Theory m) (Γ : List (Binding m))
    (v body : Expr) (c : Comp m) :
    Typing m methods theory Γ (.letE v body) c ↔ ∃ a b,
      Typing m methods theory Γ v a ∧ Typing m methods theory (.mono (Comp.pure m a.1) :: Γ) body b ∧
      Comp.le m (b.1, m.join a.2 b.2) c := by
  constructor
  · intro h; cases h with | letComputed ha hb hc => exact ⟨_, _, ha, hb, hc⟩
  · rintro ⟨a, b, ha, hb, hc⟩; exact Typing.letComputed ha hb hc

@[simp] theorem Typing.branch_iff (m : Model) (methods : MethodTable) (theory : Theory m) (Γ : List (Binding m)) (g y n : Expr) (c : Comp m) :
    Typing m methods theory Γ (.branch g y n) c ↔ ∃ eg a b,
      Typing m methods theory Γ g (m.base .bool, eg) ∧ Typing m methods theory Γ y a ∧ Typing m methods theory Γ n b ∧
      Comp.le m (m.union a.1 b.1, m.join eg (m.join a.2 b.2)) c := by
  constructor
  · intro h; cases h with | branch hg hy hn hc => exact ⟨_, _, _, hg, hy, hn, hc⟩
  · rintro ⟨eg, a, b, hg, hy, hn, hc⟩; exact Typing.branch hg hy hn hc

@[simp] theorem Typing.pair_iff (m : Model) (methods : MethodTable) (theory : Theory m) (Γ : List (Binding m)) (x y : Expr) (c : Comp m) :
    Typing m methods theory Γ (.pair x y) c ↔ ∃ a b,
      Typing m methods theory Γ x a ∧ Typing m methods theory Γ y b ∧
      Comp.le m (m.pair a.1 b.1, m.join a.2 b.2) c := by
  constructor
  · intro h; cases h with | pair hx hy hc => exact ⟨_, _, hx, hy, hc⟩
  · rintro ⟨a, b, hx, hy, hc⟩; exact Typing.pair hx hy hc

@[simp] theorem Typing.fst_iff (m : Model) (methods : MethodTable) (theory : Theory m) (Γ : List (Binding m)) (x : Expr) (c : Comp m) :
    Typing m methods theory Γ (.fst x) c ↔ ∃ a b er,
      Typing m methods theory Γ x (m.pair a b, er) ∧ Comp.le m (a, er) c := by
  constructor
  · intro h; cases h with | fst hx hc => exact ⟨_, _, _, hx, hc⟩
  · rintro ⟨a, b, er, hx, hc⟩; exact Typing.fst hx hc

@[simp] theorem Typing.snd_iff (m : Model) (methods : MethodTable) (theory : Theory m) (Γ : List (Binding m)) (x : Expr) (c : Comp m) :
    Typing m methods theory Γ (.snd x) c ↔ ∃ a b er,
      Typing m methods theory Γ x (m.pair a b, er) ∧ Comp.le m (b, er) c := by
  constructor
  · intro h; cases h with | snd hx hc => exact ⟨_, _, _, hx, hc⟩
  · rintro ⟨a, b, er, hx, hc⟩; exact Typing.snd hx hc

@[simp] theorem Typing.emptyRecord_iff (m : Model) (methods : MethodTable) (theory : Theory m) (Γ : List (Binding m)) (c : Comp m) :
    Typing m methods theory Γ .emptyRecord c ↔ Comp.le m (Comp.pure m m.emptyRecord) c := by
  constructor
  · intro h; cases h with | emptyRecord h => exact h
  · exact Typing.emptyRecord

@[simp] theorem Typing.record_iff (m : Model) (methods : MethodTable) (theory : Theory m) (Γ : List (Binding m))
    (l : Nat) (x r : Expr) (c : Comp m) :
    Typing m methods theory Γ (.record l x r) c ↔ ∃ a b,
      Typing m methods theory Γ x a ∧ Typing m methods theory Γ r b ∧ m.subTy b.1 m.emptyRecord ∧
      Comp.le m (m.record l a.1 b.1, m.join a.2 b.2) c := by
  constructor
  · intro h; cases h with | record hx hr hs hc => exact ⟨_, _, hx, hr, hs, hc⟩
  · rintro ⟨a, b, hx, hr, hs, hc⟩; exact Typing.record hx hr hs hc

@[simp] theorem Typing.field_iff (m : Model) (methods : MethodTable) (theory : Theory m) (Γ : List (Binding m))
    (l : Nat) (x : Expr) (c : Comp m) :
    Typing m methods theory Γ (.field l x) c ↔ ∃ a er,
      Typing m methods theory Γ x (m.record l a m.emptyRecord, er) ∧ Comp.le m (a, er) c := by
  constructor
  · intro h; cases h with | field hx hc => exact ⟨_, _, hx, hc⟩
  · rintro ⟨a, er, hx, hc⟩; exact Typing.field hx hc

@[simp] theorem Typing.variant_iff (m : Model) (methods : MethodTable) (theory : Theory m) (Γ : List (Binding m))
    (l : Nat) (x : Expr) (c : Comp m) :
    Typing m methods theory Γ (.variant l x) c ↔ ∃ a,
      Typing m methods theory Γ x a ∧ Comp.le m (m.variant l a.1, a.2) c := by
  constructor
  · intro h; cases h with | variant hx hc => exact ⟨_, hx, hc⟩
  · rintro ⟨a, hx, hc⟩; exact Typing.variant hx hc

@[simp] theorem Typing.method_iff (m : Model) (methods : MethodTable) (theory : Theory m)
    (Γ : List (Binding m)) (name : Nat) (c : Comp m) :
    Typing m methods theory Γ (.method name) c ↔
      ∃ ι : Fin (methods name).locals → m.Ty,
        Satisfies theory ((methods name).requirements.map (Goal.eval m (typeEnv m ι))) ∧
        Comp.le m (Comp.pure m ((methods name).value.eval m (typeEnv m ι))) c := by
  constructor
  · intro h; cases h with | method ι hr ht => exact ⟨ι, hr, ht⟩
  · rintro ⟨ι, hr, ht⟩; exact .method ι hr ht

theorem generate_models_iff_typing (m : Model) (methods : MethodTable) (theory : Theory m) (e : Expr)
    (sΓ : SchemeEnv α) (Γ : List (Binding m)) (ρ : α → Comp m)
    (out : CompTerm α) (henv : EnvRel m theory ρ sΓ Γ) :
    (generate methods sΓ e out).Holds m theory ρ ↔ Typing m methods theory Γ e (out.eval m ρ) := by
  induction e generalizing α sΓ Γ ρ out with
  | var n => simpa [generate] using henv n (out.eval m ρ)
  | method name =>
      simp only [generate, Formula.Holds, Formula.holds_roles, Formula.holds_compLe,
        Typing.method_iff, CompTerm.eval_rename, CompTerm.eval_pure, TyTerm.eval_rename,
        localEnv_comp_inl]
      apply exists_congr; intro ι
      simp [List.map_map, Function.comp_def, localEnv, typeEnv]
  | lit b => simp [generate, CompTerm.eval, CompTerm.pure, TyTerm.eval, RowTerm.eval, Comp.pure]
  | lam body ih =>
      have hb (a b : Comp m) :
          (generate methods (Scheme.mono fresh₀ :: env₂ sΓ) body fresh₁).Holds m theory (extend (extend ρ a) b) ↔
          Typing m methods theory (.mono a :: Γ) body b := by
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
          (generate methods (env₃ sΓ) f ⟨CompTerm.arrow fresh₀₃ fresh₁₃, fresh₂₃.row⟩).Holds m theory
            (extend (extend (extend ρ a) b) d) ↔ Typing m methods theory Γ f (Comp.arrow m a b, d.2) := by
        simpa only [env₃, fresh₀₃, fresh₁₃, fresh₂₃, CompTerm.eval, CompTerm.arrow,
          CompTerm.var, TyTerm.eval, RowTerm.eval, extend_none, extend_some, Comp.arrow]
          using ihf _ _ _ ⟨CompTerm.arrow fresh₀₃ fresh₁₃, fresh₂₃.row⟩ (((henv.lift a).lift b).lift d)
      have hx (a b d : Comp m) :
          (generate methods (env₃ sΓ) x fresh₀₃).Holds m theory (extend (extend (extend ρ a) b) d) ↔
          Typing m methods theory Γ x a := by
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
      exact exists_comp_row m (fun r => Typing m methods theory Γ f (Comp.arrow m a b, r) ∧
        Typing m methods theory Γ x a ∧ Comp.le m (b.1, m.join r b.2) (out.eval m ρ))
  | letE v body ihv ihb =>
      let mono : Formula α := .existsSlot (.existsSlot (
        .and (generate methods (env₂ sΓ) v fresh₀)
          (.and (generate methods (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ sΓ) body fresh₁)
            (Formula.compLe ⟨fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out)))))
      have hmono : mono.Holds m theory ρ ↔ ∃ a b,
          Typing m methods theory Γ v a ∧ Typing m methods theory (.mono (Comp.pure m a.1) :: Γ) body b ∧
          Comp.le m (b.1, m.join a.2 b.2) (out.eval m ρ) := by
        have ha (a b : Comp m) :
            (generate methods (env₂ sΓ) v fresh₀).Holds m theory (extend (extend ρ a) b) ↔ Typing m methods theory Γ v a := by
          simpa only [env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
            using ihv _ _ _ fresh₀ ((henv.lift a).lift b)
        have hb (a b : Comp m) :
            (generate methods (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ sΓ) body fresh₁).Holds m theory
              (extend (extend ρ a) b) ↔ Typing m methods theory (.mono (Comp.pure m a.1) :: Γ) body b := by
          simpa [env₂, fresh₀, fresh₁, CompTerm.pure, Comp.pure,
            CompTerm.var, CompTerm.eval, TyTerm.eval, RowTerm.eval]
            using ihb _ _ _ fresh₁ (((henv.lift a).lift b).mono (CompTerm.pure fresh₀.ty))
        simp only [mono, Formula.Holds]
        apply exists_congr; intro a
        apply exists_congr; intro b
        rw [ha, hb]
        simp [Formula.compLe, Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
          CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
      change mono.Holds m theory ρ ↔ _
      exact hmono.trans (Typing.letComputed_iff m methods theory Γ v body (out.eval m ρ)).symm
  | branch g y n ihg ihy ihn =>
      have hg (a b d : Comp m) :
          (generate methods (env₃ sΓ) g ⟨.base .bool, fresh₀₃.row⟩).Holds m theory
            (extend (extend (extend ρ a) b) d) ↔ Typing m methods theory Γ g (m.base .bool, a.2) := by
        simpa only [env₃, fresh₀₃, CompTerm.eval, CompTerm.var, TyTerm.eval, RowTerm.eval,
          extend_none, extend_some] using ihg _ _ _ ⟨.base .bool, fresh₀₃.row⟩ (((henv.lift a).lift b).lift d)
      have hy (a b d : Comp m) :
          (generate methods (env₃ sΓ) y fresh₁₃).Holds m theory (extend (extend (extend ρ a) b) d) ↔
          Typing m methods theory Γ y b := by
        simpa only [env₃, fresh₁₃, CompTerm.eval_var, extend_none, extend_some]
          using ihy _ _ _ fresh₁₃ (((henv.lift a).lift b).lift d)
      have hn (a b d : Comp m) :
          (generate methods (env₃ sΓ) n fresh₂₃).Holds m theory (extend (extend (extend ρ a) b) d) ↔
          Typing m methods theory Γ n d := by
        simpa only [env₃, fresh₂₃, CompTerm.eval_var, extend_none]
          using ihn _ _ _ fresh₂₃ (((henv.lift a).lift b).lift d)
      simp only [generate, Formula.Holds, Typing.branch_iff]
      simp only [hg, hy, hn]
      simp only [Formula.compLe, Formula.Holds]
      simp only [lift₃, CompTerm.rename, CompTerm.eval, CompTerm.var, fresh₀₃, fresh₁₃,
        fresh₂₃, TyTerm.eval, RowTerm.eval, TyTerm.eval_rename, RowTerm.eval_rename,
        extend_none, extend_some, Function.comp_def]
      exact exists_comp_row m (fun r => ∃ a b, Typing m methods theory Γ g (m.base .bool, r) ∧
        Typing m methods theory Γ y a ∧ Typing m methods theory Γ n b ∧
        Comp.le m (m.union a.1 b.1, m.join r (m.join a.2 b.2)) (out.eval m ρ))
  | pair x y ihx ihy =>
      have hx (a b : Comp m) :
          (generate methods (env₂ sΓ) x fresh₀).Holds m theory (extend (extend ρ a) b) ↔ Typing m methods theory Γ x a := by
        simpa only [env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
          using ihx _ _ _ fresh₀ ((henv.lift a).lift b)
      have hy (a b : Comp m) :
          (generate methods (env₂ sΓ) y fresh₁).Holds m theory (extend (extend ρ a) b) ↔ Typing m methods theory Γ y b := by
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
          (generate methods (env₂ sΓ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩).Holds m theory
            (extend (extend ρ a) b) ↔ Typing m methods theory Γ x (m.pair a.1 b.1, a.2) := by
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
          (generate methods (env₂ sΓ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩).Holds m theory
            (extend (extend ρ a) b) ↔ Typing m methods theory Γ x (m.pair a.1 b.1, a.2) := by
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
          (generate methods (env₂ sΓ) x fresh₀).Holds m theory (extend (extend ρ a) b) ↔ Typing m methods theory Γ x a := by
        simpa only [env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
          using ihx _ _ _ fresh₀ ((henv.lift a).lift b)
      have hr (a b : Comp m) :
          (generate methods (env₂ sΓ) r fresh₁).Holds m theory (extend (extend ρ a) b) ↔ Typing m methods theory Γ r b := by
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
          (generate methods sΓ.lift x ⟨.record l (.var none) .emptyRecord, .var none⟩).Holds m theory
            (extend ρ a) ↔ Typing m methods theory Γ x (m.record l a.1 m.emptyRecord, a.2) := by
        simpa only [CompTerm.eval, TyTerm.eval, RowTerm.eval, extend_none]
          using ih _ _ _ ⟨.record l (.var none) .emptyRecord, .var none⟩ (henv.lift a)
      simp only [generate, Formula.Holds, Typing.field_iff]
      simp only [hx]
      simp [Formula.compLe, Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
        CompTerm.rename, TyTerm.eval, RowTerm.eval, Function.comp_def, Prod.exists]
  | variant l x ih =>
      have hx (a : Comp m) :
          (generate methods sΓ.lift x (CompTerm.var none)).Holds m theory (extend ρ a) ↔ Typing m methods theory Γ x a := by
        simpa only [CompTerm.eval_var, extend_none] using ih _ _ _ (CompTerm.var none) (henv.lift a)
      simp only [generate, Formula.Holds, Typing.variant_iff]
      apply exists_congr; intro a
      rw [hx]
      simp [Formula.compLe, Formula.Holds, Comp.le, CompTerm.eval,
        CompTerm.rename, TyTerm.eval, RowTerm.eval, Function.comp_def]

/-- Public inference entry point. Its one bound slot is the inferred result;
the existing free slots of `Γ` remain parameters, not generalized variables. -/
def principal (methods : MethodTable) (Γ : SchemeEnv α) (e : Expr) : Scheme α :=
  generate methods Γ.lift e (CompTerm.var none)

/-- The principal scheme represents all and only the declarative typings. -/
theorem principal_exact (m : Model) (methods : MethodTable) (theory : Theory m) (e : Expr) (sΓ : SchemeEnv α)
    (Γ : List (Binding m)) (ρ : α → Comp m) (henv : EnvRel m theory ρ sΓ Γ) (c : Comp m) :
    (principal methods sΓ e).Holds m theory (extend ρ c) ↔ Typing m methods theory Γ e c := by
  simpa only [principal, CompTerm.eval_var, extend_none]
    using generate_models_iff_typing m methods theory e sΓ.lift Γ (extend ρ c) (CompTerm.var none) (henv.lift c)

theorem principal_sound (m : Model) (methods : MethodTable) (theory : Theory m) (e : Expr) (sΓ : SchemeEnv α)
    (Γ : List (Binding m)) (ρ : α → Comp m) (henv : EnvRel m theory ρ sΓ Γ) (c : Comp m)
    (h : (principal methods sΓ e).Holds m theory (extend ρ c)) : Typing m methods theory Γ e c :=
  (principal_exact m methods theory e sΓ Γ ρ henv c).mp h

theorem principal_complete (m : Model) (methods : MethodTable) (theory : Theory m) (e : Expr) (sΓ : SchemeEnv α)
    (Γ : List (Binding m)) (ρ : α → Comp m) (henv : EnvRel m theory ρ sΓ Γ) (c : Comp m)
    (h : Typing m methods theory Γ e c) : (principal methods sΓ e).Holds m theory (extend ρ c) :=
  (principal_exact m methods theory e sΓ Γ ρ henv c).mpr h

/-- Every sound candidate scheme is an instance-set subset of the generated
scheme. This is principality of constraints, not a solved normal-form theorem. -/
theorem principal_most_general (m : Model) (methods : MethodTable) (theory : Theory m) (e : Expr) (sΓ : SchemeEnv α)
    (Γ : List (Binding m)) (ρ : α → Comp m) (henv : EnvRel m theory ρ sΓ Γ)
    (candidate : Scheme α)
    (hsound : ∀ c, candidate.Holds m theory (extend ρ c) → Typing m methods theory Γ e c) :
    ∀ c, candidate.Holds m theory (extend ρ c) → (principal methods sΓ e).Holds m theory (extend ρ c) := by
  intro c hc
  exact principal_complete m methods theory e sΓ Γ ρ henv c (hsound c hc)

theorem generate_unbound (methods : MethodTable) (Γ : SchemeEnv α) (n : Nat) (out : CompTerm α)
    (h : Γ[n]? = none) : generate methods Γ (.var n) out = .bot := by
  simp [generate, Scheme.lookup, h]

theorem unbound_not_typable (m : Model) (methods : MethodTable) (theory : Theory m) (Γ : List (Binding m)) (n : Nat) (c : Comp m)
    (h : Γ[n]? = none) : ¬ Typing m methods theory Γ (.var n) c := by
  simp [Typing.var_iff, BindingLookup, h]


end Yulang.QualifiedInference
