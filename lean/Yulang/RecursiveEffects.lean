import Yulang.RowInference

/-!
# Recursive effect constraint generation

The existing core expression language is extended by resolved operation calls,
signed boundaries, and shallow handlers. All their subexpressions use this same
syntax, including lambda bodies and handler arms. The generator is structurally
recursive and emits a finite formula; it does not invoke a solver.

Operation signatures here are monomorphic and may mention the ambient type
slots. Those slots are renamed with the context, never freshly generalized at
an operation use. Operation-local polymorphism, role resolution, source
elaboration and operational safety are separate layers.
-/

namespace Yulang.RecursiveEffects

open Inference (Base Model Comp CompTerm TyTerm RowTerm extend extend_none extend_some
  extend_comp_some exists_comp_row exists_comp_ty fresh₀ fresh₁ fresh₀₃ fresh₁₃ fresh₂₃ lift₂ lift₃)
open RowInference (RowAlgebra RowView RowExpr Boundary heads keysRow fromCoreRow rowEnv
  eval_fromCoreRow eval_heads)

variable {Key Scope Op : Type} {algebra : RowAlgebra Key Scope}

structure Signature (m : Model) (Key : Type) where
  key : Key
  extra : List Key
  input : m.Ty
  output : m.Ty

structure SignatureTerm (Key α : Type) where
  key : Key
  extra : List Key
  input : TyTerm α
  output : TyTerm α

def SignatureTerm.rename (f : α → β) (sig : SignatureTerm Key α) : SignatureTerm Key β :=
  ⟨sig.key, sig.extra, sig.input.rename f, sig.output.rename f⟩

def SignatureTerm.eval (m : Model) (ρ : α → Comp m) (sig : SignatureTerm Key α) :
    Signature m Key := ⟨sig.key, sig.extra, sig.input.eval m ρ, sig.output.eval m ρ⟩

abbrev Signatures (Op Key α : Type) := Op → SignatureTerm Key α

def Signatures.lift (sigsTerm : Signatures Op Key α) : Signatures Op Key (Option α) :=
  fun op => (sigsTerm op).rename some

def SigRel (m : Model) (ρ : α → Comp m) (sigsTerm : Signatures Op Key α)
    (sigs : Op → Signature m Key) : Prop := ∀ op, (sigsTerm op).eval m ρ = sigs op

@[simp] theorem SignatureTerm.eval_rename (m : Model) (ρ : β → Comp m)
    (f : α → β) (sig : SignatureTerm Key α) :
    (sig.rename f).eval m ρ = sig.eval m (ρ ∘ f) := by
  simp [rename, eval]

theorem SigRel.lift {m : Model} {ρ : α → Comp m} {sigsTerm : Signatures Op Key α}
    {sigs : Op → Signature m Key} (h : SigRel m ρ sigsTerm sigs) (c : Comp m) :
    SigRel m (extend ρ c) sigsTerm.lift sigs := by
  intro op
  simpa [Signatures.lift] using h op

inductive Formula (Key Scope : Type) : Type → Type 1 where
  | top : Formula Key Scope α
  | bot : Formula Key Scope α
  | and : Formula Key Scope α → Formula Key Scope α → Formula Key Scope α
  | or : Formula Key Scope α → Formula Key Scope α → Formula Key Scope α
  | tyLe : TyTerm α → TyTerm α → Formula Key Scope α
  | rowLe : RowTerm α → RowTerm α → Formula Key Scope α
  | existsSlot : Formula Key Scope (Option α) → Formula Key Scope α
  | effectLe : RowExpr Key Scope α → RowExpr Key Scope α → Formula Key Scope α

def Formula.compLe (a b : CompTerm α) : Formula Key Scope α :=
  .and (.tyLe a.ty b.ty) (.rowLe a.row b.row)

def Formula.Holds (m : Model) (view : RowView m algebra) : {α : Type} → (α → Comp m) → Formula Key Scope α → Prop
  | _, _, .top => True
  | _, _, .bot => False
  | _, ρ, .and p q => p.Holds m view ρ ∧ q.Holds m view ρ
  | _, ρ, .or p q => p.Holds m view ρ ∨ q.Holds m view ρ
  | _, ρ, .tyLe a b => m.subTy (a.eval m ρ) (b.eval m ρ)
  | _, ρ, .rowLe a b => m.subRow (a.eval m ρ) (b.eval m ρ)
  | _, ρ, .existsSlot p => ∃ c, p.Holds m view (extend ρ c)
  | _, ρ, .effectLe a b => algebra.le (a.eval algebra (rowEnv view ρ))
      (b.eval algebra (rowEnv view ρ))

def Formula.rename (f : α → β) : Formula Key Scope α → Formula Key Scope β
  | .top => .top
  | .bot => .bot
  | .and p q => .and (p.rename f) (q.rename f)
  | .or p q => .or (p.rename f) (q.rename f)
  | .tyLe a b => .tyLe (a.rename f) (b.rename f)
  | .rowLe a b => .rowLe (a.rename f) (b.rename f)
  | .existsSlot p => .existsSlot (p.rename (Option.map f))
  | .effectLe a b => .effectLe (a.subst (fun x => .var (f x)))
      (b.subst (fun x => .var (f x)))

def liftSubst (f : α → CompTerm β) : Option α → CompTerm (Option β)
  | none => CompTerm.var none
  | some a => (f a).rename some

def Formula.subst (f : α → CompTerm β) : Formula Key Scope α → Formula Key Scope β
  | .top => .top
  | .bot => .bot
  | .and p q => .and (p.subst f) (q.subst f)
  | .or p q => .or (p.subst f) (q.subst f)
  | .tyLe a b => .tyLe (a.subst f) (b.subst f)
  | .rowLe a b => .rowLe (a.subst f) (b.subst f)
  | .existsSlot p => .existsSlot (p.subst (liftSubst f))
  | .effectLe a b => .effectLe (a.subst (fun x => fromCoreRow (f x).row))
      (b.subst (fun x => fromCoreRow (f x).row))

@[simp] theorem Formula.holds_compLe (m : Model) (view : RowView m algebra) (ρ : α → Comp m)
    (a b : CompTerm α) :
    (Formula.compLe a b).Holds m view ρ ↔ Comp.le m (a.eval m ρ) (b.eval m ρ) := Iff.rfl

@[simp] theorem Formula.holds_rename (m : Model) (view : RowView m algebra) (p : Formula Key Scope α)
    (f : α → β) (ρ : β → Comp m) :
    (p.rename f).Holds m view ρ ↔ p.Holds m view (ρ ∘ f) := by
  induction p generalizing β with
  | top => rfl
  | bot => rfl
  | and p q ihp ihq => simp [rename, Holds, ihp, ihq]
  | or p q ihp ihq => simp [rename, Holds, ihp, ihq]
  | tyLe a b => simp [rename, Holds]
  | rowLe a b => simp [rename, Holds]
  | effectLe a b =>
      simp only [rename, Holds, RowExpr.eval_subst, RowExpr.eval]
      rfl
  | existsSlot p ih =>
      simp only [rename, Holds, ih]
      apply exists_congr
      intro c
      have h : extend ρ c ∘ Option.map f = extend (ρ ∘ f) c := by
        funext x
        cases x <;> rfl
      rw [h]

@[simp] theorem Formula.holds_subst (m : Model) (view : RowView m algebra) (p : Formula Key Scope α)
    (f : α → CompTerm β) (ρ : β → Comp m) :
    (p.subst f).Holds m view ρ ↔ p.Holds m view (fun x => (f x).eval m ρ) := by
  induction p generalizing β with
  | top => rfl
  | bot => rfl
  | and p q ihp ihq => simp [subst, Holds, ihp, ihq]
  | or p q ihp ihq => simp [subst, Holds, ihp, ihq]
  | tyLe a b => simp [subst, Holds]
  | rowLe a b => simp [subst, Holds]
  | effectLe a b =>
      simp only [subst, Holds, RowExpr.eval_subst, eval_fromCoreRow]
      rfl
  | existsSlot p ih =>
      simp only [subst, Holds, ih]
      apply exists_congr
      intro c
      have h : (fun x => (liftSubst f x).eval m (extend ρ c)) =
          extend (fun x => (f x).eval m ρ) c := by
        funext x
        cases x <;> simp [liftSubst]
      rw [h]

abbrev Scheme (Key Scope α : Type) := Formula Key Scope (Option α)
abbrev SchemeEnv (Key Scope α : Type) := List (Scheme Key Scope α)

def Scheme.instantiate (s : Scheme Key Scope α) (c : CompTerm α) : Formula Key Scope α :=
  s.subst (fun | none => c | some a => CompTerm.var a)

def Scheme.mono (a : CompTerm α) : Scheme Key Scope α :=
  Formula.compLe (a.rename some) (CompTerm.var none)

/-- Rename captured slots, preserving the scheme's result slot. -/
def SchemeEnv.rename (Γ : SchemeEnv Key Scope α) (f : α → β) : SchemeEnv Key Scope β :=
  Γ.map (Formula.rename (Option.map f))

def SchemeEnv.lift (Γ : SchemeEnv Key Scope α) : SchemeEnv Key Scope (Option α) :=
  Γ.map (Formula.rename (Option.map some))

def Scheme.lookup (Γ : SchemeEnv Key Scope α) (n : Nat) (c : CompTerm α) : Formula Key Scope α :=
  match Γ[n]? with
  | none => .bot
  | some s => s.instantiate c

@[simp] theorem Scheme.holds_instantiate (m : Model) (view : RowView m algebra) (ρ : α → Comp m)
    (s : Scheme Key Scope α) (c : CompTerm α) :
    (s.instantiate c).Holds m view ρ ↔ s.Holds m view (extend ρ (c.eval m ρ)) := by
  simp only [instantiate, Formula.holds_subst]
  have h : (fun x => ((fun | none => c | some a => CompTerm.var a) x).eval m ρ) =
      extend ρ (c.eval m ρ) := by
    funext x
    cases x <;> rfl
  exact (congrArg (fun η => s.Holds m view η) h).to_iff

@[simp] theorem Scheme.holds_mono (m : Model) (view : RowView m algebra) (ρ : α → Comp m)
    (a : CompTerm α) (c : Comp m) :
    (Scheme.mono a).Holds m view (extend ρ c) ↔ Comp.le m (a.eval m ρ) c := by
  simp [mono]

inductive Expr (Op Key Scope : Type) where
  | var : Nat → Expr Op Key Scope
  | lit : Base → Expr Op Key Scope
  | lam : Expr Op Key Scope → Expr Op Key Scope
  | app : Expr Op Key Scope → Expr Op Key Scope → Expr Op Key Scope
  | letE : Expr Op Key Scope → Expr Op Key Scope → Expr Op Key Scope
  | branch : Expr Op Key Scope → Expr Op Key Scope → Expr Op Key Scope → Expr Op Key Scope
  | pair : Expr Op Key Scope → Expr Op Key Scope → Expr Op Key Scope
  | fst : Expr Op Key Scope → Expr Op Key Scope
  | snd : Expr Op Key Scope → Expr Op Key Scope
  | emptyRecord : Expr Op Key Scope
  | record : Nat → Expr Op Key Scope → Expr Op Key Scope → Expr Op Key Scope
  | field : Nat → Expr Op Key Scope → Expr Op Key Scope
  | variant : Nat → Expr Op Key Scope → Expr Op Key Scope
  | request : Op → Expr Op Key Scope → Expr Op Key Scope
  | boundary : Boundary Key Scope → Expr Op Key Scope → Expr Op Key Scope
  | handler : Op → Expr Op Key Scope → Expr Op Key Scope → Expr Op Key Scope → Expr Op Key Scope

/-- The core's nonexpansive syntax. A variable is generalizable only if its
scheme also permits a pure typing; a computation argument is not made pure. -/
def Expr.isValue : Expr Op Key Scope → Bool
  | .var _ | .lit _ | .lam _ | .emptyRecord => true
  | .pair a b | .record _ a b => a.isValue && b.isValue
  | .variant _ a => a.isValue
  | _ => false

/-- A polymorphic binding remembers the lexical environment. It does not
capture the caller's future instantiations or generalize their variables. -/
inductive Binding (m : Model) (Op Key Scope : Type) where
  | mono : Comp m → Binding m Op Key Scope
  | poly : Expr Op Key Scope → List (Binding m Op Key Scope) → Binding m Op Key Scope
  /-- An independently prescribed signature quantifies value types only.
  Inferred row assignments and the lexical environment are captured by
  `instantiate`; no fresh row assignment is supplied at a call. -/
  | signature (n : Nat) (instantiate : (Fin n → m.Ty) → Comp m) : Binding m Op Key Scope

mutual
  inductive Typing (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) : List (Binding m Op Key Scope) → Expr Op Key Scope → Comp m → Prop where
    | var : Γ[n]? = some b → BindingTyping m view sigs b c → Typing m view sigs Γ (.var n) c
    | lit : Comp.le m (Comp.pure m (m.base b)) c → Typing m view sigs Γ (.lit b) c
    | lam : Typing m view sigs (.mono a :: Γ) body b →
        Comp.le m (Comp.pure m (Comp.arrow m a b)) c → Typing m view sigs Γ (.lam body) c
    | app : Typing m view sigs Γ f (Comp.arrow m a b, ef) → Typing m view sigs Γ x a →
        Comp.le m (b.1, m.join ef b.2) c → Typing m view sigs Γ (.app f x) c
    | letValue : v.isValue = true → Typing m view sigs Γ v (Comp.pure m a) →
        Typing m view sigs (.poly v Γ :: Γ) body c → Typing m view sigs Γ (.letE v body) c
    | letComputed : Typing m view sigs Γ v a →
        Typing m view sigs (.mono (Comp.pure m a.1) :: Γ) body b →
        Comp.le m (b.1, m.join a.2 b.2) c → Typing m view sigs Γ (.letE v body) c
    | branch : Typing m view sigs Γ condition (m.base .bool, eg) →
        Typing m view sigs Γ yes a → Typing m view sigs Γ no b →
        Comp.le m (m.union a.1 b.1, m.join eg (m.join a.2 b.2)) c →
        Typing m view sigs Γ (.branch condition yes no) c
    | pair : Typing m view sigs Γ x a → Typing m view sigs Γ y b →
        Comp.le m (m.pair a.1 b.1, m.join a.2 b.2) c → Typing m view sigs Γ (.pair x y) c
    | fst : Typing m view sigs Γ x (m.pair a b, er) →
        Comp.le m (a, er) c → Typing m view sigs Γ (.fst x) c
    | snd : Typing m view sigs Γ x (m.pair a b, er) →
        Comp.le m (b, er) c → Typing m view sigs Γ (.snd x) c
    | emptyRecord : Comp.le m (Comp.pure m m.emptyRecord) c →
        Typing m view sigs Γ .emptyRecord c
    | record : Typing m view sigs Γ x a → Typing m view sigs Γ rest b → m.subTy b.1 m.emptyRecord →
        Comp.le m (m.record l a.1 b.1, m.join a.2 b.2) c →
        Typing m view sigs Γ (.record l x rest) c
    | field : Typing m view sigs Γ x (m.record l a m.emptyRecord, er) →
        Comp.le m (a, er) c → Typing m view sigs Γ (.field l x) c
    | variant : Typing m view sigs Γ x a →
        Comp.le m (m.variant l a.1, a.2) c → Typing m view sigs Γ (.variant l x) c

    | request : Typing m view sigs Γ payload ((sigs op).input, er) →
        m.subTy (sigs op).output c.1 →
        algebra.le (algebra.join (view.decode er)
          (algebra.join (algebra.head (sigs op).key) (keysRow algebra (sigs op).extra)))
          (view.decode c.2) → Typing m view sigs Γ (.request op payload) c
    | boundary : Typing m view sigs Γ body input → m.subTy input.1 c.1 →
        algebra.le (boundary.row algebra (view.decode input.2)) (view.decode c.2) →
        Typing m view sigs Γ (.boundary boundary body) c
    | handler : Typing m view sigs Γ action input →
        Typing m view sigs (.mono (Comp.pure m input.1) :: Γ) onReturn returned →
        Typing m view sigs
          (.mono (Comp.pure m (sigs op).input) ::
           .mono (Comp.pure m (Comp.arrow m (Comp.pure m (sigs op).output) input)) :: Γ)
          onOperation operated →
        m.subTy (m.union returned.1 operated.1) c.1 →
        algebra.le (algebra.join (algebra.residual [(sigs op).key] (view.decode input.2))
          (algebra.join (view.decode returned.2) (view.decode operated.2))) (view.decode c.2) →
        Typing m view sigs Γ (.handler op action onReturn onOperation) c

  inductive BindingTyping (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) : Binding m Op Key Scope → Comp m → Prop where
    | mono : Comp.le m a c → BindingTyping m view sigs (.mono a) c
    | poly : Typing m view sigs Γ v (Comp.pure m c.1) → m.subRow m.empty c.2 →
        BindingTyping m view sigs (.poly v Γ) c
    | signature {n : Nat} {instantiate : (Fin n → m.Ty) → Comp m} {ι : Fin n → m.Ty} :
        Comp.le m (instantiate ι) c →
        BindingTyping m view sigs (.signature n instantiate) c
end

def env₂ (Γ : SchemeEnv Key Scope α) := Γ.lift.lift
def env₃ (Γ : SchemeEnv Key Scope α) := Γ.lift.lift.lift

/-- Constraint generation is structurally recursive on the input expression.
Stored schemes contain formulas, so instantiating them does not recurse on a
previously seen expression. No fuel, oracle, or satisfiability assumption occurs. -/
def generate (sigsTerm : Signatures Op Key α) (Γ : SchemeEnv Key Scope α) : Expr Op Key Scope → CompTerm α → Formula Key Scope α
  | .var n, out => Scheme.lookup Γ n out
  | .lit b, out => Formula.compLe (CompTerm.pure (.base b)) out
  | .lam body, out =>
      .existsSlot (.existsSlot (
        .and (generate sigsTerm.lift.lift (Scheme.mono fresh₀ :: env₂ Γ) body fresh₁)
          (Formula.compLe (CompTerm.pure (CompTerm.arrow fresh₀ fresh₁)) (lift₂ out))))
  | .app f x, out =>
      .existsSlot (.existsSlot (.existsSlot (
        .and (generate sigsTerm.lift.lift.lift (env₃ Γ) f ⟨CompTerm.arrow fresh₀₃ fresh₁₃, fresh₂₃.row⟩)
          (.and (generate sigsTerm.lift.lift.lift (env₃ Γ) x fresh₀₃)
            (Formula.compLe ⟨fresh₁₃.ty, .join fresh₂₃.row fresh₁₃.row⟩ (lift₃ out))))))
  | .letE v body, out =>
      let monomorphic := .existsSlot (.existsSlot (
        .and (generate sigsTerm.lift.lift (env₂ Γ) v fresh₀)
          (.and (generate sigsTerm.lift.lift (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ Γ) body fresh₁)
            (Formula.compLe ⟨fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out)))))
      if v.isValue then
        let scheme : Scheme Key Scope α :=
          .and (generate sigsTerm.lift Γ.lift v (CompTerm.pure (.var none)))
            (.rowLe .empty (.var none))
        .or (.and (.existsSlot (generate sigsTerm.lift Γ.lift v (CompTerm.pure (.var none))))
          (generate sigsTerm (scheme :: Γ) body out)) monomorphic
      else
        monomorphic
  | .branch g y n, out =>
      .existsSlot (.existsSlot (.existsSlot (
        .and (generate sigsTerm.lift.lift.lift (env₃ Γ) g ⟨.base .bool, fresh₀₃.row⟩)
          (.and (generate sigsTerm.lift.lift.lift (env₃ Γ) y fresh₁₃)
            (.and (generate sigsTerm.lift.lift.lift (env₃ Γ) n fresh₂₃)
              (Formula.compLe ⟨.union fresh₁₃.ty fresh₂₃.ty,
                .join fresh₀₃.row (.join fresh₁₃.row fresh₂₃.row)⟩ (lift₃ out)))))))
  | .pair x y, out =>
      .existsSlot (.existsSlot (
        .and (generate sigsTerm.lift.lift (env₂ Γ) x fresh₀)
          (.and (generate sigsTerm.lift.lift (env₂ Γ) y fresh₁)
            (Formula.compLe ⟨.pair fresh₀.ty fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out)))))
  | .fst x, out =>
      .existsSlot (.existsSlot (
        .and (generate sigsTerm.lift.lift (env₂ Γ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩)
          (Formula.compLe ⟨fresh₀.ty, fresh₀.row⟩ (lift₂ out))))
  | .snd x, out =>
      .existsSlot (.existsSlot (
        .and (generate sigsTerm.lift.lift (env₂ Γ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩)
          (Formula.compLe ⟨fresh₁.ty, fresh₀.row⟩ (lift₂ out))))
  | .emptyRecord, out => Formula.compLe (CompTerm.pure .emptyRecord) out
  | .record l x rest, out =>
      .existsSlot (.existsSlot (
        .and (generate sigsTerm.lift.lift (env₂ Γ) x fresh₀)
          (.and (generate sigsTerm.lift.lift (env₂ Γ) rest fresh₁)
            (.and (.tyLe fresh₁.ty .emptyRecord)
              (Formula.compLe ⟨.record l fresh₀.ty fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out))))))
  | .field l x, out =>
      .existsSlot (
        .and (generate sigsTerm.lift Γ.lift x ⟨.record l (.var none) .emptyRecord, .var none⟩)
          (Formula.compLe (CompTerm.var none) (out.rename some)))
  | .variant l x, out =>
      .existsSlot (
        .and (generate sigsTerm.lift Γ.lift x (CompTerm.var none))
          (Formula.compLe ⟨.variant l (.var none), .var none⟩ (out.rename some)))
  | .request op payload, out =>
      .existsSlot (
        .and (generate sigsTerm.lift Γ.lift payload ⟨(sigsTerm op).input.rename some, .var none⟩)
          (.and (.tyLe ((sigsTerm op).output.rename some) (out.ty.rename some))
            (.effectLe (.union (.var none) (.union (.head (sigsTerm op).key) (heads (sigsTerm op).extra)))
              (fromCoreRow (out.row.rename some)))))
  | .boundary boundary body, out =>
      .existsSlot (
        .and (generate sigsTerm.lift Γ.lift body (CompTerm.var none))
          (.and (.tyLe (.var none) (out.ty.rename some))
            (.effectLe (boundary.term (.var none)) (fromCoreRow (out.row.rename some)))))
  | .handler op action onReturn onOperation, out =>
      .existsSlot (.existsSlot (.existsSlot (
        .and (generate sigsTerm.lift.lift.lift (env₃ Γ) action fresh₀₃)
          (.and (generate sigsTerm.lift.lift.lift
              (Scheme.mono (CompTerm.pure fresh₀₃.ty) :: env₃ Γ) onReturn fresh₁₃)
            (.and (generate sigsTerm.lift.lift.lift
                (Scheme.mono (CompTerm.pure ((sigsTerm.lift.lift.lift op).input)) ::
                 Scheme.mono (CompTerm.pure (CompTerm.arrow
                   (CompTerm.pure ((sigsTerm.lift.lift.lift op).output)) fresh₀₃)) :: env₃ Γ)
                onOperation fresh₂₃)
              (.and (.tyLe (.union fresh₁₃.ty fresh₂₃.ty) (lift₃ out).ty)
                (.effectLe (.union (.residual [(sigsTerm op).key] (.var (some (some none))))
                    (.union (.var (some none)) (.var none)))
                  (fromCoreRow (lift₃ out).row))))))))

def SchemeLookup (m : Model) (view : RowView m algebra) (ρ : α → Comp m) (Γ : SchemeEnv Key Scope α)
    (n : Nat) (c : Comp m) : Prop :=
  match Γ[n]? with
  | none => False
  | some s => s.Holds m view (extend ρ c)

def BindingLookup (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope)) (n : Nat) (c : Comp m) : Prop :=
  ∃ b, Γ[n]? = some b ∧ BindingTyping m view sigs b c

/-- A symbolic context represents exactly the same instances as its independent
declarative context. This relation is preserved by fresh allocation. -/
def EnvRel (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (ρ : α → Comp m) (sΓ : SchemeEnv Key Scope α)
    (Γ : List (Binding m Op Key Scope)) : Prop :=
  ∀ n c, SchemeLookup m view ρ sΓ n c ↔ BindingLookup m view sigs Γ n c

@[simp] theorem Scheme.holds_lookup (m : Model) (view : RowView m algebra) (ρ : α → Comp m)
    (Γ : SchemeEnv Key Scope α) (n : Nat) (c : CompTerm α) :
    (Scheme.lookup Γ n c).Holds m view ρ ↔ SchemeLookup m view ρ Γ n (c.eval m ρ) := by
  unfold lookup SchemeLookup
  split <;> simp [Formula.Holds]

@[simp] theorem BindingTyping.mono_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (a c : Comp m) :
    BindingTyping m view sigs (.mono a) c ↔ Comp.le m a c := by
  constructor
  · intro h; cases h with | mono h => exact h
  · exact BindingTyping.mono

@[simp] theorem BindingTyping.poly_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope))
    (v : Expr Op Key Scope) (c : Comp m) :
    BindingTyping m view sigs (.poly v Γ) c ↔
      Typing m view sigs Γ v (Comp.pure m c.1) ∧ m.subRow m.empty c.2 := by
  constructor
  · intro h; cases h with | poly hv he => exact ⟨hv, he⟩
  · rintro ⟨hv, he⟩; exact BindingTyping.poly hv he

@[simp] theorem BindingTyping.signature_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (n : Nat)
    (instantiate : (Fin n → m.Ty) → Comp m) (c : Comp m) :
    BindingTyping m view sigs (.signature n instantiate) c ↔ ∃ ι, Comp.le m (instantiate ι) c := by
  constructor
  · intro h; cases h with | signature hc => exact ⟨_, hc⟩
  · rintro ⟨ι, hc⟩; exact BindingTyping.signature hc

theorem EnvRel.nil (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (ρ : α → Comp m) : EnvRel m view sigs ρ [] [] := by
  intro n c
  simp [SchemeLookup, BindingLookup]

theorem EnvRel.cons {m : Model} {view : RowView m algebra} {sigs : Op → Signature m Key} {ρ : α → Comp m} {sΓ : SchemeEnv Key Scope α}
    {Γ : List (Binding m Op Key Scope)} {s : Scheme Key Scope α} {b : Binding m Op Key Scope} (h : EnvRel m view sigs ρ sΓ Γ)
    (head : ∀ c, s.Holds m view (extend ρ c) ↔ BindingTyping m view sigs b c) :
    EnvRel m view sigs ρ (s :: sΓ) (b :: Γ) := by
  intro n c
  cases n with
  | zero => simpa [SchemeLookup, BindingLookup] using head c
  | succ n => simpa [SchemeLookup, BindingLookup] using h n c

theorem EnvRel.mono {m : Model} {view : RowView m algebra} {sigs : Op → Signature m Key} {ρ : α → Comp m} {sΓ : SchemeEnv Key Scope α}
    {Γ : List (Binding m Op Key Scope)} (h : EnvRel m view sigs ρ sΓ Γ) (a : CompTerm α) :
    EnvRel m view sigs ρ (Scheme.mono a :: sΓ) (.mono (a.eval m ρ) :: Γ) := by
  apply h.cons
  intro c
  simp

theorem EnvRel.rename {m : Model} {view : RowView m algebra} {sigs : Op → Signature m Key} {ρ : α → Comp m} {sΓ : SchemeEnv Key Scope α}
    {Γ : List (Binding m Op Key Scope)} (h : EnvRel m view sigs ρ sΓ Γ) (f : α → β) (η : β → Comp m)
    (he : η ∘ f = ρ) : EnvRel m view sigs η (sΓ.rename f) Γ := by
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

theorem EnvRel.lift {m : Model} {view : RowView m algebra} {sigs : Op → Signature m Key} {ρ : α → Comp m} {sΓ : SchemeEnv Key Scope α}
    {Γ : List (Binding m Op Key Scope)} (h : EnvRel m view sigs ρ sΓ Γ) (a : Comp m) :
    EnvRel m view sigs (extend ρ a) sΓ.lift Γ := by
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

@[simp] theorem Typing.var_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope)) (n : Nat) (c : Comp m) :
    Typing m view sigs Γ (.var n) c ↔ BindingLookup m view sigs Γ n c := by
  constructor
  · intro h
    cases h with | var hget hb => exact ⟨_, hget, hb⟩
  · rintro ⟨b, hget, hb⟩
    exact Typing.var hget hb

@[simp] theorem Typing.lit_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope)) (b : Base) (c : Comp m) :
    Typing m view sigs Γ (.lit b) c ↔ Comp.le m (Comp.pure m (m.base b)) c := by
  constructor
  · intro h; cases h with | lit h => exact h
  · exact Typing.lit

@[simp] theorem Typing.lam_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope)) (body : Expr Op Key Scope) (c : Comp m) :
    Typing m view sigs Γ (.lam body) c ↔ ∃ a b,
      Typing m view sigs (.mono a :: Γ) body b ∧
      Comp.le m (Comp.pure m (Comp.arrow m a b)) c := by
  constructor
  · intro h; cases h with | lam hb hc => exact ⟨_, _, hb, hc⟩
  · rintro ⟨a, b, hb, hc⟩; exact Typing.lam hb hc

@[simp] theorem Typing.app_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope)) (f x : Expr Op Key Scope) (c : Comp m) :
    Typing m view sigs Γ (.app f x) c ↔ ∃ a b ef,
      Typing m view sigs Γ f (Comp.arrow m a b, ef) ∧ Typing m view sigs Γ x a ∧
      Comp.le m (b.1, m.join ef b.2) c := by
  constructor
  · intro h; cases h with | app hf hx hc => exact ⟨_, _, _, hf, hx, hc⟩
  · rintro ⟨a, b, ef, hf, hx, hc⟩; exact Typing.app hf hx hc

theorem Typing.letValue_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope)) (v body : Expr Op Key Scope) (c : Comp m)
    (hv : v.isValue = true) :
    Typing m view sigs Γ (.letE v body) c ↔
      ((∃ a, Typing m view sigs Γ v (Comp.pure m a)) ∧ Typing m view sigs (.poly v Γ :: Γ) body c) ∨
      ∃ a b, Typing m view sigs Γ v a ∧ Typing m view sigs (.mono (Comp.pure m a.1) :: Γ) body b ∧
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

theorem Typing.letComputed_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope)) (v body : Expr Op Key Scope) (c : Comp m)
    (hv : v.isValue = false) :
    Typing m view sigs Γ (.letE v body) c ↔ ∃ a b,
      Typing m view sigs Γ v a ∧ Typing m view sigs (.mono (Comp.pure m a.1) :: Γ) body b ∧
      Comp.le m (b.1, m.join a.2 b.2) c := by
  constructor
  · intro h
    cases h with
    | letValue hn _ _ => simp [hv] at hn
    | letComputed ha hb hc => exact ⟨_, _, ha, hb, hc⟩
  · rintro ⟨a, b, ha, hb, hc⟩
    exact Typing.letComputed ha hb hc

@[simp] theorem Typing.branch_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope)) (g y n : Expr Op Key Scope) (c : Comp m) :
    Typing m view sigs Γ (.branch g y n) c ↔ ∃ eg a b,
      Typing m view sigs Γ g (m.base .bool, eg) ∧ Typing m view sigs Γ y a ∧ Typing m view sigs Γ n b ∧
      Comp.le m (m.union a.1 b.1, m.join eg (m.join a.2 b.2)) c := by
  constructor
  · intro h; cases h with | branch hg hy hn hc => exact ⟨_, _, _, hg, hy, hn, hc⟩
  · rintro ⟨eg, a, b, hg, hy, hn, hc⟩; exact Typing.branch hg hy hn hc

@[simp] theorem Typing.pair_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope)) (x y : Expr Op Key Scope) (c : Comp m) :
    Typing m view sigs Γ (.pair x y) c ↔ ∃ a b,
      Typing m view sigs Γ x a ∧ Typing m view sigs Γ y b ∧
      Comp.le m (m.pair a.1 b.1, m.join a.2 b.2) c := by
  constructor
  · intro h; cases h with | pair hx hy hc => exact ⟨_, _, hx, hy, hc⟩
  · rintro ⟨a, b, hx, hy, hc⟩; exact Typing.pair hx hy hc

@[simp] theorem Typing.fst_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope)) (x : Expr Op Key Scope) (c : Comp m) :
    Typing m view sigs Γ (.fst x) c ↔ ∃ a b er,
      Typing m view sigs Γ x (m.pair a b, er) ∧ Comp.le m (a, er) c := by
  constructor
  · intro h; cases h with | fst hx hc => exact ⟨_, _, _, hx, hc⟩
  · rintro ⟨a, b, er, hx, hc⟩; exact Typing.fst hx hc

@[simp] theorem Typing.snd_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope)) (x : Expr Op Key Scope) (c : Comp m) :
    Typing m view sigs Γ (.snd x) c ↔ ∃ a b er,
      Typing m view sigs Γ x (m.pair a b, er) ∧ Comp.le m (b, er) c := by
  constructor
  · intro h; cases h with | snd hx hc => exact ⟨_, _, _, hx, hc⟩
  · rintro ⟨a, b, er, hx, hc⟩; exact Typing.snd hx hc

@[simp] theorem Typing.emptyRecord_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope)) (c : Comp m) :
    Typing m view sigs Γ .emptyRecord c ↔ Comp.le m (Comp.pure m m.emptyRecord) c := by
  constructor
  · intro h; cases h with | emptyRecord h => exact h
  · exact Typing.emptyRecord

@[simp] theorem Typing.record_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope))
    (l : Nat) (x r : Expr Op Key Scope) (c : Comp m) :
    Typing m view sigs Γ (.record l x r) c ↔ ∃ a b,
      Typing m view sigs Γ x a ∧ Typing m view sigs Γ r b ∧ m.subTy b.1 m.emptyRecord ∧
      Comp.le m (m.record l a.1 b.1, m.join a.2 b.2) c := by
  constructor
  · intro h; cases h with | record hx hr hs hc => exact ⟨_, _, hx, hr, hs, hc⟩
  · rintro ⟨a, b, hx, hr, hs, hc⟩; exact Typing.record hx hr hs hc

@[simp] theorem Typing.field_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope))
    (l : Nat) (x : Expr Op Key Scope) (c : Comp m) :
    Typing m view sigs Γ (.field l x) c ↔ ∃ a er,
      Typing m view sigs Γ x (m.record l a m.emptyRecord, er) ∧ Comp.le m (a, er) c := by
  constructor
  · intro h; cases h with | field hx hc => exact ⟨_, _, hx, hc⟩
  · rintro ⟨a, er, hx, hc⟩; exact Typing.field hx hc

@[simp] theorem Typing.variant_iff (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope))
    (l : Nat) (x : Expr Op Key Scope) (c : Comp m) :
    Typing m view sigs Γ (.variant l x) c ↔ ∃ a,
      Typing m view sigs Γ x a ∧ Comp.le m (m.variant l a.1, a.2) c := by
  constructor
  · intro h; cases h with | variant hx hc => exact ⟨_, hx, hc⟩
  · rintro ⟨a, hx, hc⟩; exact Typing.variant hx hc


@[simp] theorem Typing.request_iff (m : Model) (view : RowView m algebra)
    (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope))
    (op : Op) (payload : Expr Op Key Scope) (c : Comp m) :
    Typing m view sigs Γ (.request op payload) c ↔ ∃ er,
      Typing m view sigs Γ payload ((sigs op).input, er) ∧ m.subTy (sigs op).output c.1 ∧
      algebra.le (algebra.join (view.decode er)
        (algebra.join (algebra.head (sigs op).key) (keysRow algebra (sigs op).extra)))
        (view.decode c.2) := by
  constructor
  · intro h; cases h with | request hp ht he => exact ⟨_, hp, ht, he⟩
  · rintro ⟨er, hp, ht, he⟩; exact .request hp ht he

@[simp] theorem Typing.boundary_iff (m : Model) (view : RowView m algebra)
    (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope))
    (boundary : Boundary Key Scope) (body : Expr Op Key Scope) (c : Comp m) :
    Typing m view sigs Γ (.boundary boundary body) c ↔ ∃ input,
      Typing m view sigs Γ body input ∧ m.subTy input.1 c.1 ∧
      algebra.le (boundary.row algebra (view.decode input.2)) (view.decode c.2) := by
  constructor
  · intro h; cases h with | boundary hb ht he => exact ⟨_, hb, ht, he⟩
  · rintro ⟨input, hb, ht, he⟩; exact .boundary hb ht he

@[simp] theorem Typing.handler_iff (m : Model) (view : RowView m algebra)
    (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope))
    (op : Op) (action onReturn onOperation : Expr Op Key Scope) (c : Comp m) :
    Typing m view sigs Γ (.handler op action onReturn onOperation) c ↔
      ∃ input returned operated, Typing m view sigs Γ action input ∧
        Typing m view sigs (.mono (Comp.pure m input.1) :: Γ) onReturn returned ∧
        Typing m view sigs
          (.mono (Comp.pure m (sigs op).input) ::
           .mono (Comp.pure m (Comp.arrow m (Comp.pure m (sigs op).output) input)) :: Γ)
          onOperation operated ∧
        m.subTy (m.union returned.1 operated.1) c.1 ∧
        algebra.le (algebra.join (algebra.residual [(sigs op).key] (view.decode input.2))
          (algebra.join (view.decode returned.2) (view.decode operated.2))) (view.decode c.2) := by
  constructor
  · intro h; cases h with | handler hi hr ho ht he => exact ⟨_, _, _, hi, hr, ho, ht, he⟩
  · rintro ⟨input, returned, operated, hi, hr, ho, ht, he⟩; exact .handler hi hr ho ht he

/-- Exactness of the generated constraint scheme. Both directions quantify
over all semantic types and rows; neither assumes that a solver succeeds.
The environment hypothesis only relates input schemes to input bindings. -/
theorem generate_models_iff_typing (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (e : Expr Op Key Scope)
    (sigsTerm : Signatures Op Key α) (sΓ : SchemeEnv Key Scope α) (Γ : List (Binding m Op Key Scope)) (ρ : α → Comp m)
    (out : CompTerm α) (henv : EnvRel m view sigs ρ sΓ Γ) (hsig : SigRel m ρ sigsTerm sigs) :
    (generate sigsTerm sΓ e out).Holds m view ρ ↔ Typing m view sigs Γ e (out.eval m ρ) := by
  induction e generalizing α sigsTerm sΓ Γ ρ out with
  | var n => simpa [generate] using henv n (out.eval m ρ)
  | lit b => simp [generate, CompTerm.eval, CompTerm.pure, TyTerm.eval, RowTerm.eval, Comp.pure]
  | lam body ih =>
      have hb (a b : Comp m) :
          (generate sigsTerm.lift.lift (Scheme.mono fresh₀ :: env₂ sΓ) body fresh₁).Holds m view (extend (extend ρ a) b) ↔
          Typing m view sigs (.mono a :: Γ) body b := by
        simpa only [fresh₀, fresh₁, env₂, CompTerm.eval_var, extend_some, extend_none]
          using ih (sigsTerm := sigsTerm.lift.lift) _ _ _ fresh₁ (((henv.lift a).lift b).mono fresh₀) ((hsig.lift a).lift b)
      simp only [generate, Formula.Holds, Typing.lam_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      rw [hb]
      simp [Formula.compLe, Formula.Holds, Comp.le, Comp.arrow, Comp.pure,
        CompTerm.eval, CompTerm.arrow, CompTerm.pure, fresh₀, fresh₁, lift₂,
        CompTerm.rename, TyTerm.eval, RowTerm.eval, CompTerm.var, Function.comp_def]
  | app f x ihf ihx =>
      have hf (a b d : Comp m) :
          (generate sigsTerm.lift.lift.lift (env₃ sΓ) f ⟨CompTerm.arrow fresh₀₃ fresh₁₃, fresh₂₃.row⟩).Holds m view
            (extend (extend (extend ρ a) b) d) ↔ Typing m view sigs Γ f (Comp.arrow m a b, d.2) := by
        simpa only [env₃, fresh₀₃, fresh₁₃, fresh₂₃, CompTerm.eval, CompTerm.arrow,
          CompTerm.var, TyTerm.eval, RowTerm.eval, extend_none, extend_some, Comp.arrow]
          using ihf (sigsTerm := sigsTerm.lift.lift.lift) _ _ _ ⟨CompTerm.arrow fresh₀₃ fresh₁₃, fresh₂₃.row⟩ (((henv.lift a).lift b).lift d) (((hsig.lift a).lift b).lift d)
      have hx (a b d : Comp m) :
          (generate sigsTerm.lift.lift.lift (env₃ sΓ) x fresh₀₃).Holds m view (extend (extend (extend ρ a) b) d) ↔
          Typing m view sigs Γ x a := by
        simpa only [env₃, fresh₀₃, CompTerm.eval_var, extend_some, extend_none]
          using ihx (sigsTerm := sigsTerm.lift.lift.lift) _ _ _ fresh₀₃ (((henv.lift a).lift b).lift d) (((hsig.lift a).lift b).lift d)
      simp only [generate, Formula.Holds, Typing.app_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      simp only [hf, hx]
      simp only [Formula.compLe, Formula.Holds]
      simp only [lift₃, CompTerm.rename, CompTerm.eval, CompTerm.var, fresh₁₃,
        fresh₂₃, TyTerm.eval, RowTerm.eval, TyTerm.eval_rename, RowTerm.eval_rename,
        extend_none, extend_some, Function.comp_def]
      exact exists_comp_row m (fun r => Typing m view sigs Γ f (Comp.arrow m a b, r) ∧
        Typing m view sigs Γ x a ∧ Comp.le m (b.1, m.join r b.2) (out.eval m ρ))
  | letE v body ihv ihb =>
      let mono : Formula Key Scope α := .existsSlot (.existsSlot (
        .and (generate sigsTerm.lift.lift (env₂ sΓ) v fresh₀)
          (.and (generate sigsTerm.lift.lift (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ sΓ) body fresh₁)
            (Formula.compLe ⟨fresh₁.ty, .join fresh₀.row fresh₁.row⟩ (lift₂ out)))))
      have hmono : mono.Holds m view ρ ↔ ∃ a b,
          Typing m view sigs Γ v a ∧ Typing m view sigs (.mono (Comp.pure m a.1) :: Γ) body b ∧
          Comp.le m (b.1, m.join a.2 b.2) (out.eval m ρ) := by
        have ha (a b : Comp m) :
            (generate sigsTerm.lift.lift (env₂ sΓ) v fresh₀).Holds m view (extend (extend ρ a) b) ↔ Typing m view sigs Γ v a := by
          simpa only [env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
            using ihv (sigsTerm := sigsTerm.lift.lift) _ _ _ fresh₀ ((henv.lift a).lift b) ((hsig.lift a).lift b)
        have hb (a b : Comp m) :
            (generate sigsTerm.lift.lift (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ sΓ) body fresh₁).Holds m view
              (extend (extend ρ a) b) ↔ Typing m view sigs (.mono (Comp.pure m a.1) :: Γ) body b := by
          simpa [env₂, fresh₀, fresh₁, CompTerm.pure, Comp.pure,
            CompTerm.var, CompTerm.eval, TyTerm.eval, RowTerm.eval]
            using ihb (sigsTerm := sigsTerm.lift.lift) _ _ _ fresh₁ (((henv.lift a).lift b).mono (CompTerm.pure fresh₀.ty)) ((hsig.lift a).lift b)
        simp only [mono, Formula.Holds]
        apply exists_congr; intro a
        apply exists_congr; intro b
        rw [ha, hb]
        simp [Formula.compLe, Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
          CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
      cases hv : v.isValue with
      | true =>
          let scheme : Scheme Key Scope α := .and
            (generate sigsTerm.lift sΓ.lift v (CompTerm.pure (.var none))) (.rowLe .empty (.var none))
          have hvalue (c : Comp m) :
              (generate sigsTerm.lift sΓ.lift v (CompTerm.pure (.var none))).Holds m view (extend ρ c) ↔
              Typing m view sigs Γ v (Comp.pure m c.1) := by
            simpa only [CompTerm.eval_pure, TyTerm.eval, extend_none]
              using ihv (sigsTerm := sigsTerm.lift) _ _ _ (CompTerm.pure (.var none)) (henv.lift c) (hsig.lift c)
          have hscheme : ∀ c, scheme.Holds m view (extend ρ c) ↔ BindingTyping m view sigs (.poly v Γ) c := by
            intro c
            simp only [scheme, Formula.Holds, hvalue, RowTerm.eval, extend_none,
              BindingTyping.poly_iff]
          have hbody := ihb (sigsTerm := sigsTerm) (scheme :: sΓ) (.poly v Γ :: Γ) ρ out (henv.cons hscheme) hsig
          simp only [generate, hv]
          change (((∃ c, (generate sigsTerm.lift sΓ.lift v (CompTerm.pure (.var none))).Holds m view (extend ρ c)) ∧
            (generate sigsTerm (scheme :: sΓ) body out).Holds m view ρ) ∨ mono.Holds m view ρ) ↔ _
          rw [Typing.letValue_iff m view sigs Γ v body (out.eval m ρ) hv]
          apply or_congr
          · simp only [hvalue]
            rw [hbody]
            exact and_congr (exists_comp_ty m (fun a => Typing m view sigs Γ v (Comp.pure m a))) Iff.rfl
          · exact hmono
      | false =>
          simp only [generate, hv]
          change mono.Holds m view ρ ↔ _
          exact hmono.trans (Typing.letComputed_iff m view sigs Γ v body (out.eval m ρ) hv).symm
  | branch g y n ihg ihy ihn =>
      have hg (a b d : Comp m) :
          (generate sigsTerm.lift.lift.lift (env₃ sΓ) g ⟨.base .bool, fresh₀₃.row⟩).Holds m view
            (extend (extend (extend ρ a) b) d) ↔ Typing m view sigs Γ g (m.base .bool, a.2) := by
        simpa only [env₃, fresh₀₃, CompTerm.eval, CompTerm.var, TyTerm.eval, RowTerm.eval,
          extend_none, extend_some] using ihg (sigsTerm := sigsTerm.lift.lift.lift) _ _ _ ⟨.base .bool, fresh₀₃.row⟩ (((henv.lift a).lift b).lift d) (((hsig.lift a).lift b).lift d)
      have hy (a b d : Comp m) :
          (generate sigsTerm.lift.lift.lift (env₃ sΓ) y fresh₁₃).Holds m view (extend (extend (extend ρ a) b) d) ↔
          Typing m view sigs Γ y b := by
        simpa only [env₃, fresh₁₃, CompTerm.eval_var, extend_none, extend_some]
          using ihy (sigsTerm := sigsTerm.lift.lift.lift) _ _ _ fresh₁₃ (((henv.lift a).lift b).lift d) (((hsig.lift a).lift b).lift d)
      have hn (a b d : Comp m) :
          (generate sigsTerm.lift.lift.lift (env₃ sΓ) n fresh₂₃).Holds m view (extend (extend (extend ρ a) b) d) ↔
          Typing m view sigs Γ n d := by
        simpa only [env₃, fresh₂₃, CompTerm.eval_var, extend_none]
          using ihn (sigsTerm := sigsTerm.lift.lift.lift) _ _ _ fresh₂₃ (((henv.lift a).lift b).lift d) (((hsig.lift a).lift b).lift d)
      simp only [generate, Formula.Holds, Typing.branch_iff]
      simp only [hg, hy, hn]
      simp only [Formula.compLe, Formula.Holds]
      simp only [lift₃, CompTerm.rename, CompTerm.eval, CompTerm.var, fresh₀₃, fresh₁₃,
        fresh₂₃, TyTerm.eval, RowTerm.eval, TyTerm.eval_rename, RowTerm.eval_rename,
        extend_none, extend_some, Function.comp_def]
      exact exists_comp_row m (fun r => ∃ a b, Typing m view sigs Γ g (m.base .bool, r) ∧
        Typing m view sigs Γ y a ∧ Typing m view sigs Γ n b ∧
        Comp.le m (m.union a.1 b.1, m.join r (m.join a.2 b.2)) (out.eval m ρ))
  | pair x y ihx ihy =>
      have hx (a b : Comp m) :
          (generate sigsTerm.lift.lift (env₂ sΓ) x fresh₀).Holds m view (extend (extend ρ a) b) ↔ Typing m view sigs Γ x a := by
        simpa only [env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
          using ihx (sigsTerm := sigsTerm.lift.lift) _ _ _ fresh₀ ((henv.lift a).lift b) ((hsig.lift a).lift b)
      have hy (a b : Comp m) :
          (generate sigsTerm.lift.lift (env₂ sΓ) y fresh₁).Holds m view (extend (extend ρ a) b) ↔ Typing m view sigs Γ y b := by
        simpa only [env₂, fresh₁, CompTerm.eval_var, extend_none]
          using ihy (sigsTerm := sigsTerm.lift.lift) _ _ _ fresh₁ ((henv.lift a).lift b) ((hsig.lift a).lift b)
      simp only [generate, Formula.Holds, Typing.pair_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      rw [hx, hy]
      simp [Formula.compLe, Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
        CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
  | fst x ih =>
      have hx (a b : Comp m) :
          (generate sigsTerm.lift.lift (env₂ sΓ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩).Holds m view
            (extend (extend ρ a) b) ↔ Typing m view sigs Γ x (m.pair a.1 b.1, a.2) := by
        simpa only [env₂, fresh₀, fresh₁, CompTerm.eval, CompTerm.var, TyTerm.eval, RowTerm.eval,
          extend_none, extend_some] using ih (sigsTerm := sigsTerm.lift.lift) _ _ _ ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩ ((henv.lift a).lift b) ((hsig.lift a).lift b)
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
          (generate sigsTerm.lift.lift (env₂ sΓ) x ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩).Holds m view
            (extend (extend ρ a) b) ↔ Typing m view sigs Γ x (m.pair a.1 b.1, a.2) := by
        simpa only [env₂, fresh₀, fresh₁, CompTerm.eval, CompTerm.var, TyTerm.eval, RowTerm.eval,
          extend_none, extend_some] using ih (sigsTerm := sigsTerm.lift.lift) _ _ _ ⟨.pair fresh₀.ty fresh₁.ty, fresh₀.row⟩ ((henv.lift a).lift b) ((hsig.lift a).lift b)
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
          (generate sigsTerm.lift.lift (env₂ sΓ) x fresh₀).Holds m view (extend (extend ρ a) b) ↔ Typing m view sigs Γ x a := by
        simpa only [env₂, fresh₀, CompTerm.eval_var, extend_none, extend_some]
          using ihx (sigsTerm := sigsTerm.lift.lift) _ _ _ fresh₀ ((henv.lift a).lift b) ((hsig.lift a).lift b)
      have hr (a b : Comp m) :
          (generate sigsTerm.lift.lift (env₂ sΓ) r fresh₁).Holds m view (extend (extend ρ a) b) ↔ Typing m view sigs Γ r b := by
        simpa only [env₂, fresh₁, CompTerm.eval_var, extend_none]
          using ihr (sigsTerm := sigsTerm.lift.lift) _ _ _ fresh₁ ((henv.lift a).lift b) ((hsig.lift a).lift b)
      simp only [generate, Formula.Holds, Typing.record_iff]
      apply exists_congr; intro a
      apply exists_congr; intro b
      rw [hx, hr]
      simp [Formula.compLe, Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
        CompTerm.rename, fresh₀, fresh₁, lift₂, TyTerm.eval, RowTerm.eval, Function.comp_def]
  | field l x ih =>
      have hx (a : Comp m) :
          (generate sigsTerm.lift sΓ.lift x ⟨.record l (.var none) .emptyRecord, .var none⟩).Holds m view
            (extend ρ a) ↔ Typing m view sigs Γ x (m.record l a.1 m.emptyRecord, a.2) := by
        simpa only [CompTerm.eval, TyTerm.eval, RowTerm.eval, extend_none]
          using ih (sigsTerm := sigsTerm.lift) _ _ _ ⟨.record l (.var none) .emptyRecord, .var none⟩ (henv.lift a) (hsig.lift a)
      simp only [generate, Formula.Holds, Typing.field_iff]
      simp only [hx]
      simp [Formula.compLe, Formula.Holds, Comp.le, CompTerm.eval, CompTerm.var,
        CompTerm.rename, TyTerm.eval, RowTerm.eval, Function.comp_def, Prod.exists]
  | variant l x ih =>
      have hx (a : Comp m) :
          (generate sigsTerm.lift sΓ.lift x (CompTerm.var none)).Holds m view (extend ρ a) ↔ Typing m view sigs Γ x a := by
        simpa only [CompTerm.eval_var, extend_none] using ih (sigsTerm := sigsTerm.lift) _ _ _ (CompTerm.var none) (henv.lift a) (hsig.lift a)
      simp only [generate, Formula.Holds, Typing.variant_iff]
      apply exists_congr; intro a
      rw [hx]
      simp [Formula.compLe, Formula.Holds, Comp.le, CompTerm.eval,
        CompTerm.rename, TyTerm.eval, RowTerm.eval, Function.comp_def]

  | request op payload ih =>
      have hp (c : Comp m) :
          (generate sigsTerm.lift sΓ.lift payload
            ⟨(sigsTerm op).input.rename some, .var none⟩).Holds m view (extend ρ c) ↔
          Typing m view sigs Γ payload ((sigs op).input, c.2) := by
        have hinput := congrArg Signature.input (hsig op)
        simp only [SignatureTerm.eval] at hinput
        simpa [CompTerm.eval, TyTerm.eval, RowTerm.eval, SignatureTerm.eval, hinput] using
          ih sigsTerm.lift sΓ.lift Γ (extend ρ c)
            ⟨(sigsTerm op).input.rename some, .var none⟩ (henv.lift c) (hsig.lift c)
      have hkey := congrArg Signature.key (hsig op)
      have hextra := congrArg Signature.extra (hsig op)
      have houtput := congrArg Signature.output (hsig op)
      simp only [SignatureTerm.eval] at hkey hextra houtput
      simp only [generate, Formula.Holds, Typing.request_iff, hp,
        TyTerm.eval_rename, extend_comp_some, RowExpr.eval, eval_heads, eval_fromCoreRow,
        RowTerm.eval_rename, rowEnv, extend_none, CompTerm.eval, hkey, hextra, houtput]
      exact exists_comp_row m (fun er => Typing m view sigs Γ payload ((sigs op).input, er) ∧
        m.subTy (sigs op).output (out.ty.eval m ρ) ∧
        algebra.le (algebra.join (view.decode er)
          (algebra.join (algebra.head (sigs op).key) (keysRow algebra (sigs op).extra)))
          (view.decode (out.row.eval m ρ)))
  | boundary boundary body ih =>
      have hb (input : Comp m) :
          (generate sigsTerm.lift sΓ.lift body (CompTerm.var none)).Holds m view (extend ρ input) ↔
          Typing m view sigs Γ body input := by
        simpa using ih sigsTerm.lift sΓ.lift Γ (extend ρ input)
          (CompTerm.var none) (henv.lift input) (hsig.lift input)
      simp only [generate, Formula.Holds, Typing.boundary_iff]
      apply exists_congr; intro input
      rw [hb]
      simp [TyTerm.eval, CompTerm.eval, Boundary.eval_term, RowExpr.eval, rowEnv]
  | handler op action onReturn onOperation iha ihr iho =>
      have hi (input returned operated : Comp m) :
          (generate sigsTerm.lift.lift.lift (env₃ sΓ) action fresh₀₃).Holds m view
            (extend (extend (extend ρ input) returned) operated) ↔
          Typing m view sigs Γ action input := by
        simpa [env₃, fresh₀₃] using iha sigsTerm.lift.lift.lift (env₃ sΓ) Γ
          (extend (extend (extend ρ input) returned) operated) fresh₀₃
          (((henv.lift input).lift returned).lift operated)
          (((hsig.lift input).lift returned).lift operated)
      have hr (input returned operated : Comp m) :
          (generate sigsTerm.lift.lift.lift
              (Scheme.mono (CompTerm.pure fresh₀₃.ty) :: env₃ sΓ) onReturn fresh₁₃).Holds m view
            (extend (extend (extend ρ input) returned) operated) ↔
          Typing m view sigs (.mono (Comp.pure m input.1) :: Γ) onReturn returned := by
        simpa [env₃, fresh₀₃, fresh₁₃, CompTerm.var, CompTerm.pure, CompTerm.eval,
          TyTerm.eval, RowTerm.eval, Comp.pure] using ihr sigsTerm.lift.lift.lift _ _
          (extend (extend (extend ρ input) returned) operated) fresh₁₃
          ((((henv.lift input).lift returned).lift operated).mono (CompTerm.pure fresh₀₃.ty))
          (((hsig.lift input).lift returned).lift operated)
      have ho (input returned operated : Comp m) :
          (generate sigsTerm.lift.lift.lift
              (Scheme.mono (CompTerm.pure ((sigsTerm.lift.lift.lift op).input)) ::
               Scheme.mono (CompTerm.pure (CompTerm.arrow
                 (CompTerm.pure ((sigsTerm.lift.lift.lift op).output)) fresh₀₃)) :: env₃ sΓ)
              onOperation fresh₂₃).Holds m view
            (extend (extend (extend ρ input) returned) operated) ↔
          Typing m view sigs
            (.mono (Comp.pure m (sigs op).input) ::
             .mono (Comp.pure m (Comp.arrow m (Comp.pure m (sigs op).output) input)) :: Γ)
            onOperation operated := by
        have hs := ((hsig.lift input).lift returned).lift operated
        have hinput := congrArg Signature.input (hs op)
        have houtput := congrArg Signature.output (hs op)
        simp only [SignatureTerm.eval] at hinput houtput
        have he := ((((henv.lift input).lift returned).lift operated).mono
          (CompTerm.pure (CompTerm.arrow
            (CompTerm.pure ((sigsTerm.lift.lift.lift op).output)) fresh₀₃))).mono
              (CompTerm.pure ((sigsTerm.lift.lift.lift op).input))
        simpa only [CompTerm.eval_pure, CompTerm.arrow, CompTerm.pure, TyTerm.eval, RowTerm.eval,
          Comp.pure, Comp.arrow, fresh₀₃, fresh₂₃, CompTerm.var, CompTerm.eval, env₃,
          extend_some, extend_none, hinput, houtput] using
          iho sigsTerm.lift.lift.lift _ _
            (extend (extend (extend ρ input) returned) operated) fresh₂₃ he hs
      have hkey := congrArg Signature.key (hsig op)
      simp only [SignatureTerm.eval] at hkey
      simp only [generate, Formula.Holds, Typing.handler_iff]
      apply exists_congr; intro input
      apply exists_congr; intro returned
      apply exists_congr; intro operated
      rw [hi, hr, ho]
      simp [RowExpr.eval, rowEnv, CompTerm.eval, fresh₁₃, fresh₂₃,
        lift₃, CompTerm.rename, CompTerm.var, TyTerm.eval, Function.comp_def, hkey]

/-- Public inference entry point. Its one bound slot is the inferred result;
the existing free slots of `Γ` remain parameters, not generalized variables. -/
def principal (sigsTerm : Signatures Op Key α) (Γ : SchemeEnv Key Scope α) (e : Expr Op Key Scope) : Scheme Key Scope α :=
  generate sigsTerm.lift Γ.lift e (CompTerm.var none)

/-- The principal scheme represents all and only the declarative typings. -/
theorem principal_exact (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (e : Expr Op Key Scope) (sigsTerm : Signatures Op Key α) (sΓ : SchemeEnv Key Scope α)
    (Γ : List (Binding m Op Key Scope)) (ρ : α → Comp m) (henv : EnvRel m view sigs ρ sΓ Γ) (hsig : SigRel m ρ sigsTerm sigs) (c : Comp m) :
    (principal sigsTerm sΓ e).Holds m view (extend ρ c) ↔ Typing m view sigs Γ e c := by
  simpa only [principal, CompTerm.eval_var, extend_none]
    using generate_models_iff_typing m view sigs e sigsTerm.lift sΓ.lift Γ (extend ρ c) (CompTerm.var none) (henv.lift c) (hsig.lift c)

theorem principal_sound (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (e : Expr Op Key Scope) (sigsTerm : Signatures Op Key α) (sΓ : SchemeEnv Key Scope α)
    (Γ : List (Binding m Op Key Scope)) (ρ : α → Comp m) (henv : EnvRel m view sigs ρ sΓ Γ) (hsig : SigRel m ρ sigsTerm sigs) (c : Comp m)
    (h : (principal sigsTerm sΓ e).Holds m view (extend ρ c)) : Typing m view sigs Γ e c :=
  (principal_exact m view sigs e sigsTerm sΓ Γ ρ henv hsig c).mp h

theorem principal_complete (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (e : Expr Op Key Scope) (sigsTerm : Signatures Op Key α) (sΓ : SchemeEnv Key Scope α)
    (Γ : List (Binding m Op Key Scope)) (ρ : α → Comp m) (henv : EnvRel m view sigs ρ sΓ Γ) (hsig : SigRel m ρ sigsTerm sigs) (c : Comp m)
    (h : Typing m view sigs Γ e c) : (principal sigsTerm sΓ e).Holds m view (extend ρ c) :=
  (principal_exact m view sigs e sigsTerm sΓ Γ ρ henv hsig c).mpr h

/-- Every sound candidate scheme is an instance-set subset of the generated
scheme. This is principality of constraints, not a solved normal-form theorem. -/
theorem principal_most_general (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (e : Expr Op Key Scope) (sigsTerm : Signatures Op Key α) (sΓ : SchemeEnv Key Scope α)
    (Γ : List (Binding m Op Key Scope)) (ρ : α → Comp m) (henv : EnvRel m view sigs ρ sΓ Γ) (hsig : SigRel m ρ sigsTerm sigs)
    (candidate : Scheme Key Scope α)
    (hsound : ∀ c, candidate.Holds m view (extend ρ c) → Typing m view sigs Γ e c) :
    ∀ c, candidate.Holds m view (extend ρ c) → (principal sigsTerm sΓ e).Holds m view (extend ρ c) := by
  intro c hc
  exact principal_complete m view sigs e sigsTerm sΓ Γ ρ henv hsig c (hsound c hc)

theorem generate_unbound (sigsTerm : Signatures Op Key α) (Γ : SchemeEnv Key Scope α) (n : Nat) (out : CompTerm α)
    (h : Γ[n]? = none) : generate sigsTerm Γ (.var n) out = .bot := by
  simp [generate, Scheme.lookup, h]

theorem unbound_not_typable (m : Model) (view : RowView m algebra) (sigs : Op → Signature m Key) (Γ : List (Binding m Op Key Scope)) (n : Nat) (c : Comp m)
    (h : Γ[n]? = none) : ¬ Typing m view sigs Γ (.var n) c := by
  simp [Typing.var_iff, BindingLookup, h]

/-- Formula size counts logical nodes. Type-term sizes are separate; there is
no performance claim that scheme instantiation is constant time. -/
def Formula.nodes : Formula Key Scope α → Nat
  | .top | .bot | .tyLe _ _ | .rowLe _ _ | .effectLe _ _ => 1
  | .and p q | .or p q => 1 + p.nodes + q.nodes
  | .existsSlot p => 1 + p.nodes

theorem Formula.nodes_pos (p : Formula Key Scope α) : 0 < p.nodes := by
  cases p <;> simp [nodes] <;> omega

theorem Formula.nodes_rename (p : Formula Key Scope α) (f : α → β) :
    (p.rename f).nodes = p.nodes := by
  induction p generalizing β <;> simp_all [rename, nodes]

theorem Formula.nodes_subst (p : Formula Key Scope α) (f : α → CompTerm β) :
    (p.subst f).nodes = p.nodes := by
  induction p generalizing β <;> simp_all [subst, nodes]

theorem Scheme.instantiation_nodes (s : Scheme Key Scope α) (c : CompTerm α) :
    (s.instantiate c).nodes = s.nodes := by
  simp [instantiate, Formula.nodes_subst]


end Yulang.RecursiveEffects
