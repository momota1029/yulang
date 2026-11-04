import Yulang.Inference
import Yulang.Effects

/-!
# Constraint generation for resolved operations and shallow handler rules

This is a compositional rule layer over `Inference.Expr`. Body and arm expressions
use the already-proved core generator, including higher-order applications and
value-restricted let. Operation keys include family, operation and family arguments.
The continuation handed to a shallow arm retains the original input row.

Operation-local type variables use finite existential instantiation at calls and
universal checking at handler arms, with a fixed outer environment and result.
The layer does not claim a source elaborator, complete operation-pattern coverage,
role constraints on locals, or a whole-language operational preservation theorem.
It gives exact finite quantified constraints for these resolved typing rules.
-/

namespace Yulang.EffectInference

open Inference Effects

/-- An adapter from an inference model to the occurrence rows already verified
in `Effects`. The concrete structural model has the identity adapter. -/
structure RowView (m : Model) (Key : Type) where
  decode : m.Row → Row Key
  decode_empty : decode m.empty = []
  decode_join : ∀ a b, decode (m.join a b) = decode a ++ decode b
  subtype_iff : ∀ a b, m.subRow a b ↔ RowSubset (decode a) (decode b)

/-- A resolved monomorphic operation signature. `extra` is additive: the
operation's own key is always emitted as well. Free type slots are shared with
the ambient context and are not operation-local quantifiers. -/
structure Signature (α Family Operation Argument : Type) where
  key : OperationKey Family Operation Argument
  input : TyTerm α
  output : TyTerm α
  extra : List (OperationKey Family Operation Argument) := []

abbrev SigKey (Family Operation Argument : Type) := OperationKey Family Operation Argument

/-- Operation-local type variables are distinct from captured ambient slots.
Only family parameters occur in keys and extra atoms, not local variables. -/
structure PolySignature (α : Type) (n : Nat) (Family Operation Argument : Type) where
  key : OperationKey Family Operation Argument
  input : TyTerm (α ⊕ Fin n)
  output : TyTerm (α ⊕ Fin n)
  extra : List (OperationKey Family Operation Argument) := []

/-- Locals range over value types; their row projection is always empty. -/
def localEnv (m : Model) (ρ : α → Comp m) (ι : Fin n → m.Ty) :
    α ⊕ Fin n → Comp m := Sum.elim ρ (Comp.pure m ∘ ι)

@[simp] theorem localEnv_comp_inl (m : Model) (ρ : α → Comp m) (ι : Fin n → m.Ty) :
    localEnv m ρ ι ∘ Sum.inl = ρ := rfl

/-- View locals as slots inside their binder, without changing the monomorphic API. -/
def PolySignature.mono (sig : PolySignature α n F O A) : Signature (α ⊕ Fin n) F O A :=
  ⟨sig.key, sig.input, sig.output, sig.extra⟩

def PolySignature.rename (sig : PolySignature α n F O A) (f : α → β) :
    PolySignature β n F O A :=
  ⟨sig.key, sig.input.rename (Sum.map f id), sig.output.rename (Sum.map f id), sig.extra⟩

@[simp] theorem localEnv_map (m : Model) (ρ : β → Comp m) (ι : Fin n → m.Ty) (f : α → β) :
    localEnv m ρ ι ∘ Sum.map f id = localEnv m (ρ ∘ f) ι := by
  funext x; cases x <;> rfl

/-- Neither the result type nor its row can depend on an operation-local choice. -/
theorem local_result_no_escape (m : Model) (ρ : α → Comp m) (out : CompTerm α)
    (ι κ : Fin n → m.Ty) :
    (out.rename Sum.inl).eval m (localEnv m ρ ι) = out.eval m ρ ∧
    (out.rename Sum.inl).eval m (localEnv m ρ κ) = out.eval m ρ := by
  simp

/-- Every local choice represents the same outer environment, including schemes. -/
theorem local_outer_environment (m : Model) (ρ : α → Comp m)
    (sΓ : SchemeEnv α) (Γ : List (Binding m)) (henv : EnvRel m ρ sΓ Γ)
    (ι : Fin n → m.Ty) : EnvRel m (localEnv m ρ ι) (sΓ.rename Sum.inl) Γ :=
  henv.rename Sum.inl _ rfl

def heads (keys : List Key) : RowExpr α Key :=
  keys.foldr (fun key row => .union (.head key) row) .empty

def fromCoreRow : RowTerm α → RowExpr α Key
  | .var a => .var a
  | .empty => .empty
  | .join a b => .union (fromCoreRow a) (fromCoreRow b)

def rowEnv (view : RowView m Key) (ρ : α → Comp m) : α → Row Key :=
  fun a => view.decode (ρ a).2

@[simp] theorem eval_heads [DecidableEq Key] (ρ : α → Row Key) (keys : List Key) :
    RowExpr.eval ρ (heads keys) = keys.map (fun k => ({key := k} : Occurrence Key)) := by
  induction keys <;> simp_all [heads, RowExpr.eval]

@[simp] theorem eval_fromCoreRow [DecidableEq Key] (view : RowView m Key)
    (ρ : α → Comp m) (r : RowTerm α) :
    RowExpr.eval (rowEnv view ρ) (fromCoreRow r) = view.decode (r.eval m ρ) := by
  induction r <;> simp_all [fromCoreRow, RowExpr.eval, RowTerm.eval, rowEnv,
    view.decode_empty, view.decode_join]

/-- Extra atoms are first-order row inclusions over exact occurrence transforms.
Core formulas remain finite data and are not replaced with typing predicates. -/
inductive Constraint (Key : Type) : Type → Type 1 where
  | core : Formula α → Constraint Key α
  | rowLe : RowExpr α Key → RowExpr α Key → Constraint Key α
  | and : Constraint Key α → Constraint Key α → Constraint Key α
  | existsSlot : Constraint Key (Option α) → Constraint Key α
  /-- Fresh type slots at each call, with no restriction on their chosen types. -/
  | existsTypes : (n : Nat) → Constraint Key (α ⊕ Fin n) → Constraint Key α
  /-- Rigid locals: the body must hold for every local type assignment. -/
  | forallTypes : (n : Nat) → Constraint Key (α ⊕ Fin n) → Constraint Key α

def Constraint.Holds [DecidableEq Key] (view : RowView m Key) :
    {α : Type} → (α → Comp m) → Constraint Key α → Prop
  | _, ρ, .core p => p.Holds m ρ
  | _, ρ, .rowLe a b => RowSubset
      (RowExpr.eval (rowEnv view ρ) a) (RowExpr.eval (rowEnv view ρ) b)
  | _, ρ, .and p q => p.Holds view ρ ∧ q.Holds view ρ
  | _, ρ, .existsSlot p => ∃ c, p.Holds view (extend ρ c)
  | _, ρ, .existsTypes _ p => ∃ ι, p.Holds view (localEnv m ρ ι)
  | _, ρ, .forallTypes _ p => ∀ ι, p.Holds view (localEnv m ρ ι)

def requestConstraints (Γ : SchemeEnv α) (sig : Signature α F O A)
    (payload : Expr) (out : CompTerm α) : Constraint (SigKey F O A) α :=
  .existsSlot (
    .and (.core (generate Γ.lift payload ⟨sig.input.rename some, .var none⟩))
      (.and (.core (.tyLe (sig.output.rename some) (out.ty.rename some)))
        (.rowLe (.union (.var none) (.union (.head sig.key) (heads sig.extra)))
          (fromCoreRow (out.row.rename some)))))

inductive RequestTyping (view : RowView m (SigKey F O A))
    (Γ : List (Binding m)) (key : SigKey F O A) (extra : List (SigKey F O A))
    (input output : m.Ty) (payload : Expr) (out : Comp m) : Prop where
  | intro : Typing m Γ payload (input, er) → m.subTy output out.1 →
      RowSubset (view.decode er ++ ({key := key} :: extra.map (fun k => {key := k})))
        (view.decode out.2) → RequestTyping view Γ key extra input output payload out

inductive Boundary (Key : Type) where
  | protect : Nat → Permission Key → Boundary Key
  | release : Nat → Boundary Key

def Boundary.row (boundary : Boundary Key) (row : Row Key) : Row Key :=
  match boundary with
  | .protect scope permission => Effects.protect scope permission row
  | .release scope => Effects.release scope row

def Boundary.term (boundary : Boundary Key) (row : RowExpr α Key) : RowExpr α Key :=
  match boundary with
  | .protect scope permission => .protect scope permission row
  | .release scope => .release scope row

@[simp] theorem Boundary.eval_term [DecidableEq Key] (b : Boundary Key)
    (ρ : α → Row Key) (r : RowExpr α Key) :
    RowExpr.eval ρ (b.term r) = b.row (RowExpr.eval ρ r) := by
  cases b <;> rfl

def boundaryConstraints (Γ : SchemeEnv α) (boundary : Boundary Key)
    (body : Expr) (out : CompTerm α) : Constraint Key α :=
  .existsSlot (
    .and (.core (generate Γ.lift body (CompTerm.var none)))
      (.and (.core (.tyLe (.var none) (out.ty.rename some)))
        (.rowLe (boundary.term (.var none)) (fromCoreRow (out.row.rename some)))))

inductive BoundaryTyping (view : RowView m Key) (boundary : Boundary Key)
    (Γ : List (Binding m)) (body : Expr) (out : Comp m) : Prop where
  | intro : Typing m Γ body input → m.subTy input.1 out.1 →
      RowSubset (boundary.row (view.decode input.2)) (view.decode out.2) →
      BoundaryTyping view boundary Γ body out

/-- Payload is local variable 0; the pure continuation value is variable 1.
Calling that continuation returns the ORIGINAL action computation, including
its entire row, as required by shallow rather than deep handling. -/
def armEnvironment (Γ : SchemeEnv α) (input : CompTerm α)
    (payload response : TyTerm α) : SchemeEnv α :=
  Scheme.mono (CompTerm.pure payload) ::
    Scheme.mono (CompTerm.pure (CompTerm.arrow (CompTerm.pure response) input)) :: Γ

def semanticArmEnvironment (m : Model) (Γ : List (Binding m)) (input : Comp m)
    (payload response : m.Ty) : List (Binding m) :=
  .mono (Comp.pure m payload) ::
    .mono (Comp.pure m (Comp.arrow m (Comp.pure m response) input)) :: Γ

def handlerConstraints (Γ : SchemeEnv α) (sig : Signature α F O A)
    (action onReturn onOperation : Expr) (out : CompTerm α) : Constraint (SigKey F O A) α :=
  .existsSlot (.existsSlot (.existsSlot (
    .and (.core (generate (env₃ Γ) action fresh₀₃))
      (.and (.core (generate (Scheme.mono (CompTerm.pure fresh₀₃.ty) :: env₃ Γ) onReturn fresh₁₃))
        (.and (.core (generate
            (armEnvironment (env₃ Γ) fresh₀₃
              (sig.input.rename (fun x => some (some (some x))))
              (sig.output.rename (fun x => some (some (some x)))))
            onOperation fresh₂₃))
          (.and (.core (.tyLe (.union fresh₁₃.ty fresh₂₃.ty) (lift₃ out).ty))
            (.rowLe (.union (.residual [sig.key] (.var (some (some none))))
                (.union (.var (some none)) (.var none)))
              (fromCoreRow (lift₃ out).row))))))))

inductive HandlerTyping [DecidableEq (SigKey F O A)]
    (view : RowView m (SigKey F O A)) (Γ : List (Binding m)) (key : SigKey F O A)
    (payload response : m.Ty) (action onReturn onOperation : Expr) (out : Comp m) : Prop where
  | intro : Typing m Γ action input →
      Typing m (.mono (Comp.pure m input.1) :: Γ) onReturn returned →
      Typing m (semanticArmEnvironment m Γ input payload response) onOperation operated →
      m.subTy (m.union returned.1 operated.1) out.1 →
      RowSubset (residual [key] (view.decode input.2) ++
        (view.decode returned.2 ++ view.decode operated.2)) (view.decode out.2) →
      HandlerTyping view Γ key payload response action onReturn onOperation out

theorem armEnvironment_related (m : Model) (ρ : α → Comp m)
    (sΓ : SchemeEnv α) (Γ : List (Binding m)) (henv : EnvRel m ρ sΓ Γ)
    (input : CompTerm α) (payload response : TyTerm α) :
    EnvRel m ρ (armEnvironment sΓ input payload response)
      (semanticArmEnvironment m Γ (input.eval m ρ) (payload.eval m ρ) (response.eval m ρ)) := by
  simpa [armEnvironment, semanticArmEnvironment, CompTerm.pure, CompTerm.arrow,
    CompTerm.eval, TyTerm.eval, RowTerm.eval, Comp.pure, Comp.arrow]
    using (henv.mono (CompTerm.pure (CompTerm.arrow (CompTerm.pure response) input))).mono
      (CompTerm.pure payload)

@[simp] theorem requestTyping_iff (view : RowView m (SigKey F O A))
    (Γ : List (Binding m)) (key : SigKey F O A) (extra : List (SigKey F O A))
    (input output : m.Ty) (payload : Expr) (out : Comp m) :
    RequestTyping view Γ key extra input output payload out ↔ ∃ er,
      Typing m Γ payload (input, er) ∧ m.subTy output out.1 ∧
        RowSubset (view.decode er ++ ({key := key} :: extra.map (fun k => {key := k})))
          (view.decode out.2) := by
  constructor
  · intro h; cases h with | intro hp ht he => exact ⟨_, hp, ht, he⟩
  · rintro ⟨er, hp, ht, he⟩; exact .intro hp ht he

/-- The operation's own effect is present even when extra effects were declared. -/
theorem request_constraints_exact [DecidableEq (SigKey F O A)]
    (view : RowView m (SigKey F O A)) (sΓ : SchemeEnv α) (Γ : List (Binding m))
    (ρ : α → Comp m) (henv : EnvRel m ρ sΓ Γ) (sig : Signature α F O A)
    (payload : Expr) (out : CompTerm α) :
    (requestConstraints sΓ sig payload out).Holds view ρ ↔
      RequestTyping view Γ sig.key sig.extra (sig.input.eval m ρ) (sig.output.eval m ρ)
        payload (out.eval m ρ) := by
  have hp (c : Comp m) :
      (generate sΓ.lift payload ⟨sig.input.rename some, .var none⟩).Holds m (extend ρ c) ↔
      Typing m Γ payload (sig.input.eval m ρ, c.2) := by
    simpa [CompTerm.eval, TyTerm.eval, RowTerm.eval]
      using generate_models_iff_typing m payload sΓ.lift Γ (extend ρ c)
        ⟨sig.input.rename some, .var none⟩ (henv.lift c)
  simp only [requestConstraints, Constraint.Holds, requestTyping_iff]
  simp only [hp, Formula.Holds, TyTerm.eval_rename, extend_comp_some,
    RowExpr.eval, eval_heads, eval_fromCoreRow, RowTerm.eval_rename]
  simp only [rowEnv, extend_none, CompTerm.eval, List.singleton_append]
  exact exists_comp_row m (fun er => Typing m Γ payload (sig.input.eval m ρ, er) ∧
    m.subTy (sig.output.eval m ρ) (out.ty.eval m ρ) ∧
    RowSubset (view.decode er ++ ({key := sig.key} :: sig.extra.map (fun k => {key := k})))
      (view.decode (out.row.eval m ρ)))

@[simp] theorem boundaryTyping_iff (view : RowView m Key) (boundary : Boundary Key)
    (Γ : List (Binding m)) (body : Expr) (out : Comp m) :
    BoundaryTyping view boundary Γ body out ↔ ∃ input,
      Typing m Γ body input ∧ m.subTy input.1 out.1 ∧
        RowSubset (boundary.row (view.decode input.2)) (view.decode out.2) := by
  constructor
  · intro h; cases h with | intro hb ht he => exact ⟨_, hb, ht, he⟩
  · rintro ⟨input, hb, ht, he⟩; exact .intro hb ht he

theorem boundary_constraints_exact [DecidableEq Key]
    (view : RowView m Key) (sΓ : SchemeEnv α) (Γ : List (Binding m))
    (ρ : α → Comp m) (henv : EnvRel m ρ sΓ Γ) (boundary : Boundary Key)
    (body : Expr) (out : CompTerm α) :
    (boundaryConstraints sΓ boundary body out).Holds view ρ ↔
      BoundaryTyping view boundary Γ body (out.eval m ρ) := by
  have hb (input : Comp m) :
      (generate sΓ.lift body (CompTerm.var none)).Holds m (extend ρ input) ↔
      Typing m Γ body input := by
    simpa using generate_models_iff_typing m body sΓ.lift Γ (extend ρ input)
      (CompTerm.var none) (henv.lift input)
  simp only [boundaryConstraints, Constraint.Holds, boundaryTyping_iff]
  apply exists_congr; intro input
  rw [hb]
  simp [Formula.Holds, TyTerm.eval, CompTerm.eval, Boundary.eval_term,
    RowExpr.eval, rowEnv]

@[simp] theorem handlerTyping_iff [DecidableEq (SigKey F O A)]
    (view : RowView m (SigKey F O A)) (Γ : List (Binding m)) (key : SigKey F O A)
    (payload response : m.Ty) (action onReturn onOperation : Expr) (out : Comp m) :
    HandlerTyping view Γ key payload response action onReturn onOperation out ↔ ∃ input returned operated,
      Typing m Γ action input ∧
      Typing m (.mono (Comp.pure m input.1) :: Γ) onReturn returned ∧
      Typing m (semanticArmEnvironment m Γ input payload response) onOperation operated ∧
      m.subTy (m.union returned.1 operated.1) out.1 ∧
      RowSubset (residual [key] (view.decode input.2) ++
        (view.decode returned.2 ++ view.decode operated.2)) (view.decode out.2) := by
  constructor
  · intro h; cases h with | intro hi hr ho ht he => exact ⟨_, _, _, hi, hr, ho, ht, he⟩
  · rintro ⟨input, returned, operated, hi, hr, ho, ht, he⟩
    exact .intro hi hr ho ht he

/-- Exact generation for a resolved shallow-handler rule. Capturing one
operation never erases a different operation from the same family. -/
theorem handler_constraints_exact [DecidableEq (SigKey F O A)]
    (view : RowView m (SigKey F O A)) (sΓ : SchemeEnv α) (Γ : List (Binding m))
    (ρ : α → Comp m) (henv : EnvRel m ρ sΓ Γ) (sig : Signature α F O A)
    (action onReturn onOperation : Expr) (out : CompTerm α) :
    (handlerConstraints sΓ sig action onReturn onOperation out).Holds view ρ ↔
      HandlerTyping view Γ sig.key (sig.input.eval m ρ) (sig.output.eval m ρ)
        action onReturn onOperation (out.eval m ρ) := by
  have hi (input returned operated : Comp m) :
      (generate (env₃ sΓ) action fresh₀₃).Holds m (extend (extend (extend ρ input) returned) operated) ↔
      Typing m Γ action input := by
    simpa [env₃, fresh₀₃] using generate_models_iff_typing m action (env₃ sΓ) Γ
      (extend (extend (extend ρ input) returned) operated) fresh₀₃
      (((henv.lift input).lift returned).lift operated)
  have hr (input returned operated : Comp m) :
      (generate (Scheme.mono (CompTerm.pure fresh₀₃.ty) :: env₃ sΓ) onReturn fresh₁₃).Holds m
        (extend (extend (extend ρ input) returned) operated) ↔
      Typing m (.mono (Comp.pure m input.1) :: Γ) onReturn returned := by
    simpa [env₃, fresh₀₃, fresh₁₃, CompTerm.var, CompTerm.pure, CompTerm.eval,
      TyTerm.eval, RowTerm.eval, Comp.pure]
      using generate_models_iff_typing m onReturn _ _
        (extend (extend (extend ρ input) returned) operated) fresh₁₃
        ((((henv.lift input).lift returned).lift operated).mono (CompTerm.pure fresh₀₃.ty))
  have ho (input returned operated : Comp m) :
      (generate (armEnvironment (env₃ sΓ) fresh₀₃
          (sig.input.rename (fun x => some (some (some x))))
          (sig.output.rename (fun x => some (some (some x))))) onOperation fresh₂₃).Holds m
        (extend (extend (extend ρ input) returned) operated) ↔
      Typing m (semanticArmEnvironment m Γ input (sig.input.eval m ρ) (sig.output.eval m ρ))
        onOperation operated := by
    have hrel := armEnvironment_related m (extend (extend (extend ρ input) returned) operated)
      (env₃ sΓ) Γ (((henv.lift input).lift returned).lift operated) fresh₀₃
      (sig.input.rename (fun x => some (some (some x))))
      (sig.output.rename (fun x => some (some (some x))))
    simpa [env₃, fresh₀₃, fresh₂₃, Function.comp_def]
      using generate_models_iff_typing m onOperation _ _
        (extend (extend (extend ρ input) returned) operated) fresh₂₃ hrel
  simp only [handlerConstraints, Constraint.Holds, handlerTyping_iff]
  apply exists_congr; intro input
  apply exists_congr; intro returned
  apply exists_congr; intro operated
  rw [hi, hr, ho]
  simp [Formula.Holds, RowExpr.eval, rowEnv, CompTerm.eval, fresh₁₃, fresh₂₃,
    lift₃, CompTerm.rename, CompTerm.var, TyTerm.eval, Function.comp_def]

/-! Operation-local polymorphism. Action and return-arm witnesses are chosen
before the rigid locals. Only the operation-arm witness may depend on them. -/

def polyRequestConstraints (Γ : SchemeEnv α) (sig : PolySignature α n F O A)
    (payload : Expr) (out : CompTerm α) : Constraint (SigKey F O A) α :=
  .existsTypes n (requestConstraints (Γ.rename Sum.inl) sig.mono payload (out.rename Sum.inl))

/-- Independent call rule: any local type instantiation may be chosen. -/
inductive PolyRequestTyping (view : RowView m (SigKey F O A))
    (Γ : List (Binding m)) (key : SigKey F O A) (extra : List (SigKey F O A))
    (input output : (Fin n → m.Ty) → m.Ty) (payload : Expr) (out : Comp m) : Prop where
  | intro (ι : Fin n → m.Ty) :
      RequestTyping view Γ key extra (input ι) (output ι) payload out →
      PolyRequestTyping view Γ key extra input output payload out

theorem poly_request_constraints_exact [DecidableEq (SigKey F O A)]
    (view : RowView m (SigKey F O A)) (sΓ : SchemeEnv α) (Γ : List (Binding m))
    (ρ : α → Comp m) (henv : EnvRel m ρ sΓ Γ) (sig : PolySignature α n F O A)
    (payload : Expr) (out : CompTerm α) :
    (polyRequestConstraints sΓ sig payload out).Holds view ρ ↔
      PolyRequestTyping view Γ sig.key sig.extra
        (fun ι => sig.input.eval m (localEnv m ρ ι))
        (fun ι => sig.output.eval m (localEnv m ρ ι)) payload (out.eval m ρ) := by
  change (∃ ι, (requestConstraints _ _ _ _).Holds view (localEnv m ρ ι)) ↔ _
  constructor
  · rintro ⟨ι, h⟩
    apply PolyRequestTyping.intro ι
    simpa [PolySignature.mono] using
      (request_constraints_exact view _ Γ _ (local_outer_environment m ρ sΓ Γ henv ι)
        sig.mono payload (out.rename Sum.inl)).mp h
  · intro h
    cases h with
    | intro ι h =>
      refine ⟨ι, (request_constraints_exact view _ Γ _
        (local_outer_environment m ρ sΓ Γ henv ι) sig.mono payload (out.rename Sum.inl)).mpr ?_⟩
      simpa [PolySignature.mono] using h

/-- One monomorphic arm, with the common action and return results fixed. -/
def operationArmConstraints (Γ : SchemeEnv α) (sig : Signature α F O A)
    (input returned out : CompTerm α) (onOperation : Expr) : Constraint (SigKey F O A) α :=
  .existsSlot (
    .and (.core (generate (armEnvironment Γ.lift (input.rename some)
      (sig.input.rename some) (sig.output.rename some)) onOperation (CompTerm.var none)))
      (.and (.core (.tyLe (.union (returned.ty.rename some) (.var none)) (out.ty.rename some)))
        (.rowLe (.union (.residual [sig.key] (fromCoreRow (input.row.rename some)))
          (.union (fromCoreRow (returned.row.rename some)) (.var none)))
          (fromCoreRow (out.row.rename some)))))

theorem operation_arm_constraints_exact [DecidableEq (SigKey F O A)]
    (view : RowView m (SigKey F O A)) (sΓ : SchemeEnv α) (Γ : List (Binding m))
    (ρ : α → Comp m) (henv : EnvRel m ρ sΓ Γ) (sig : Signature α F O A)
    (input returned out : CompTerm α) (onOperation : Expr) :
    (operationArmConstraints sΓ sig input returned out onOperation).Holds view ρ ↔
      ∃ operated, Typing m (semanticArmEnvironment m Γ (input.eval m ρ)
        (sig.input.eval m ρ) (sig.output.eval m ρ)) onOperation operated ∧
      m.subTy (m.union (returned.eval m ρ).1 operated.1) (out.eval m ρ).1 ∧
      RowSubset (residual [sig.key] (view.decode (input.eval m ρ).2) ++
        (view.decode (returned.eval m ρ).2 ++ view.decode operated.2))
        (view.decode (out.eval m ρ).2) := by
  have ho (operated : Comp m) :
      (generate (armEnvironment sΓ.lift (input.rename some) (sig.input.rename some)
        (sig.output.rename some)) onOperation (CompTerm.var none)).Holds m (extend ρ operated) ↔
      Typing m (semanticArmEnvironment m Γ (input.eval m ρ)
        (sig.input.eval m ρ) (sig.output.eval m ρ)) onOperation operated := by
    simpa using generate_models_iff_typing m onOperation _ _ (extend ρ operated)
      (CompTerm.var none) (armEnvironment_related m (extend ρ operated) sΓ.lift Γ
        (henv.lift operated) (input.rename some) (sig.input.rename some) (sig.output.rename some))
  simp only [operationArmConstraints, Constraint.Holds]
  apply exists_congr; intro operated
  rw [ho]
  simp [Formula.Holds, RowExpr.eval, rowEnv, CompTerm.eval, TyTerm.eval]

def polyHandlerConstraints (Γ : SchemeEnv α) (sig : PolySignature α n F O A)
    (action onReturn onOperation : Expr) (out : CompTerm α) : Constraint (SigKey F O A) α :=
  .existsSlot (.existsSlot (
    .and (.core (generate (env₂ Γ) action fresh₀))
      (.and (.core (generate (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ Γ) onReturn fresh₁))
        (.forallTypes n (operationArmConstraints ((env₂ Γ).rename Sum.inl)
          (sig.rename (fun x => some (some x))).mono
          (fresh₀.rename Sum.inl) (fresh₁.rename Sum.inl) ((lift₂ out).rename Sum.inl) onOperation)))))

/-- Independent rigid rule. The outer context, result, action type and return
arm type are fixed before quantifying over all local types. -/
inductive PolyHandlerTyping [DecidableEq (SigKey F O A)] (view : RowView m (SigKey F O A))
    (Γ : List (Binding m)) (key : SigKey F O A)
    (payload response : (Fin n → m.Ty) → m.Ty)
    (action onReturn onOperation : Expr) (out : Comp m) : Prop where
  | intro : Typing m Γ action input →
      Typing m (.mono (Comp.pure m input.1) :: Γ) onReturn returned →
      (∀ ι, ∃ operated,
        Typing m (semanticArmEnvironment m Γ input (payload ι) (response ι)) onOperation operated ∧
        m.subTy (m.union returned.1 operated.1) out.1 ∧
        RowSubset (residual [key] (view.decode input.2) ++
          (view.decode returned.2 ++ view.decode operated.2)) (view.decode out.2)) →
      PolyHandlerTyping view Γ key payload response action onReturn onOperation out

@[simp] theorem polyHandlerTyping_iff [DecidableEq (SigKey F O A)]
    (view : RowView m (SigKey F O A)) (Γ : List (Binding m)) (key : SigKey F O A)
    (payload response : (Fin n → m.Ty) → m.Ty)
    (action onReturn onOperation : Expr) (out : Comp m) :
    PolyHandlerTyping view Γ key payload response action onReturn onOperation out ↔
      ∃ input returned, Typing m Γ action input ∧
        Typing m (.mono (Comp.pure m input.1) :: Γ) onReturn returned ∧
        ∀ ι, ∃ operated,
          Typing m (semanticArmEnvironment m Γ input (payload ι) (response ι)) onOperation operated ∧
          m.subTy (m.union returned.1 operated.1) out.1 ∧
          RowSubset (residual [key] (view.decode input.2) ++
            (view.decode returned.2 ++ view.decode operated.2)) (view.decode out.2) := by
  constructor
  · intro h; cases h with | intro hi hr ho => exact ⟨_, _, hi, hr, ho⟩
  · rintro ⟨_, _, hi, hr, ho⟩; exact .intro hi hr ho

theorem poly_handler_constraints_exact [DecidableEq (SigKey F O A)]
    (view : RowView m (SigKey F O A)) (sΓ : SchemeEnv α) (Γ : List (Binding m))
    (ρ : α → Comp m) (henv : EnvRel m ρ sΓ Γ) (sig : PolySignature α n F O A)
    (action onReturn onOperation : Expr) (out : CompTerm α) :
    (polyHandlerConstraints sΓ sig action onReturn onOperation out).Holds view ρ ↔
      PolyHandlerTyping view Γ sig.key
        (fun ι => sig.input.eval m (localEnv m ρ ι))
        (fun ι => sig.output.eval m (localEnv m ρ ι))
        action onReturn onOperation (out.eval m ρ) := by
  have hi (input returned : Comp m) :
      (generate (env₂ sΓ) action fresh₀).Holds m (extend (extend ρ input) returned) ↔
      Typing m Γ action input := by
    simpa [env₂, fresh₀] using generate_models_iff_typing m action (env₂ sΓ) Γ
      (extend (extend ρ input) returned) fresh₀ ((henv.lift input).lift returned)
  have hr (input returned : Comp m) :
      (generate (Scheme.mono (CompTerm.pure fresh₀.ty) :: env₂ sΓ) onReturn fresh₁).Holds m
        (extend (extend ρ input) returned) ↔
      Typing m (.mono (Comp.pure m input.1) :: Γ) onReturn returned := by
    simpa [env₂, fresh₀, fresh₁, CompTerm.var, CompTerm.pure, CompTerm.eval,
      TyTerm.eval, RowTerm.eval, Comp.pure] using generate_models_iff_typing m onReturn _ _
        (extend (extend ρ input) returned) fresh₁
        (((henv.lift input).lift returned).mono (CompTerm.pure fresh₀.ty))
  simp only [polyHandlerConstraints, Constraint.Holds, polyHandlerTyping_iff]
  apply exists_congr; intro input
  apply exists_congr; intro returned
  rw [hi, hr]
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply forall_congr'; intro ι
  have ha := operation_arm_constraints_exact view ((env₂ sΓ).rename Sum.inl) Γ
    (localEnv m (extend (extend ρ input) returned) ι)
    (local_outer_environment m _ (env₂ sΓ) Γ ((henv.lift input).lift returned) ι)
    (sig.rename (fun x => some (some x))).mono
    (fresh₀.rename Sum.inl) (fresh₁.rename Sum.inl) ((lift₂ out).rename Sum.inl) onOperation
  have he : extend (extend ρ input) returned ∘ (fun x => some (some x)) = ρ := rfl
  simpa only [PolySignature.mono, PolySignature.rename, CompTerm.eval_rename,
    TyTerm.eval_rename, localEnv_comp_inl, localEnv_map, he, fresh₀, fresh₁, lift₂,
    CompTerm.eval_var, extend_some, extend_none] using ha

/--
The generated handler rule composes the independently supplied effect bounds
of its action and arms. These bounds are explicit premises: this theorem does
not assert a runtime interpretation of the core language. The operation premise
receives a continuation bounded by the ORIGINAL input row, not its residual.
-/
theorem generated_handler_composes_effect_bounds [DecidableEq (SigKey F O A)]
    (view : RowView m (SigKey F O A)) (sΓ : SchemeEnv α) (Γ : List (Binding m))
    (ρ : α → Comp m) (henv : EnvRel m ρ sΓ Γ) (sig : Signature α F O A)
    (action onReturn onOperation : Expr) (out : CompTerm α)
    (checked : (handlerConstraints sΓ sig action onReturn onOperation out).Holds view ρ)
    (computation : Computation (SigKey F O A) Payload Response Value)
    (returnRuntime : Value → Computation (SigKey F O A) Payload Response Result)
    (operationRuntime : Occurrence (SigKey F O A) → Payload →
      (Response → Computation (SigKey F O A) Payload Response Value) →
        Computation (SigKey F O A) Payload Response Result)
    (actionBound : ∀ input, Typing m Γ action input →
      Computation.BoundedBy (view.decode input.2) computation)
    (returnBound : ∀ (input returned : Comp m),
      Typing m (.mono (Comp.pure m input.1) :: Γ) onReturn returned →
      ∀ value, Computation.BoundedBy (view.decode returned.2) (returnRuntime value))
    (operationBound : ∀ (input operated : Comp m),
      Typing m (semanticArmEnvironment m Γ input (sig.input.eval m ρ) (sig.output.eval m ρ))
        onOperation operated →
      ∀ occurrence payload resume, Capturable [sig.key] occurrence →
        (∀ response, Computation.BoundedBy (view.decode input.2) (resume response)) →
        Computation.BoundedBy (view.decode operated.2) (operationRuntime occurrence payload resume)) :
    Computation.BoundedBy (view.decode (out.eval m ρ).2)
      (Computation.shallowHandle [sig.key] returnRuntime operationRuntime computation) := by
  have ht := (handler_constraints_exact view sΓ Γ ρ henv sig action onReturn onOperation out).mp checked
  rcases (handlerTyping_iff view Γ sig.key (sig.input.eval m ρ) (sig.output.eval m ρ)
    action onReturn onOperation (out.eval m ρ)).mp ht with
    ⟨input, returned, operated, hi, hr, ho, _, he⟩
  apply Computation.bounded_mono he
  apply Computation.shallowHandle_bounded [sig.key] (view.decode input.2)
    (view.decode returned.2 ++ view.decode operated.2) returnRuntime operationRuntime
  · intro value
    exact Computation.bounded_mono (fun _ h => List.mem_append.mpr (Or.inl h))
      (returnBound input returned hr value)
  · intro occurrence payload resume capturable resumeBound
    exact Computation.bounded_mono (fun _ h => List.mem_append.mpr (Or.inr h))
      (operationBound input operated ho occurrence payload resume capturable resumeBound)
  · exact actionBound input hi

/-- An arm that re-emits the handled operation keeps it in the output budget. -/
theorem reemitted_operation_is_not_subtracted [DecidableEq Key]
    (key : Key) (input returnEffects : Row Key) :
    ({key := key} : Occurrence Key) ∈ residual [key] input ++
      (returnEffects ++ [{key := key}]) := by
  simp

/-- Partial handling leaves a distinct operation, including one in the same
family, in the action's residual before any arm effects are added. -/
theorem other_operation_is_not_subtracted [DecidableEq (SigKey F O A)]
    (handled other : SigKey F O A) (different : other ≠ handled)
    (input returnEffects operationEffects : Row (SigKey F O A))
    (present : ({key := other} : Occurrence (SigKey F O A)) ∈ input) :
    ({key := other} : Occurrence (SigKey F O A)) ∈ residual [handled] input ++
      (returnEffects ++ operationEffects) := by
  apply List.mem_append.mpr
  apply Or.inl
  apply (mem_residual _ _ _).mpr
  refine ⟨present, ?_⟩
  simp [Capturable, different]

end Yulang.EffectInference
