import Yulang.CommonEffectMixedDeclarations

/-!
Independent typing for the unchanged recursive effect source with the finite
mixed-kind operation table. Ordinary constructors retain their existing rules;
requests instantiate both local sorts and handler arms quantify both rigidly.
The incoming environment, input computation, returned computation and final
result stay outside those binders. Resumptions retain the entire original
input row (shallow handling). This is resolved source: permissions and partial
arm coverage are explicit finite data, not newly inferred metadata.
-/
namespace Yulang.CommonEffectMixedSource
open Core.PresenceGeneration (Comp CompTerm TyTerm RowTerm)
open CommonEffectRequestGeneration (Computation Permission)
open CommonEffectKindedFormula (Locals)
open CommonEffectMixedDeclarations (SemanticSignature)
open Inference (Base)
export CommonEffectRecursiveSource (Expr Boundary)

def handlerKeys (signatures : List SemanticSignature) (operations : Fin count → Nat) : List Nat :=
  (List.finRange count).filterMap (fun i => (signatures[operations i]?).map (·.key))

def partialKeys (signatures : List SemanticSignature) (arms : Fin count → CommonEffectArmCoverage.Arm) : List Nat :=
  (List.finRange count).filterMap (fun i =>
    if (arms i).total then (signatures[(arms i).operation]?).map (·.key) else none)

variable {scopes : Nat}

inductive Binding (scopes : Nat) where
  | mono : Computation → Binding scopes
  | poly : Expr scopes → List (Binding scopes) → Binding scopes
  /-- An independently prescribed signature quantifies value types only.
  Inferred row assignments and the lexical environment are captured by
  `instantiate`; no fresh row assignment is supplied at a call. -/
  | signature (n : Nat) (instantiate : (Fin n → Common.Ty) → Computation) : Binding scopes
mutual
  inductive Typing (signatures : List SemanticSignature) : List (Binding scopes) → Expr scopes → Computation → Prop where
    | var : Γ[n]? = some b → BindingTyping signatures b c → Typing signatures Γ (.var n) c
    | lit : Comp.le Common.model (Comp.pure Common.model (Common.model.base b)) c → Typing signatures Γ (.lit b) c
    | lam : Typing signatures (.mono a :: Γ) body b →
        Comp.le Common.model (Comp.pure Common.model (Comp.arrow Common.model a b)) c → Typing signatures Γ (.lam body) c
    | app : Typing signatures Γ f (Comp.arrow Common.model a b, ef) → Typing signatures Γ x a →
        Comp.le Common.model (b.1, Common.model.join ef b.2) c → Typing signatures Γ (.app f x) c
    | letValue : v.isValue = true → Typing signatures Γ v (Comp.pure Common.model a) →
        Typing signatures (.poly v Γ :: Γ) body c → Typing signatures Γ (.letE v body) c
    | letComputed : Typing signatures Γ v a →
        Typing signatures (.mono (Comp.pure Common.model a.1) :: Γ) body b →
        Comp.le Common.model (b.1, Common.model.join a.2 b.2) c → Typing signatures Γ (.letE v body) c
    | branch : Typing signatures Γ condition (Common.model.base .bool, eg) →
        Typing signatures Γ yes a → Typing signatures Γ no b →
        Comp.le Common.model (Common.model.union a.1 b.1, Common.model.join eg (Common.model.join a.2 b.2)) c →
        Typing signatures Γ (.branch condition yes no) c
    | pair : Typing signatures Γ x a → Typing signatures Γ y b →
        Comp.le Common.model (Common.model.pair a.1 b.1, Common.model.join a.2 b.2) c → Typing signatures Γ (.pair x y) c
    | fst : Typing signatures Γ x (Common.model.pair a b, er) →
        Comp.le Common.model (a, er) c → Typing signatures Γ (.fst x) c
    | snd : Typing signatures Γ x (Common.model.pair a b, er) →
        Comp.le Common.model (b, er) c → Typing signatures Γ (.snd x) c
    | emptyRecord : Comp.le Common.model (Comp.pure Common.model Common.model.exactEmpty) c →
        Typing signatures Γ .emptyRecord c
    | record : Typing signatures Γ x a → Typing signatures Γ rest b → Common.model.subTy b.1 Common.model.emptyRecord →
        Comp.le Common.model (Common.model.record l a.1 b.1, Common.model.join a.2 b.2) c →
        Typing signatures Γ (.record l x rest) c
    /-- Both operands are checked; the base and fallback rows are joined even
    when the base already supplies the field. -/
    | recordDefault : Typing signatures Γ source a → Typing signatures Γ fallback b →
        Common.model.subTy a.1 Common.model.emptyRecord →
        Comp.le Common.model (Common.model.recordDefault l a.1 b.1, Common.model.join a.2 b.2) c →
        Typing signatures Γ (.recordDefault l source fallback) c
    | field : Typing signatures Γ x (Common.model.required l a, er) →
        Comp.le Common.model (a, er) c → Typing signatures Γ (.field l x) c
    | variant : Typing signatures Γ x a →
        Comp.le Common.model (Common.model.variant l a.1, a.2) c → Typing signatures Γ (.variant l x) c

    | request {signature : SemanticSignature} {locals : Locals signature.types signature.rows} :
        signatures[operation]? = some signature →
        Typing signatures Γ payload (signature.input locals, payloadRow) →
        Common.Subtype (signature.output locals) c.1 →
        Common.rowLe (Common.rowJoin payloadRow (Common.rowJoin
          ((CommonSignedRows.commonAlgebra scopes).head signature.key)
          (RowInference.keysRow (CommonSignedRows.commonAlgebra scopes) signature.extra))) c.2 →
        Typing signatures Γ (.request operation payload) c
    | boundary : Typing signatures Γ body input → Common.Subtype input.1 c.1 →
        Common.rowLe (boundary.eval input.2) c.2 → Typing signatures Γ (.boundary boundary body) c
    | handler {signature : SemanticSignature}
        {operated : (Locals signature.types signature.rows) → Computation} :
        signatures[operation]? = some signature → permission.allows signature.key = true →
        Typing signatures Γ action input →
        Typing signatures (.mono (Comp.pure Common.model input.1) :: Γ) onReturn returned →
        (∀ locals, Typing signatures
          (.mono (Comp.pure Common.model (signature.input locals)) ::
           .mono (Comp.pure Common.model (Comp.arrow Common.model
             (Comp.pure Common.model (signature.output locals)) input)) :: Γ) onOperation (operated locals)) →
        (∀ locals, Common.Subtype (.union returned.1 (operated locals).1) c.1) →
        (∀ locals, Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual [signature.key] input.2)
          (Common.rowJoin returned.2 (operated locals).2)) c.2) →
        Typing signatures Γ (.handler permission operation action onReturn onOperation) c
    | multiHandler {count : Nat} {operations : Fin count → Nat} {bodies : Fin count → Expr scopes}
        {armSignatures : Fin count → SemanticSignature}
        {operated : (i : Fin count) → (Locals (armSignatures i).types (armSignatures i).rows) → Computation} :
        (∀ i, signatures[operations i]? = some (armSignatures i)) →
        (∀ i, permission.allows (armSignatures i).key = true) →
        Typing signatures Γ action input →
        Typing signatures (.mono (Comp.pure Common.model input.1) :: Γ) onReturn returned →
        (∀ i locals, Typing signatures
          (.mono (Comp.pure Common.model ((armSignatures i).input locals)) ::
           .mono (Comp.pure Common.model (Comp.arrow Common.model
             (Comp.pure Common.model ((armSignatures i).output locals)) input)) :: Γ)
          (bodies i) (operated i locals)) →
        Common.Subtype returned.1 c.1 →
        Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual (handlerKeys signatures operations) input.2)
          returned.2) c.2 →
        (∀ i locals, Comp.le Common.model (operated i locals) c) →
        Typing signatures Γ (.multiHandler permission operations action onReturn bodies) c
    | partialHandler {count : Nat} {arms : Fin count → CommonEffectArmCoverage.Arm} {bodies : Fin count → Expr scopes}
        {armSignatures : Fin count → SemanticSignature}
        {operated : (i : Fin count) → (Locals (armSignatures i).types (armSignatures i).rows) → Computation} :
        (∀ i, signatures[(arms i).operation]? = some (armSignatures i)) →
        (∀ i, permission.allows (armSignatures i).key = true) →
        Typing signatures Γ action input →
        Typing signatures (.mono (Comp.pure Common.model input.1) :: Γ) onReturn returned →
        (∀ i locals, Typing signatures
          (.mono (Comp.pure Common.model ((armSignatures i).input locals)) ::
           .mono (Comp.pure Common.model (Comp.arrow Common.model
             (Comp.pure Common.model ((armSignatures i).output locals)) input)) :: Γ)
          (bodies i) (operated i locals)) →
        Common.Subtype returned.1 c.1 →
        Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual (partialKeys signatures arms) input.2)
          returned.2) c.2 →
        (∀ i locals, Comp.le Common.model (operated i locals) c) →
        Typing signatures Γ (.partialHandler permission arms action onReturn bodies) c

  inductive BindingTyping (signatures : List SemanticSignature) : Binding scopes → Computation → Prop where
    | mono : Comp.le Common.model a c → BindingTyping signatures (.mono a) c
    | poly : Typing signatures Γ v (Comp.pure Common.model c.1) → Common.model.subRow Common.model.empty c.2 →
        BindingTyping signatures (.poly v Γ) c
    | signature {n : Nat} {instantiate : (Fin n → Common.model.Ty) → Computation} {ι : Fin n → Common.model.Ty} :
        Comp.le Common.model (instantiate ι) c →
        BindingTyping signatures (.signature n instantiate) c
end

def BindingLookup (signatures : List SemanticSignature) (bindings : List (Binding scopes))
    (index : Nat) (out : Computation) : Prop :=
  ∃ binding, bindings[index]? = some binding ∧ BindingTyping signatures binding out

@[simp] theorem BindingTyping.mono_iff (signatures : List SemanticSignature) (a c : Computation) :
    BindingTyping (scopes := scopes) signatures (.mono a) c ↔ Comp.le Common.model a c := by
  constructor
  · intro h; cases h with | mono h => exact h
  · exact BindingTyping.mono

@[simp] theorem BindingTyping.poly_iff (signatures : List SemanticSignature) (Γ : List (Binding scopes))
    (v : Expr scopes) (c : Computation) :
    BindingTyping signatures (.poly v Γ) c ↔
      Typing signatures Γ v (Comp.pure Common.model c.1) ∧ Common.model.subRow Common.model.empty c.2 := by
  constructor
  · intro h; cases h with | poly hv he => exact ⟨hv, he⟩
  · rintro ⟨hv, he⟩; exact BindingTyping.poly hv he

@[simp] theorem BindingTyping.signature_iff (signatures : List SemanticSignature) (n : Nat)
    (instantiate : (Fin n → Common.model.Ty) → Computation) (c : Computation) :
    BindingTyping (scopes := scopes) signatures (.signature n instantiate) c ↔ ∃ ι, Comp.le Common.model (instantiate ι) c := by
  constructor
  · intro h; cases h with | signature hc => exact ⟨_, hc⟩
  · rintro ⟨ι, hc⟩; exact BindingTyping.signature hc

@[simp] theorem Typing.var_iff (signatures : List SemanticSignature) (Γ : List (Binding scopes)) (n : Nat) (c : Computation) :
    Typing signatures Γ (.var n) c ↔ BindingLookup signatures Γ n c := by
  constructor
  · intro h
    cases h with | var hget hb => exact ⟨_, hget, hb⟩
  · rintro ⟨b, hget, hb⟩
    exact Typing.var hget hb

/-- Strict default extension retains the full constructor result and both rows. -/
@[simp] theorem Typing.recordDefault_iff (signatures : List SemanticSignature) (Γ : List (Binding scopes))
    (l : Nat) (source fallback : Expr scopes) (c : Computation) :
    Typing signatures Γ (.recordDefault l source fallback) c ↔ ∃ a b,
      Typing signatures Γ source a ∧ Typing signatures Γ fallback b ∧ Common.model.subTy a.1 Common.model.emptyRecord ∧
      Comp.le Common.model (Common.model.recordDefault l a.1 b.1, Common.model.join a.2 b.2) c := by
  constructor
  · intro h; cases h with | recordDefault ha hb hs hc => exact ⟨_, _, ha, hb, hs, hc⟩
  · rintro ⟨a, b, ha, hb, hs, hc⟩; exact Typing.recordDefault ha hb hs hc

@[simp] theorem Typing.lit_iff (signatures : List SemanticSignature) (Γ : List (Binding scopes)) (b : Base) (c : Computation) :
    Typing signatures Γ (.lit b) c ↔ Comp.le Common.model (Comp.pure Common.model (Common.model.base b)) c := by
  constructor
  · intro h; cases h with | lit h => exact h
  · exact Typing.lit

@[simp] theorem Typing.lam_iff (signatures : List SemanticSignature) (Γ : List (Binding scopes)) (body : Expr scopes) (c : Computation) :
    Typing signatures Γ (.lam body) c ↔ ∃ a b,
      Typing signatures (.mono a :: Γ) body b ∧
      Comp.le Common.model (Comp.pure Common.model (Comp.arrow Common.model a b)) c := by
  constructor
  · intro h; cases h with | lam hb hc => exact ⟨_, _, hb, hc⟩
  · rintro ⟨a, b, hb, hc⟩; exact Typing.lam hb hc

@[simp] theorem Typing.app_iff (signatures : List SemanticSignature) (Γ : List (Binding scopes)) (f x : Expr scopes) (c : Computation) :
    Typing signatures Γ (.app f x) c ↔ ∃ a b ef,
      Typing signatures Γ f (Comp.arrow Common.model a b, ef) ∧ Typing signatures Γ x a ∧
      Comp.le Common.model (b.1, Common.model.join ef b.2) c := by
  constructor
  · intro h; cases h with | app hf hx hc => exact ⟨_, _, _, hf, hx, hc⟩
  · rintro ⟨a, b, ef, hf, hx, hc⟩; exact Typing.app hf hx hc

theorem Typing.letValue_iff (signatures : List SemanticSignature) (Γ : List (Binding scopes)) (v body : Expr scopes) (c : Computation)
    (hv : v.isValue = true) :
    Typing signatures Γ (.letE v body) c ↔
      ((∃ a, Typing signatures Γ v (Comp.pure Common.model a)) ∧ Typing signatures (.poly v Γ :: Γ) body c) ∨
      ∃ a b, Typing signatures Γ v a ∧ Typing signatures (.mono (Comp.pure Common.model a.1) :: Γ) body b ∧
        Comp.le Common.model (b.1, Common.model.join a.2 b.2) c := by
  constructor
  · intro h
    cases h with
    | letValue _ ha hb => exact Or.inl ⟨⟨_, ha⟩, hb⟩
    | letComputed ha hb hc => exact Or.inr ⟨_, _, ha, hb, hc⟩
  · intro h
    rcases h with ⟨⟨a, ha⟩, hb⟩ | ⟨a, b, ha, hb, hc⟩
    · exact Typing.letValue hv ha hb
    · exact Typing.letComputed ha hb hc

theorem Typing.letComputed_iff (signatures : List SemanticSignature) (Γ : List (Binding scopes)) (v body : Expr scopes) (c : Computation)
    (hv : v.isValue = false) :
    Typing signatures Γ (.letE v body) c ↔ ∃ a b,
      Typing signatures Γ v a ∧ Typing signatures (.mono (Comp.pure Common.model a.1) :: Γ) body b ∧
      Comp.le Common.model (b.1, Common.model.join a.2 b.2) c := by
  constructor
  · intro h
    cases h with
    | letValue hn _ _ => simp [hv] at hn
    | letComputed ha hb hc => exact ⟨_, _, ha, hb, hc⟩
  · rintro ⟨a, b, ha, hb, hc⟩
    exact Typing.letComputed ha hb hc

@[simp] theorem Typing.branch_iff (signatures : List SemanticSignature) (Γ : List (Binding scopes)) (g y n : Expr scopes) (c : Computation) :
    Typing signatures Γ (.branch g y n) c ↔ ∃ eg a b,
      Typing signatures Γ g (Common.model.base .bool, eg) ∧ Typing signatures Γ y a ∧ Typing signatures Γ n b ∧
      Comp.le Common.model (Common.model.union a.1 b.1, Common.model.join eg (Common.model.join a.2 b.2)) c := by
  constructor
  · intro h; cases h with | branch hg hy hn hc => exact ⟨_, _, _, hg, hy, hn, hc⟩
  · rintro ⟨eg, a, b, hg, hy, hn, hc⟩; exact Typing.branch hg hy hn hc

@[simp] theorem Typing.pair_iff (signatures : List SemanticSignature) (Γ : List (Binding scopes)) (x y : Expr scopes) (c : Computation) :
    Typing signatures Γ (.pair x y) c ↔ ∃ a b,
      Typing signatures Γ x a ∧ Typing signatures Γ y b ∧
      Comp.le Common.model (Common.model.pair a.1 b.1, Common.model.join a.2 b.2) c := by
  constructor
  · intro h; cases h with | pair hx hy hc => exact ⟨_, _, hx, hy, hc⟩
  · rintro ⟨a, b, hx, hy, hc⟩; exact Typing.pair hx hy hc

@[simp] theorem Typing.fst_iff (signatures : List SemanticSignature) (Γ : List (Binding scopes)) (x : Expr scopes) (c : Computation) :
    Typing signatures Γ (.fst x) c ↔ ∃ a b er,
      Typing signatures Γ x (Common.model.pair a b, er) ∧ Comp.le Common.model (a, er) c := by
  constructor
  · intro h; cases h with | fst hx hc => exact ⟨_, _, _, hx, hc⟩
  · rintro ⟨a, b, er, hx, hc⟩; exact Typing.fst hx hc

@[simp] theorem Typing.snd_iff (signatures : List SemanticSignature) (Γ : List (Binding scopes)) (x : Expr scopes) (c : Computation) :
    Typing signatures Γ (.snd x) c ↔ ∃ a b er,
      Typing signatures Γ x (Common.model.pair a b, er) ∧ Comp.le Common.model (b, er) c := by
  constructor
  · intro h; cases h with | snd hx hc => exact ⟨_, _, _, hx, hc⟩
  · rintro ⟨a, b, er, hx, hc⟩; exact Typing.snd hx hc

@[simp] theorem Typing.emptyRecord_iff (signatures : List SemanticSignature) (Γ : List (Binding scopes)) (c : Computation) :
    Typing signatures Γ .emptyRecord c ↔ Comp.le Common.model (Comp.pure Common.model Common.model.exactEmpty) c := by
  constructor
  · intro h; cases h with | emptyRecord h => exact h
  · exact Typing.emptyRecord

@[simp] theorem Typing.record_iff (signatures : List SemanticSignature) (Γ : List (Binding scopes))
    (l : Nat) (x r : Expr scopes) (c : Computation) :
    Typing signatures Γ (.record l x r) c ↔ ∃ a b,
      Typing signatures Γ x a ∧ Typing signatures Γ r b ∧ Common.model.subTy b.1 Common.model.emptyRecord ∧
      Comp.le Common.model (Common.model.record l a.1 b.1, Common.model.join a.2 b.2) c := by
  constructor
  · intro h; cases h with | record hx hr hs hc => exact ⟨_, _, hx, hr, hs, hc⟩
  · rintro ⟨a, b, hx, hr, hs, hc⟩; exact Typing.record hx hr hs hc

@[simp] theorem Typing.field_iff (signatures : List SemanticSignature) (Γ : List (Binding scopes))
    (l : Nat) (x : Expr scopes) (c : Computation) :
    Typing signatures Γ (.field l x) c ↔ ∃ a er,
      Typing signatures Γ x (Common.model.required l a, er) ∧ Comp.le Common.model (a, er) c := by
  constructor
  · intro h; cases h with | field hx hc => exact ⟨_, _, hx, hc⟩
  · rintro ⟨a, er, hx, hc⟩; exact Typing.field hx hc

@[simp] theorem Typing.variant_iff (signatures : List SemanticSignature) (Γ : List (Binding scopes))
    (l : Nat) (x : Expr scopes) (c : Computation) :
    Typing signatures Γ (.variant l x) c ↔ ∃ a,
      Typing signatures Γ x a ∧ Comp.le Common.model (Common.model.variant l a.1, a.2) c := by
  constructor
  · intro h; cases h with | variant hx hc => exact ⟨_, hx, hc⟩
  · rintro ⟨a, hx, hc⟩; exact Typing.variant hx hc


/-- Constructor inversion exposes exactly the intended quantifier order.
The function in the inductive rule is only a choice of these arm witnesses. -/
theorem Typing.handler_iff (signatures : List SemanticSignature) (environment : List (Binding scopes))
    (permission : Permission) (operation : Nat) (action onReturn onOperation : Expr scopes) (out : Computation) :
    Typing signatures environment (.handler permission operation action onReturn onOperation) out ↔
      ∃ signature, signatures[operation]? = some signature ∧ permission.allows signature.key = true ∧
      ∃ input returned,
        Typing signatures environment action input ∧
        Typing signatures (.mono (Comp.pure Common.model input.1) :: environment) onReturn returned ∧
        ∀ locals : Locals signature.types signature.rows, ∃ operated : Computation,
          Typing signatures
            (.mono (Comp.pure Common.model (signature.input locals)) ::
             .mono (Comp.pure Common.model (Comp.arrow Common.model
               (Comp.pure Common.model (signature.output locals)) input)) :: environment) onOperation operated ∧
          Common.Subtype (.union returned.1 operated.1) out.1 ∧
          Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual [signature.key] input.2)
            (Common.rowJoin returned.2 operated.2)) out.2 := by
  constructor
  · intro typed
    cases typed with
    | handler found permitted actionTyped returnTyped armTyped values rows =>
      exact ⟨_, found, permitted, _, _, actionTyped, returnTyped,
        fun locals => ⟨_, armTyped locals, values locals, rows locals⟩⟩
  · rintro ⟨signature, found, permitted, input, returned, actionTyped, returnTyped, arms⟩
    exact Typing.handler (operated := fun locals => Classical.choose (arms locals)) found permitted actionTyped returnTyped
      (fun locals => (Classical.choose_spec (arms locals)).1)
      (fun locals => (Classical.choose_spec (arms locals)).2.1)
      (fun locals => (Classical.choose_spec (arms locals)).2.2)

theorem Typing.request_iff (signatures : List SemanticSignature) (environment : List (Binding scopes))
    (operation : Nat) (payload : Expr scopes) (out : Computation) :
    Typing signatures environment (.request operation payload) out ↔
      ∃ signature, signatures[operation]? = some signature ∧
      ∃ locals : Locals signature.types signature.rows, ∃ row : Common.Row,
        Typing signatures environment payload (signature.input locals, row) ∧
        Common.Subtype (signature.output locals) out.1 ∧
        Common.rowLe (Common.rowJoin row (Common.rowJoin
          ((CommonSignedRows.commonAlgebra scopes).head signature.key)
          (RowInference.keysRow (CommonSignedRows.commonAlgebra scopes) signature.extra))) out.2 := by
  constructor
  · intro typed
    cases typed with
    | request found payloadTyped value row => exact ⟨_, found, _, _, payloadTyped, value, row⟩
  · rintro ⟨signature, found, locals, row, payloadTyped, valueBound, rowBound⟩
    exact .request (locals := locals) found payloadTyped valueBound rowBound

theorem Typing.boundary_iff (signatures : List SemanticSignature) (environment : List (Binding scopes))
    (boundary : Boundary scopes) (body : Expr scopes) (out : Computation) :
    Typing signatures environment (.boundary boundary body) out ↔
      ∃ input, Typing signatures environment body input ∧ Common.Subtype input.1 out.1 ∧
        Common.rowLe (boundary.eval input.2) out.2 := by
  constructor
  · intro typed
    cases typed with | boundary typed value row => exact ⟨_, typed, value, row⟩
  · rintro ⟨input, typed, value, row⟩
    exact .boundary typed value row
/-- The return and residual bounds stay outside the universal arms, including
the zero-arm case. Each local type may choose only its own arm result. -/
theorem Typing.multiHandler_iff (signatures : List SemanticSignature) (environment : List (Binding scopes))
    (permission : Permission) (operations : Fin count → Nat) (action onReturn : Expr scopes)
    (bodies : Fin count → Expr scopes) (out : Computation) :
    Typing signatures environment (.multiHandler permission operations action onReturn bodies) out ↔
      ∃ armSignatures : Fin count → SemanticSignature,
      (∀ i, signatures[operations i]? = some (armSignatures i)) ∧
      (∀ i, permission.allows (armSignatures i).key = true) ∧
      ∃ input returned,
        Typing signatures environment action input ∧
        Typing signatures (.mono (Comp.pure Common.model input.1) :: environment) onReturn returned ∧
        Common.Subtype returned.1 out.1 ∧
        Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual (handlerKeys signatures operations) input.2)
          returned.2) out.2 ∧
        ∀ i, ∀ locals : Locals (armSignatures i).types (armSignatures i).rows, ∃ operated : Computation,
          Typing signatures
            (.mono (Comp.pure Common.model ((armSignatures i).input locals)) ::
             .mono (Comp.pure Common.model (Comp.arrow Common.model
               (Comp.pure Common.model ((armSignatures i).output locals)) input)) :: environment) (bodies i) operated ∧
          Comp.le Common.model operated out := by
  constructor
  · intro typed
    cases typed with
    | multiHandler found allowed actionTyped returnTyped arms values rows bounds =>
      exact ⟨_, found, allowed, _, _, actionTyped, returnTyped, values, rows,
        fun i locals => ⟨_, arms i locals, bounds i locals⟩⟩
  · rintro ⟨armSignatures, found, allowed, input, returned, actionTyped, returnTyped, values, rows, arms⟩
    exact Typing.multiHandler (operated := fun i locals => Classical.choose (arms i locals))
      found allowed actionTyped returnTyped (fun i locals => (Classical.choose_spec (arms i locals)).1)
      values rows (fun i locals => (Classical.choose_spec (arms i locals)).2)
theorem Typing.multiHandler_separate_iff (signatures : List SemanticSignature) (environment : List (Binding scopes))
    (permission : Permission) (operations : Fin count → Nat) (action onReturn : Expr scopes)
    (bodies : Fin count → Expr scopes) (out : Computation) :
    Typing signatures environment (.multiHandler permission operations action onReturn bodies) out ↔
      ∃ input returned,
        Typing signatures environment action input ∧
        Typing signatures (.mono (Comp.pure Common.model input.1) :: environment) onReturn returned ∧
        Common.Subtype returned.1 out.1 ∧
        Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual (handlerKeys signatures operations) input.2)
          returned.2) out.2 ∧
        ∀ i, ∃ signature, signatures[operations i]? = some signature ∧ permission.allows signature.key = true ∧
          ∀ locals : Locals signature.types signature.rows, ∃ operated : Computation,
            Typing signatures
              (.mono (Comp.pure Common.model (signature.input locals)) ::
               .mono (Comp.pure Common.model (Comp.arrow Common.model
                 (Comp.pure Common.model (signature.output locals)) input)) :: environment) (bodies i) operated ∧
            Comp.le Common.model operated out := by
  rw [Typing.multiHandler_iff]
  constructor
  · rintro ⟨sigs, found, allowed, input, returned, ha, hr, hv, he, arms⟩
    exact ⟨input, returned, ha, hr, hv, he, fun i => ⟨sigs i, found i, allowed i, arms i⟩⟩
  · rintro ⟨input, returned, ha, hr, hv, he, arms⟩
    refine ⟨fun i => Classical.choose (arms i), fun i => (Classical.choose_spec (arms i)).1,
      fun i => (Classical.choose_spec (arms i)).2.1, input, returned, ha, hr, hv, he, ?_⟩
    exact fun i => (Classical.choose_spec (arms i)).2.2
theorem Typing.partialHandler_iff (signatures : List SemanticSignature) (environment : List (Binding scopes))
    (permission : Permission) (operations : Fin count → CommonEffectArmCoverage.Arm) (action onReturn : Expr scopes)
    (bodies : Fin count → Expr scopes) (out : Computation) :
    Typing signatures environment (.partialHandler permission operations action onReturn bodies) out ↔
      ∃ armSignatures : Fin count → SemanticSignature,
      (∀ i, signatures[(operations i).operation]? = some (armSignatures i)) ∧
      (∀ i, permission.allows (armSignatures i).key = true) ∧
      ∃ input returned,
        Typing signatures environment action input ∧
        Typing signatures (.mono (Comp.pure Common.model input.1) :: environment) onReturn returned ∧
        Common.Subtype returned.1 out.1 ∧
        Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual (partialKeys signatures operations) input.2)
          returned.2) out.2 ∧
        ∀ i, ∀ locals : Locals (armSignatures i).types (armSignatures i).rows, ∃ operated : Computation,
          Typing signatures
            (.mono (Comp.pure Common.model ((armSignatures i).input locals)) ::
             .mono (Comp.pure Common.model (Comp.arrow Common.model
               (Comp.pure Common.model ((armSignatures i).output locals)) input)) :: environment) (bodies i) operated ∧
          Comp.le Common.model operated out := by
  constructor
  · intro typed
    cases typed with
    | partialHandler found allowed actionTyped returnTyped arms values rows bounds =>
      exact ⟨_, found, allowed, _, _, actionTyped, returnTyped, values, rows,
        fun i locals => ⟨_, arms i locals, bounds i locals⟩⟩
  · rintro ⟨armSignatures, found, allowed, input, returned, actionTyped, returnTyped, values, rows, arms⟩
    exact Typing.partialHandler (operated := fun i locals => Classical.choose (arms i locals))
      found allowed actionTyped returnTyped (fun i locals => (Classical.choose_spec (arms i locals)).1)
      values rows (fun i locals => (Classical.choose_spec (arms i locals)).2)
theorem Typing.partialHandler_separate_iff (signatures : List SemanticSignature) (environment : List (Binding scopes))
    (permission : Permission) (operations : Fin count → CommonEffectArmCoverage.Arm) (action onReturn : Expr scopes)
    (bodies : Fin count → Expr scopes) (out : Computation) :
    Typing signatures environment (.partialHandler permission operations action onReturn bodies) out ↔
      ∃ input returned,
        Typing signatures environment action input ∧
        Typing signatures (.mono (Comp.pure Common.model input.1) :: environment) onReturn returned ∧
        Common.Subtype returned.1 out.1 ∧
        Common.rowLe (Common.rowJoin (CommonSignedRows.commonResidual (partialKeys signatures operations) input.2)
          returned.2) out.2 ∧
        ∀ i, ∃ signature, signatures[(operations i).operation]? = some signature ∧ permission.allows signature.key = true ∧
          ∀ locals : Locals signature.types signature.rows, ∃ operated : Computation,
            Typing signatures
              (.mono (Comp.pure Common.model (signature.input locals)) ::
               .mono (Comp.pure Common.model (Comp.arrow Common.model
                 (Comp.pure Common.model (signature.output locals)) input)) :: environment) (bodies i) operated ∧
            Comp.le Common.model operated out := by
  rw [Typing.partialHandler_iff]
  constructor
  · rintro ⟨sigs, found, allowed, input, returned, ha, hr, hv, he, arms⟩
    exact ⟨input, returned, ha, hr, hv, he, fun i => ⟨sigs i, found i, allowed i, arms i⟩⟩
  · rintro ⟨input, returned, ha, hr, hv, he, arms⟩
    refine ⟨fun i => Classical.choose (arms i), fun i => (Classical.choose_spec (arms i)).1,
      fun i => (Classical.choose_spec (arms i)).2.1, input, returned, ha, hr, hv, he, ?_⟩
    exact fun i => (Classical.choose_spec (arms i)).2.2
end Yulang.CommonEffectMixedSource
