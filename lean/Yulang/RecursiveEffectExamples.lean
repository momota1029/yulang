import Yulang.RecursiveEffects
import Yulang.SignedStructural

/-!
# Nested effects in the principal constraint generator

These examples use the actual signed-row model, with a unit-to-unit operation
for each natural-number key. They exercise effects inside handlers, operation
arms, lambda bodies, applications and computed bindings. Rejection quantifies
over every possible intermediate typing, rather than only one chosen witness.

The expressions are resolved core terms with explicit boundary transports; no
surface elaboration or operation-local polymorphism is asserted here.
-/

namespace Yulang.RecursiveEffects.Examples

open Inference (Base Comp CompTerm TyTerm RowTerm)
open SignedStructural (model rowView RowLe row_refl row_bottom)
open Directed (raw protect release allowNone Capturable Occurrence)

private abbrev M := model 1 Nat
private abbrev V := rowView 1 Nat
private abbrev ValueType := SignedStructural.Ty 1 Nat
private abbrev Term := Expr Nat Nat (Fin 1)
private abbrev Context := List (Binding M Nat Nat (Fin 1))

def scope : Fin 1 := 0

def signatures : Nat → Signature M Nat :=
  fun key => ⟨key, [], .base .unit, .base .unit⟩

def symbolicSignatures : Signatures Nat Nat α :=
  fun key => ⟨key, [], .base .unit, .base .unit⟩

theorem signatures_related (ρ : α → Comp M) :
    SigRel M ρ symbolicSignatures signatures := fun _ => rfl

private theorem literal_typed (Γ : Context) (base : Base) :
    Typing M V signatures Γ (.lit base) (.base base, []) :=
  .lit ⟨.refl _, row_refl _⟩

private theorem zero_var_typed (Γ : Context) (c : Comp M) :
    Typing M V signatures (.mono c :: Γ) (.var 0) c :=
  .var rfl (.mono ⟨.refl _, row_refl _⟩)

def signal (key : Nat) : Term := .request key (.lit .unit)

private theorem signal_typed (Γ : Context) (key : Nat) :
    Typing M V signatures Γ (signal key) (.base .unit, [raw key]) := by
  apply Typing.request (er := [])
  · exact literal_typed Γ .unit
  · exact .refl _
  · exact row_refl _

/-- Every typing of an operation call retains the operation's raw occurrence. -/
theorem signal_present (Γ : Context) (key : Nat) (c : Comp M)
    (typed : Typing M V signatures Γ (signal key) c) : List.Mem (raw (n := 1) key) c.2 := by
  cases typed with
  | request _ _ inclusion =>
      exact inclusion _ (by simp [signatures, RowInference.signedAlgebra, RowInference.keysRow])

/-- The first handler's arm requests a distinct operation. -/
def inner : Term := .handler 0 (signal 0) (.var 0) (signal 1)

/-- The outer handler processes the request emitted by the inner arm. -/
def nested : Term := .handler 1 inner (.var 0) (.lit .unit)

theorem inner_typed (Γ : Context) :
    Typing M V signatures Γ inner (.base .unit, [raw 1]) := by
  apply Typing.handler (m := M) (view := V) (sigs := signatures) (input := (.base .unit, [raw 0]))
    (returned := (.base .unit, [])) (operated := (.base .unit, [raw 1]))
  · exact signal_typed Γ 0
  · exact zero_var_typed Γ _
  · exact signal_typed _ 1
  · exact .unionElim (.refl _) (.refl _)
  · change RowLe (Directed.residual [0] [raw 0] ++ ([] ++ [raw 1])) [raw 1]
    simpa [Directed.residual, Capturable, raw] using row_refl [raw (n := 1) 1]

theorem nested_typed (Γ : Context) :
    Typing M V signatures Γ nested (.base .unit, []) := by
  apply Typing.handler (m := M) (view := V) (sigs := signatures) (input := (.base .unit, [raw 1]))
    (returned := (.base .unit, [])) (operated := (.base .unit, []))
  · exact inner_typed Γ
  · exact zero_var_typed Γ _
  · exact literal_typed _ .unit
  · exact .unionElim (.refl _) (.refl _)
  · change RowLe (Directed.residual [1] [raw 1] ++ ([] ++ [])) []
    simpa [Directed.residual, Capturable, raw] using row_refl ([] : Directed.Row 1 Nat)

theorem generated_nested_handler_pure :
    (generate (symbolicSignatures (α := Unit)) [] nested (CompTerm.pure (.base .unit))).Holds
      M V (fun _ => (.base .unit, [])) := by
  apply (generate_models_iff_typing M V signatures nested _ [] [] _ _
    (EnvRel.nil _ _ _ _) (signatures_related _)).mpr
  exact nested_typed []

/-- Handling key 0 does not subtract a new key 0 emitted by its own arm. -/
def reemitting : Term := .handler 0 (signal 0) (.var 0) (signal 0)

theorem reemitting_present (Γ : Context) (c : Comp M)
    (typed : Typing M V signatures Γ reemitting c) : List.Mem (raw (n := 1) 0) c.2 := by
  cases typed with
  | handler _ _ operated _ inclusion =>
      exact inclusion _ (List.mem_append.mpr (Or.inr
        (List.mem_append.mpr (Or.inr (signal_present _ 0 _ operated)))))

theorem generated_reemitting_handler_not_pure (result : TyTerm Unit)
    (ρ : Unit → Comp M) :
    ¬ (generate symbolicSignatures [] reemitting (CompTerm.pure result)).Holds M V ρ := by
  intro checked
  have typed := (generate_models_iff_typing M V signatures reemitting _ [] [] ρ _
    (EnvRel.nil _ _ _ _) (signatures_related _)).mp checked
  have impossible := reemitting_present [] _ typed
  cases impossible

private def transport (boundary : RowInference.Boundary Nat (Fin 1))
    (occurrence : Occurrence 1 Nat) : Occurrence 1 Nat :=
  match boundary with
  | .protect boundary mask => protect boundary mask occurrence
  | .release boundary mask => release boundary mask occurrence

private theorem transported_signal_typed (Γ : Context)
    (boundary : RowInference.Boundary Nat (Fin 1)) (key : Nat) :
    Typing M V signatures Γ (.boundary boundary (signal key))
      (.base .unit, [transport boundary (raw key)]) := by
  apply Typing.boundary (m := M) (view := V) (sigs := signatures)
    (input := (.base .unit, [raw key]))
  · exact signal_typed Γ key
  · exact .refl _
  · cases boundary <;> exact row_refl _

private theorem transported_signal_present (Γ : Context)
    (boundary : RowInference.Boundary Nat (Fin 1)) (key : Nat) (c : Comp M)
    (typed : Typing M V signatures Γ (.boundary boundary (signal key)) c) :
    List.Mem (transport boundary (raw key)) c.2 := by
  cases typed with
  | boundary body _ inclusion =>
      have member := signal_present Γ key _ body
      cases boundary with
      | protect boundary mask =>
          exact inclusion _ (List.mem_map.mpr ⟨raw key, member, rfl⟩)
      | release boundary mask =>
          exact inclusion _ (List.mem_map.mpr ⟨raw key, member, rfl⟩)

/-- Both the protected and negative-debt request must pass through the handler. -/
def maskedHandler (boundary : RowInference.Boundary Nat (Fin 1)) : Term :=
  .handler 0 (.boundary boundary (signal 0)) (.var 0) (.lit .unit)

private theorem masked_handler_typed (Γ : Context)
    (boundary : RowInference.Boundary Nat (Fin 1))
    (blocked : ¬ Capturable [0] (transport boundary (raw 0))) :
    Typing M V signatures Γ (maskedHandler boundary)
      (.base .unit, [transport boundary (raw 0)]) := by
  apply Typing.handler (m := M) (view := V) (sigs := signatures)
    (input := (.base .unit, [transport boundary (raw 0)]))
    (returned := (.base .unit, [])) (operated := (.base .unit, []))
  · exact transported_signal_typed Γ boundary 0
  · exact zero_var_typed Γ _
  · exact literal_typed _ .unit
  · exact .unionElim (.refl _) (.refl _)
  · change RowLe (Directed.residual [0] [transport boundary (raw 0)] ++ ([] ++ []))
      [transport boundary (raw 0)]
    simpa [Directed.residual, blocked] using row_refl [transport boundary (raw 0)]

private theorem masked_handler_present (Γ : Context)
    (boundary : RowInference.Boundary Nat (Fin 1))
    (blocked : ¬ Capturable [0] (transport boundary (raw 0))) (c : Comp M)
    (typed : Typing M V signatures Γ (maskedHandler boundary) c) :
    List.Mem (transport boundary (raw 0)) c.2 := by
  cases typed with
  | handler body _ _ _ inclusion =>
      have member := transported_signal_present Γ boundary 0 _ body
      apply inclusion
      apply List.mem_append.mpr
      left
      change List.Mem _ (List.filter (fun occurrence => !decide (Capturable [0] occurrence)) _)
      exact List.mem_filter.mpr ⟨member, by simp [blocked]⟩

theorem protected_handler_present (Γ : Context) (c : Comp M)
    (typed : Typing M V signatures Γ (maskedHandler (.protect scope allowNone)) c) :
    List.Mem (protect scope allowNone (raw 0)) c.2 :=
  masked_handler_present Γ _
    (Directed.protected_not_capturable [0] scope allowNone (raw 0) rfl rfl) c typed

theorem negative_debt_handler_present (Γ : Context) (c : Comp M)
    (typed : Typing M V signatures Γ (maskedHandler (.release scope allowNone)) c) :
    List.Mem (release scope allowNone (raw 0)) c.2 :=
  masked_handler_present Γ _
    (Directed.negative_debt_not_capturable [0] scope allowNone (raw 0) rfl rfl) c typed

theorem generated_protected_handler_retains_guard :
    (generate (symbolicSignatures (α := Unit)) [] (maskedHandler (.protect scope allowNone))
      ⟨.base .unit, .var ()⟩).Holds M V
        (fun _ => (.base .unit, [protect scope allowNone (raw 0)])) := by
  apply (generate_models_iff_typing M V signatures _ _ [] [] _ _
    (EnvRel.nil _ _ _ _) (signatures_related _)).mpr
  exact masked_handler_typed [] _
    (Directed.protected_not_capturable [0] scope allowNone (raw 0) rfl rfl)

theorem generated_negative_debt_handler_retains_debt :
    (generate (symbolicSignatures (α := Unit)) [] (maskedHandler (.release scope allowNone))
      ⟨.base .unit, .var ()⟩).Holds M V
        (fun _ => (.base .unit, [release scope allowNone (raw 0)])) := by
  apply (generate_models_iff_typing M V signatures _ _ [] [] _ _
    (EnvRel.nil _ _ _ _) (signatures_related _)).mpr
  exact masked_handler_typed [] _
    (Directed.negative_debt_not_capturable [0] scope allowNone (raw 0) rfl rfl)

theorem generated_protected_handler_cannot_erase (result : TyTerm Unit) (ρ : Unit → Comp M) :
    ¬ (generate symbolicSignatures [] (maskedHandler (.protect scope allowNone))
      (CompTerm.pure result)).Holds M V ρ := by
  intro checked
  have typed := (generate_models_iff_typing M V signatures _ _ [] [] ρ _
    (EnvRel.nil _ _ _ _) (signatures_related _)).mp checked
  have impossible := protected_handler_present [] _ typed
  cases impossible

theorem generated_negative_debt_cannot_erase (result : TyTerm Unit) (ρ : Unit → Comp M) :
    ¬ (generate symbolicSignatures [] (maskedHandler (.release scope allowNone))
      (CompTerm.pure result)).Holds M V ρ := by
  intro checked
  have typed := (generate_models_iff_typing M V signatures _ _ [] [] ρ _
    (EnvRel.nil _ _ _ _) (signatures_related _)).mp checked
  have impossible := negative_debt_handler_present [] _ typed
  cases impossible

/-- An effectful argument is a computation; an ignoring lambda does not force it. -/
def ignoredArgument : Term := .app (.lam (.lit .unit)) (signal 0)

theorem ignored_argument_typed (Γ : Context) :
    Typing M V signatures Γ ignoredArgument (.base .unit, []) := by
  apply Typing.app (m := M) (view := V) (sigs := signatures) (a := (.base .unit, [raw 0])) (b := (.base .unit, [])) (ef := [])
  · exact .lam (literal_typed _ .unit) ⟨.refl _, row_refl _⟩
  · exact signal_typed Γ 0
  · exact ⟨.refl _, row_refl _⟩

theorem generated_ignored_computation_argument_pure :
    (generate (symbolicSignatures (α := Unit)) [] ignoredArgument
      (CompTerm.pure (.base .unit))).Holds M V (fun _ => (.base .unit, [])) := by
  apply (generate_models_iff_typing M V signatures _ _ [] [] _ _
    (EnvRel.nil _ _ _ _) (signatures_related _)).mpr
  exact ignored_argument_typed []

/-- In contrast, a computed binding evaluates the request before its body. -/
def computedSignal : Term := .letE (signal 0) (.lit .unit)

theorem computed_signal_typed (Γ : Context) :
    Typing M V signatures Γ computedSignal (.base .unit, [raw 0]) := by
  exact .letComputed (signal_typed Γ 0) (literal_typed _ .unit) ⟨.refl _, row_refl _⟩

theorem computed_signal_present (Γ : Context) (c : Comp M)
    (typed : Typing M V signatures Γ computedSignal c) : List.Mem (raw (n := 1) 0) c.2 := by
  cases typed with
  | letValue value _ _ => cases value
  | letComputed request _ inclusion =>
      exact inclusion.2 _ (List.mem_append.mpr (Or.inl (signal_present Γ 0 _ request)))

theorem generated_computed_binding_cannot_erase (result : TyTerm Unit) (ρ : Unit → Comp M) :
    ¬ (generate symbolicSignatures [] computedSignal (CompTerm.pure result)).Holds M V ρ := by
  intro checked
  have typed := (generate_models_iff_typing M V signatures _ _ [] [] ρ _
    (EnvRel.nil _ _ _ _) (signatures_related _)).mp checked
  have impossible := computed_signal_present [] _ typed
  cases impossible

/-- A generalized lambda contains a handler, whose action contains a request. -/
def handledBody : Term := .handler 0 (signal 0) (.var 0) (.lit .unit)
def handlerLambda : Term := .lam handledBody

def polymorphicHandlerLambda : Term := .letE handlerLambda
  (.pair (.app (.var 0) (.lit .int)) (.app (.var 0) (.lit .str)))

private theorem handled_body_typed (Γ : Context) :
    Typing M V signatures Γ handledBody (.base .unit, []) := by
  apply Typing.handler (m := M) (view := V) (sigs := signatures)
    (input := (.base .unit, [raw 0]))
    (returned := (.base .unit, [])) (operated := (.base .unit, []))
  · exact signal_typed Γ 0
  · exact zero_var_typed Γ _
  · exact literal_typed _ .unit
  · exact .unionElim (.refl _) (.refl _)
  · change RowLe (Directed.residual [0] [raw 0] ++ ([] ++ [])) []
    simpa [Directed.residual, Capturable, raw] using row_refl ([] : Directed.Row 1 Nat)

private theorem handler_lambda_typed (Γ : Context) (input : Comp M) :
    Typing M V signatures Γ handlerLambda
      (Comp.arrow M input (.base .unit, []), []) :=
  .lam (handled_body_typed _) ⟨.refl _, row_refl _⟩

private theorem polymorphic_lambda_use (Γ : Context) (base : Base) :
    Typing M V signatures (.poly handlerLambda Γ :: Γ)
      (.app (.var 0) (.lit base)) (.base .unit, []) := by
  apply Typing.app (m := M) (view := V) (sigs := signatures)
    (a := (.base base, [])) (b := (.base .unit, [])) (ef := [])
  · exact .var rfl (.poly (handler_lambda_typed Γ _) (row_refl _))
  · exact literal_typed _ base
  · exact ⟨.refl _, row_refl _⟩

theorem polymorphic_handler_lambda_typed (Γ : Context) :
    Typing M V signatures Γ polymorphicHandlerLambda
      (.pair (.base .unit) (.base .unit), []) := by
  apply Typing.letValue (m := M) (view := V) (sigs := signatures) rfl
    (handler_lambda_typed Γ (.base .unit, []))
  exact .pair (polymorphic_lambda_use Γ .int) (polymorphic_lambda_use Γ .str)
    ⟨.refl _, row_refl _⟩

theorem generated_generalized_handler_body :
    (generate (symbolicSignatures (α := Unit)) [] polymorphicHandlerLambda
      (CompTerm.pure (.pair (.base .unit) (.base .unit)))).Holds M V
        (fun _ => (.base .unit, [])) := by
  apply (generate_models_iff_typing M V signatures _ _ [] [] _ _
    (EnvRel.nil _ _ _ _) (signatures_related _)).mpr
  exact polymorphic_handler_lambda_typed []

end Yulang.RecursiveEffects.Examples
