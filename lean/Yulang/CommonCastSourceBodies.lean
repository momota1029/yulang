import Yulang.CommonCastRouteExecution
import Yulang.OperationalTyping

/-!
# Route bodies derived from actual resolved source checking

The input contains source expressions, not externally supplied plans or effect
bounds. The existing independent operational typing judgment characterizes the
finite declaration checker. Its proved source soundness supplies the body bound
and every returned value's endpoint type. Valid endpoint values are represented
explicitly, including higher-order values with their latent row contracts.

This is the resolved operational source bridge. Connecting its shapes and
endpoint contracts to arbitrary Common boundary descriptions remains separate.
-/

namespace Yulang.CommonCastSourceBodies

open Directed PureCasts

variable {vertices scopes : Nat} {Key Atom : Type} [DecidableEq Key]

structure Source (scopes : Nat) (Key Atom : Type)
    (inputShape outputShape : OperationalTyping.Shape) where
  input : OperationalTyping.VTy scopes Key inputShape
  output : OperationalTyping.VTy scopes Key outputShape
  expression : OperationalTyping.Expr scopes Key Atom [inputShape] outputShape

def Source.environment (source : Source scopes Key Atom inputShape outputShape) :=
  OperationalTyping.Env.cons (OperationalTyping.CTy.pure source.input) OperationalTyping.Env.nil

/-- Independent declaration validation, using source typing and its ordinary
subsumption judgment. It does not assume evaluation or a supplied body bound. -/
def Source.Valid (source : Source scopes Key Atom inputShape outputShape) : Prop :=
  ∃ result, OperationalTyping.Typing source.environment source.expression result ∧
    OperationalTyping.CLe result (OperationalTyping.CTy.pure source.output)

def Source.check (source : Source scopes Key Atom inputShape outputShape) : Bool :=
  match OperationalTyping.infer source.environment source.expression with
  | none => false
  | some result => OperationalTyping.checkC result (OperationalTyping.CTy.pure source.output)

theorem Source.check_exact (source : Source scopes Key Atom inputShape outputShape) :
    source.check = true ↔ source.Valid := by
  constructor
  · intro checked
    cases inferred : OperationalTyping.infer source.environment source.expression with
    | none => simp [Source.check, inferred] at checked
    | some result =>
        exact ⟨result, OperationalTyping.infer_sound _ _ _ inferred,
          (OperationalTyping.checkC_exact _ _).mp (by
            simpa [Source.check, inferred] using checked)⟩
  · rintro ⟨result, typed, compatible⟩
    have inferred := OperationalTyping.infer_complete typed
    simp [Source.check, inferred, (OperationalTyping.checkC_exact _ _).mpr compatible]

abbrev Source.Input (source : Source scopes Key Atom inputShape outputShape) :=
  { value : OperationalTyping.Value scopes Key Atom inputShape // OperationalTyping.ValidValue source.input value }

abbrev Source.Output (source : Source scopes Key Atom inputShape outputShape) :=
  { value : OperationalTyping.Value scopes Key Atom outputShape // OperationalTyping.ValidValue source.output value }

def Source.run (source : Source scopes Key Atom inputShape outputShape) (value : source.Input) :
    OperationalTyping.Tree scopes Key Atom outputShape :=
  OperationalTyping.eval (OperationalTyping.Env.cons (.pure value.val) OperationalTyping.Env.nil) source.expression

theorem Source.run_valid (source : Source scopes Key Atom inputShape outputShape)
    (valid : source.Valid) (value : source.Input) :
    OperationalTyping.Valid (OperationalTyping.CTy.pure source.output) (source.run value) := by
  obtain ⟨result, typed, subtype⟩ := valid
  apply OperationalTyping.subtype_sound subtype
  apply OperationalTyping.typing_sound typed
  apply OperationalTyping.EnvValid.cons
  · intro shape index
    exact nomatch index
  · exact OperationalTyping.valid_pure _ value.val value.property

private def refineReturns {A : Type} {P : A → Prop}
    (tree : Computation scopes Key Atom Atom A)
    (valid : OperationalTyping.AllReturns P tree) :
    Computation scopes Key Atom Atom { value : A // P value } :=
  match tree with
  | .pure value => .pure ⟨value, valid⟩
  | .request occurrence payload resume =>
      .request occurrence payload (fun response => refineReturns (resume response) (valid response))

omit [DecidableEq Key] in
private theorem refine_bounded {A : Type} {P : A → Prop}
    (tree : Computation scopes Key Atom Atom A)
    (valid : OperationalTyping.AllReturns P tree) (row : Row scopes Key) :
    Computation.BoundedBy row (refineReturns tree valid) ↔ Computation.BoundedBy row tree := by
  induction tree with
  | pure value => rfl
  | request occurrence payload resume ih =>
      simp only [refineReturns, Computation.BoundedBy, Computation.AllRequests]
      exact and_congr Iff.rfl (forall_congr' fun response => ih response (valid response))

/-- Purity and output typing are obtained from actual source checking. -/
def Source.declaration (source : Source scopes Key Atom inputShape outputShape)
    (checked : source.check = true) :
    Declaration scopes Key Atom Atom source.Input source.Output where
  body := fun value => refineReturns (source.run value)
    (source.run_valid (source.check_exact.mp checked) value).2
  row := []
  bounded := fun value => (refine_bounded _ _ []).mpr
    (source.run_valid (source.check_exact.mp checked) value).1

@[simp] theorem Source.declaration_checked
    (source : Source scopes Key Atom inputShape outputShape) (checked : source.check = true) :
    (source.declaration checked).check = true := rfl

/-- A finite edge registry stores source syntax and endpoint annotations.
No external conversion plan, cast contract or semantic body bound occurs here. -/
structure Registry (adj : FiniteReachability.Adj vertices)
    (shape : Fin vertices → OperationalTyping.Shape) (types : (vertex : Fin vertices) → OperationalTyping.VTy scopes Key (shape vertex)) where
  expression : ∀ source target, target ∈ adj source →
    OperationalTyping.Expr scopes Key Atom [shape source] (shape target)

def Registry.source {adj : FiniteReachability.Adj vertices}
    {shape : Fin vertices → OperationalTyping.Shape}
    {types : (vertex : Fin vertices) → OperationalTyping.VTy scopes Key (shape vertex)}
    (registry : Registry adj shape types (Atom := Atom)) (source target : Fin vertices)
    (edge : target ∈ adj source) : Source scopes Key Atom (shape source) (shape target) :=
  ⟨types source, types target, registry.expression source target edge⟩

def Registry.Valid {adj : FiniteReachability.Adj vertices}
    {shape : Fin vertices → OperationalTyping.Shape}
    {types : (vertex : Fin vertices) → OperationalTyping.VTy scopes Key (shape vertex)}
    (registry : Registry adj shape types (Atom := Atom)) : Prop :=
  ∀ source target edge, (registry.source source target edge).Valid

def Registry.bodies {adj : FiniteReachability.Adj vertices}
    {shape : Fin vertices → OperationalTyping.Shape}
    {types : (vertex : Fin vertices) → OperationalTyping.VTy scopes Key (shape vertex)}
    (registry : Registry adj shape types (Atom := Atom)) (valid : registry.Valid) :
    CommonCastRouteExecution.Bodies adj
      (fun vertex => { value : OperationalTyping.Value scopes Key Atom (shape vertex) // OperationalTyping.ValidValue (types vertex) value })
      scopes Key Atom Atom where
  declaration := fun source target edge =>
    (registry.source source target edge).declaration
      ((registry.source source target edge).check_exact.mpr (valid source target edge))
  checked := fun _ _ _ => rfl

theorem source_registry_compile_exact {adj : FiniteReachability.Adj vertices}
    {shape : Fin vertices → OperationalTyping.Shape}
    {types : (vertex : Fin vertices) → OperationalTyping.VTy scopes Key (shape vertex)}
    (registry : Registry adj shape types (Atom := Atom)) (valid : registry.Valid)
    (source target : Fin vertices) :
    (CommonCastRouteExecution.compile (registry.bodies valid) source target).isSome = true ↔
      FiniteReachability.Reach adj [source] target :=
  CommonCastRouteExecution.compile_exact _ source target

end Yulang.CommonCastSourceBodies

namespace Yulang.CommonCastSourceBodies

open Directed PureCasts
variable {vertices scopes : Nat} {Key Atom : Type} [DecidableEq Key]

omit [DecidableEq Key] in
private theorem refine_executes {A : Type} {P : A → Prop}
    (tree : Computation scopes Key Atom Atom A)
    (valid : OperationalTyping.AllReturns P tree) :
    mapValue Subtype.val (refineReturns tree valid) = tree := by
  induction tree with
  | pure value => rfl
  | request occurrence payload resume ih =>
      exact congrArg (Computation.request occurrence payload)
        (funext fun response => ih response (valid response))

/-- Erasing the output's typing proof gives exactly evaluation of the original
source expression in the input environment, including every response branch. -/
theorem Source.declaration_executes_source
    (source : Source scopes Key Atom inputShape outputShape)
    (checked : source.check = true) (input : source.Input) :
    mapValue Subtype.val ((source.declaration checked).body input) = source.run input :=
  refine_executes _ _

def Registry.check {adj : FiniteReachability.Adj vertices}
    {shape : Fin vertices → OperationalTyping.Shape}
    {types : (vertex : Fin vertices) → OperationalTyping.VTy scopes Key (shape vertex)}
    (registry : Registry adj shape types (Atom := Atom)) : Bool :=
  (List.finRange vertices).all fun source => (adj source).attach.all fun target =>
    (registry.source source target.val target.property).check

theorem Registry.check_exact {adj : FiniteReachability.Adj vertices}
    {shape : Fin vertices → OperationalTyping.Shape}
    {types : (vertex : Fin vertices) → OperationalTyping.VTy scopes Key (shape vertex)}
    (registry : Registry adj shape types (Atom := Atom)) :
    registry.check = true ↔ registry.Valid := by
  simp only [Registry.check, List.all_eq_true, List.mem_finRange, forall_const,
    Source.check_exact, Registry.Valid]
  constructor
  · intro checked source target edge
    exact checked source ⟨target, edge⟩ (by simp)
  · intro valid source target _
    exact valid source target.val target.property

def Registry.synthesize {adj : FiniteReachability.Adj vertices}
    {shape : Fin vertices → OperationalTyping.Shape}
    {types : (vertex : Fin vertices) → OperationalTyping.VTy scopes Key (shape vertex)}
    (registry : Registry adj shape types (Atom := Atom)) (source target : Fin vertices) :=
  if checked : registry.check = true then
    CommonCastRouteExecution.compile (registry.bodies (registry.check_exact.mp checked)) source target
  else none

/-- Raw finite source declarations are checked, a route is computed, and their
actual bodies are composed. No input plan, body bound, cast contract, fuel or
successful-check premise is used. The independent validation still belongs to
the resolved operational model, not the missing Common source bridge. -/
theorem source_registry_synthesize_exact {adj : FiniteReachability.Adj vertices}
    {shape : Fin vertices → OperationalTyping.Shape}
    {types : (vertex : Fin vertices) → OperationalTyping.VTy scopes Key (shape vertex)}
    (registry : Registry adj shape types (Atom := Atom)) (source target : Fin vertices) :
    (registry.synthesize source target).isSome = true ↔
      registry.Valid ∧ FiniteReachability.Reach adj [source] target := by
  by_cases checked : registry.check = true
  · simp only [Registry.synthesize, checked, ↓reduceDIte,
      source_registry_compile_exact, registry.check_exact.mp checked, true_and]
  · have invalid : ¬ registry.Valid := fun valid => checked (registry.check_exact.mpr valid)
    simp [Registry.synthesize, checked, invalid]

end Yulang.CommonCastSourceBodies
