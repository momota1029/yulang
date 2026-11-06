import Yulang.OperationalTyping

/-!
# Written-order application in the resolved operational core

Decision 43 makes ordinary application strict, including unused arguments.
The historical computation-argument model remains unchanged. This module
lowers strict application to two ordinary computed lets in that model and
proves equality with an independently defined strict evaluator, for every
expression and environment. Evaluation of the function precedes evaluation
of the argument; the function receives the resulting pure value.

The checker runs on the actual lowered syntax. Its soundness therefore uses
the existing independently defined target typing, not an assumed runtime
bound. This is a resolved, annotated fragment: source shape inference,
permission elaboration and parsing are not supplied by this lowering.
-/

namespace Yulang.StrictApplication

open Directed OperationalTyping

abbrev Renaming (Γ Δ : List Shape) := ∀ {shape}, Var Γ shape → Var Δ shape

def Renaming.lift (rename : Renaming Γ Δ) : Renaming (shape :: Γ) (shape :: Δ)
  | _, .here => .here
  | _, .there index => .there (rename index)

def pull (rename : Renaming Γ Δ) (environment : Env F Δ) : Env F Γ :=
  ⟨fun index => environment (rename index)⟩

@[simp] theorem pull_lift_cons (rename : Renaming Γ Δ) (first : F shape)
    (rest : Env F Δ) :
    pull rename.lift (Env.cons first rest) = Env.cons first (pull rename rest) := by
  apply congrArg Env.mk
  funext shape index
  cases index <;> rfl

@[simp] theorem pull_there_cons (first : F shape) (rest : Env F Γ) :
    pull (fun index => Var.there index) (Env.cons first rest) = rest := rfl

def rename (mapping : Renaming Γ Δ) : Expr n Key Atom Γ shape → Expr n Key Atom Δ shape
  | .var index => .var (mapping index)
  | .lit value => .lit value
  | .lam input body => .lam input (rename mapping.lift body)
  | .app function argument => .app (rename mapping function) (rename mapping argument)
  | .pair left right => .pair (rename mapping left) (rename mapping right)
  | .fst expression => .fst (rename mapping expression)
  | .snd expression => .snd (rename mapping expression)
  | .letE value body => .letE (rename mapping value) (rename mapping.lift body)
  | .request key payload => .request key (rename mapping payload)
  | .boundary boundary body => .boundary boundary (rename mapping body)
  | .handler key output action onReturn onOperation =>
      .handler key output (rename mapping action) (rename mapping.lift onReturn)
        (rename (Renaming.lift (Renaming.lift mapping)) onOperation)
  | .widen output body => .widen output (rename mapping body)

/-- Renaming is interpreted by pulling back the actual runtime environment. -/
theorem eval_rename [DecidableEq Key] (expression : Expr n Key Atom Γ shape)
    (mapping : Renaming Γ Δ) (runtime : Env (Tree n Key Atom) Δ) :
    OperationalTyping.eval runtime (rename mapping expression) =
      OperationalTyping.eval (pull mapping runtime) expression := by
  induction expression generalizing Δ with
  | var | lit => rfl
  | lam input body ih =>
      simp only [rename, OperationalTyping.eval]
      congr 1
      funext argument
      rw [ih, pull_lift_cons]
  | app function argument ihf iha =>
      simp only [rename, OperationalTyping.eval, ihf, iha]
  | pair left right ihl ihr =>
      simp only [rename, OperationalTyping.eval, ihl, ihr]
  | fst expression ih | snd expression ih =>
      simp only [rename, OperationalTyping.eval, ih]
  | request key expression ih =>
      simp only [rename, OperationalTyping.eval, ih]
  | boundary bound expression ih =>
      simp only [rename, OperationalTyping.eval, ih]
  | widen output expression ih =>
      simp only [rename, OperationalTyping.eval, ih]
  | letE value body ihv ihb =>
      simp only [rename, OperationalTyping.eval, ihv, ihb, pull_lift_cons]
  | handler key output action onReturn onOperation iha ihr iho =>
      simp only [rename, OperationalTyping.eval, iha, ihr, iho, pull_lift_cons]

theorem infer_rename [DecidableEq Key] (expression : Expr n Key Atom Γ shape)
    (mapping : Renaming Γ Δ) (types : Env (CTy n Key) Δ) :
    OperationalTyping.infer types (rename mapping expression) =
      OperationalTyping.infer (pull mapping types) expression := by
  induction expression generalizing Δ with
  | var | lit => rfl
  | handler key output action onReturn onOperation iha ihr iho =>
      simp only [rename, OperationalTyping.infer, iha, ihr, iho, operationTypes, pull_lift_cons]
  | _ => simp only [rename, OperationalTyping.infer, pull_lift_cons, *]

/-- Both source operands are evaluated before applying the function value.
The de Bruijn shifts retain their original lexical environments. -/
def forceApplication (function : Expr n Key Atom Γ (.arrow a b))
    (argument : Expr n Key Atom Γ a) : Expr n Key Atom Γ b :=
  .letE function (.letE (rename (fun index => Var.there index) argument)
    (.app (.var (.there .here)) (.var .here)))

theorem eval_forceApplication [DecidableEq Key]
    (function : Expr n Key Atom Γ (.arrow a b)) (argument : Expr n Key Atom Γ a)
    (runtime : Env (Tree n Key Atom) Γ) :
    OperationalTyping.eval runtime (forceApplication function argument) =
      (OperationalTyping.eval runtime function).bind (fun f =>
        (OperationalTyping.eval runtime argument).bind (fun value => f (.pure value))) := by
  simp only [forceApplication, OperationalTyping.eval, eval_rename, pull_there_cons,
    Env.cons_here, Env.cons_there, Computation.bind]

/-- Strict application adds both operand rows in written order. Compatibility
is checked on the already evaluated argument value, whose immediate row is empty. -/
theorem infer_forceApplication [DecidableEq Key]
    (function : Expr n Key Atom Γ (.arrow a b)) (argument : Expr n Key Atom Γ a)
    (types : Env (CTy n Key) Γ) (input : CTy n Key a) (output : CTy n Key b)
    (functionRow : Row n Key) (actual : CTy n Key a)
    (functionInferred : OperationalTyping.infer types function =
      some ⟨CTy.arrow input output, functionRow⟩)
    (argumentInferred : OperationalTyping.infer types argument = some actual)
    (compatible : CLe (CTy.pure actual.value) input) :
    OperationalTyping.infer types (forceApplication function argument) =
      some ⟨output.value, functionRow ++ (actual.row ++ output.row)⟩ := by
  have checked : checkC (⟨actual.value, []⟩ : CTy n Key a)
      (⟨input.value, input.row⟩ : CTy n Key a) = true :=
    (checkC_exact (CTy.pure actual.value) input).mpr compatible
  simp [forceApplication, OperationalTyping.infer, infer_rename, pull_there_cons,
    functionInferred, argumentInferred, CTy.arrow, CTy.pure, checked]

/-- The complete resolved syntax is traversed, including lambda bodies and
both handler arms. Only the application convention changes. -/
def compile : Expr n Key Atom Γ shape → Expr n Key Atom Γ shape
  | .var index => .var index
  | .lit value => .lit value
  | .lam input body => .lam input (compile body)
  | .app function argument => forceApplication (compile function) (compile argument)
  | .pair left right => .pair (compile left) (compile right)
  | .fst expression => .fst (compile expression)
  | .snd expression => .snd (compile expression)
  | .letE value body => .letE (compile value) (compile body)
  | .request key payload => .request key (compile payload)
  | .boundary boundary body => .boundary boundary (compile body)
  | .handler key output action onReturn onOperation =>
      .handler key output (compile action) (compile onReturn) (compile onOperation)
  | .widen output body => .widen output (compile body)

/-- Direct strict evaluation, defined without `compile` or type inference. -/
def eval [DecidableEq Key] (runtime : Env (Tree n Key Atom) Γ) :
    Expr n Key Atom Γ shape → Tree n Key Atom shape
  | .var index => runtime index
  | .lit value => .pure value
  | .lam _ body => .pure (fun argument => eval (Env.cons argument runtime) body)
  | .app function argument => (eval runtime function).bind fun f =>
      (eval runtime argument).bind fun value => f (.pure value)
  | .pair left right => (eval runtime left).bind fun first =>
      (eval runtime right).bind fun last => .pure (first, last)
  | .fst expression => (eval runtime expression).bind fun value => .pure value.1
  | .snd expression => (eval runtime expression).bind fun value => .pure value.2
  | .letE value body => (eval runtime value).bind fun value =>
      eval (Env.cons (.pure value) runtime) body
  | .request key payload => (eval runtime payload).bind fun value =>
      .request (raw key) value (fun response => .pure response)
  | .boundary boundary body => Computation.mapRequests boundary.transform (eval runtime body)
  | .handler key _ action onReturn onOperation =>
      Computation.shallowHandle [key]
        (fun value => eval (Env.cons (.pure value) runtime) onReturn)
        (fun _ payload resume =>
          eval (Env.cons (s := .atom) (.pure payload)
            (Env.cons (s := .arrow .atom _) (.pure (fun argument => argument.bind resume)) runtime))
            onOperation)
        (eval runtime action)
  | .widen _ body => eval runtime body

/-- Equality of whole request trees includes payloads, every continuation,
handler arms, signed weights, and higher-order returned values. -/
theorem compile_correct [DecidableEq Key] (expression : Expr n Key Atom Γ shape)
    (runtime : Env (Tree n Key Atom) Γ) :
    OperationalTyping.eval runtime (compile expression) = eval runtime expression := by
  induction expression with
  | app function argument ihf iha =>
      simp only [compile, eval_forceApplication, eval, ihf, iha]
  | _ => simp only [compile, OperationalTyping.eval, eval, *]

def infer [DecidableEq Key] (types : Env (CTy n Key) Γ)
    (expression : Expr n Key Atom Γ shape) : Option (CTy n Key shape) :=
  OperationalTyping.infer types (compile expression)

/-- Acceptance is exactly the existing independent typing of the actual
lowered program; it is not the historical typing of the unlowered program. -/
theorem infer_exact [DecidableEq Key] (expression : Expr n Key Atom Γ shape)
    (types : Env (CTy n Key) Γ) (output : CTy n Key shape) :
    infer types expression = some output ↔ Typing types (compile expression) output :=
  OperationalTyping.infer_exact (compile expression) types output

theorem inferred_operationally_valid [DecidableEq Key]
    (expression : Expr n Key Atom Γ shape) (types : Env (CTy n Key) Γ)
    (output : CTy n Key shape) (accepted : infer types expression = some output)
    (runtime : Env (Tree n Key Atom) Γ) (environment : EnvValid types runtime) :
    Valid output (eval runtime expression) := by
  rw [← compile_correct]
  exact typing_sound ((infer_exact expression types output).mp accepted) runtime environment

theorem closed_inferred_bound [DecidableEq Key]
    (expression : Expr n Key Atom [] shape) (output : CTy n Key shape)
    (accepted : infer Env.nil expression = some output) :
    Computation.BoundedBy output.row (eval Env.nil expression) :=
  (inferred_operationally_valid expression Env.nil output accepted Env.nil
    (fun index => nomatch index)).1

theorem closed_inferred_values [DecidableEq Key]
    (expression : Expr n Key Atom [] shape) (output : CTy n Key shape)
    (accepted : infer Env.nil expression = some output) :
    AllReturns (ValidValue output.value) (eval Env.nil expression) :=
  (inferred_operationally_valid expression Env.nil output accepted Env.nil
    (fun index => nomatch index)).2

/-- Discarding a successful value retains every request and response branch. -/
theorem discard_bound_iff (row : Row n Key)
    (action : Computation n Key Payload Response A) (value : B) :
    Computation.BoundedBy row (action.bind fun _ => .pure value) ↔
      Computation.BoundedBy row action := by
  induction action with
  | pure => rfl
  | request occurrence payload resume ih =>
      simp only [Computation.bind, Computation.bounded_request_iff]
      exact and_congr Iff.rfl (forall_congr' ih)

/-- Even an ignored ordinary argument runs, with exactly its request bound. -/
theorem unused_argument_bound_iff [DecidableEq Key]
    (runtime : Env (Tree n Key Atom) Γ) (input : CTy n Key a)
    (argument : Expr n Key Atom Γ a) (value : Atom) (row : Row n Key) :
    Computation.BoundedBy row (eval runtime (.app (.lam input (.lit value)) argument)) ↔
      Computation.BoundedBy row (eval runtime argument) :=
  discard_bound_iff row (eval runtime argument) value

end Yulang.StrictApplication
