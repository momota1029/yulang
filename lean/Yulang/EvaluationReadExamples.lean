import Yulang.Initialization

/-! Regression witnesses for decision 23, including actual read prefixes. -/
namespace Yulang.EvaluationSafety.Examples

open EvaluationOrder Inference

def emptyStore : Store n := fun _ => none

theorem empty_store_closed (world : Module n) : ClosedStore world emptyStore := by
  intro name value found
  cases found

/-- `id f = f; factory x = id (\y -> late); k = factory () (); late = compute ()`. -/
def factoryGap : Program 4 where
  body
    | 0 => .lam (.bound 0)
    | 1 => .lam (.app (.reference 0) (.lam (.reference 3)))
    | 2 => .app (.app (.reference 1) .lit) .lit
    | _ => .app (.lam .lit) .lit
  position := Fin.val

def factoryWorld : Module 4 := ⟨factoryGap, []⟩

theorem old_direct_check_misses_argument_closure :
    EvaluationOrder.check factoryGap [] = true := by decide

theorem returned_argument_closure_rejected : check factoryWorld = false := by decide

theorem factory_returns_captured_closure (store : Store 4) :
    Eval factoryGap store [] (.app (.reference 1) .lit) (.closure (.reference 3) [.unit]) [] := by
  have factory : Eval factoryGap store [] (.reference 1)
      (.closure (.app (.reference 0) (.lam (.reference 3))) []) [] :=
    .namedValue rfl .closure
  have identity : Eval factoryGap store [.unit] (.reference 0) (.closure (.bound 0) []) [] :=
    .namedValue rfl .closure
  have body : Eval factoryGap store [.unit] (.app (.reference 0) (.lam (.reference 3)))
      (.closure (.reference 3) [.unit]) [] :=
    .app identity .closure (.bound rfl)
  exact .app factory .unit body

/-- No value for `late` is needed: this prefix attempts its read before checking
whether it is initialized. The checker, not a store premise, rules it out. -/
theorem returned_argument_closure_attempts_late (store : Store 4) :
    Reads factoryGap store [] (factoryGap.body 2) 3 :=
  .appBody (factory_returns_captured_closure store) .unit (.read rfl)

theorem generated_factory_gap_has_no_solution (m : Model) (ρ : α → Comp m) (Γ : SchemeEnv α) :
    ¬ (Initialization.generate Γ factoryGap []).Holds m ρ := by
  intro solution
  have earlier := Initialization.generated_initializer_read_earlier m ρ Γ factoryGap [] solution
    emptyStore (empty_store_closed factoryWorld) 2 3 rfl
    (returned_argument_closure_attempts_late emptyStore)
  change 3 < 2 at earlier
  omega

/-- The callee is a captured local parameter: no named edge identifies it. -/
def argumentCall : EvaluationOrder.Expr 2 :=
  .app (.lam (.app (.bound 0) .lit)) (.lam (.reference 1))

def argumentProgram : Program 2 where
  body
    | 0 => argumentCall
    | _ => .app (.lam .lit) .lit
  position := Fin.val

def argumentWorld : Module 2 := ⟨argumentProgram, []⟩

theorem parameter_callback_rejected : check argumentWorld = false := by decide

theorem parameter_callback_attempts_late (store : Store 2) :
    Reads argumentProgram store [] argumentCall 1 :=
  .appBody .closure .closure (.appBody (.bound rfl) .unit (.read rfl))

/-- Pair storage and projection can hide the callee's syntactic identity. -/
def pairCall : EvaluationOrder.Expr 2 :=
  .app (.fst (.pair (.lam (.reference 1)) .lit)) .lit

def pairProgram : Program 2 where
  body
    | 0 => pairCall
    | _ => .app (.lam .lit) .lit
  position := Fin.val

def pairWorld : Module 2 := ⟨pairProgram, []⟩

theorem projected_callback_rejected : check pairWorld = false := by decide

theorem projected_callback_attempts_late (store : Store 2) :
    Reads pairProgram store [] pairCall 1 :=
  .appBody (.fst (.pair .closure .unit)) .unit (.read rfl)

def reorderedPairProgram : Program 2 :=
  { pairProgram with position := fun name => if name = 0 then 1 else 0 }

def reorderedPairWorld : Module 2 := ⟨reorderedPairProgram, []⟩

theorem projected_callback_after_initialization_accepted : check reorderedPairWorld = true := by
  decide

theorem wrapping_projected_callback_delays_read : checkAt pairWorld 0 (.lam pairCall) = true :=
  checkAt_lambda _ _ _

/-- A nonempty actual prefix, built by evaluating and recording `late` first. -/
theorem projected_callback_prefix :
    EvaluatedPrefix reorderedPairWorld 1 (record emptyStore 1 .unit) := by
  change EvaluatedPrefix reorderedPairWorld (reorderedPairProgram.position 1 + 1)
    (record emptyStore 1 .unit)
  exact .step .empty (by decide) rfl (.app .closure .unit .unit)

theorem initialized_projected_callback_reads_present_value :
    ∃ value, (record emptyStore 1 .unit : Store 2) 1 = some value := by
  apply accepted_prefix_initializer_read_initialized reorderedPairWorld _ 0 projected_callback_prefix
    projected_callback_after_initialization_accepted rfl
  exact .appBody (.fst (.pair .closure .unit)) .unit (.read rfl)

/-- A computed store value contains a closure whose code is another module
function. Looking up the value does not evaluate that function's body. -/
def storedProgram : Program 4 where
  body
    | 0 => .lam (.reference 3)
    | 1 => .app (.lam (.pair (.reference 0) .lit)) .lit
    | 2 => .app (.fst (.reference 1)) .lit
    | _ => .app (.lam .lit) .lit
  position := Fin.val

def storedWorld : Module 4 := ⟨storedProgram, []⟩

def pairStore : Store 4 := fun name =>
  if name = 1 then some (.pair (.closure (.reference 3) []) .unit) else none

theorem pair_store_closed : ClosedStore storedWorld pairStore := by
  intro name value found
  by_cases same : name = 1
  · simp [pairStore, same] at found
    subst value
    refine .pair (.closure ?_ (by simp)) .unit
    exact declaration_within storedWorld 0
  · simp [pairStore, same] at found

theorem computed_store_callback_attempts_late :
    Reads storedProgram pairStore [] (storedProgram.body 2) 3 := by
  have fetched : Eval storedProgram pairStore [] (.reference 1)
      (.pair (.closure (.reference 3) []) .unit) [1] :=
    .read rfl (by simp [pairStore])
  have projected : Eval storedProgram pairStore [] (.fst (.reference 1))
      (.closure (.reference 3) []) [1] := .fst fetched
  exact .appBody projected .unit (.read rfl)

theorem computed_store_callback_rejected : check storedWorld = false := by decide

/-- Statement lambdas are included in the fallback, even if no declaration
contains a lambda mentioning this computed binding. -/
def statementProgram : Program 1 where
  body _ := .app (.lam .lit) .lit
  position _ := 1

def statementCall : EvaluationOrder.Expr 1 :=
  .app (.lam (.app (.bound 0) .lit)) (.lam (.reference 0))

def statementWorld : Module 1 := ⟨statementProgram, [⟨0, statementCall⟩]⟩

theorem statement_anonymous_body_rejected : check statementWorld = false := by decide

theorem statement_anonymous_body_attempts_future (store : Store 1) :
    Reads statementProgram store [] statementCall 0 :=
  .appBody .closure .closure (.appBody (.bound rfl) .unit (.read rfl))

end Yulang.EvaluationSafety.Examples
