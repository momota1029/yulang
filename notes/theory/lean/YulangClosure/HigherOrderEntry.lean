import YulangClosure.HigherOrderEnvironment

namespace YulangClosure.HigherOrder

/-- Source application evaluates the callee first. The argument is shifted out
of the fresh callee binder before being delayed. -/
def sourceApply (callee argument : Comp) : Comp :=
  .bind callee (.dynamicCall (.var 0) (.delay (renameComp Nat.succ argument)))

theorem sourceApply_typed (hf : CompTyped env callee (.callable a b))
    (ha : CompTyped env argument a) : CompTyped env (sourceApply callee argument) b :=
  .bind hf (.dynamicCall (.var rfl) (.delay (renameComp_typed ha (fun _ _ h => h))))

/-- Projection used only for a typed computation construction. Full adapters
remain in the plans below; this is not operational metadata erasure. -/
def adapterBody : Adapter → Comp
  | .mk _ _ body _ _ => body

theorem adapterBody_typed (h : AdapterTyped env adapter a b) :
    CompTyped (extend env a) (adapterBody adapter) b := by
  cases h with
  | mk h => exact h

def applyAdapter (adapter : Adapter) (v : Value) : Comp :=
  substComp (single v) (adapterBody adapter)

theorem applyAdapter_typed (h : AdapterTyped env adapter a b)
    (hv : ValueTyped env v a) : CompTyped env (applyAdapter adapter v) b :=
  substitute_top (adapterBody_typed h) hv

def consumeResult (body : Comp) (consumer : Adapter) : Comp :=
  .bind body (adapterBody consumer)

theorem consumeResult_typed (hb : CompTyped env body b)
    (hc : AdapterTyped env consumer b r) : CompTyped env (consumeResult body consumer) r :=
  .bind hb (adapterBody_typed hc)

/-- Value entry forces the carrier, then binds its value into the body. -/
def valueEntry (body : Comp) (carrier : Value) : Comp := .bind (.force carrier) body

theorem valueEntry_typed (hb : CompTyped (extend env a) body b)
    (hc : ValueTyped env carrier (.thunk a)) : CompTyped env (valueEntry body carrier) b :=
  .bind (.force hc) hb

/-- Computation entry substitutes the carrier itself; no force is inserted. -/
def computationEntry (body : Comp) (carrier : Value) : Comp := substComp (single carrier) body

theorem computationEntry_typed (hb : CompTyped (extend env (.thunk a)) body b)
    (hc : ValueTyped env carrier (.thunk a)) : CompTyped env (computationEntry body carrier) b :=
  substitute_top hb hc

structure LambdaEntryPlan where
  mode : Original.Mode
  receipt : ReceiptTemplate
  argument : Ty
  bodyResult : Ty
  result : Ty
  body : Comp
  consumer : Adapter
  carrier : Value

def LambdaEntryPlan.computation (p : LambdaEntryPlan) : Comp :=
  consumeResult
    (match p.mode with
    | .value => valueEntry p.body p.carrier
    | .computation => computationEntry p.body p.carrier)
    p.consumer

theorem lambda_value_plan_typed (receipt : ReceiptTemplate)
    (hb : CompTyped (extend env a) body b) (hc : AdapterTyped env consumer b r)
    (ha : ValueTyped env carrier (.thunk a)) :
    CompTyped env (LambdaEntryPlan.computation
      ⟨.value, receipt, a, b, r, body, consumer, carrier⟩) r :=
  consumeResult_typed (valueEntry_typed hb ha) hc

theorem lambda_computation_plan_typed (receipt : ReceiptTemplate)
    (hb : CompTyped (extend env (.thunk a)) body b) (hc : AdapterTyped env consumer b r)
    (ha : ValueTyped env carrier (.thunk a)) :
    CompTyped env (LambdaEntryPlan.computation
      ⟨.computation, receipt, a, b, r, body, consumer, carrier⟩) r :=
  consumeResult_typed (computationEntry_typed hb ha) hc

/-- Input adaptation runs inside the delayed carrier. The output adapter runs
on the inner call's returned value. Entire adapter metadata is retained. -/
structure WrapEntryPlan where
  inner : Value
  input : Adapter
  output : Adapter
  carrier : Value

def WrapEntryPlan.computation (p : WrapEntryPlan) : Comp :=
  consumeResult
    (.dynamicCall p.inner (.delay (.bind (.force p.carrier) (adapterBody p.input))))
    p.output

theorem wrap_plan_typed (hf : ValueTyped env inner (.callable a b))
    (hi : AdapterTyped env input c a) (ho : AdapterTyped env output b d)
    (hc : ValueTyped env carrier (.thunk c)) :
    CompTyped env (WrapEntryPlan.computation ⟨inner, input, output, carrier⟩) d :=
  consumeResult_typed
    (.dynamicCall hf (.delay (.bind (.force hc) (adapterBody_typed hi)))) ho

/-- Full retained plan after closing the ambient captures. Its carrier already
belongs to the caller's closed argument construction. -/
def captureEntryPlan (captures : Nat → Value) (p : LambdaEntryPlan) : LambdaEntryPlan :=
  { p with
    body := substComp (lift captures) p.body
    consumer := substAdapter captures p.consumer }

theorem captured_value_plan_typed [DecidableEq K]
    {arena : NativeClosureEnvironment.Arena K D} {env : Nat}
    {store : Nat → Option Value} {layout : Environment.Layout K} {values : List Value}
    (success : Environment.realize arena env store layout = some values)
    (cells : Environment.CellsTyped arena env store layout) (filler : Value)
    (receipt : ReceiptTemplate)
    (hb : CompTyped (extend (Environment.context layout) a) body b)
    (hc : AdapterTyped (Environment.context layout) consumer b r)
    (ha : ValueTyped emptyContext carrier (.thunk a)) :
    CompTyped emptyContext
      (captureEntryPlan (Environment.substitution filler values)
        ⟨.value, receipt, a, b, r, body, consumer, carrier⟩).computation r :=
  lambda_value_plan_typed receipt
    (Environment.close_bound_body success cells filler hb)
    (Environment.close_adapter success cells filler hc) ha

theorem captured_computation_plan_typed [DecidableEq K]
    {arena : NativeClosureEnvironment.Arena K D} {env : Nat}
    {store : Nat → Option Value} {layout : Environment.Layout K} {values : List Value}
    (success : Environment.realize arena env store layout = some values)
    (cells : Environment.CellsTyped arena env store layout) (filler : Value)
    (receipt : ReceiptTemplate)
    (hb : CompTyped (extend (Environment.context layout) (.thunk a)) body b)
    (hc : AdapterTyped (Environment.context layout) consumer b r)
    (ha : ValueTyped emptyContext carrier (.thunk a)) :
    CompTyped emptyContext
      (captureEntryPlan (Environment.substitution filler values)
        ⟨.computation, receipt, a, b, r, body, consumer, carrier⟩).computation r :=
  lambda_computation_plan_typed receipt
    (Environment.close_bound_body success cells filler hb)
    (Environment.close_adapter success cells filler hc) ha

/-- Distinguishing equation: argument variable zero becomes variable one beneath
callee binding, so the delayed argument does not accidentally refer to the callee. -/
theorem sourceApply_argument_shift (callee : Comp) :
    sourceApply callee (.ret (.var 0)) =
      .bind callee (.dynamicCall (.var 0) (.delay (.ret (.var 1)))) := rfl

/-- Plans retain the complete consumer, including its paths and view occurrences. -/
theorem retained_consumer (mode receipt a b r body consumer carrier) :
    (LambdaEntryPlan.mk mode receipt a b r body consumer carrier).consumer = consumer := rfl

theorem retained_wrap_adapters (inner input output carrier) :
    (WrapEntryPlan.mk inner input output carrier).input = input ∧
    (WrapEntryPlan.mk inner input output carrier).output = output := ⟨rfl, rfl⟩

end YulangClosure.HigherOrder
