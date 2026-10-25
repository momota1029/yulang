import YulangClosure.CallContextTyping

namespace YulangClosure.TypedCall

/-- Finite syntactic wrap decomposition. This records the existing argument
thunk construction and pending-result order; it asserts no execution step. -/
inductive PeelFunction :
    Function → Value → List Adapter →
    Function → Value → List Adapter → Prop where
  | lambda
      (mode : Original.Mode) (receipt : ReceiptTemplate)
      (argument bodyResult result : Original.Ty)
      (body : Comp) (consumer : Adapter)
      (carrier : Value) (pending : List Adapter) :
      PeelFunction
        (.lambda mode receipt argument bodyResult result body consumer)
        carrier pending
        (.lambda mode receipt argument bodyResult result body consumer)
        carrier pending
  | wrap
      {inner leaf : Function}
      {argumentAdapter resultAdapter : Adapter}
      {carrier finalCarrier : Value}
      {pending finalPending : List Adapter}
      (rest :
        PeelFunction inner
          (delayArgument carrier argumentAdapter)
          (resultAdapter :: pending)
          leaf finalCarrier finalPending) :
      PeelFunction (.wrap inner argumentAdapter resultAdapter)
        carrier pending leaf finalCarrier finalPending

/-- Every finite function spine has a syntactically constructed lambda leaf,
independently of any typing hypothesis or endpoint equality. -/
theorem peelFunction_exists
    (f : Function) (carrier : Value) (pending : List Adapter) :
    ∃ (mode : Original.Mode) (receipt : ReceiptTemplate)
      (leafArgument bodyResult leafResult : Original.Ty)
      (body : Comp) (consumer : Adapter)
      (finalCarrier : Value) (finalPending : List Adapter),
      PeelFunction f carrier pending
        (.lambda mode receipt leafArgument bodyResult leafResult body consumer)
        finalCarrier finalPending := by
  induction f generalizing carrier pending with
  | lambda mode receipt argument bodyResult result body consumer =>
      exact ⟨mode, receipt, argument, bodyResult, result, body, consumer,
        carrier, pending,
        PeelFunction.lambda mode receipt argument bodyResult result body consumer
          carrier pending⟩
  | wrap inner argumentAdapter resultAdapter ih =>
      obtain ⟨mode, receipt, argument, bodyResult, result, body, consumer,
        finalCarrier, finalPending, rest⟩ :=
        ih (delayArgument carrier argumentAdapter) (resultAdapter :: pending)
      exact ⟨mode, receipt, argument, bodyResult, result, body, consumer,
        finalCarrier, finalPending, PeelFunction.wrap rest⟩

/-- The inert argument thunk has the adapter's output type. Its body remains
under delay; this derivation does not evaluate the adapter. -/
theorem delayArgument_typed
    {carrier : Value} {argument innerArgument : Original.Ty}
    (adapter : Adapter)
    (hcarrier :
      ValueTyped Original.emptyContext carrier (.thunk argument))
    (hinput : adapter.input = argument)
    (houtput : adapter.output = innerArgument) :
    ValueTyped Original.emptyContext
      (delayArgument carrier adapter) (.thunk innerArgument) := by
  have hforce : CompTyped Original.emptyContext (.force carrier) adapter.input := by
    simpa only [hinput] using (CompTyped.force hcarrier)
  have hbind : CompTyped Original.emptyContext
      (.bind (.force carrier) adapter.body) adapter.output :=
    CompTyped.bind hforce adapter.typed
  simpa only [delayArgument, houtput] using (ValueTyped.delay hbind)

/-- Peeling preserves the typed carrier and the entire pending-result suffix.
Each outer wrap is prepended before recursion, so a deeper wrap's result
adapter precedes it in the final inner-to-outer list. -/
theorem peelFunction_typed
    {f leaf : Function} {carrier finalCarrier : Value}
    {pending finalPending : List Adapter}
    {argument result finalResult : Original.Ty}
    (hpeel : PeelFunction f carrier pending leaf finalCarrier finalPending)
    (hf : FunctionTyped f argument result)
    (hcarrier :
      ValueTyped Original.emptyContext carrier (.thunk argument))
    (hpending : AdaptersTyped pending result finalResult) :
    ∃ leafArgument leafResult,
      FunctionTyped leaf leafArgument leafResult ∧
      ValueTyped Original.emptyContext
        finalCarrier (.thunk leafArgument) ∧
      AdaptersTyped finalPending leafResult finalResult := by
  induction hpeel generalizing argument result finalResult with
  | lambda =>
      exact ⟨argument, result, hf, hcarrier, hpending⟩
  | wrap rest ih =>
      cases hf with
      | wrap hinner hinput houtput hrinput hroutput =>
          exact ih hinner
            (delayArgument_typed _ hcarrier hinput houtput)
            (AdaptersTyped.cons _ _ _ _ _ hrinput hroutput hpending)

end YulangClosure.TypedCall
