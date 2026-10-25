import YulangClosure.CallEntryTypingRepair
import YulangClosure.CallPeelingTyping

namespace YulangClosure.TypedCall

/-- A typed finite function spine decomposes to its actual lambda leaf, and
the existing Call entry computation at that leaf has the original result
type. This assembles syntax typing only; it proves no execution step. -/
theorem completeCallEntry_typed
    {f : Function} {carrier : Value} {pending : List Adapter}
    {argument result finalResult : Original.Ty}
    (hf : FunctionTyped f argument result)
    (hcarrier :
      ValueTyped Original.emptyContext carrier (.thunk argument))
    (hpending : AdaptersTyped pending result finalResult) :
    ∃ (mode : Original.Mode) (receipt : ReceiptTemplate)
      (leafArgument bodyResult leafResult : Original.Ty)
      (body : Comp) (consumer : Adapter)
      (leafCarrier : Value) (finalPending : List Adapter),
      PeelFunction f carrier pending
        (.lambda mode receipt leafArgument bodyResult leafResult body consumer)
        leafCarrier finalPending ∧
      CompTyped Original.emptyContext
        (callEntryBody mode leafCarrier body consumer finalPending)
        finalResult := by
  obtain ⟨mode, receipt, leafArgument, bodyResult, leafResult,
      body, consumer, leafCarrier, finalPending, hpeel⟩ :=
    peelFunction_exists f carrier pending
  obtain ⟨typedLeafArgument, typedLeafResult, hleaf, hleafCarrier,
      hleafPending⟩ := peelFunction_typed hpeel hf hcarrier hpending
  have hbody : CompTyped Original.emptyContext
      (callEntryBody mode leafCarrier body consumer finalPending) finalResult := by
    cases hleaf with
    | lambdaValue receipt' argument' bodyResult' leafResult' body'
        resultConsumer htypedBody hconsumer hresult =>
      have hpendingLeaf :
          AdaptersTyped finalPending consumer.output finalResult := by
        rw [hresult]
        exact hleafPending
      exact callEntryBody_typed .value consumer finalPending
        hleafCarrier htypedBody hconsumer hpendingLeaf
    | lambdaComputation receipt' argument' bodyResult' leafResult' body'
        resultConsumer htypedBody hconsumer hresult =>
      have hpendingLeaf :
          AdaptersTyped finalPending consumer.output finalResult := by
        rw [hresult]
        exact hleafPending
      exact callEntryBody_typed .computation consumer finalPending
        hleafCarrier htypedBody hconsumer hpendingLeaf
  exact ⟨mode, receipt, leafArgument, bodyResult, leafResult, body,
    consumer, leafCarrier, finalPending, hpeel, hbody⟩

end YulangClosure.TypedCall
