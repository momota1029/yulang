import YulangClosure.CallContextTyping

namespace YulangClosure.TypedCall

/-- Both entry modes retain the declared consumer and the full pending
inner-to-outer adapter list in the constructed computation. -/
theorem callEntryBody_typed
    (mode : Original.Mode)
    {carrier : Value} {body : Comp}
    {argument bodyResult finalResult : Original.Ty}
    (consumer : Adapter) (pending : List Adapter)
    (hcarrier :
      ValueTyped Original.emptyContext carrier (.thunk argument))
    (hbody :
      CompTyped
        (Original.extend Original.emptyContext
          (match mode with
           | .value => argument
           | .computation => .thunk argument))
        body bodyResult)
    (hconsumer : consumer.input = bodyResult)
    (hpending : AdaptersTyped pending consumer.output finalResult) :
    CompTyped Original.emptyContext
      (callEntryBody mode carrier body consumer pending) finalResult := by
  have hentered : CompTyped Original.emptyContext
      (match mode with
       | .value => valueEntryBody carrier body
       | .computation => computationEntryBody body carrier)
      bodyResult := by
    cases mode with
    | value =>
        exact CompTyped.bind (CompTyped.force hcarrier) hbody
    | computation =>
        exact computationEntryBody_typed hbody hcarrier
  have hinput : CompTyped Original.emptyContext
      (match mode with
       | .value => valueEntryBody carrier body
       | .computation => computationEntryBody body carrier)
      consumer.input := by
    simpa only [hconsumer] using hentered
  have hconsumed : CompTyped Original.emptyContext
      (.bind
        (match mode with
         | .value => valueEntryBody carrier body
         | .computation => computationEntryBody body carrier)
        consumer.body)
      consumer.output :=
    CompTyped.bind hinput consumer.typed
  simpa only [callEntryBody, consumeCallResult] using
    (adaptersTyped_plugResultAdapters hpending _ hconsumed)

end YulangClosure.TypedCall
