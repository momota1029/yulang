import YulangClosure.CallContextTyping

namespace YulangClosure.TypedCall

/-- Entry, the declared consumer, and the pending adapter suffix are typed
within each entry-mode branch. -/
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
  cases mode with
  | value =>
      have hentered : CompTyped Original.emptyContext
          (valueEntryBody carrier body) bodyResult :=
        CompTyped.bind (CompTyped.force hcarrier) hbody
      have hinput : CompTyped Original.emptyContext
          (valueEntryBody carrier body) consumer.input := by
        simpa only [hconsumer] using hentered
      have hconsumed : CompTyped Original.emptyContext
          (.bind (valueEntryBody carrier body) consumer.body)
          consumer.output :=
        CompTyped.bind hinput consumer.typed
      simpa only [callEntryBody, consumeCallResult] using
        (adaptersTyped_plugResultAdapters hpending _ hconsumed)
  | computation =>
      have hentered : CompTyped Original.emptyContext
          (computationEntryBody body carrier) bodyResult :=
        computationEntryBody_typed hbody hcarrier
      have hinput : CompTyped Original.emptyContext
          (computationEntryBody body carrier) consumer.input := by
        simpa only [hconsumer] using hentered
      have hconsumed : CompTyped Original.emptyContext
          (.bind (computationEntryBody body carrier) consumer.body)
          consumer.output :=
        CompTyped.bind hinput consumer.typed
      simpa only [callEntryBody, consumeCallResult] using
        (adaptersTyped_plugResultAdapters hpending _ hconsumed)

end YulangClosure.TypedCall
