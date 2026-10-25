import YulangClosure.CoreExecution

namespace YulangClosure.TypedCall

/-- A typed frame list types its actual hole-to-outer-frame plugging order. -/
theorem contextTyping_plugFrames
    {env : Original.Context} {frames : List ContextFrame}
    {a b : Original.Ty}
    (hframes : ContextTyping env frames a b)
    (hole : Comp) (hhole : CompTyped env hole a) :
    CompTyped env (plugFrames frames hole) b := by
  induction hframes generalizing hole with
  | nil =>
      simpa [plugFrames] using hhole
  | bind hbody _ ih =>
      simpa [plugFrames, plugFrame] using
        (ih _ (CompTyped.bind hhole hbody))
  | scope _ ih =>
      simpa [plugFrames, plugFrame] using
        (ih _ (CompTyped.scope hhole))
  | expose effectView resultView _ ih =>
      simpa [plugFrames, plugFrame] using
        (ih _ (CompTyped.expose effectView resultView hhole))
  | adapter hbody _ ih =>
      simpa [plugFrames, plugFrame] using
        (ih _ (CompTyped.bind hhole hbody))

/-- A typed adapter list types its actual inner-to-outer plugging order. -/
theorem adaptersTyped_plugResultAdapters
    {adapters : List Adapter} {a b : Original.Ty}
    (hadapters : AdaptersTyped adapters a b)
    (body : Comp)
    (hbody : CompTyped Original.emptyContext body a) :
    CompTyped Original.emptyContext
      (plugResultAdapters adapters body) b := by
  induction hadapters generalizing body with
  | nil _ =>
      simpa [plugResultAdapters] using hbody
  | cons adapter _ _ _ middle hInput hOutput _ ih =>
      have hinput : CompTyped Original.emptyContext body adapter.input := by
        simpa only [hInput] using hbody
      have hstep : CompTyped Original.emptyContext
          (.bind body adapter.body) adapter.output :=
        CompTyped.bind hinput adapter.typed
      have hmiddle : CompTyped Original.emptyContext
          (.bind body adapter.body) middle := by
        simpa only [hOutput] using hstep
      simpa [plugResultAdapters] using (ih _ hmiddle)

/-- The stored context derivation, consumer derivation, and pending adapter
derivation type the computation assembled by `plugEvaluationContext`. -/
theorem plugEvaluationContext_typed
    {Suffix : Type}
    (context : EvaluationContext Suffix)
    (hole : Comp)
    (hhole : CompTyped Original.emptyContext hole context.holeType) :
    CompTyped Original.emptyContext
      (plugEvaluationContext context hole) context.resultType := by
  have hframes : CompTyped Original.emptyContext
      (plugFrames context.frames hole) context.contextResultType :=
    contextTyping_plugFrames context.contextTyped hole hhole
  have hconsumerInput : CompTyped Original.emptyContext
      (plugFrames context.frames hole) context.bodyResultConsumer.input := by
    simpa only [context.bodyConsumerInputTyped, ← context.bodyResultTyped] using hframes
  have hconsumerOutput : CompTyped Original.emptyContext
      (.bind (plugFrames context.frames hole) context.bodyResultConsumer.body)
      context.resultAdapterInput := by
    simpa only [context.bodyResultOutputTyped] using
      (CompTyped.bind hconsumerInput context.bodyResultConsumer.typed)
  have hpending : CompTyped Original.emptyContext
      (plugResultAdapters context.pendingResultAdapters
        (.bind (plugFrames context.frames hole) context.bodyResultConsumer.body))
      context.pendingResultOutput :=
    adaptersTyped_plugResultAdapters context.pendingResultsTyped _ hconsumerOutput
  simpa only [plugEvaluationContext, context.finalResultTyped] using hpending

end YulangClosure.TypedCall
