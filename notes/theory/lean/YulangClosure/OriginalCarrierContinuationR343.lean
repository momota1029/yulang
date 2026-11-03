import YulangClosure.OriginalHigherOrderCorrespondenceR343

/-!
R343 carrier revision: pending computed-callee consumer for R314's actual
`(make 1) value` source. This uses the candidate HigherOrder value calculus.
It does not interpret original C_f, authenticate Inputs, or close R339/R306/R159.
- Only the genuine decoded R315 initializer is substituted for source Name 8.
- The operation body RETURNS a delayed request; its declaration consumer FORCES
  it before publication, using the frozen R343 carrier projection.
- The pending outer application, declaration result consumers, full operation
  instance and every typed response view are retained.
- Interaction traces include zero, internal, publication and multi-shot response
  developments; no returning trace or completed child is an input.
-/
namespace YulangClosure.OriginalCarrierContinuationR343

open HigherOrder HigherOrder.Safety
open OriginalHigherOrderCorrespondenceR343
open OriginalSourceContinuationR342 (identityAdapter identityValue plug_steps)
open OriginalTickDeclaredResponseR321

/-- Pending OUTER source application. Argument code remains under Delay. -/
def outerSuffix (argument : Int) : EvalContext :=
  .bind .hole (.dynamicCall (.var 0) (.delay (.ret (.int argument))))

def selectedProgram (receipts : Nat → ReceiptTemplate) (argument : Int) : Comp :=
  (outerSuffix argument).plug (program intType receipts 1)

/-- The same two source names: lexical value first, module make second. -/
def closeNames (receipts : Nat → ReceiptTemplate) (argument : Int) : Nat → Value
  | 0 => .int argument
  | 1 => makeValue intType receipts
  | n + 2 => .var n

/-- Projection of the independently exported R314 source, followed by lexical
substitution of the independently decoded R315 module initializer. It does not
assume a finished phase body or change source binding/name identity. -/
theorem selected_source_projection (origin : OriginalSource.Declaration)
    (receipts : Nat → ReceiptTemplate) (argument : Int) :
    project origin receipts (argumentTypes intType) (resultTypes intType) 16
      [some 1, some 8] OriginalScopedSourceEventMapR314.Fixture.selected =
        some (sourceApply (sourceApply (.ret (.var 1)) (.ret (.int 1))) (.ret (.var 0))) ∧
    substComp (closeNames receipts argument)
      (sourceApply (sourceApply (.ret (.var 1)) (.ret (.int 1))) (.ret (.var 0))) =
        selectedProgram receipts argument := by
  constructor <;> rfl

theorem outer_suffix_typed (argument : Int) :
    ContextTyped emptyContext (outerSuffix argument) (.callable intType intType) intType :=
  .bind .hole (.dynamicCall (.var rfl) (.delay (.ret .int)))

theorem selected_program_typed (receipts : Nat → ReceiptTemplate) (argument : Int) :
    CompTyped emptyContext (selectedProgram receipts argument) intType :=
  plug_typed (outer_suffix_typed argument) (program_typed intType receipts 1)

/-- Append the literal outer context to a captured context; this changes no
operation, payload, response binder or saved continuation code. -/
def appendContext (outer inner : EvalContext) : EvalContext :=
  match outer with
  | .hole => inner
  | .bind k body => .bind (appendContext k inner) body
  | .scope owner k => .scope owner (appendContext k inner)
  | .expose ev rv k => .expose ev rv (appendContext k inner)

theorem append_context_plug (outer inner : EvalContext) (body : Comp) :
    (appendContext outer inner).plug body = outer.plug (inner.plug body) := by
  induction outer with
  | hole => rfl
  | bind k body ih => exact congrArg (fun m => Comp.bind m body) ih
  | scope owner k ih => exact congrArg (Comp.scope owner) ih
  | expose ev rv k ih => exact congrArg (Comp.expose ev rv) ih

def selectedSaved (receipts : Nat → ReceiptTemplate) (argument : Int) : Interaction.Saved :=
  { saved intType receipts 1 with
    context := appendContext (outerSuffix argument) (savedContext intType receipts) }

theorem selected_request_exact (receipts : Nat → ReceiptTemplate) (argument : Int) :
    (selectedSaved receipts argument).request =
      (outerSuffix argument).plug (saved intType receipts 1).request := rfl

theorem selected_resume_exact (receipts : Nat → ReceiptTemplate) (argument : Int)
    (response : Value) :
    (selectedSaved receipts argument).resume response =
      (outerSuffix argument).plug ((saved intType receipts 1).resume response) := rfl

theorem selected_prefix (receipts : Nat → ReceiptTemplate) (argument : Int) :
    Steps (selectedProgram receipts argument) (events intType receipts 1)
      (selectedSaved receipts argument).request :=
  plug_steps (outerSuffix argument) (actual_prefix intType receipts 1)

theorem selected_capture_typed (receipts : Nat → ReceiptTemplate) (argument : Int) :
    Interaction.SavedTyped (selectedSaved receipts argument) intType :=
  Interaction.capture_typed
    (HigherOrder.Safety.trace_preservation (selected_prefix receipts argument)
      (selected_program_typed receipts argument))

/-- Actual returned lambda is entered by the pending source caller. The two
bind Returns include its original result consumer. The argument's Force is
present even though this particular body simply returns it. -/
def finalPlan (receipts : Nat → ReceiptTemplate) (argument : Int) : LambdaEntryPlan :=
  ⟨.value, receipts 2, intType, intType, intType,
    .ret (.var 0), identityAdapter intType, .delay (.ret (.int argument))⟩

theorem identity_consumed (receipts : Nat → ReceiptTemplate) (argument : Int) :
    Steps ((outerSuffix argument).plug (.ret (identityValue intType receipts)))
      [.silent, .lambdaEntry (finalPlan receipts argument), .silent, .silent, .silent]
      (.ret (.int argument)) := by
  refine .cons .bindReturn ?_
  refine .cons .callLambda ?_
  refine .cons (.bind (.bind .force)) ?_
  refine .cons (.bind .bindReturn) ?_
  refine .cons .bindReturn ?_
  exact .refl _

def deliveryEvents (receipts : Nat → ReceiptTemplate) (argument : Int) : List HigherOrder.Safety.Event :=
  [.silent, .silent] ++
    [.silent, .lambdaEntry (finalPlan receipts argument), .silent, .silent, .silent]

theorem steps_trans (first : Steps m before n) (second : Steps n after last) :
    Steps m (before ++ after) last := by
  induction first with
  | refl => exact second
  | cons step rest ih => exact .cons step (ih second)

/-- Every response, without requiring it be a canonical literal, follows the
same source statement-discard and callee-result consumers into the caller. -/
theorem selected_response_delivery (receipts : Nat → ReceiptTemplate) (argument : Int)
    (response : Value) :
    Steps ((selectedSaved receipts argument).resume response)
      (deliveryEvents receipts argument)
      (.ret (.int argument)) := by
  have first := plug_steps (outerSuffix argument)
    (actual_response_return intType receipts 1 response)
  have last := identity_consumed receipts argument
  exact steps_trans first last


namespace Development
open HigherOrder.Interaction

theorem internal_trace (steps : Steps m trace n) (arena : List Saved) :
    Trace ⟨m, arena, .running⟩ (trace.map Action.internal) ⟨n, arena, .running⟩ := by
  induction steps with
  | refl => exact .refl _
  | cons step rest ih => exact .cons (.internal step) True.intro ih

theorem trace_trans (first : Trace s before t) (second : Trace t suffix last) :
    Trace s (before ++ suffix) last := by
  induction first with
  | refl => exact second
  | cons step protocol rest ih => exact .cons step protocol (ih second)

def published (receipts : Nat → ReceiptTemplate) (argument : Int) : State :=
  ⟨(selectedSaved receipts argument).request, [selectedSaved receipts argument], .waiting 0⟩

def prefixActions (receipts : Nat → ReceiptTemplate) (argument : Int) : List Action :=
  (events intType receipts 1).map Action.internal ++ [.publish 0 (selectedSaved receipts argument)]

/-- The callee's original ten transitions and actual publication are outputs,
not hypotheses. The published handle has the caller's still unexecuted suffix. -/
theorem source_publication (receipts : Nat → ReceiptTemplate) (argument : Int) :
    Trace (initial (selectedProgram receipts argument)) (prefixActions receipts argument)
      (published receipts argument) := by
  apply trace_trans (internal_trace (selected_prefix receipts argument) [])
  exact .cons (.publish [] (selectedSaved receipts argument)) True.intro (.refl _)

/-- Both original exported trees and the full source-Key primitive resolution
feed the constructed publication. This supplies syntax, physical declaration,
and candidate value typing together; it supplies no original Inputs contract. -/
theorem authentic_source_publication (origin : OriginalSource.Declaration)
    (receipts : Nat → ReceiptTemplate) (argument : Int) :
    OriginalModuleContextBindingR315.decodeMake 16
      OriginalModuleContextBindingR315.Native.Make.rootInitializer =
        some OriginalModuleContextBindingR315.makeInitializer ∧
    project origin receipts (argumentTypes intType) (resultTypes intType) 16 []
      OriginalModuleContextBindingR315.makeInitializer = some (.ret (makeValue intType receipts)) ∧
    OriginalScopedSourceEventMapR314.decode OriginalScopedSourceEventMapR314.Fixture.data 7 1 =
      some OriginalScopedSourceEventMapR314.Fixture.selected ∧
    project origin receipts (argumentTypes intType) (resultTypes intType) 16
      [some 1, some 8] OriginalScopedSourceEventMapR314.Fixture.selected =
        some (sourceApply (sourceApply (.ret (.var 1)) (.ret (.int 1))) (.ret (.var 0))) ∧
    substComp (closeNames receipts argument)
      (sourceApply (sourceApply (.ret (.var 1)) (.ret (.int 1))) (.ret (.var 0))) =
        selectedProgram receipts argument ∧
    OriginalSourcePrimitiveBridgeR336.sourceRequest origin
      (OriginalSourceScopedInterpretationR335.tickRequest origin).operands.callee.key
      .primitiveDeclarationInstance = some tickOperation ∧
    Trace (initial (selectedProgram receipts argument)) (prefixActions receipts argument)
      (published receipts argument) ∧ StateTyped (published receipts argument) intType := by
  have projection := selected_source_projection origin receipts argument
  have trace := source_publication receipts argument
  exact ⟨OriginalModuleContextBindingR315.make_initializer_decoded,
    actual_source_projection origin intType receipts,
    OriginalScopedSourceEventMapR314.Fixture.selected_decodes,
    projection.1, projection.2, OriginalSourcePrimitiveBridgeR336.tick_request_resolves origin,
    trace, Interaction.trace_preservation trace
      (initial_typed (selected_program_typed receipts argument))⟩

/-- Every finite suffix starts at an actually reached, published Request. No
termination/Return condition is imposed. Old handle 0 continues to denote the
same operation, payload, response binder and pending caller suffix. -/
theorem every_development (receipts : Nat → ReceiptTemplate) (argument : Int)
    (development : Trace (published receipts argument) actions current) :
    StateTyped current intType ∧ Progress current ∧
      lookup current.arena 0 = some (selectedSaved receipts argument) := by
  have initialTrace := source_publication receipts argument
  have all := trace_trans initialTrace development
  have safe := closed_program_interaction_safety (selected_program_typed receipts argument) all
  exact ⟨safe.1, safe.2,
    trace_immutable development 0 (selectedSaved receipts argument) rfl⟩

/-- Resume the SAME source-published handle from every later protocol-respecting
state. Original TypedCall responses
are embedded with their complete ordered view lists and full operation instance.
The returned lambda's actual caller consumes the argument after the response. -/
theorem response_after_every_development
    (receipts : Nat → ReceiptTemplate) (argument : Int)
    (development : Trace (published receipts argument) actions current)
    (response : TypedCall.Value)
    (typed : TypedCall.ValueTyped Original.emptyContext response tickOperation.responseType) :
    Protocol current (.response 0 (embedOperation tickOperation) (embedValue response)) ∧
    Trace current
      (.response 0 (embedOperation tickOperation) (embedValue response) ::
        ((deliveryEvents receipts argument).map Action.internal))
      ⟨.ret (.int argument), current.arena, .running⟩ ∧
    StateTyped ⟨.ret (.int argument), current.arena, .running⟩ intType ∧
    lookup current.arena 0 = some (selectedSaved receipts argument) := by
  have reached := every_development receipts argument development
  have responseTyped := embedValue_typed typed (empty_embedding emptyContext)
  have protocol : Protocol current (.response 0 (embedOperation tickOperation) (embedValue response)) :=
    response_protocol reached.2.2 responseTyped
  have resumed : Trace current
      (.response 0 (embedOperation tickOperation) (embedValue response) ::
        ((deliveryEvents receipts argument).map Action.internal))
      ⟨.ret (.int argument), current.arena, .running⟩ := by
    exact .cons (.response reached.2.2) protocol
      (internal_trace (selected_response_delivery receipts argument (embedValue response)) current.arena)
  exact ⟨protocol, resumed, Interaction.trace_preservation resumed reached.1, reached.2.2⟩

end Development
end YulangClosure.OriginalCarrierContinuationR343
