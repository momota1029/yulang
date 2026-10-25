import YulangClosure.ControlTyping
import YulangClosure.Contracts

/-! A concrete five-step prefix of the frozen Call relation. This construction
does not assert that any frontend or native producer emits this Call. -/
namespace YulangClosure.Control

private abbrev viewedForceUnit : Original.Ty := .base .unit

private def viewedForceIdentityBody : TypedCall.Comp := .ret (.var 0)

private def viewedForceReceipt : TypedCall.ReceiptTemplate := ⟨[], []⟩

private def viewedForceConsumer : TypedCall.Adapter where
  input := viewedForceUnit
  output := viewedForceUnit
  body := viewedForceIdentityBody
  typed := .ret (.var rfl)
  pathCorrespondences := []
  capturedViews := []

private def viewedForceFunction : TypedCall.Function :=
  .lambda .value viewedForceReceipt viewedForceUnit viewedForceUnit
    viewedForceUnit viewedForceIdentityBody viewedForceConsumer

private theorem viewedForceFunctionTyped :
    TypedCall.FunctionTyped viewedForceFunction viewedForceUnit viewedForceUnit :=
  .lambdaValue viewedForceReceipt viewedForceUnit viewedForceUnit viewedForceUnit
    viewedForceIdentityBody viewedForceConsumer (.ret (.var rfl)) rfl rfl

private def viewedForceCarrierValue (occurrence : TypedCall.ViewOccurrence) :
    TypedCall.Value :=
  .view (.delay (.ret (.original .unit))) occurrence

private def viewedForceCarrier (occurrence : TypedCall.ViewOccurrence) :
    TypedCall.Carrier where
  underlying := viewedForceCarrierValue occurrence
  carrierType := .thunk viewedForceUnit
  typed := .view (.delay (.ret (.original .unit)))
  occurrences := [occurrence]
  receipts := []

private def viewedForceView (occurrence : TypedCall.ViewOccurrence) :
    TypedCall.CallView where
  receiverOwner := 0
  sourceReceipt := viewedForceReceipt
  carrierOccurrences := [occurrence]
  interfaces := []
  adapterPaths := []
  capturedViews := []

/-- All CallTerm fields are supplied; its result is definitionally unit. -/
def viewedForceCallTerm (occurrence : TypedCall.ViewOccurrence) :
    TypedCall.CallTerm where
  function := viewedForceFunction
  argument := viewedForceCarrier occurrence
  inputType := viewedForceUnit
  resultType := viewedForceUnit
  functionTyped := viewedForceFunctionTyped
  argumentIsThunk := rfl
  callView := viewedForceView occurrence
  sourceReceiptMatches := rfl
  wrapPlanMatches := rfl
  activeOwners := []
  receiverFresh := by intro h; cases h

/-- Both identity bind frames, the receiver scope and the literal suffix remain. -/
def viewedForceTarget {W : Type} (world : W)
    (occurrence : TypedCall.ViewOccurrence) (suffix : List Frame) : CallState W :=
  ⟨world, .active (.force (viewedForceCarrierValue occurrence)),
    [.bind viewedForceIdentityBody, .bind viewedForceIdentityBody, .scope 0],
    viewedForceView occurrence, viewedForceUnit, [], [occurrence], [], suffix⟩

/-- The specific witness is exposed so finite typing can use its unit result
without extracting an unrecorded result-type equality from an existential. -/
theorem viewed_force_prefix {W : Type} (md : Metadata W) (world : W)
    (occurrence : TypedCall.ViewOccurrence) (suffix : List Frame) :
    Prefix (CallControlStep md) 5
      (CallState.initial (viewedForceCallTerm occurrence) world suffix)
      (viewedForceTarget world occurrence suffix) := by
  have h0 := Prefix.refl (step := CallControlStep md)
    (CallState.initial (viewedForceCallTerm occurrence) world suffix)
  have h1 := Prefix.snoc h0
    (CallControlStep.start (md := md) (viewedForceCallTerm occurrence) world suffix)
  have h2 := Prefix.snoc h1
    (CallControlStep.attachReceipt world .value viewedForceReceipt
      viewedForceUnit viewedForceUnit viewedForceUnit viewedForceIdentityBody
      viewedForceConsumer viewedForceFunctionTyped
      (viewedForceCarrierValue occurrence) [] [.scope 0]
      (viewedForceView occurrence) viewedForceUnit [] [occurrence] [] suffix)
  have h3 := Prefix.snoc h2
    (CallControlStep.enterLambda world .value viewedForceReceipt
      viewedForceUnit viewedForceUnit viewedForceUnit viewedForceIdentityBody
      viewedForceConsumer viewedForceFunctionTyped
      (viewedForceCarrierValue occurrence) [] [.scope 0]
      (viewedForceView occurrence) viewedForceUnit [] [occurrence] [] suffix)
  have h4 := Prefix.snoc h3
    (CallControlStep.enterBind world
      (.bind (.force (viewedForceCarrierValue occurrence)) viewedForceIdentityBody)
      viewedForceIdentityBody [.scope 0] (viewedForceView occurrence)
      viewedForceUnit [] [occurrence] [] suffix)
  exact Prefix.snoc h4
    (CallControlStep.enterBind world (.force (viewedForceCarrierValue occurrence))
      viewedForceIdentityBody [.bind viewedForceIdentityBody, .scope 0]
      (viewedForceView occurrence) viewedForceUnit [] [occurrence] [] suffix)

/-- For every independently typed suffix, an actual initial Call reaches the
View-wrapped Force head in exactly five existing transitions. -/
theorem viewed_force_reachable {W : Type} (md : Metadata W) (sig : Signature)
    (world : W) (occurrence : TypedCall.ViewOccurrence) (suffix : List Frame)
    {result : Ty}
    (hsuffix : FramesTyped sig suffix (.original (.base .unit)) result) :
    ∃ (term : TypedCall.CallTerm) (target : CallState W),
      Prefix (CallControlStep md) 5 (CallState.initial term world suffix) target ∧
      target.head = .active
        (.force (.view (.delay (.ret (.original .unit))) occurrence)) := by
  clear hsuffix
  exact ⟨viewedForceCallTerm occurrence, viewedForceTarget world occurrence suffix,
    viewed_force_prefix md world occurrence suffix, rfl⟩

end YulangClosure.Control
