import YulangClosure.OriginalIdentityRealization
import YulangClosure.OriginalCalleeDelayProvenance

/-!
Source receipt boundary evidence, not a receipt admission interpretation.

Call semantic input realization §6 orders source Invoke/Receive before Force.
OriginalRecursivePair.receiveWorld supplies the source receipt token, while
OriginalFormalShared.PairExecution.presentInvocation retains independent
current/path/consumer/incidence operands. None of the declarations below
identifies that source event with the native Value-entry callback receipt.
The missing source readout/LocalAdmissions owner law is left open in the
assignment handoff; no new admission predicate is introduced here.
-/
namespace YulangClosure.OriginalSourceValueEntryAdmission

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceEvents OriginalFormalShared OriginalRecursivePair
open NativeClosureEnvironment SourceIdentityWorld

variable {s : Sorts} {D ViewData Rest View : Type}

/-- The selected source constructor supplies one exact receipt record.
This is independent of carrier Return, body typing and future callbacks. -/
theorem source_receipt_record (execution : PairExecution D ViewData Rest) :
    (receiveWorld (enterWorld execution.initial execution.entry.call execution.entry.provider)
      execution.entry).receiving.receipts.cell execution.initial.receiving.receipts.size =
      some execution.receipt :=
  constructed_original_receipt execution

/-- The source recipe presents the same carrier/view/receipt to Invoke.
It does not supply the other independent receipt-event readouts. -/
theorem presented_receipt_fields (execution : PairExecution D ViewData Rest)
    (assignment : OriginalWorldReadout.ViewAssignment (nativeReceiptSorts s Nat Nat) Nat)
    (template : OriginalSourceEnvironment.Invocation (nativeReceiptSorts s Nat Nat) Nat) :
    (execution.presentInvocation assignment template).carrier = assignment.carrier execution.argument.value ∧
    (execution.presentInvocation assignment template).carrierRoot = assignment.root execution.argument.value ∧
    (execution.presentInvocation assignment template).view = execution.argument.view ∧
    (execution.presentInvocation assignment template).receipt = execution.receipt :=
  constructed_invocation_operands execution assignment template

/-- These fields remain exactly the independent template fields. No actual
Receive transition or receipt-event equation is inferred for them. -/
theorem independent_receive_fields (execution : PairExecution D ViewData Rest)
    (assignment : OriginalWorldReadout.ViewAssignment (nativeReceiptSorts s Nat Nat) Nat)
    (template : OriginalSourceEnvironment.Invocation (nativeReceiptSorts s Nat Nat) Nat) :
    (execution.presentInvocation assignment template).current = template.current ∧
    (execution.presentInvocation assignment template).path = template.path ∧
    (execution.presentInvocation assignment template).consumer = template.consumer ∧
    (execution.presentInvocation assignment template).incidence = template.incidence :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Source receipt already has a two-step prefix without a Force-start
premise. The independent carrier graph and every start remain arbitrary. -/
theorem source_receipt_prefix (execution : PairExecution D ViewData Rest) :
    Prefix (InvocationMove execution.carrier execution.entry execution.plan execution.start)
      2 (.before execution.initial)
      (.received (receiveWorld
        (enterWorld execution.initial execution.entry.call execution.entry.provider) execution.entry)) :=
  .snoc (.snoc (.refl _) (.begin _)) (.receipt _)

/-- Decoding uses the supplied receipt Current directly and retains the
active input and descriptor assignment. This equation does not admit data
and does not validate the supplied receipt's Current or typed fields. -/
theorem receipt_decoder_uses_supplied_current (readout : RuntimeReadout s View)
    (state : Decoded s View) (parameter : OriginalParameterWorld.Parameter)
    (receipt : ReceiptData s View) (candidate : ScopedValue (Payload s View))
    (parents : List (EventStep (Payload s View)))
    (payload : candidate.data = .runtime (.receipt receipt)) :
    let after := decodeFrame readout state ⟨receiptBinder parameter, candidate, parents⟩
    after.assignment.event.history = receipt.after.history ∧
    after.assignment.event.current = receipt.after.configuration ∧
    after.active = state.active ∧
    after.assignment.descriptor = state.assignment.descriptor := by
  simp [decodeFrame, payload, Decoded.retain, Decoded.runtime,
    RuntimeReadout.event, Runtime.after, Runtime.endpoints]

/-- The source Receive store cannot be the unchanged Callee Delay pre-Force
store. This compares those two specified representations only; it is not a
counterexample to the whole source/native correspondence obligation. -/
theorem source_receipt_store_differs_from_preforce
    {C Dict Schema : Type}
    (raw : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (entry : EntryData Name Nat Site) (site : Site) (label environment : Nat)
    (metadata : OriginalCalleeDelayProvenance.Metadata) :
    (receiveWorld (enterWorld (OriginalCalleeDelayProvenance.project raw).world
      entry.call entry.provider) entry).receiving.receipts ≠
    (OriginalCalleeDelayProvenance.project
      (OriginalCalleeDelayProvenance.appendView
        (OriginalCalleeDelayProvenance.allocate raw site label environment)
        raw.values.length metadata)).world.receiving.receipts := by
  intro same
  have sizes := congrArg (fun store => store.size) same
  change (OriginalCalleeDelayProvenance.project raw).world.receiving.receipts.size + 1 =
    (OriginalCalleeDelayProvenance.project raw).world.receiving.receipts.size at sizes
  exact Nat.ne_of_gt (Nat.lt_succ_self _) sizes

end YulangClosure.OriginalSourceValueEntryAdmission
