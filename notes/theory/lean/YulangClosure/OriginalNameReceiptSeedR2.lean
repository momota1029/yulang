import YulangClosure.OriginalNameEntryCorrespondence

/-!
Constructor equations at the still-open receipt-seed/readback boundary.
These do not construct an actual native Use or ReturnAlignment. RuntimeReadout
and native.fields have independent semantic fields; their source realization
must precede an application to constructed_name_realization.
-/
namespace YulangClosure.OriginalNameReceiptSeed

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceEvents OriginalParameterWorld OriginalParameterSemantics
open OriginalFormalShared OriginalWorldReadout OriginalIdentityRealization

variable {s b : Sorts} {D ViewData Rest Body View : Type}

/-- The actual invocation constructor owns the complete active CallInput.
This equation selects no semantic readout from native handles. -/
theorem invocation_owns_active (readout : RuntimeReadout s View)
    (before : Decoded s View) (binder : Binder) (invocation : Invocation s View) :
    (before.runtime readout binder (.invocation invocation)).active =
      some ((invocation.challenge
        (readout.event before.fixedFrames before.assignment.event binder (.invocation invocation))
        (before.assignment.descriptor ⟨binder.site, .descriptor⟩) before.viewMeaning).input) := rfl

/-- Receipt preserves the active invocation and static fiber/eta0, while its
current configuration comes from the receipt. Assignment/witness are readout
results, so no preservation of views or shared witness is asserted. -/
theorem receipt_constructor_fields (readout : RuntimeReadout s View)
    (before : Decoded s View) (binder : Binder) (receipt : ReceiptData s View) :
    (before.runtime readout binder (.receipt receipt)).active = before.active ∧
    (before.runtime readout binder (.receipt receipt)).assignment.event.fiber = before.assignment.event.fiber ∧
    (before.runtime readout binder (.receipt receipt)).assignment.event.eta0 = before.assignment.event.eta0 ∧
    (before.runtime readout binder (.receipt receipt)).assignment.event.current = receipt.after.configuration ∧
    (before.runtime readout binder (.receipt receipt)).assignment.event.eta =
      readout.eta before.fixedFrames before.assignment.event binder (.receipt receipt) ∧
    (before.runtime readout binder (.receipt receipt)).assignment.event.witness =
      readout.witness before.fixedFrames before.assignment.event binder (.receipt receipt) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Force's constructor retains these four coordinates relative to *its own*
demand. It does not connect that demand to a separately decoded receipt. -/
theorem prefix_preserves_indices
    (native : OriginalNameForceExtraction.Native b D ViewData Rest Body View)
    (delay : OriginalIdentityCarrier.NameDelay)
    (demand : Event (OriginalNameForceExtraction.S b D ViewData Rest Body View)) (fuel : Nat) :
    (OriginalNameForceExtraction.eventAt native delay demand fuel).fiber = demand.fiber ∧
    (OriginalNameForceExtraction.eventAt native delay demand fuel).eta0 = demand.eta0 ∧
    (OriginalNameForceExtraction.eventAt native delay demand fuel).eta.views = demand.eta.views ∧
    (OriginalNameForceExtraction.eventAt native delay demand fuel).witness.shared = demand.witness.shared := by
  unfold OriginalNameForceExtraction.eventAt
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Exact expansion of ReturnAlignment.readback. None of these seven
component equations follows from equal native value/view/owner handles.
Packet construction supplies the history equation; the other fields require
the actual semantic Return readout and the same saved frames/receipt event. -/
theorem return_readback_iff
    (readout : RuntimeReadout (OriginalNameForceExtraction.S b D ViewData Rest Body View) View)
    (frames : List (Frame (Payload (OriginalNameForceExtraction.S b D ViewData Rest Body View) View)))
    (before : Event (OriginalNameForceExtraction.S b D ViewData Rest Body View))
    (parameter : Parameter) (views : ViewAssignment (OriginalNameForceExtraction.Base b) Nat)
    (packet : OriginalReturnWorld.Packet (OriginalNameForceExtraction.Base b) D ViewData Rest Body View)
    (event : Event (OriginalNameForceExtraction.S b D ViewData Rest Body View)) :
    OriginalReturnWorld.fields readout frames before parameter views packet =
      OriginalNameEntryCorrespondence.eventFields event ↔
    packet.history = event.history ∧
    (readout.eta frames before (returnBinder parameter)
      (.returnRebind (packet.outcome views parameter))).original = event.eta.original ∧
    (readout.witness frames before (returnBinder parameter)
      (.returnRebind (packet.outcome views parameter))).current = event.witness.current ∧
    readout.scope frames before (returnBinder parameter)
      (.returnRebind (packet.outcome views parameter)) = event.scope ∧
    readout.authority frames before (returnBinder parameter)
      (.returnRebind (packet.outcome views parameter)) = event.authority ∧
    readout.incidence frames before (returnBinder parameter)
      (.returnRebind (packet.outcome views parameter)) = event.incidence ∧
    readout.dictionary frames before (returnBinder parameter)
      (.returnRebind (packet.outcome views parameter)) = event.dictionary := by
  simp only [OriginalReturnWorld.fields, OriginalNameEntryCorrespondence.eventFields, EventFields.mk.injEq]


/-- Every runtime constructor, including invocation and receipt, keeps the
original fiber and eta0. Its assignment/witness outputs may still change. -/
theorem runtime_preserves_static (readout : RuntimeReadout s View)
    (state : Decoded s View) (binder : Binder) (data : Runtime s View) :
    (state.runtime readout binder data).assignment.event.fiber = state.assignment.event.fiber ∧
    (state.runtime readout binder data).assignment.event.eta0 = state.assignment.event.eta0 :=
  ⟨rfl, rfl⟩

/-- All decoder payload constructors are covered, including arbitrary logical
EventProof, retained Shared, runtime and root frames. No source form is dropped. -/
theorem frame_preserves_static (readout : RuntimeReadout s View)
    (state : Decoded s View) (frame : Frame (Payload s View)) :
    (decodeFrame readout state frame).assignment.event.fiber = state.assignment.event.fiber ∧
    (decodeFrame readout state frame).assignment.event.eta0 = state.assignment.event.eta0 := by
  unfold decodeFrame
  split <;> exact ⟨rfl, rfl⟩

/-- A complete original preparation keeps static indices for an arbitrary
finite list of source frames, with no successful-execution hypothesis. -/
theorem frames_preserve_static (readout : RuntimeReadout s View)
    (initial : Decoded s View) (frames : List (Frame (Payload s View))) :
    (frames.foldl (decodeFrame readout) initial).assignment.event.fiber = initial.assignment.event.fiber ∧
    (frames.foldl (decodeFrame readout) initial).assignment.event.eta0 = initial.assignment.event.eta0 := by
  induction frames generalizing initial with
  | nil => exact ⟨rfl, rfl⟩
  | cons frame frames ih =>
      have first := frame_preserves_static readout initial frame
      have rest := ih (decodeFrame readout initial frame)
      exact ⟨rest.1.trans first.1, rest.2.trans first.2⟩

/-- The entire original dependent prior telescope is retained. This equation
supplies no initial root, native decoder or original world certificate. -/
theorem telescope_preserves_static (readout : RuntimeReadout s View)
    (initial : Decoded s View) (scope : List ScopeEntry) (telescope : Telescope s View scope) :
    (replayTelescope readout initial telescope).assignment.event.fiber = initial.assignment.event.fiber ∧
    (replayTelescope readout initial telescope).assignment.event.eta0 = initial.assignment.event.eta0 :=
  frames_preserve_static readout initial telescope.frames

/-- Receipt and demand preparations may be different frame lists and have
different current configurations/evidence. If both are constructed from the
same original decoded root, the first two alignment coordinates follow by
constructor composition; no receipt/demand event equality is introduced.
The missing native-to-decoder realization of these lists is not established. -/
theorem preparations_preserve_static
    (native : OriginalNameForceExtraction.Native b D ViewData Rest Body View)
    (readout : RuntimeReadout (OriginalNameForceExtraction.S b D ViewData Rest Body View) View)
    (initial : Decoded (OriginalNameForceExtraction.S b D ViewData Rest Body View) View)
    (receiptFrames demandFrames :
      List (Frame (Payload (OriginalNameForceExtraction.S b D ViewData Rest Body View) View)))
    (delay : OriginalIdentityCarrier.NameDelay) (fuel : Nat) :
    (receiptFrames.foldl (decodeFrame readout) initial).assignment.event.fiber =
      (OriginalNameForceExtraction.eventAt native delay
        (demandFrames.foldl (decodeFrame readout) initial).assignment.event fuel).fiber ∧
    (receiptFrames.foldl (decodeFrame readout) initial).assignment.event.eta0 =
      (OriginalNameForceExtraction.eventAt native delay
        (demandFrames.foldl (decodeFrame readout) initial).assignment.event fuel).eta0 := by
  have receipt := frames_preserve_static readout initial receiptFrames
  have demand := frames_preserve_static readout initial demandFrames
  have forced := prefix_preserves_indices native delay
    (demandFrames.foldl (decodeFrame readout) initial).assignment.event fuel
  exact ⟨receipt.1.trans (forced.1.trans demand.1).symm,
    receipt.2.trans (forced.2.1.trans demand.2).symm⟩

/-- Exact first remaining view equation: the fixed source interpretation must
already match the actual demand. Prefix execution cannot establish that fact. -/
theorem force_view_equation_iff
    (native : OriginalNameForceExtraction.Native b D ViewData Rest Body View)
    (delay : OriginalIdentityCarrier.NameDelay)
    (demand : Event (OriginalNameForceExtraction.S b D ViewData Rest Body View))
    (fuel : Nat) (sourceViews : ViewAssignment (OriginalNameForceExtraction.Base b) Nat) :
    sourceViews = (OriginalNameForceExtraction.eventAt native delay demand fuel).eta.views ↔
      sourceViews = demand.eta.views := by
  rw [(prefix_preserves_indices native delay demand fuel).2.2.1]

/-- Shared witness is another independent receipt-to-demand equation. An
EventProof or runtime readout may change it before the demand is constructed. -/
theorem force_shared_equation_iff
    (native : OriginalNameForceExtraction.Native b D ViewData Rest Body View)
    (delay : OriginalIdentityCarrier.NameDelay)
    (receipt demand : Event (OriginalNameForceExtraction.S b D ViewData Rest Body View))
    (fuel : Nat) :
    receipt.witness.shared =
      (OriginalNameForceExtraction.eventAt native delay demand fuel).witness.shared ↔
      receipt.witness.shared = demand.witness.shared := by
  rw [(prefix_preserves_indices native delay demand fuel).2.2.2]

end YulangClosure.OriginalNameReceiptSeed
