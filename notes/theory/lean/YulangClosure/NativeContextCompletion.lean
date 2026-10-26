import YulangClosure.NativeContextReadback
import YulangClosure.NativeReplayAcknowledgement

/-! Concrete queue callbacks for emitted Effect children. The function acts on
one shared readback/drain state; its successful return constructs the native
enqueue event. Dependency emissions are retained separately because the frozen
readback driver has no child-admission dependency event. No memo or pending key
is used as a completion certificate. -/
namespace YulangClosure.NativeContextCompletion

open NativeMergeExpansion NativeContextExpansion
open NativeReplayCurrent (Pair admittedChild sourceContext)
namespace R
export NativeContextReadback (State Work Frame Control Relation Task Run Step)
end R

structure Plan where
  relation : Nat
  task : Nat
  front : Bool := false
  reserved : Bool := true
  deriving DecidableEq, Repr

structure Emission where
  pair : Pair
  plan : Plan
  deriving DecidableEq, Repr

structure Receipt where
  key : Key
  work : NativeDrainOwnership.Work
  deriving DecidableEq, Repr

structure CallbackState (t : Tables) where
  native : NativeContextReadback.State t
  derived : List (Nat × Nat) := []

structure Result (t : Tables) where
  state : CallbackState t
  receipt : Option Receipt

/-- Selected interned IDs are checked against the complete child key and raw
child task. Existing relation IDs are legal and still enqueue a NEW occurrence.
The source view/weight interner guard remains the actual sourceAvailable check. -/
def rawGuard {t : Tables} (s : NativeContextReadback.State t) (parent : Key)
    (processing : Nat) (pair : Pair) (plan : Plan) : Bool :=
  let child := admittedChild (admissionTables t) s.effectMap parent pair
  sourceAvailable t pair.2 && relationGuard child &&
    decide (s.relations processing = some (.effect parent)) &&
    decide (s.relations plan.relation = some (.effect child)) &&
    decide (s.tasks plan.task = some (.effect pair.1 pair.2))

def queued {t : Tables} (s : NativeContextReadback.State t) (plan : Plan) :
    NativeContextReadback.State t :=
  NativeContextReadback.controlOnly s
    (NativeDrainOwnership.pushWork s.control
      (NativeDrainOwnership.work s.control plan.task plan.relation none) plan.front)

/-- Admission/Derived precedes reserve/queue. A failed reservation returns the
state AFTER dependency admission and no queue receipt, just as enqueue_item
can fail after candidate_context_admit. This is not a rollback claim. -/
def enqueueChild {t : Tables} (s : CallbackState t) (parent : Key)
    (processing : Nat) (input : Emission) : Result t :=
  match s.native.control.frames with
  | [] => ⟨s, none⟩
  | f :: _ =>
      if f.phase = .working ∧ f.current.isSome = true ∧ f.processing = some processing ∧
          rawGuard s.native parent processing input.pair input.plan = true then
        let admitted := { s with derived := s.derived ++ [(processing, input.plan.relation)] }
        if input.plan.reserved then
          ⟨{ admitted with native := queued s.native input.plan },
            some ⟨admittedChild (admissionTables t) s.native.effectMap parent input.pair,
              NativeDrainOwnership.work s.native.control input.plan.task input.plan.relation none⟩⟩
        else ⟨admitted, none⟩
      else ⟨s, none⟩

/-- Full table identities and source-local Context follow from successful raw
lookup checks, not a semantic callback or a completed-body assumption. -/
theorem raw_guard_exact {t : Tables} {s : NativeContextReadback.State t}
    {parent : Key} {processing : Nat} {pair : Pair} {plan : Plan}
    (guard : rawGuard s parent processing pair plan = true) :
    let child := admittedChild (admissionTables t) s.effectMap parent pair
    sourceAvailable t pair.2 = true ∧ relationGuard child = true ∧
      s.relations processing = some (.effect parent) ∧
      s.relations plan.relation = some (.effect child) ∧
      s.tasks plan.task = some (.effect pair.1 pair.2) := by
  simpa only [rawGuard, Bool.and_eq_true_iff, decide_eq_true_eq, and_assoc] using guard

/-- The exact callback successful-return inversion, including caller identity. -/
theorem enqueue_success {t : Tables} {s : CallbackState t} {parent : Key}
    {processing : Nat} {input : Emission} {receipt : Receipt}
    (success : (enqueueChild s parent processing input).receipt = some receipt) :
    ∃ f fs, s.native.control.frames = f :: fs ∧ f.phase = .working ∧
      f.current.isSome = true ∧ f.processing = some processing ∧
      rawGuard s.native parent processing input.pair input.plan = true ∧
      input.plan.reserved = true ∧
      receipt = ⟨admittedChild (admissionTables t) s.native.effectMap parent input.pair,
        NativeDrainOwnership.work s.native.control input.plan.task input.plan.relation none⟩ ∧
      (enqueueChild s parent processing input).state =
        ⟨queued s.native input.plan, s.derived ++ [(processing, input.plan.relation)]⟩ := by
  unfold enqueueChild at success ⊢
  split at success
  · cases success
  · rename_i f fs top
    split at success
    · rename_i guard
      split at success
      · rename_i reserved
        cases success
        exact ⟨f, fs, top, guard.1, guard.2.1, guard.2.2.1, guard.2.2.2,
          reserved, rfl, by simp [guard, reserved]⟩
      · cases success
    · cases success

/-- Queue insertion is the existing native event, and its unchanged-frame
projection is an existing readback event from the SAME state. -/
theorem queued_step {t : Tables} (s : NativeContextReadback.State t) (plan : Plan)
    (f : NativeDrainOwnership.Frame) (fs : List NativeDrainOwnership.Frame)
    (top : s.control.frames = f :: fs) (working : f.phase = .working) :
    NativeDrainOwnership.Step s.control (queued s plan).control ∧
      NativeContextReadback.Step t s (queued s plan) := by
  have native : NativeDrainOwnership.Step s.control (queued s plan).control :=
    .enqueuePlain s.control f fs plan.task plan.relation plan.front top working
  refine ⟨native, .control s (queued s plan).control native ?_ ?_⟩
  · rfl
  · intro _; rfl

theorem queued_work {t : Tables} (s : NativeContextReadback.State t) (plan : Plan) :
    let w := NativeDrainOwnership.work s.control plan.task plan.relation none
    w ∈ (queued s plan).control.queue ∧ w ∈ (queued s plan).control.issued ∧
      w.ticket = none ∧ w.relation = plan.relation ∧ w.task = plan.task ∧
      (queued s plan).control.frames = s.control.frames ∧
      (queued s plan).memo = s.memo ∧ (queued s plan).owners = s.owners := by
  cases front : plan.front <;>
    simp [front, queued, NativeContextReadback.controlOnly, NativeDrainOwnership.pushWork,
      NativeDrainOwnership.work]

theorem enqueue_constructs_history {t : Tables} {s : CallbackState t} {parent : Key}
    {processing : Nat} {input : Emission} {receipt : Receipt}
    (success : (enqueueChild s parent processing input).receipt = some receipt) :
    NativeContextReadback.Run t s.native (enqueueChild s parent processing input).state.native ∧
      receipt.work ∈ (enqueueChild s parent processing input).state.native.control.queue ∧
      receipt.work ∈ (enqueueChild s parent processing input).state.native.control.issued ∧
      receipt.work.ticket = none ∧
      (processing, receipt.work.relation) ∈ (enqueueChild s parent processing input).state.derived ∧
      receipt.key.context = sourceContext (admissionTables t) input.pair.2 ∧
      receipt.key.sources = parent.sources ∧ receipt.key.transformer = parent.transformer := by
  obtain ⟨f, fs, top, working, _, _, _, _, same, result⟩ := enqueue_success success
  rw [result, same]
  have owned := queued_work s.native input.plan
  exact ⟨.snoc (.nil _) (queued_step s.native input.plan f fs top working).2,
    owned.1, owned.2.1, owned.2.2.1, by simp [NativeDrainOwnership.work], rfl, rfl, rfl⟩

/-- All callback outcomes refine the existing forward history, including failed
reservations. A failure never invents a queue event. -/
theorem enqueue_run {t : Tables} (s : CallbackState t) (parent : Key)
    (processing : Nat) (input : Emission) :
    NativeContextReadback.Run t s.native (enqueueChild s parent processing input).state.native := by
  cases h : (enqueueChild s parent processing input).receipt with
  | some receipt => exact (enqueue_constructs_history h).1
  | none =>
      unfold enqueueChild at h ⊢
      split
      · exact .nil _
      · split
        · split
          · simp_all
          · exact .nil _
        · exact .nil _

theorem enqueue_issued_retained {t : Tables} (s : CallbackState t) (parent : Key)
    (processing : Nat) (input : Emission) {w : NativeDrainOwnership.Work}
    (issued : w ∈ s.native.control.issued) :
    w ∈ (enqueueChild s parent processing input).state.native.control.issued := by
  unfold enqueueChild
  split
  · exact issued
  · split
    · split
      · exact List.mem_append_left _ issued
      · exact issued
    · exact issued

structure BatchResult (t : Tables) where
  state : CallbackState t
  receipts : List Receipt
  remaining : List Emission

def enqueueChildren {t : Tables} (parent : Key) (processing : Nat)
    (s : CallbackState t) : List Emission → BatchResult t
  | [] => ⟨s, [], []⟩
  | input :: rest =>
      let first := enqueueChild s parent processing input
      match first.receipt with
      | none => ⟨first.state, [], input :: rest⟩
      | some receipt =>
          let tail := enqueueChildren parent processing first.state rest
          ⟨tail.state, receipt :: tail.receipts, tail.remaining⟩

theorem run_trans {t : Tables} {s u v : NativeContextReadback.State t}
    (first : NativeContextReadback.Run t s u) (last : NativeContextReadback.Run t u v) :
    NativeContextReadback.Run t s v := by
  induction last with
  | nil => exact first
  | snoc _ event ih => exact .snoc ih event

theorem batch_run {t : Tables} (parent : Key) (processing : Nat) (s : CallbackState t)
    (inputs : List Emission) :
    NativeContextReadback.Run t s.native (enqueueChildren parent processing s inputs).state.native := by
  induction inputs generalizing s with
  | nil => exact .nil _
  | cons input rest ih =>
      simp only [enqueueChildren]
      cases h : (enqueueChild s parent processing input).receipt with
      | none => exact enqueue_run s parent processing input
      | some receipt => exact run_trans (enqueue_run s parent processing input) (ih _)

theorem batch_issued_retained {t : Tables} (parent : Key) (processing : Nat)
    (s : CallbackState t) (inputs : List Emission) {w : NativeDrainOwnership.Work}
    (issued : w ∈ s.native.control.issued) :
    w ∈ (enqueueChildren parent processing s inputs).state.native.control.issued := by
  induction inputs generalizing s with
  | nil => exact issued
  | cons input rest ih =>
      simp only [enqueueChildren]
      cases h : (enqueueChild s parent processing input).receipt with
      | none => exact enqueue_issued_retained s parent processing input issued
      | some receipt => exact ih _ (enqueue_issued_retained s parent processing input issued)

theorem batch_receipts_issued {t : Tables} (parent : Key) (processing : Nat)
    (s : CallbackState t) (inputs : List Emission) :
    ∀ receipt ∈ (enqueueChildren parent processing s inputs).receipts,
      receipt.work ∈ (enqueueChildren parent processing s inputs).state.native.control.issued := by
  induction inputs generalizing s with
  | nil => simp [enqueueChildren]
  | cons input rest ih =>
      simp only [enqueueChildren]
      cases h : (enqueueChild s parent processing input).receipt with
      | none => simp
      | some receipt =>
          intro selected member
          rcases List.mem_cons.mp member with same | later
          · subst selected
            exact batch_issued_retained parent processing _ rest (enqueue_constructs_history h).2.2.1
          · exact ih _ selected later

/-- A failed later callback retains all earlier successfully issued occurrences;
its unprocessed suffix is explicit, rather than pretending the batch succeeded. -/
theorem batch_partial_prefix {t : Tables} (parent : Key) (processing : Nat)
    (s : CallbackState t) (inputs : List Emission) :
    (enqueueChildren parent processing s inputs).receipts.length +
      (enqueueChildren parent processing s inputs).remaining.length = inputs.length := by
  induction inputs generalizing s with
  | nil => rfl
  | cons input rest ih =>
      simp only [enqueueChildren]
      cases h : (enqueueChild s parent processing input).receipt with
      | none => simp
      | some receipt => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using congrArg Nat.succ (ih _)

/-- This removes only drain control to express precisely the state fields a
successful or failed enqueue cannot change. -/
def contextData {t : Tables} (s : NativeContextReadback.State t) : NativeContextReadback.State t :=
  { s with control := NativeDrainOwnership.initial }

theorem enqueue_context_data {t : Tables} (s : CallbackState t) (parent : Key)
    (processing : Nat) (input : Emission) :
    contextData (enqueueChild s parent processing input).state.native = contextData s.native := by
  unfold enqueueChild
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

theorem enqueue_frames {t : Tables} (s : CallbackState t) (parent : Key)
    (processing : Nat) (input : Emission) :
    (enqueueChild s parent processing input).state.native.control.frames = s.native.control.frames := by
  unfold enqueueChild
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

theorem batch_context_data {t : Tables} (parent : Key) (processing : Nat)
    (s : CallbackState t) (inputs : List Emission) :
    contextData (enqueueChildren parent processing s inputs).state.native = contextData s.native := by
  induction inputs generalizing s with
  | nil => rfl
  | cons input rest ih =>
      simp only [enqueueChildren]
      cases h : (enqueueChild s parent processing input).receipt with
      | none => exact enqueue_context_data s parent processing input
      | some receipt => exact (ih _).trans (enqueue_context_data s parent processing input)

theorem batch_frames {t : Tables} (parent : Key) (processing : Nat)
    (s : CallbackState t) (inputs : List Emission) :
    (enqueueChildren parent processing s inputs).state.native.control.frames = s.native.control.frames := by
  induction inputs generalizing s with
  | nil => rfl
  | cons input rest ih =>
      simp only [enqueueChildren]
      cases h : (enqueueChild s parent processing input).receipt with
      | none => exact enqueue_frames s parent processing input
      | some receipt => exact (ih _).trans (enqueue_frames s parent processing input)

/-- Exact ordered child alignment is computed by the callback traversal. The
premise states that traversal reached its end, not that any child is complete. -/
theorem batch_complete_keys {t : Tables} (parent : Key) (processing : Nat)
    (s : CallbackState t) (inputs : List Emission)
    (complete : (enqueueChildren parent processing s inputs).remaining = []) :
    (enqueueChildren parent processing s inputs).receipts.map Receipt.key =
      inputs.map (fun input => admittedChild (admissionTables t) s.native.effectMap parent input.pair) := by
  induction inputs generalizing s with
  | nil => rfl
  | cons input rest ih =>
      simp only [enqueueChildren] at complete ⊢
      cases h : (enqueueChild s parent processing input).receipt with
      | none => simp [h] at complete
      | some receipt =>
          simp only [h] at complete ⊢
          have key : receipt.key = admittedChild (admissionTables t) s.native.effectMap parent input.pair := by
            obtain ⟨f, fs, top, working, current, processing, raw, reserved, same, state⟩ := enqueue_success h
            exact congrArg Receipt.key same
          have maps : (enqueueChild s parent processing input).state.native.effectMap = s.native.effectMap :=
            congrArg (fun state => state.effectMap) (enqueue_context_data s parent processing input)
          simp only [List.map_cons, key]
          rw [ih _ complete, maps]

/-- Native enqueue reuses an interned relation without replacing the caller's
memo owner. Repeated emissions remain separate serial occurrences. -/
theorem repeated_relation_new_occurrence {t : Tables} (s : NativeContextReadback.State t)
    (plan : Plan) :
    (NativeDrainOwnership.work (queued s plan).control plan.task plan.relation none).serial =
      (NativeDrainOwnership.work s.control plan.task plan.relation none).serial + 1 ∧
    (queued s plan).memo = s.memo ∧ (queued s plan).owners = s.owners := by
  exact ⟨rfl, rfl, rfl⟩

theorem native_step_issued_retained {s u : NativeDrainOwnership.State}
    (event : NativeDrainOwnership.Step s u) {w : NativeDrainOwnership.Work}
    (issued : w ∈ s.issued) : w ∈ u.issued := by
  cases event <;> simp_all [NativeDrainOwnership.pushWork]

theorem native_run_issued_retained {s u : NativeDrainOwnership.State}
    (history : NativeDrainOwnership.Run s u) {w : NativeDrainOwnership.Work}
    (issued : w ∈ s.issued) : w ∈ u.issued := by
  induction history with
  | nil => exact issued
  | snoc history event ih => exact native_step_issued_retained event ih

/-- Compose a completed Context owner with its actual successful child callbacks.
The list equality is the constructor's emitted list, not a closure hypothesis.
The resulting seal and every child's occurrence share one forward driver run. -/
theorem finish_after_callbacks {t : Tables} {s : CallbackState t}
    (prior : NativeContextReadback.Run t (NativeContextReadback.initial t) s.native)
    (owner : NativeContextReadback.Owner t) (inputs : List Emission)
    (complete : (enqueueChildren owner.key owner.relation s inputs).remaining = [])
    (f : NativeDrainOwnership.Frame) (fs : List NativeDrainOwnership.Frame)
    (top : s.native.control.frames = f :: fs) (working : f.phase = .working)
    (current : f.current = some owner.work) (processing : f.processing = some owner.relation)
    (owned : s.native.owners owner.work = some owner)
    (a : Availability) (levels : Nat → Nat) (body : Body) (transitions : Nat)
    (result : NativeContextReadback.finishPrefix t a levels s.native.effectMap owner.key
      owner.ready.packet.segment = some body)
    (children : body.children = inputs.map (fun input =>
      admittedChild (admissionTables t) s.native.effectMap owner.key input.pair)) :
    let batch := enqueueChildren owner.key owner.relation s inputs
    let packet : NativeContextReadback.BodyPacket t :=
      ⟨owner.key, body, .finished owner.ready.packet.construction a levels s.native.effectMap body result⟩
    let final := NativeContextReadback.finishOwner batch.state.native f fs owner packet transitions
    NativeContextReadback.Run t (NativeContextReadback.initial t) final ∧
      (owner, packet) ∈ final.seals ∧
      ∀ child ∈ body.children, ∃ receipt ∈ batch.receipts,
        receipt.key = child ∧ receipt.work ∈ final.control.issued := by
  dsimp only
  let batch := enqueueChildren owner.key owner.relation s inputs
  have data := batch_context_data owner.key owner.relation s inputs
  have maps : batch.state.native.effectMap = s.native.effectMap :=
    congrArg (fun state => state.effectMap) data
  have owners : batch.state.native.owners = s.native.owners :=
    congrArg (fun state => state.owners) data
  have frame : batch.state.native.control.frames = f :: fs :=
    (batch_frames owner.key owner.relation s inputs).trans top
  have done := NativeContextReadback.Step.finish batch.state.native f fs owner a levels body transitions
    frame working current processing (owners ▸ owned) (by simpa [maps] using result)
  refine ⟨run_trans (run_trans prior (batch_run owner.key owner.relation s inputs)) (.snoc (.nil _) done), ?_, ?_⟩
  · simp [NativeContextReadback.finishOwner]
  · intro child member
    have keys := batch_complete_keys owner.key owner.relation s inputs complete
    have selected : child ∈ batch.receipts.map Receipt.key := by rw [keys, ← children]; exact member
    obtain ⟨receipt, receiptMember, same⟩ := List.mem_map.mp selected
    exact ⟨receipt, receiptMember, same,
      batch_receipts_issued owner.key owner.relation s inputs receipt receiptMember⟩

/-- The selected fresh relation slot is filled by the existing interner event.
The absence/uniqueness arguments are raw table guards, not body completion. -/
theorem intern_child_event {t : Tables} (s : NativeContextReadback.State t)
    (parent : Key) (pair : Pair) (relation : Nat)
    (fresh : s.relations relation = none)
    (unique : ∀ old, s.relations old ≠ some (.effect
      (admittedChild (admissionTables t) s.effectMap parent pair)))
    (valid : relationGuard (admittedChild (admissionTables t) s.effectMap parent pair) = true) :
    let child := admittedChild (admissionTables t) s.effectMap parent pair
    let next := { s with relations := NativeContextReadback.put s.relations relation (.effect child) }
    NativeContextReadback.Step t s next ∧ next.relations relation = some (.effect child) ∧
      next.control = s.control ∧ next.memo = s.memo := by
  exact ⟨.intern s relation _ fresh unique valid,
    by simp [NativeContextReadback.put], rfl, rfl⟩

/-- Explicit failed-reservation readback: dependency admission has happened;
the queue/caller/memo stay at their pre-queue values and there is no receipt. -/
theorem enqueue_reservation_failure {t : Tables} (s : CallbackState t) (parent : Key)
    (processing : Nat) (input : Emission) (f : NativeDrainOwnership.Frame)
    (fs : List NativeDrainOwnership.Frame) (top : s.native.control.frames = f :: fs)
    (working : f.phase = .working) (current : f.current.isSome = true)
    (caller : f.processing = some processing)
    (raw : rawGuard s.native parent processing input.pair input.plan = true)
    (failed : input.plan.reserved = false) :
    enqueueChild s parent processing input =
      ⟨⟨s.native, s.derived ++ [(processing, input.plan.relation)]⟩, none⟩ := by
  simp [enqueueChild, top, working, current, caller, raw, failed]

/-- Apply the constructive callback history to the existing settled consumer.
No child-complete predicate is assumed: every child's issued occurrence comes
from enqueueChildren, then its actual receipt/body comes from the same later
forward history. The later history may contain duplicates and arbitrary merges. -/
theorem callbacks_settled_readback {t : Tables} {s : CallbackState t}
    (prior : NativeContextReadback.Run t (NativeContextReadback.initial t) s.native)
    (parent : Key) (processing : Nat) (inputs : List Emission)
    (complete : (enqueueChildren parent processing s inputs).remaining = [])
    (body : Body)
    (children : body.children = inputs.map (fun input =>
      admittedChild (admissionTables t) s.native.effectMap parent input.pair))
    (settled : NativeContextReadback.State t)
    (later : NativeContextReadback.Run t
      (enqueueChildren parent processing s inputs).state.native settled)
    (queue : settled.control.queue = []) (stack : settled.control.frames = []) :
    NativeContextReadback.Run t (NativeContextReadback.initial t) settled ∧
      (∀ child ∈ body.children, ∃ emitted ∈ (enqueueChildren parent processing s inputs).receipts,
        emitted.key = child ∧ ∃ receipt ∈ settled.receipts,
          receipt.work = emitted.work ∧ NativeContextReadback.Resolved settled receipt ∧
          NativeContextReadback.RouteValid settled receipt.route) ∧
      (∀ ticket ∈ settled.control.transferred, ∃ receipt ∈ settled.control.acknowledgements,
        receipt.ticket = ticket ∧ receipt.diagnosed = true) := by
  have history := run_trans (run_trans prior (batch_run parent processing s inputs)) later
  refine ⟨history, ?_, NativeDrainOwnership.quiescent_replay_acknowledged
    (NativeContextReadback.run_control history) queue stack⟩
  intro child member
  have keys := batch_complete_keys parent processing s inputs complete
  have selected : child ∈ (enqueueChildren parent processing s inputs).receipts.map Receipt.key := by
    rw [keys, ← children]; exact member
  obtain ⟨emitted, selected, same⟩ := List.mem_map.mp selected
  have issued := native_run_issued_retained (NativeContextReadback.run_control later)
    (batch_receipts_issued parent processing s inputs emitted selected)
  obtain ⟨receipt, stored, work, resolved, route⟩ :=
    NativeContextReadback.quiescent_original_context_readback history queue stack emitted.work issued
  exact ⟨emitted, selected, same, receipt, stored, work, resolved, route⟩

end YulangClosure.NativeContextCompletion


