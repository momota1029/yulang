import YulangClosure.NativeContextCompletion

/-! Constructor-derived emissions for the accepted Context decomposition.
The raw emitted pairs are computed from each actual inline operand outcome,
then the existing callback traversal creates real queue occurrences. No caller
supplies a favorable body child list. The remaining Rust extraction, interner
allocation, synchronous bound callbacks and lifetime obligations stay explicit.
-/
namespace YulangClosure.NativeContextCallbackConstruction

open NativeMergeExpansion NativeContextExpansion NativeContextCompletion
open NativeReplayCurrent (Pair admittedChild currentPair)

/-- The emitted child list follows from actual collect/admit computations;
this discharges list correspondence without assuming callback completion. -/
theorem admissions_exact_keys {t : Tables} {a : Availability} {q : Nat → Nat}
    {parent : Key} {pairs : List Pair} {keys : List Key}
    (aligned : Aligned (fun pair key => admit t a q parent pair = some key) pairs keys) :
    keys = pairs.map (admittedChild (admissionTables t) q parent) := by
  induction aligned with
  | nil => rfl
  | cons admitted aligned ih =>
      rw [(admit_payload admitted).1, ih]
      rfl

theorem operand_emission_exact {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {context : Nat} {pair : Pair} {keys : List Key}
    (computed : applyEffect t a levels q parent context pair = some (.children keys)) :
    ∃ pairs, Effect.checkOperand q (effectTables t) pair.1 pair.2 = .children pairs ∧
      keys = pairs.map (admittedChild (admissionTables t) q parent) := by
  obtain ⟨pairs, operand, admitted⟩ := apply_children_admitted computed
  exact ⟨pairs, operand, admissions_exact_keys admitted⟩

def emissions (pairs : List Pair) (plans : List Plan) : List Emission :=
  (pairs.zip plans).map fun entry => ⟨entry.1, entry.2⟩

theorem emissions_pairs (pairs : List Pair) (plans : List Plan)
    (length : pairs.length = plans.length) : (emissions pairs plans).map Emission.pair = pairs := by
  induction pairs generalizing plans with
  | nil => cases plans <;> simp_all [emissions]
  | cons pair rest ih =>
      cases plans with
      | nil => simp at length
      | cons plan plans =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at length
          simpa [emissions, List.zip_cons_cons, List.map_map] using congrArg (List.cons pair) (ih plans length)

/-- Direct collect/admit-to-worklist bridge for an actual operand child list.
The callback traversal independently constructs queue events; a.enqueue=true
from the pure decomposition is never used as their ownership certificate. -/
theorem collected_callbacks_issue_all {t : Tables} {s : CallbackState t}
    (parent : Key) (processing : Nat) (a : Availability)
    (pairs : List Pair) (keys : List Key) (plans : List Plan)
    (computed : collect (admit t a s.native.effectMap parent) pairs = some keys)
    (length : pairs.length = plans.length)
    (complete : (enqueueChildren parent processing s (emissions pairs plans)).remaining = []) :
    NativeContextReadback.Run t s.native
      (enqueueChildren parent processing s (emissions pairs plans)).state.native ∧
      (enqueueChildren parent processing s (emissions pairs plans)).receipts.map Receipt.key = keys ∧
      ∀ child ∈ keys, ∃ receipt ∈ (enqueueChildren parent processing s (emissions pairs plans)).receipts,
        receipt.key = child ∧ receipt.work ∈
          (enqueueChildren parent processing s (emissions pairs plans)).state.native.control.issued := by
  have admitted := admissions_exact_keys (collect_exact _ computed)
  have exactKeys := batch_complete_keys parent processing s (emissions pairs plans) complete
  have mapped : (emissions pairs plans).map (fun input =>
      admittedChild (admissionTables t) s.native.effectMap parent input.pair) =
      pairs.map (admittedChild (admissionTables t) s.native.effectMap parent) := by
    calc
      _ = ((emissions pairs plans).map Emission.pair).map
          (admittedChild (admissionTables t) s.native.effectMap parent) := by simp only [List.map_map, Function.comp_def]
      _ = _ := by rw [emissions_pairs pairs plans length]
  rw [mapped, ← admitted] at exactKeys
  refine ⟨batch_run parent processing s (emissions pairs plans), exactKeys, ?_⟩
  intro child member
  rw [← exactKeys] at member
  obtain ⟨receipt, selected, same⟩ := List.mem_map.mp member
  exact ⟨receipt, selected, same, batch_receipts_issued _ _ _ _ receipt selected⟩

/-- Raw child pairs emitted by one actual operand callback. The leaf tag
selects whether that callback emitted children; its operand table supplies the
ordered list. Other leaves emit no plain child tasks. -/
def leafPairs (t : Tables) (q : Nat → Nat) (pair : Pair) : Leaf → List Pair
  | .children _ => match Effect.checkOperand q (effectTables t) pair.1 pair.2 with
      | .children pairs => pairs
      | _ => []
  | _ => []

theorem apply_emissions_exact {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {context : Nat} {pair : Pair} {leaf : Leaf}
    (computed : applyEffect t a levels q parent context pair = some leaf) :
    leaf.childKeys = (leafPairs t q pair leaf).map (admittedChild (admissionTables t) q parent) := by
  cases leaf with
  | localReturn => rfl
  | bound fiber => rfl
  | conflict pair => rfl
  | children keys =>
      obtain ⟨pairs, operand, admitted⟩ := operand_emission_exact computed
      simpa [leafPairs, operand, Leaf.childKeys] using admitted

theorem filter_emissions_exact {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {view : Nat} {leaf : Leaf}
    (computed : applyFilter t a levels q parent view = some leaf) :
    leaf.childKeys = (leafPairs t q ((currentPair q parent).1, .allowance view) leaf).map
      (admittedChild (admissionTables t) q parent) := by
  cases leaf with
  | localReturn => rfl
  | bound fiber => rfl
  | conflict pair => rfl
  | children keys => exact apply_emissions_exact (filter_children_from_apply computed)

def checkPairs (t : Tables) (q : Nat → Nat) (parent : Key) (check : Check) : List Pair :=
  leafPairs t q ((currentPair q parent).1, .allowance check.view) check.leaf

/-- Checks retain parser order; continuation pairs follow ALL inline checks. -/
def bodyPairs (t : Tables) (q : Nat → Nat) (parent : Key) (body : Body) : List Pair :=
  body.checks.flatMap (checkPairs t q parent) ++
    body.continuation.toList.flatMap (leafPairs t q (currentPair q parent))

theorem check_emissions_exact {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {weight : Nat} {check : Check}
    (computed : checkFilter t a levels q parent weight = some check) :
    check.leaf.childKeys = (checkPairs t q parent check).map
      (admittedChild (admissionTables t) q parent) := by
  obtain ⟨_, payload, _, view, _, applied⟩ := check_filter_exact computed
  unfold checkPairs
  rw [view]
  exact filter_emissions_exact applied

theorem flatMap_pointwise {α β : Type} {xs : List α} {f g : α → List β}
    (same : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [same x (by simp), ih (fun y member => same y (List.mem_cons_of_mem _ member))]

/-- Exact whole-body constructor census. The list equality is a conclusion
proved from decompose's actual checks and continuation, never a supplied premise. -/
theorem body_emissions_exact {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {parsed : Parsed} {body : Body}
    (computed : decompose t a levels q parent parsed = some body) :
    body.children = (bodyPairs t q parent body).map (admittedChild (admissionTables t) q parent) := by
  obtain ⟨_, checks, _, _, _, continuation, _⟩ := decompose_exact computed
  have checked : ∀ check ∈ body.checks, check.leaf.childKeys =
      (checkPairs t q parent check).map (admittedChild (admissionTables t) q parent) := by
    intro check member
    obtain ⟨weight, _, called⟩ := aligned_member_right checks member
    exact check_emissions_exact called
  have rest : ∀ leaf ∈ body.continuation.toList, leaf.childKeys =
      (leafPairs t q (currentPair q parent) leaf).map
        (admittedChild (admissionTables t) q parent) := by
    intro leaf member
    exact apply_emissions_exact (continuation leaf (Option.mem_toList.mp member))
  simp only [Body.children, Body.leaves, List.flatMap_append, List.flatMap_map,
    bodyPairs, List.map_append, List.map_flatMap]
  rw [flatMap_pointwise checked, flatMap_pointwise rest]

/-- Constructor-derived emission equality for the exact staged fresh owner. -/
theorem fresh_finish_emissions {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {fuel : Nat} {parent : Key} {segment : NativeContextReadback.Prefix} {body : Body}
    (prepared : NativeContextReadback.prepare t a levels q fuel parent = some segment)
    (finished : NativeContextReadback.finishPrefix t a levels q parent segment = some body)
    (published : a.publish = true) :
    body.children = (bodyPairs t q parent body).map (admittedChild (admissionTables t) q parent) := by
  have expanded : expand t a levels q fuel parent = some body := by
    rw [← NativeContextReadback.staged_expand t a levels q fuel parent published, prepared]
    exact finished
  unfold expand at expanded
  split at expanded
  · obtain ⟨parsed, _, computed⟩ := Option.bind_eq_some_iff.mp expanded
    exact body_emissions_exact computed
  · cases expanded

/-- Select queue plans by the computed emission list. Length validation happens
before callbacks, so an insufficient plan vector cannot silently drop children.
A selected batch still retains the exact failure suffix from enqueueChildren. -/
def enqueueBody {t : Tables} (s : CallbackState t) (parent : Key) (processing : Nat)
    (body : Body) (plans : List Plan) : Option (BatchResult t) :=
  let pairs := bodyPairs t s.native.effectMap parent body
  if pairs.length = plans.length then
    some (enqueueChildren parent processing s (emissions pairs plans))
  else none

theorem enqueue_body_exact {t : Tables} {s : CallbackState t} {parent : Key}
    {processing : Nat} {body : Body} {plans : List Plan} {batch : BatchResult t}
    (computed : enqueueBody s parent processing body plans = some batch) :
    (bodyPairs t s.native.effectMap parent body).length = plans.length ∧
      batch = enqueueChildren parent processing s
        (emissions (bodyPairs t s.native.effectMap parent body) plans) := by
  dsimp only [enqueueBody] at computed
  split at computed
  · rename_i length
    exact ⟨length, (Option.some.inj computed).symm⟩
  · cases computed

theorem emissions_mapped {t : Tables} (q : Nat → Nat) (parent : Key)
    (pairs : List Pair) (plans : List Plan) (length : pairs.length = plans.length) :
    (emissions pairs plans).map (fun input => admittedChild (admissionTables t) q parent input.pair) =
      pairs.map (admittedChild (admissionTables t) q parent) := by
  calc
    _ = ((emissions pairs plans).map Emission.pair).map
        (admittedChild (admissionTables t) q parent) := by simp only [List.map_map, Function.comp_def]
    _ = _ := by rw [emissions_pairs pairs plans length]

/-- Every actual fresh complete body gets the exact callback-generated work
list. Both the body list and its correspondence to receipts are conclusions. -/
theorem fresh_body_callbacks {t : Tables} {s : CallbackState t}
    (parent : Key) (processing : Nat) (a : Availability) (levels : Nat → Nat) (fuel : Nat)
    (segment : NativeContextReadback.Prefix) (body : Body) (plans : List Plan)
    (prepared : NativeContextReadback.prepare t a levels s.native.effectMap fuel parent = some segment)
    (finished : NativeContextReadback.finishPrefix t a levels s.native.effectMap parent segment = some body)
    (published : a.publish = true) (batch : BatchResult t)
    (selected : enqueueBody s parent processing body plans = some batch)
    (complete : batch.remaining = []) :
    NativeContextReadback.Run t s.native batch.state.native ∧
      batch.receipts.map Receipt.key = body.children ∧
      (∀ child ∈ body.children, ∃ receipt ∈ batch.receipts,
        receipt.key = child ∧ receipt.work ∈ batch.state.native.control.issued) ∧
      contextData batch.state.native = contextData s.native ∧
      batch.state.native.control.frames = s.native.control.frames := by
  obtain ⟨length, same⟩ := enqueue_body_exact selected
  subst batch
  have childKeys := fresh_finish_emissions prepared finished published
  have keys := batch_complete_keys parent processing s
    (emissions (bodyPairs t s.native.effectMap parent body) plans) complete
  rw [emissions_mapped s.native.effectMap parent _ plans length, ← childKeys] at keys
  refine ⟨batch_run _ _ _ _, keys, ?_, batch_context_data _ _ _ _, batch_frames _ _ _ _⟩
  intro child member
  rw [← keys] at member
  obtain ⟨receipt, selected, same⟩ := List.mem_map.mp member
  exact ⟨receipt, selected, same, batch_receipts_issued _ _ _ _ receipt selected⟩

/-- Direct application to the existing body owner finish. No supplied emitted
list equality appears: it is derived from actual prepare/finish computations. -/
theorem constructed_finish_after_callbacks {t : Tables} {s : CallbackState t}
    (prior : NativeContextReadback.Run t (NativeContextReadback.initial t) s.native)
    (owner : NativeContextReadback.Owner t) (a : Availability) (levels : Nat → Nat)
    (fuel : Nat) (body : Body) (plans : List Plan)
    (prepared : NativeContextReadback.prepare t a levels s.native.effectMap fuel owner.key =
      some owner.ready.packet.segment)
    (finished : NativeContextReadback.finishPrefix t a levels s.native.effectMap owner.key
      owner.ready.packet.segment = some body)
    (published : a.publish = true)
    (length : (bodyPairs t s.native.effectMap owner.key body).length = plans.length)
    (complete : (enqueueChildren owner.key owner.relation s
      (emissions (bodyPairs t s.native.effectMap owner.key body) plans)).remaining = [])
    (f : NativeDrainOwnership.Frame) (fs : List NativeDrainOwnership.Frame)
    (top : s.native.control.frames = f :: fs) (working : f.phase = .working)
    (current : f.current = some owner.work) (processing : f.processing = some owner.relation)
    (owned : s.native.owners owner.work = some owner) (transitions : Nat) :
    let batch := enqueueChildren owner.key owner.relation s
      (emissions (bodyPairs t s.native.effectMap owner.key body) plans)
    let packet : NativeContextReadback.BodyPacket t :=
      ⟨owner.key, body, .finished owner.ready.packet.construction a levels s.native.effectMap body finished⟩
    let final := NativeContextReadback.finishOwner batch.state.native f fs owner packet transitions
    NativeContextReadback.Run t (NativeContextReadback.initial t) final ∧
      (owner, packet) ∈ final.seals ∧
      ∀ child ∈ body.children, ∃ receipt ∈ batch.receipts,
        receipt.key = child ∧ receipt.work ∈ final.control.issued := by
  apply finish_after_callbacks prior owner _ complete f fs top working current processing owned
    a levels body transitions finished
  rw [emissions_mapped s.native.effectMap owner.key _ plans length]
  exact fresh_finish_emissions prepared finished published

/-- Same-history settlement application after constructor-derived callbacks.
Merges/duplicates belong to the explicit later driver history; no favorable
body-child coverage callback or memo completion certificate is assumed. -/
theorem constructed_callbacks_settled {t : Tables} {s : CallbackState t}
    (prior : NativeContextReadback.Run t (NativeContextReadback.initial t) s.native)
    (parent : Key) (processing : Nat) (a : Availability) (levels : Nat → Nat) (fuel : Nat)
    (segment : NativeContextReadback.Prefix) (body : Body) (plans : List Plan)
    (prepared : NativeContextReadback.prepare t a levels s.native.effectMap fuel parent = some segment)
    (finished : NativeContextReadback.finishPrefix t a levels s.native.effectMap parent segment = some body)
    (published : a.publish = true)
    (length : (bodyPairs t s.native.effectMap parent body).length = plans.length)
    (complete : (enqueueChildren parent processing s
      (emissions (bodyPairs t s.native.effectMap parent body) plans)).remaining = [])
    (settled : NativeContextReadback.State t)
    (later : NativeContextReadback.Run t
      (enqueueChildren parent processing s
        (emissions (bodyPairs t s.native.effectMap parent body) plans)).state.native settled)
    (queue : settled.control.queue = []) (stack : settled.control.frames = []) :
    NativeContextReadback.Run t (NativeContextReadback.initial t) settled ∧
      (∀ child ∈ body.children, ∃ emitted ∈
          (enqueueChildren parent processing s
            (emissions (bodyPairs t s.native.effectMap parent body) plans)).receipts,
        emitted.key = child ∧ ∃ receipt ∈ settled.receipts,
          receipt.work = emitted.work ∧ NativeContextReadback.Resolved settled receipt ∧
          NativeContextReadback.RouteValid settled receipt.route) ∧
      (∀ ticket ∈ settled.control.transferred, ∃ receipt ∈ settled.control.acknowledgements,
        receipt.ticket = ticket ∧ receipt.diagnosed = true) := by
  apply callbacks_settled_readback prior parent processing _ complete body _ settled later queue stack
  rw [emissions_mapped s.native.effectMap parent _ plans length]
  exact fresh_finish_emissions prepared finished published

/-- Forward callback construction from its raw native guards. -/
theorem enqueue_from_guards {t : Tables} (s : CallbackState t) (parent : Key)
    (processing : Nat) (input : Emission) (f : NativeDrainOwnership.Frame)
    (fs : List NativeDrainOwnership.Frame) (top : s.native.control.frames = f :: fs)
    (working : f.phase = .working) (current : f.current.isSome = true)
    (caller : f.processing = some processing)
    (raw : rawGuard s.native parent processing input.pair input.plan = true)
    (reserved : input.plan.reserved = true) :
    (enqueueChild s parent processing input).receipt =
      some ⟨admittedChild (admissionTables t) s.native.effectMap parent input.pair,
        NativeDrainOwnership.work s.native.control input.plan.task input.plan.relation none⟩ := by
  simp [enqueueChild, top, working, current, caller, raw, reserved]

theorem raw_guard_context_data {t : Tables} {s u : NativeContextReadback.State t}
    (same : contextData s = contextData u) (parent : Key) (processing : Nat)
    (input : Emission) :
    rawGuard s parent processing input.pair input.plan = rawGuard u parent processing input.pair input.plan := by
  have maps := congrArg (fun state => state.effectMap) same
  have relations := congrArg (fun state => state.relations) same
  have tasks := congrArg (fun state => state.tasks) same
  change s.effectMap = u.effectMap at maps
  change s.relations = u.relations at relations
  change s.tasks = u.tasks at tasks
  simp only [rawGuard, maps, relations, tasks]

/-- The batch end is derived from the actual interner/table/resource/caller
checks. No completion certificate for any child is needed. -/
theorem batch_completes_from_guards {t : Tables} (s : CallbackState t)
    (parent : Key) (processing : Nat) (inputs : List Emission)
    (f : NativeDrainOwnership.Frame) (fs : List NativeDrainOwnership.Frame)
    (top : s.native.control.frames = f :: fs) (working : f.phase = .working)
    (current : f.current.isSome = true) (caller : f.processing = some processing)
    (guards : ∀ input ∈ inputs,
      rawGuard s.native parent processing input.pair input.plan = true ∧ input.plan.reserved = true) :
    (enqueueChildren parent processing s inputs).remaining = [] := by
  induction inputs generalizing s with
  | nil => rfl
  | cons input rest ih =>
      have first := guards input (by simp)
      have success := enqueue_from_guards s parent processing input f fs top working current caller first.1 first.2
      simp only [enqueueChildren, success]
      apply ih _ ((enqueue_frames s parent processing input).trans top)
      intro later member
      have selected := guards later (List.mem_cons_of_mem _ member)
      refine ⟨?_, selected.2⟩
      rw [raw_guard_context_data (enqueue_context_data s parent processing input)]
      exact selected.1

/-- Exact occurrence serials are consecutive even for an unsuccessful prefix;
reuse of relation IDs cannot merge distinct child work occurrences. -/
theorem batch_receipt_serials {t : Tables} (s : CallbackState t) (parent : Key)
    (processing : Nat) (inputs : List Emission) :
    (enqueueChildren parent processing s inputs).receipts.map (fun receipt => receipt.work.serial) =
      List.range' s.native.control.nextWork (enqueueChildren parent processing s inputs).receipts.length := by
  induction inputs generalizing s with
  | nil => rfl
  | cons input rest ih =>
      simp only [enqueueChildren]
      cases success : (enqueueChild s parent processing input).receipt with
      | none => rfl
      | some receipt =>
          obtain ⟨f, fs, top, working, current, caller, raw, reserved, same, output⟩ := enqueue_success success
          have serial : receipt.work.serial = s.native.control.nextWork := congrArg (fun receipt => receipt.work.serial) same
          have next : (enqueueChild s parent processing input).state.native.control.nextWork =
              s.native.control.nextWork + 1 := by rw [output]; rfl
          simp only [List.map_cons, List.length_cons, List.range'_succ, serial, ih, next]

/-- Distinct serials are proved from the actual allocated work stream, including
repeated identical relation/task IDs. -/
theorem batch_receipt_serials_distinct {t : Tables} (s : CallbackState t) (parent : Key)
    (processing : Nat) (inputs : List Emission) :
    ((enqueueChildren parent processing s inputs).receipts.map
      (fun receipt => receipt.work.serial)).Nodup := by
  rw [batch_receipt_serials]
  exact List.nodup_range'

/-- Parent application with both earlier supplied seams removed. The source
constructors determine the complete ordered child list; raw operational guards
make the callback traversal succeed; the actual finish event seals the body;
the same later history supplies each child's completed body/readback. -/
theorem guarded_finished_children_settled {t : Tables} {s : CallbackState t}
    (prior : NativeContextReadback.Run t (NativeContextReadback.initial t) s.native)
    (owner : NativeContextReadback.Owner t) (a : Availability) (levels : Nat → Nat)
    (fuel : Nat) (body : Body) (plans : List Plan)
    (prepared : NativeContextReadback.prepare t a levels s.native.effectMap fuel owner.key =
      some owner.ready.packet.segment)
    (finished : NativeContextReadback.finishPrefix t a levels s.native.effectMap owner.key
      owner.ready.packet.segment = some body)
    (published : a.publish = true)
    (length : (bodyPairs t s.native.effectMap owner.key body).length = plans.length)
    (f : NativeDrainOwnership.Frame) (fs : List NativeDrainOwnership.Frame)
    (top : s.native.control.frames = f :: fs) (working : f.phase = .working)
    (current : f.current = some owner.work) (processing : f.processing = some owner.relation)
    (owned : s.native.owners owner.work = some owner)
    (guards : ∀ input ∈ emissions (bodyPairs t s.native.effectMap owner.key body) plans,
      rawGuard s.native owner.key owner.relation input.pair input.plan = true ∧ input.plan.reserved = true)
    (transitions : Nat) (settled : NativeContextReadback.State t)
    (later :
      let batch := enqueueChildren owner.key owner.relation s
        (emissions (bodyPairs t s.native.effectMap owner.key body) plans)
      let packet : NativeContextReadback.BodyPacket t :=
        ⟨owner.key, body, .finished owner.ready.packet.construction a levels s.native.effectMap body finished⟩
      NativeContextReadback.Run t
        (NativeContextReadback.finishOwner batch.state.native f fs owner packet transitions) settled)
    (queue : settled.control.queue = []) (stack : settled.control.frames = []) :
    let batch := enqueueChildren owner.key owner.relation s
      (emissions (bodyPairs t s.native.effectMap owner.key body) plans)
    let packet : NativeContextReadback.BodyPacket t :=
      ⟨owner.key, body, .finished owner.ready.packet.construction a levels s.native.effectMap body finished⟩
    let completed := NativeContextReadback.finishOwner batch.state.native f fs owner packet transitions
    NativeContextReadback.Run t (NativeContextReadback.initial t) settled ∧
      (owner, packet) ∈ completed.seals ∧
      (∀ child ∈ body.children, ∃ emitted ∈ batch.receipts,
        emitted.key = child ∧ ∃ receipt ∈ settled.receipts,
          receipt.work = emitted.work ∧ NativeContextReadback.Resolved settled receipt ∧
          NativeContextReadback.RouteValid settled receipt.route) ∧
      (∀ ticket ∈ settled.control.transferred, ∃ receipt ∈ settled.control.acknowledgements,
        receipt.ticket = ticket ∧ receipt.diagnosed = true) := by
  have live : f.current.isSome = true := by simp [current]
  have complete := batch_completes_from_guards s owner.key owner.relation _ f fs top working live processing guards
  have built := constructed_finish_after_callbacks prior owner a levels fuel body plans prepared finished
    published length complete f fs top working current processing owned transitions
  have history := run_trans built.1 later
  refine ⟨history, built.2.1, ?_, NativeDrainOwnership.quiescent_replay_acknowledged
    (NativeContextReadback.run_control history) queue stack⟩
  intro child member
  obtain ⟨emitted, selected, key, issued⟩ := built.2.2 child member
  have retained := native_run_issued_retained (NativeContextReadback.run_control later) issued
  obtain ⟨receipt, stored, work, resolved, route⟩ :=
    NativeContextReadback.quiescent_original_context_readback history queue stack emitted.work retained
  exact ⟨emitted, selected, key, receipt, stored, work, resolved, route⟩

end YulangClosure.NativeContextCallbackConstruction



