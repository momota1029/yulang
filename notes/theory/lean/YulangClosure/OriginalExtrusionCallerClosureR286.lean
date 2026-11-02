import YulangClosure.OriginalExtrusionStorageClosureR285

/-! Conditional caller-reference closure of the operation-local extrusion model.
The caller payload is copied into retained Parents and external requests. Its
raw and canonical Value references therefore need an explicit entry premise. -/
namespace YulangClosure.OriginalExtrusionCallerClosureR286

open OriginalExtrusionWork
open OriginalExtrusionRowValidityR283
open OriginalExtrusionCaptureValidityR284
open OriginalExtrusionStorageClosureR285

/-- Both the raw Value reference and its kind-separated canonical image are
valid in the current store. Structural terms retain their raw term label. -/
def ValueRefValid (s : State) (endpoint : NativeValuePorts.ValueEndpoint) : Prop :=
  ValueValid s endpoint ∧ ValueValid s (endpoint.rename s.qv)

def RequestValid (s : State) (caller : NativeValueStructure.Request) : Prop :=
  ValueRefValid s caller.lower ∧ ValueRefValid s caller.upper

def CurrentCallerValid (s : State) : Prop := RequestValid s s.operation.caller

def SavedCallersValid (s : State) : Prop :=
  ∀ parent ∈ s.parents, RequestValid s parent.operation.caller

/-- The local storage invariant together with every current and retained
caller endpoint, including raw and canonical Value bounds. -/
def CallerClosure (s : State) : Prop :=
  StorageClosed s ∧ CurrentCallerValid s ∧ SavedCallersValid s

def CallerFieldsValid (s : State) : Prop :=
  CurrentCallerValid s ∧ SavedCallersValid s

theorem caller_closure_storage (s : State) (h : CallerClosure s) : StorageClosed s := h.1

theorem caller_closure_capture_complete (s : State) (h : CallerClosure s) :
    CaptureComplete s := storage_implies_capture_complete s h.1

theorem capture_gap_not_caller_closure (caller : NativeValueStructure.Request) :
    ¬ CallerClosure (captureGap caller) := by
  intro h
  exact capture_gap_not_storage caller h.1

theorem view_tail_gap_not_caller_closure : ¬ CallerClosure viewTailGap := by
  intro h
  exact view_tail_gap_not_storage h.1

theorem current_caller_implies_r285 (s : State) (h : CurrentCallerValid s) :
    CallerRowsValid s := ⟨h.1.1, h.2.1⟩

theorem caller_closure_not_universal_computed_input :
    ¬ (∀ caller : NativeValueStructure.Request,
      CallerClosure (Computed.rowInput caller)) := by
  exact no_universal_computed_input_with_caller CallerClosure
    (fun _ h => current_caller_implies_r285 _ h.2.1)

/-- This is an equivalence of model predicates, not a claim that arbitrary
Requests or production entries satisfy the four endpoint checks. -/
theorem computed_rowInput_caller_closure_iff (caller : NativeValueStructure.Request) :
    CallerClosure (Computed.rowInput caller) ↔
      RequestValid (Computed.rowInput caller) caller := by
  constructor
  · intro h
    exact h.2.1
  · intro h
    exact ⟨computed_rowInput_storage caller, h, by simp [SavedCallersValid, Computed.rowInput]⟩

theorem computed_rowInput_caller_closure (caller : NativeValueStructure.Request)
    (valid : RequestValid (Computed.rowInput caller) caller) :
    CallerClosure (Computed.rowInput caller) :=
  (computed_rowInput_caller_closure_iff caller).2 valid

theorem value_valid_allocate (s : State) (key : CopyKey)
    (endpoint : NativeValuePorts.ValueEndpoint) (h : ValueValid s endpoint) :
    ValueValid (s.allocate key) endpoint := by
  cases key with
  | mk keyEndpoint polarity target =>
    cases keyEndpoint <;> cases endpoint <;>
      simp_all [ValueValid, State.allocate, State.storedTerm] <;> omega

theorem value_ref_valid_allocate (s : State) (key : CopyKey)
    (endpoint : NativeValuePorts.ValueEndpoint) (h : ValueRefValid s endpoint) :
    ValueRefValid (s.allocate key) endpoint := by
  cases endpoint with
  | row id =>
    have hq := value_canonical_old_after_allocate s key id h.1
    constructor
    · exact value_valid_allocate s key (.row id) h.1
    · change (s.allocate key).qv id < (s.allocate key).values.length
      rw [hq]
      have hc : s.qv id < s.values.length := h.2
      cases key with
      | mk keyEndpoint polarity target =>
        cases keyEndpoint <;> simp only [State.allocate, List.length_append,
          List.length_singleton, Nat.add_one] <;> omega
  | _ =>
    cases key with
    | mk keyEndpoint polarity target =>
      cases keyEndpoint <;>
        simp_all [ValueRefValid, ValueValid, NativeValuePorts.ValueEndpoint.rename,
          State.allocate, State.storedTerm]

theorem request_valid_allocate (s : State) (key : CopyKey)
    (caller : NativeValueStructure.Request) (h : RequestValid s caller) :
    RequestValid (s.allocate key) caller :=
  ⟨value_ref_valid_allocate s key caller.lower h.1,
    value_ref_valid_allocate s key caller.upper h.2⟩

/-- A frame that preserves the Value-store size, old canonical map, and term
directory preserves exact raw/canonical caller validity. Bounds can change. -/
theorem value_ref_valid_same_frame (s t : State)
    (endpoint : NativeValuePorts.ValueEndpoint)
    (hlen : t.values.length = s.values.length)
    (hqv : t.qv = s.qv) (hterms : t.terms = s.terms)
    (h : ValueRefValid s endpoint) : ValueRefValid t endpoint := by
  cases endpoint <;>
    simp_all [ValueRefValid, ValueValid, NativeValuePorts.ValueEndpoint.rename,
      State.storedTerm]

theorem request_valid_same_frame (s t : State)
    (caller : NativeValueStructure.Request)
    (hlen : t.values.length = s.values.length)
    (hqv : t.qv = s.qv) (hterms : t.terms = s.terms)
    (h : RequestValid s caller) : RequestValid t caller :=
  ⟨value_ref_valid_same_frame s t caller.lower hlen hqv hterms h.1,
    value_ref_valid_same_frame s t caller.upper hlen hqv hterms h.2⟩

/-- Structural caller labels require preservation of their exact stored term;
row callers require only growing Value storage and the unchanged old qv entry. -/
theorem value_valid_mono (s t : State)
    (endpoint : NativeValuePorts.ValueEndpoint)
    (hlen : s.values.length ≤ t.values.length)
    (hterm : ∀ term, s.storedTerm term ≠ none → t.storedTerm term ≠ none)
    (h : ValueValid s endpoint) : ValueValid t endpoint := by
  cases endpoint <;> simp_all [ValueValid] <;> omega

theorem value_ref_valid_mono (s t : State)
    (endpoint : NativeValuePorts.ValueEndpoint)
    (hlen : s.values.length ≤ t.values.length)
    (hqv : ∀ id, id < s.values.length → t.qv id = s.qv id)
    (hterm : ∀ term, s.storedTerm term ≠ none → t.storedTerm term ≠ none)
    (h : ValueRefValid s endpoint) : ValueRefValid t endpoint := by
  cases endpoint with
  | row id =>
    refine ⟨value_valid_mono s t (.row id) hlen hterm h.1, ?_⟩
    change t.qv id < t.values.length
    rw [hqv id h.1]
    exact Nat.lt_of_lt_of_le h.2 hlen
  | _ =>
    simp_all [ValueRefValid, ValueValid, NativeValuePorts.ValueEndpoint.rename]

theorem request_valid_mono (s t : State)
    (caller : NativeValueStructure.Request)
    (hlen : s.values.length ≤ t.values.length)
    (hqv : ∀ id, id < s.values.length → t.qv id = s.qv id)
    (hterm : ∀ term, s.storedTerm term ≠ none → t.storedTerm term ≠ none)
    (h : RequestValid s caller) : RequestValid t caller :=
  ⟨value_ref_valid_mono s t caller.lower hlen hqv hterm h.1,
    value_ref_valid_mono s t caller.upper hlen hqv hterm h.2⟩

theorem caller_fields_same_frame (s t : State)
    (hop : t.operation = s.operation)
    (hlen : t.values.length = s.values.length)
    (hqv : t.qv = s.qv) (hterms : t.terms = s.terms)
    (hparents : t.parents = s.parents)
    (h : CallerFieldsValid s) : CallerFieldsValid t := by
  constructor
  · simpa [CurrentCallerValid, hop] using
      request_valid_same_frame s t s.operation.caller hlen hqv hterms h.1
  · intro parent membership
    exact request_valid_same_frame s t parent.operation.caller hlen hqv hterms
      (h.2 parent (by simpa [hparents] using membership))

theorem caller_fields_select (s popped : State) (task : Work)
    (selected : select s = some (task, popped))
    (h : CallerFieldsValid s) : CallerFieldsValid popped := by
  unfold select at selected
  cases hw : s.work with
  | cons item rest =>
    simp [hw] at selected
    rcases selected with ⟨_, hpopped⟩
    subst popped
    exact caller_fields_same_frame s {s with work := rest} rfl rfl rfl rfl rfl h
  | nil =>
    cases hp : s.pendingBounds with
    | nil => simp [hw, hp] at selected
    | cons item rest =>
      simp [hw, hp] at selected
      rcases selected with ⟨_, hpopped⟩
      subst popped
      exact caller_fields_same_frame s {s with pendingBounds := rest}
        rfl rfl rfl rfl rfl h

theorem rows_valid_work_tail (s : State) (task : Work) (rest : List Work)
    (h : RowsValid {s with work := task :: rest}) :
    RowsValid {s with work := rest} := by
  rcases h with ⟨hinit, hqv, hqe, hvalues, heffects, hterms, hrows,
    hstruct, hwork, hpend, hports, hparents, hindex⟩
  refine ⟨hinit, hqv, hqe, hvalues, heffects, hterms, hrows,
    hstruct, ?_, hpend, hports, hparents, hindex⟩
  intro item hm
  exact hwork item (List.mem_cons_of_mem task hm)

theorem rows_valid_pending_tail (s : State) (task : Work) (rest : List Work)
    (h : RowsValid {s with pendingBounds := task :: rest}) :
    RowsValid {s with pendingBounds := rest} := by
  rcases h with ⟨hinit, hqv, hqe, hvalues, heffects, hterms, hrows,
    hstruct, hwork, hpend, hports, hparents, hindex⟩
  refine ⟨hinit, hqv, hqe, hvalues, heffects, hterms, hrows,
    hstruct, hwork, ?_, hports, hparents, hindex⟩
  intro item hm
  exact hpend item (List.mem_cons_of_mem task hm)

theorem view_refs_valid_work_tail (s : State) (task : Work) (rest : List Work)
    (h : ViewRefsValid {s with work := task :: rest}) :
    ViewRefsValid {s with work := rest} := by
  rcases h with ⟨hinitial, heffects, hterms, hcaptures, hrows,
    hstructure, hwork, hpending, hports, hparents⟩
  refine ⟨hinitial, heffects, hterms, hcaptures, hrows,
    hstructure, ?_, hpending, hports, hparents⟩
  intro item hm
  exact hwork item (List.mem_cons_of_mem task hm)

theorem view_refs_valid_pending_tail (s : State) (task : Work) (rest : List Work)
    (h : ViewRefsValid {s with pendingBounds := task :: rest}) :
    ViewRefsValid {s with pendingBounds := rest} := by
  rcases h with ⟨hinitial, heffects, hterms, hcaptures, hrows,
    hstructure, hwork, hpending, hports, hparents⟩
  refine ⟨hinitial, heffects, hterms, hcaptures, hrows,
    hstructure, hwork, ?_, hports, hparents⟩
  intro item hm
  exact hpending item (List.mem_cons_of_mem task hm)

theorem storage_closed_work_tail (s : State) (task : Work) (rest : List Work)
    (h : StorageClosed {s with work := task :: rest}) :
    StorageClosed {s with work := rest} := by
  rcases h with ⟨hrows, hcaptures, ht, hl, hv, hb, hm, hp⟩
  exact ⟨rows_valid_work_tail s task rest hrows, hcaptures, ht, hl,
    view_refs_valid_work_tail s task rest hv, hb, hm, hp⟩

theorem storage_closed_pending_tail (s : State) (task : Work) (rest : List Work)
    (h : StorageClosed {s with pendingBounds := task :: rest}) :
    StorageClosed {s with pendingBounds := rest} := by
  rcases h with ⟨hrows, hcaptures, ht, hl, hv, hb, hm, hp⟩
  exact ⟨rows_valid_pending_tail s task rest hrows, hcaptures, ht, hl,
    view_refs_valid_pending_tail s task rest hv, hb, hm, hp⟩

theorem caller_closure_select (s popped : State) (task : Work)
    (selected : select s = some (task, popped))
    (h : CallerClosure s) : CallerClosure popped := by
  have hfields : CallerFieldsValid popped :=
    caller_fields_select s popped task selected ⟨h.2.1, h.2.2⟩
  constructor
  · unfold select at selected
    cases hw : s.work with
    | cons item rest =>
      simp [hw] at selected
      rcases selected with ⟨_, hpopped⟩
      subst popped
      have hs : {s with work := item :: rest} = s := by
        rw [← hw]
      exact storage_closed_work_tail s item rest (by rw [hs]; exact h.1)
    | nil =>
      cases hp : s.pendingBounds with
      | nil => simp [hw, hp] at selected
      | cons item rest =>
        simp [hw, hp] at selected
        rcases selected with ⟨_, hpopped⟩
        subst popped
        have hs : {s with pendingBounds := item :: rest} = s := by
          rw [← hp]
        have htail : {s with work := [], pendingBounds := rest} =
            {s with pendingBounds := rest} := by
          rw [← hw]
        rw [htail]
        exact storage_closed_pending_tail s item rest (by rw [hs]; exact h.1)
  · exact hfields

theorem current_caller_valid_allocate (s : State) (key : CopyKey)
    (h : CurrentCallerValid s) : CurrentCallerValid (s.allocate key) := by
  cases key with
  | mk endpoint polarity target =>
    cases endpoint <;> exact request_valid_allocate s
      ⟨_, polarity, target⟩ s.operation.caller h

theorem saved_callers_valid_allocate (s : State) (key : CopyKey)
    (h : SavedCallersValid s) : SavedCallersValid (s.allocate key) := by
  intro parent membership
  cases key with
  | mk endpoint polarity target =>
    cases endpoint <;>
      exact request_valid_allocate s ⟨_, polarity, target⟩ parent.operation.caller
        (h parent (by simpa [State.allocate] using membership))

theorem current_caller_valid_retain (s : State) (key : CopyKey) (copy : Endpoint)
    (h : CurrentCallerValid s) : CurrentCallerValid (s.retain key copy) := h

theorem saved_callers_valid_retain (s : State) (key : CopyKey) (copy : Endpoint)
    (hold : SavedCallersValid s) (hcurrent : CurrentCallerValid s) :
    SavedCallersValid (s.retain key copy) := by
  intro parent membership
  have hm : parent ∈ s.parents ∨ parent =
      ⟨copy, key.endpoint, key.polarity, key.target, s.operation⟩ := by
    simpa [State.retain] using membership
  rcases hm with old | new
  · exact hold parent old
  · subst parent
    exact hcurrent

theorem caller_fields_valid_retain (s : State) (key : CopyKey) (copy : Endpoint)
    (h : CallerFieldsValid s) : CallerFieldsValid (s.retain key copy) :=
  ⟨current_caller_valid_retain s key copy h.1,
    saved_callers_valid_retain s key copy h.2 h.1⟩

theorem caller_fields_valid_allocate (s : State) (key : CopyKey)
    (h : CallerFieldsValid s) : CallerFieldsValid (s.allocate key) :=
  ⟨current_caller_valid_allocate s key h.1, saved_callers_valid_allocate s key h.2⟩

theorem caller_fields_valid_physicalInsert (s t : State) (raw : RawBound)
    (inserted : physicalInsert s raw = .ok t)
    (h : CallerFieldsValid s) : CallerFieldsValid t := by
  unfold physicalInsert at inserted
  dsimp only at inserted
  split at inserted
  · simp only [requireSome] at inserted
    split at inserted
    · cases inserted
    · cases inserted
      apply caller_fields_same_frame s _
      all_goals first | rfl | simp only [List.length_set] | exact h
  · simp only [requireSome] at inserted
    split at inserted
    · cases inserted
    · cases inserted
      apply caller_fields_same_frame s _
      all_goals first | rfl | simp only [List.length_set] | exact h
  · simp at inserted

/-- The computed pre-link state has already allocated its row, retained its
Parent, and published the row memo. Calls and memo writes do not alter caller
references or their store. -/
theorem caller_fields_valid_prepared (s : State) (key : CopyKey)
    (h : CallerFieldsValid s) : CallerFieldsValid (prepared s key) := by
  let a : State := {s with calls := s.calls + 1}
  have ha : CallerFieldsValid a :=
    caller_fields_same_frame s a rfl rfl rfl rfl rfl h
  have hb : CallerFieldsValid (a.allocate key) := caller_fields_valid_allocate a key ha
  have hc : CallerFieldsValid ((a.allocate key).retain key (s.freshEndpoint key.endpoint)) :=
    caller_fields_valid_retain (a.allocate key) key (s.freshEndpoint key.endpoint) hb
  simpa [prepared, a] using
    (caller_fields_same_frame
      ((a.allocate key).retain key (s.freshEndpoint key.endpoint))
      (prepared s key) rfl rfl rfl rfl rfl hc)

/-- A failed native link gate leaves the newly retained Parent published.
The theorem establishes the caller component of that partial failure state. -/
theorem failed_before_link_caller_fields (s : State) (key : CopyKey)
    (old : List Endpoint) (error : Failure)
    (room : (match key.endpoint with
      | .value _ => s.values.length | .effect _ => s.effects.length) < 2^32)
    (h : CallerFieldsValid s) :
    CallerFieldsValid (resultState
      (copiedRow (fun _ point => if point = .linkBeforeAppend then .error error else .ok ())
        s key old)) := by
  rw [memo_precedes_link_call s key old error room]
  exact caller_fields_same_frame (prepared s key)
    {prepared s key with calls := (prepared s key).calls + 1}
    rfl rfl rfl rfl rfl (caller_fields_valid_prepared s key h)

theorem caller_fields_valid_preLink (s : State) (key : CopyKey)
    (h : CallerFieldsValid s) : CallerFieldsValid (preLink s key) :=
  caller_fields_same_frame (prepared s key) (preLink s key)
    rfl rfl rfl rfl rfl (caller_fields_valid_prepared s key h)

theorem caller_fields_check_failure (funds : Funding) (point : Check)
    (s : State) (next : State → Result) (error : Failure)
    (failed : funds s.calls point = .error error)
    (h : CallerFieldsValid s) :
    CallerFieldsValid (resultState (check funds point s next)) := by
  simp only [check, failed, resultState]
  exact caller_fields_same_frame s {s with calls := s.calls + 1}
    rfl rfl rfl rfl rfl h

theorem internCell_preserves_caller_store_fields (s t : State)
    (cell : StoredCell) (label : Nat)
    (computed : internCell s cell = .ok (t, label)) :
    t.operation = s.operation ∧ t.values = s.values ∧ t.qv = s.qv ∧
      t.parents = s.parents := by
  unfold internCell at computed
  split at computed
  next found =>
    split at computed
    · cases computed
      exact ⟨rfl, rfl, rfl, rfl⟩
    · cases computed
  next =>
    dsimp only at computed
    split at computed
    · cases computed
    · cases computed
      exact ⟨rfl, rfl, rfl, rfl⟩

theorem caller_fields_valid_internCell (s t : State)
    (cell : StoredCell) (label : Nat)
    (computed : internCell s cell = .ok (t, label))
    (h : CallerFieldsValid s) : CallerFieldsValid t := by
  obtain ⟨hop, hvalues, hqv, hparents⟩ :=
    internCell_preserves_caller_store_fields s t cell label computed
  have hterms : ∀ term, s.storedTerm term ≠ none → t.storedTerm term ≠ none := by
    intro term old
    cases hfound : s.storedTerm term with
    | none => simp [hfound] at old
    | some stored =>
      rw [cell_constructor_immutable s t cell label computed term stored hfound]
      simp
  have hlen : s.values.length ≤ t.values.length := by
    simp [hvalues]
  have hq : ∀ id, id < s.values.length → t.qv id = s.qv id := by
    intro id _
    rw [hqv]
  constructor
  · simpa [CurrentCallerValid, hop] using
      request_valid_mono s t s.operation.caller hlen hq hterms h.1
  · intro parent membership
    exact request_valid_mono s t parent.operation.caller hlen hq hterms
      (h.2 parent (by simpa [hparents] using membership))

/-- The actual post-append funding gate can fail after both Parent retention
and physical insertion. Its returned state still has valid caller references. -/
theorem after_link_check_failure_caller_fields (funds : Funding) (s linked : State)
    (key : CopyKey) (next : State → Result) (error : Failure)
    (link : physicalInsert (preLink s key)
      ⟨key.endpoint, opposite key.polarity, s.freshEndpoint key.endpoint⟩ = .ok linked)
    (failed : funds linked.calls .linkAfterAppend = .error error)
    (h : CallerFieldsValid s) :
    CallerFieldsValid (resultState (check funds .linkAfterAppend linked next)) := by
  have hpre := caller_fields_valid_preLink s key h
  have hlinked := caller_fields_valid_physicalInsert (preLink s key) linked
    ⟨key.endpoint, opposite key.polarity, s.freshEndpoint key.endpoint⟩ link hpre
  exact caller_fields_check_failure funds .linkAfterAppend linked next error failed hlinked

theorem current_caller_valid_replace (s : State) (operation : Operation)
    (h : RequestValid s operation.caller) :
    CurrentCallerValid {s with operation := operation} := h

theorem current_caller_valid_initializeLocal (s : State) (operation : Operation)
    (h : RequestValid s operation.caller) :
    CurrentCallerValid (initializeLocal s operation) := h

theorem saved_callers_valid_initializeLocal (s : State) (operation : Operation)
    (h : SavedCallersValid s) : SavedCallersValid (initializeLocal s operation) := h

theorem saved_callers_valid_replace (s : State) (operation : Operation)
    (h : SavedCallersValid s) :
    SavedCallersValid {s with operation := operation} := h

theorem caller_fields_valid_initializeLocal (s : State) (operation : Operation)
    (hcaller : RequestValid s operation.caller)
    (hsaved : SavedCallersValid s) :
    CallerFieldsValid (initializeLocal s operation) :=
  ⟨current_caller_valid_initializeLocal s operation hcaller,
    saved_callers_valid_initializeLocal s operation hsaved⟩

theorem bound_request_caller_valid (s : State) (owner : Endpoint)
    (p : NativeMergeExpansion.Polarity) (copied : Endpoint) (source : RawBound)
    (h : CurrentCallerValid s) :
    RequestValid s (boundRequest s owner p copied source).operation.caller := h

/-- The selected Bound branch publishes the copied caller against the exact
returned state, including both raw and canonical Value endpoints. -/
theorem selected_bound_external_caller_valid (funds : Funding) (s popped : State)
    (owner : Endpoint) (p : NativeMergeExpansion.Polarity)
    (child : CopyKey) (source : RawBound) (copied : Endpoint)
    (selected : select s = some (.bound owner p child source, popped))
    (memo : popped.lookup child = some copied)
    (h : CallerFieldsValid s) :
    step funds s = .external popped (.bound (boundRequest popped owner p copied source)) ∧
    RequestValid popped
      (boundRequest popped owner p copied source).operation.caller := by
  constructor
  · exact selected_bound_dispatch funds s popped owner p child source copied selected memo
  · exact bound_request_caller_valid popped owner p copied source
      (caller_fields_select s popped _ selected h).1

theorem selected_bound_external_result_caller_valid (funds : Funding) (s popped : State)
    (owner : Endpoint) (p : NativeMergeExpansion.Polarity)
    (child : CopyKey) (source : RawBound) (copied : Endpoint)
    (selected : select s = some (.bound owner p child source, popped))
    (memo : popped.lookup child = some copied)
    (h : CallerClosure s) :
    RequestValid (resultState (step funds s))
      (boundRequest popped owner p copied source).operation.caller := by
  rw [selected_bound_dispatch funds s popped owner p child source copied selected memo]
  exact bound_request_caller_valid popped owner p copied source
    (caller_closure_select s popped _ selected h).2.1

theorem selected_bound_caller_fields (funds : Funding) (s popped : State)
    (owner : Endpoint) (p : NativeMergeExpansion.Polarity)
    (child : CopyKey) (source : RawBound)
    (selected : select s = some (.bound owner p child source, popped))
    (h : CallerFieldsValid s) :
    CallerFieldsValid (resultState (step funds s)) := by
  simpa [step, selected, bound_perform_retains_state] using
    caller_fields_select s popped _ selected h

theorem selected_incoming_caller_fields (funds : Funding) (s popped : State)
    (tail view : Nat) (source : CopyKey) (original : RawBound)
    (selected : select s = some (.incomingAllowance tail view source original, popped))
    (h : CallerFieldsValid s) :
    CallerFieldsValid (resultState (step funds s)) := by
  simpa [step, selected, incoming_perform_retains_state] using
    caller_fields_select s popped _ selected h

theorem selected_effect_view_caller_fields (funds : Funding) (s popped : State)
    (key : CopyKey) (view : Nat) (child : CopyKey)
    (selected : select s = some (.effectView key view child, popped))
    (h : CallerFieldsValid s) :
    CallerFieldsValid (resultState (step funds s)) := by
  simpa [step, selected, effect_view_perform_retains_state] using
    caller_fields_select s popped _ selected h

/-- For these three Work constructors, `perform` only transfers or fails;
the queue pop was proved separately against all stored-reference clauses. -/
theorem selected_bound_preserves_caller_closure (funds : Funding) (s popped : State)
    (owner : Endpoint) (p : NativeMergeExpansion.Polarity)
    (child : CopyKey) (source : RawBound)
    (selected : select s = some (.bound owner p child source, popped))
    (h : CallerClosure s) :
    CallerClosure (resultState (step funds s)) := by
  simpa [step, selected, bound_perform_retains_state] using
    caller_closure_select s popped _ selected h

/-- A Visit whose row memo was already published is a no-op after queue pop.
New Visit allocations and structural continuation still need separate proofs. -/
theorem selected_memoized_visit_preserves_caller_closure
    (funds : Funding) (s popped : State) (key : CopyKey) (copied : Endpoint)
    (selected : select s = some (.visit key, popped))
    (found : popped.rows key = some copied)
    (h : CallerClosure s) :
    CallerClosure (resultState (step funds s)) := by
  rw [show step funds s = perform funds popped (.visit key) from by simp [step, selected]]
  change CallerClosure (resultState (visit funds popped key))
  rw [memoized_visit funds popped key copied found]
  exact caller_closure_select s popped _ selected h

theorem selected_aggregate_slice_failure_preserves_caller_closure
    (funds : Funding) (s popped : State) (kind : Aggregate)
    (key : CopyKey) (start len : Nat) (error : Failure)
    (selected : select s = some (aggregateWork kind key start len, popped))
    (sliceFailed : slice popped start len
      (if kind = .tuple then .identityExhausted else .receiptMismatch) = .error error)
    (h : CallerClosure s) :
    CallerClosure (resultState (step funds s)) := by
  have hp := caller_closure_select s popped _ selected h
  cases kind <;>
    simp at sliceFailed <;>
    simpa [step, selected, aggregateWork, perform, finishAggregate, resultState,
      sliceFailed] using hp

theorem selected_empty_function_failure_preserves_caller_closure
    (funds : Funding) (s popped : State) (key : CopyKey)
    (originals : NativeValuePorts.FunctionTerms)
    (selected : select s = some (.function key [] originals, popped))
    (h : CallerClosure s) :
    CallerClosure (resultState (step funds s)) := by
  have hp := caller_closure_select s popped _ selected h
  simpa [step, selected, perform, finishFunction, rebuildTerms, resultState]
    using hp

theorem selected_incoming_preserves_caller_closure (funds : Funding) (s popped : State)
    (tail view : Nat) (source : CopyKey) (original : RawBound)
    (selected : select s = some (.incomingAllowance tail view source original, popped))
    (h : CallerClosure s) :
    CallerClosure (resultState (step funds s)) := by
  simpa [step, selected, incoming_perform_retains_state] using
    caller_closure_select s popped _ selected h

theorem selected_effect_view_preserves_caller_closure (funds : Funding) (s popped : State)
    (key : CopyKey) (view : Nat) (child : CopyKey)
    (selected : select s = some (.effectView key view child, popped))
    (h : CallerClosure s) :
    CallerClosure (resultState (step funds s)) := by
  simpa [step, selected, effect_view_perform_retains_state] using
    caller_closure_select s popped _ selected h

theorem no_selected_work_preserves_caller_closure (funds : Funding) (s : State)
    (none : select s = none) (h : CallerClosure s) :
    CallerClosure (resultState (step funds s)) := by
  simp only [step, none]
  split <;> exact h

theorem computed_row_bound_caller_eq (caller : NativeValueStructure.Request) :
    (Computed.rowBoundState caller).operation.caller = caller := rfl

theorem computed_row_bound_values_length (caller : NativeValueStructure.Request) :
    (Computed.rowBoundState caller).values.length = 3 := rfl

theorem computed_row_bound_terms (caller : NativeValueStructure.Request) :
    (Computed.rowBoundState caller).terms = [] := rfl

theorem computed_row_bound_qv (caller : NativeValueStructure.Request) (id : Nat) :
    (Computed.rowBoundState caller).qv id = id := by
  change (if id = 2 then id else id) = id
  split <;> rfl

theorem computed_row_bound_parents (caller : NativeValueStructure.Request) :
    (Computed.rowBoundState caller).parents =
      [⟨.value (.row 2), .value (.row 0), .negative, 1,
        (Computed.rowInput caller).operation⟩] := rfl

theorem computed_row_bound_caller_fields (caller : NativeValueStructure.Request)
    (valid : RequestValid (Computed.rowInput caller) caller) :
    CallerFieldsValid (Computed.rowBoundState caller) := by
  have hlen : (Computed.rowInput caller).values.length ≤
      (Computed.rowBoundState caller).values.length := by
    simp [Computed.rowInput, computed_row_bound_values_length]
  have hqv : ∀ id, id < (Computed.rowInput caller).values.length →
      (Computed.rowBoundState caller).qv id = (Computed.rowInput caller).qv id := by
    intro id _
    simpa [Computed.rowInput] using computed_row_bound_qv caller id
  have hterm : ∀ term, (Computed.rowInput caller).storedTerm term ≠ none →
      (Computed.rowBoundState caller).storedTerm term ≠ none := by
    intro term old
    simp [State.storedTerm, Computed.rowInput] at old
  have hrequest := request_valid_mono
    (Computed.rowInput caller) (Computed.rowBoundState caller) caller
    hlen hqv hterm valid
  constructor
  · simpa [CurrentCallerValid, computed_row_bound_caller_eq] using hrequest
  · intro parent membership
    rw [computed_row_bound_parents] at membership
    simp only [List.mem_singleton] at membership
    subst parent
    simpa [Computed.rowInput] using hrequest

/-- The concrete emitted Bound request retains valid caller endpoints against
the computed returned state under precisely the initial caller premise. -/
theorem computed_bound_request_caller_valid (caller : NativeValueStructure.Request)
    (valid : RequestValid (Computed.rowInput caller) caller) :
    RequestValid (Computed.rowBoundState caller)
      (Computed.rowBoundRequest caller).operation.caller := by
  simpa [CurrentCallerValid, Computed.rowBoundRequest,
    OriginalExtrusionWork.boundRequest] using
    (computed_row_bound_caller_fields caller valid).1

theorem computed_prefix_bound_result_caller_valid (caller : NativeValueStructure.Request)
    (valid : RequestValid (Computed.rowInput caller) caller) :
    RequestValid (resultState (runPrefix funded 3 (Computed.rowInput caller)))
      (Computed.rowBoundRequest caller).operation.caller := by
  change RequestValid (Computed.rowBoundState caller)
    (Computed.rowBoundRequest caller).operation.caller
  exact computed_bound_request_caller_valid caller valid

def rowBoundShape (caller : NativeValueStructure.Request) : State :=
  { operation := (Computed.rowInput caller).operation
    qv := fun id => if id = 2 then id else id
    values := [⟨2, [2], [1], [], []⟩, ⟨1, [], [], [], []⟩, ⟨1, [], [], [], []⟩]
    rows := memoPut
      (memoPut (fun _ => none) ⟨.value (.row 0), .negative, 1⟩ (.value (.row 2)))
      ⟨.value (.row 1), .negative, 1⟩ (.value (.row 1))
    parents := [⟨.value (.row 2), .value (.row 0), .negative, 1,
      (Computed.rowInput caller).operation⟩]
    calls := 8 }

theorem rowBoundShape_eq (caller : NativeValueStructure.Request) :
    Computed.rowBoundState caller = rowBoundShape caller := rfl

theorem computed_row_bound_storage (caller : NativeValueStructure.Request) :
    StorageClosed (Computed.rowBoundState caller) := by
  rw [rowBoundShape_eq]
  simp [StorageClosed, RowsValid, CapturesValid, ViewTailsValid,
    LeafRefsValid, ViewRefsValid, CaptureBucketsValid, MemoKindsValid,
    ParentKindsValid, rowBoundShape, Computed.rowInput, memoPut,
    EndpointValid, ValueValid, EffectValid, ValueBoundsValid, EffectBoundsValid,
    CellValid, ParentValid, WorkValid, SameKind, State.storedTerm]
  repeat' constructor
  all_goals
    intro key endpoint found
    by_cases h1 : key = ⟨.value (.row 1), .negative, 1⟩
    · subst key
      simp at found
      subst endpoint
      simp [KeyValid, EndpointValid, ValueValid,
        KeyViewRefValid, EndpointViewRefValid]
    · by_cases h0 : key = ⟨.value (.row 0), .negative, 1⟩
      · subst key
        simp at found
        subst endpoint
        simp [KeyValid, EndpointValid, ValueValid,
          KeyViewRefValid, EndpointViewRefValid]
      · simp_all

theorem computed_row_prefix_caller_closure (caller : NativeValueStructure.Request)
    (valid : RequestValid (Computed.rowInput caller) caller) :
    CallerClosure (resultState (runPrefix funded 3 (Computed.rowInput caller))) := by
  change CallerClosure (Computed.rowBoundState caller)
  exact ⟨computed_row_bound_storage caller, computed_row_bound_caller_fields caller valid⟩

end YulangClosure.OriginalExtrusionCallerClosureR286
