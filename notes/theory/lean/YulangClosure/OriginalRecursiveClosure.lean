import YulangClosure.OriginalWorldReadout

/-!
Canonical retained evidence at actual source-owned formal Return paths.
The registry traverses every source Call owner; a fixed strategy reads only
the original declaration, actual event path, source formal and raw Outcome.
It retains the entire completed outcome and never reads a future frame or a
later description choice. Pending outcomes do not materialize this output.

This supplies a lawful data constructor for a canonical assignment. The old
Lambda builder does not yet install this formal Shared output, and original
returnRebind admission/full Function correspondence remain open. No recursive
L4 or whole-source counterexample is claimed.
-/
namespace YulangClosure.OriginalRecursiveClosure

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment OriginalWorldReadout

/-- Every closure owner in the source-derived registry contributes its actual
formal site. Applications do not manufacture formal-rebind owners. -/
def hasFormal (owners : List CallOwner) (formal : Site) : Bool :=
  owners.any fun owner => match owner with
    | .closure _ _ ownFormal _ _ => ownFormal == formal
    | .application _ _ _ _ => false

theorem registered_formal (owners : List CallOwner) (site : Site) (context : Context)
    (formal pattern body : Site)
    (present : CallOwner.closure site context formal pattern body ∈ owners) :
    hasFormal owners formal = true := by
  induction owners with
  | nil => simp at present
  | cons owner rest ih =>
      rcases List.mem_cons.mp present with same | later
      · subst owner
        simp [hasFormal]
      · have found := ih later
        simp only [hasFormal, List.any_cons] at found ⊢
        simp only [found, Bool.or_true]

/-- Registration comes from the actual original source Lambda constructor,
not from a supplied source derivation or a provider-output predicate. -/
theorem lambda_formal_registered (context : Context) (site : Site) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) :
    hasFormal (sourceCallOwners context (.lambda ⟨site, none⟩ formal pattern body)) formal.site = true := by
  have head := source_lambda_call_owner context site formal pattern body
  generalize sourceCallOwners context (.lambda ⟨site, none⟩ formal pattern body) = owners at head ⊢
  cases owners with
  | nil => cases head
  | cons owner rest =>
      have same : owner = CallOwner.closure site context formal.site pattern.site body.site := Option.some.inj head
      subst owner
      exact registered_formal _ _ _ _ _ _ List.mem_cons_self

/-- Retain all raw output fields, including observation, actual current
history/configuration, every endpoint object and every binding address.
The source descriptor map is fixed independently of later checking views. -/
structure RetainedRebind (s : Sorts) (View : Type) where
  key : AnchorKey (Payload s View)
  outcome : Outcome s
  sourceDescriptor : s.Descriptor

/-- A deterministic source-owned constructor on the original raw anchor key.
It reads only a completed Value return at a registered source formal owner.
It is not a new admission predicate and does not filter Function challenges. -/
def retainedRebind (owners : List CallOwner) (descriptors : Site → s.Descriptor)
    (key : AnchorKey (Payload s View)) : Option (RetainedRebind s View) :=
  if key.binder.kind = .shared ∧ hasFormal owners key.binder.site = true then
    match key.path.getLast? with
    | none => none
    | some step =>
        if step.source = key.binder.site ∧ step.kind = .returnRebind then
          match step.data with
          | .runtime (.returnRebind outcome) => match outcome.result with
              | some (.value _ _) => some ⟨key, outcome, descriptors key.binder.site⟩
              | _ => none
          | _ => none
        else none
  else none

/-- The exact post-Return key supplied by the existing original environment
constructor. The Shared binder itself adds no raw event to that path. -/
def formalReturnKey (environment : Environment (Payload s View)) (formal : Site)
    (occurrence : Nat) (outcome : Outcome s) : AnchorKey (Payload s View) :=
  (environment.extend ⟨formal, .returnRebind, 0⟩
    (scopeCandidate environment occurrence (.runtime (.returnRebind outcome)))).anchorKey
      ⟨formal, .shared, 0⟩

theorem formal_return_key_fields (environment : Environment (Payload s View)) (formal occurrence : Nat)
    (outcome : Outcome s) :
    (formalReturnKey environment formal occurrence outcome).origin = environment.origin ∧
    (formalReturnKey environment formal occurrence outcome).binder = ⟨formal, .shared, 0⟩ ∧
    (formalReturnKey environment formal occurrence outcome).path = environment.eventPath ++
      [⟨formal, .returnRebind, occurrence, .runtime (.returnRebind outcome)⟩] := ⟨rfl, rfl, rfl⟩

/-- Every actual completed raw Return at every registered owner has its exact
retained output. No event/readback equation or semantic safety is a premise. -/
theorem completed_return_retained (owners : List CallOwner) (descriptors : Site → s.Descriptor)
    (environment : Environment (Payload s View)) (formal occurrence : Nat)
    (registered : hasFormal owners formal = true) (outcome : Outcome s)
    (value : s.Value) (root : s.Root) (returned : outcome.result = some (.value value root)) :
    retainedRebind owners descriptors (formalReturnKey environment formal occurrence outcome) =
      some ⟨formalReturnKey environment formal occurrence outcome, outcome, descriptors formal⟩ := by
  simp [retainedRebind, formalReturnKey, Environment.anchorKey, Environment.extend,
    Binder.isEvent, ActualEvent.path, scopeCandidate, registered, returned]

/-- A pending raw outcome never fabricates formal rebind evidence. Pending
strict-call observations retain the unfinished suffix separately. -/
theorem pending_return_no_retained (owners : List CallOwner) (descriptors : Site → s.Descriptor)
    (environment : Environment (Payload s View)) (formal occurrence : Nat)
    (outcome : Outcome s) (pending : outcome.result = none) :
    retainedRebind owners descriptors (formalReturnKey environment formal occurrence outcome) = none := by
  simp [retainedRebind, formalReturnKey, Environment.anchorKey, Environment.extend,
    Binder.isEvent, ActualEvent.path, scopeCandidate, pending]

/-- The constructor cannot materialize an unfinished output at any raw key,
even a key not supplied by the canonical source-prefix theorem. -/
theorem retained_is_completed (owners : List CallOwner) (descriptors : Site → s.Descriptor)
    (key : AnchorKey (Payload s View)) (output : RetainedRebind s View)
    (present : retainedRebind owners descriptors key = some output) :
    ∃ value root, output.outcome.result = some (.value value root) := by
  unfold retainedRebind at present
  split at present
  · cases last : key.path.getLast? with
    | none => simp [last] at present
    | some step =>
        simp only [last] at present
        split at present
        · cases data : step.data with
          | root data | logical kind data | shared data => simp [data] at present
          | runtime raw =>
              cases raw with
              | invocation raw | receipt raw | response raw | rigidOperation raw | oneShot raw =>
                  simp [data] at present
              | returnRebind outcome =>
                  simp only [data] at present
                  cases result : outcome.result with
                  | none => simp [result] at present
                  | some object =>
                      cases object with
                      | carrier carrier root => simp [result] at present
                      | value value root =>
                          simp only [result, Option.some.injEq] at present
                          subst output
                          exact ⟨value, root, result⟩
        · cases present
  · cases present

/-- One fixed representation of the complete retained output. Bindings and
installed-object fields are already supplied by actual runtime/native-world
readouts; this Shared frame retains their entire raw tuple in its witness.
No logical membership proof is converted into an executed dictionary. -/
def retainedShared (encode : RetainedRebind s View → s.WitnessValue)
    (output : RetainedRebind s View) : Shared s :=
  ⟨[], [], encode output⟩

/-- Fix the strategy once, before source events. Non-formal and unmatched
anchors retain the original map. All registered completed formal keys use the
same raw-key construction; no source owner is selected after an observation. -/
def canonicalAnchors
    (original : AnchorKey (Payload s View) → ScopedValue (Payload s View))
    (origin : Declaration) (owners : List CallOwner) (descriptors : Site → s.Descriptor)
    (encode : RetainedRebind s View → s.WitnessValue)
    (key : AnchorKey (Payload s View)) : ScopedValue (Payload s View) :=
  if key.origin = origin then
    match retainedRebind owners descriptors key with
    | none => original key
    | some output => ⟨.shared (retainedShared encode output), ⟨key.path, 0⟩⟩
  else original key

def withCanonicalAnchors (environment : Environment (Payload s View))
    (owners : List CallOwner) (descriptors : Site → s.Descriptor)
    (encode : RetainedRebind s View → s.WitnessValue) : Environment (Payload s View) :=
  {environment with anchors := canonicalAnchors environment.anchors environment.origin owners descriptors encode}

/-- The original anchor mechanism reads the newly constructed Shared output
at the exact completed Return path, with no supplied registration equality. -/
theorem completed_return_shared_anchor (owners : List CallOwner) (descriptors : Site → s.Descriptor)
    (encode : RetainedRebind s View → s.WitnessValue)
    (environment : Environment (Payload s View)) (formal occurrence : Nat)
    (registered : hasFormal owners formal = true) (outcome : Outcome s)
    (value : s.Value) (root : s.Root) (returned : outcome.result = some (.value value root)) :
    let prepared := withCanonicalAnchors environment owners descriptors encode
    let actual := prepared.extend ⟨formal, .returnRebind, 0⟩
      (scopeCandidate prepared occurrence (.runtime (.returnRebind outcome)))
    actual.anchorValue ⟨formal, .shared, 0⟩ =
      ⟨.shared (retainedShared encode
        ⟨formalReturnKey environment formal occurrence outcome, outcome, descriptors formal⟩),
        ⟨(formalReturnKey environment formal occurrence outcome).path, 0⟩⟩ := by
  change canonicalAnchors environment.anchors environment.origin owners descriptors encode
    (formalReturnKey environment formal occurrence outcome) = _
  rw [canonicalAnchors, ite_eq_left (show
    (formalReturnKey environment formal occurrence outcome).origin = environment.origin from rfl)]
  rw [completed_return_retained owners descriptors environment formal occurrence registered outcome value root returned]

/-- Logical descriptions never change the key read by this retained strategy.
Their own proof witnesses remain separate and may depend on their full frame. -/
theorem logical_frame_keeps_return_key (environment : Environment (Payload s View))
    (kind : LogicalKind) (site arity : Nat) (data : Logical s View)
    (logicalOccurrence formal returnOccurrence : Nat) (outcome : Outcome s) :
    formalReturnKey
      (environment.extend ⟨site, kind.binderKind, arity⟩
        (scopeCandidate environment logicalOccurrence (.logical kind data)))
      formal returnOccurrence outcome = formalReturnKey environment formal returnOccurrence outcome := by
  cases kind <;> rfl

/-- The original strategy stays fixed under every later source extension.
In particular introducing a new key does not overwrite any earlier key. -/
theorem every_old_anchor_preserved (environment : Environment (Payload s View))
    (binder : Binder) (candidate : ScopedValue (Payload s View))
    (oldKey : AnchorKey (Payload s View)) :
    (environment.extend binder candidate).anchors oldKey = environment.anchors oldKey := rfl

/-- A physical path invariant of source-constructed frames, without typing or
membership. The empty root and every actual extension satisfy its constructors. -/
def FramePathsWithin (environment : Environment Value) : Prop :=
  ∀ frame ∈ environment.frames, frame.entryPath.length ≤ environment.eventPath.length

theorem empty_frame_paths (environment : Environment Value) (empty : environment.frames = []) :
    FramePathsWithin environment := by simp [FramePathsWithin, empty]

theorem extend_frame_paths (environment : Environment Value) (before : FramePathsWithin environment)
    (binder : Binder) (candidate : ScopedValue Value) :
    FramePathsWithin (environment.extend binder candidate) := by
  intro frame present
  change frame ∈ environment.frames ++ [⟨binder, candidate, environment.eventPath⟩] at present
  have grows : environment.eventPath.length ≤ (environment.extend binder candidate).eventPath.length := by
    simp only [Environment.extend]
    split
    · simp [ActualEvent.path]
    · exact Nat.le_refl _
  rcases List.mem_append.mp present with old | added
  · exact Nat.le_trans (before frame old) grows
  · have same : frame = ⟨binder, candidate, environment.eventPath⟩ := List.mem_singleton.mp added
    subst frame
    exact grows

/-- Freshness is derived from an actual new Return step. It is not inferred
from unrelated provider IDs or stipulated for an arbitrary witness slot. -/
theorem completed_return_key_fresh (environment : Environment (Payload s View))
    (within : FramePathsWithin environment) (formal occurrence : Nat) (outcome : Outcome s)
    (frame : Frame (Payload s View)) (old : frame ∈ environment.frames) :
    formalReturnKey environment formal occurrence outcome ≠
      ⟨environment.origin, frame.entryPath, frame.binder⟩ := by
  intro equal
  have lengths := congrArg (fun key : AnchorKey (Payload s View) => key.path.length) equal
  have bounded := within frame old
  simp [formalReturnKey, Environment.anchorKey, Environment.extend, Binder.isEvent,
    ActualEvent.path, scopeCandidate] at lengths
  omega

/-- Decode actual Return followed by its new retained Shared frame. Every
older full Shared record survives, and exactly the new complete record is
appended. Current EventFields continue to come from the actual runtime
readout; the earlier entire witness map is not equated with the new one. -/
theorem actual_return_shared_frames (readout : RuntimeReadout s View)
    (state : Decoded s View) (returnBinder sharedBinder : Binder) (outcome : Outcome s)
    (returnedEvent sharedEvent : ActualEvent (Payload s View))
    (returnPath sharedPath : List (EventStep (Payload s View))) (shared : Shared s) :
    sharedFrames
      (decodeFrame readout
        (decodeFrame readout state ⟨returnBinder, ⟨.runtime (.returnRebind outcome), returnedEvent⟩, returnPath⟩)
        ⟨sharedBinder, ⟨.shared shared, sharedEvent⟩, sharedPath⟩).fixedFrames =
      sharedFrames state.fixedFrames ++ [⟨sharedBinder, ⟨.shared shared, sharedEvent⟩, sharedPath⟩] := by
  simp only [decodeFrame, Decoded.retain, Decoded.shared, runtime_preserves_prior_fixed_prefix,
    sharedFrames, List.filter_append, List.filter_cons, List.filter_nil,
    Bool.false_eq_true, ite_false, List.append_nil, ite_true]

/-- The constructor covers every closure formal in the entire original raw
source registry, including nested lambdas and repeated calls to one closure.
No single owning application is selected as the allowed event domain. -/
theorem every_source_formal_return (context : Context) (source : Source category)
    (descriptors : Site → s.Descriptor) (environment : Environment (Payload s View))
    (lambda : Site) (localContext : Context) (formal pattern body occurrence : Nat)
    (owner : CallOwner.closure lambda localContext formal pattern body ∈ sourceCallOwners context source)
    (outcome : Outcome s) (value : s.Value) (root : s.Root)
    (returned : outcome.result = some (.value value root)) :
    retainedRebind (sourceCallOwners context source) descriptors
      (formalReturnKey environment formal occurrence outcome) =
      some ⟨formalReturnKey environment formal occurrence outcome, outcome, descriptors formal⟩ :=
  completed_return_retained _ descriptors environment formal occurrence
    (registered_formal _ lambda localContext formal pattern body owner) outcome value root returned

/-- Consume the computed output through the actual original Environment and
Decoded constructors. The complete earlier Shared frames survive and the new
Shared frame is genuinely appended. The current witness comes from the new
Return readout, not from equality with the preceding witness.
-/
theorem decode_computed_formal_shared (owners : List CallOwner) (descriptors : Site → s.Descriptor)
    (encode : RetainedRebind s View → s.WitnessValue) (readout : RuntimeReadout s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (formal occurrence : Nat)
    (registered : hasFormal owners formal = true) (outcome : Outcome s)
    (value : s.Value) (root : s.Root) (returned : outcome.result = some (.value value root)) :
    let prepared := withCanonicalAnchors environment owners descriptors encode
    let returnBinder : Binder := ⟨formal, .returnRebind, 0⟩
    let sharedBinder : Binder := ⟨formal, .shared, 0⟩
    let returnedValue := scopeCandidate prepared occurrence (.runtime (.returnRebind outcome))
    let actual := prepared.extend returnBinder returnedValue
    let retained := actual.anchorValue sharedBinder
    ∃ after, decode readout (actual.extend sharedBinder retained) = some after ∧
      sharedFrames after.fixedFrames = sharedFrames state.fixedFrames ++
        [⟨sharedBinder, retained, actual.eventPath⟩] ∧
      after.assignment.event.current = outcome.after.configuration ∧
      after.assignment.event.witness =
        readout.witness state.fixedFrames state.assignment.event returnBinder (.returnRebind outcome) := by
  let prepared := withCanonicalAnchors environment owners descriptors encode
  let returnBinder : Binder := ⟨formal, .returnRebind, 0⟩
  let sharedBinder : Binder := ⟨formal, .shared, 0⟩
  let returnedValue := scopeCandidate prepared occurrence (.runtime (.returnRebind outcome))
  let actual := prepared.extend returnBinder returnedValue
  let retained := actual.anchorValue sharedBinder
  let first := decodeFrame readout state ⟨returnBinder, returnedValue, prepared.eventPath⟩
  have firstDecoded : decode readout actual = some first :=
    decode_extend readout prepared returnBinder returnedValue state decoded
  have shared : retained =
      ⟨.shared (retainedShared encode
        ⟨formalReturnKey environment formal occurrence outcome, outcome, descriptors formal⟩),
        ⟨(formalReturnKey environment formal occurrence outcome).path, 0⟩⟩ :=
    completed_return_shared_anchor owners descriptors encode environment formal occurrence
      registered outcome value root returned
  change ∃ after, decode readout (actual.extend sharedBinder retained) = some after ∧
    sharedFrames after.fixedFrames = sharedFrames state.fixedFrames ++
      [⟨sharedBinder, retained, actual.eventPath⟩] ∧
    after.assignment.event.current = outcome.after.configuration ∧
    after.assignment.event.witness =
      readout.witness state.fixedFrames state.assignment.event returnBinder (.returnRebind outcome)
  refine ⟨decodeFrame readout first ⟨sharedBinder, retained, actual.eventPath⟩,
    decode_extend readout actual sharedBinder retained first firstDecoded, ?_, ?_, ?_⟩
  · rw [shared]
    exact actual_return_shared_frames readout state returnBinder sharedBinder outcome
      returnedValue.event ⟨(formalReturnKey environment formal occurrence outcome).path, 0⟩
      prepared.eventPath actual.eventPath
      (retainedShared encode
        ⟨formalReturnKey environment formal occurrence outcome, outcome, descriptors formal⟩)
  · rw [shared]
    rfl
  · rw [shared]
    rfl

/-- A complete preceding telescope is built by the existing original source
extension operation. It retains logical and runtime frames in source order. -/
def extendPrefix (environment : Environment Value) (entries : List (Binder × ScopedValue Value)) :
    Environment Value :=
  entries.foldl (fun current entry => current.extend entry.1 entry.2) environment

theorem prefix_original_strategy (environment : Environment Value)
    (entries : List (Binder × ScopedValue Value)) :
    (extendPrefix environment entries).anchors = environment.anchors ∧
    (extendPrefix environment entries).origin = environment.origin := by
  induction entries generalizing environment with
  | nil => exact ⟨rfl, rfl⟩
  | cons entry rest ih =>
      exact ih (environment.extend entry.1 entry.2)

theorem canonical_anchors_idempotent
    (original : AnchorKey (Payload s View) → ScopedValue (Payload s View))
    (origin : Declaration) (owners : List CallOwner) (descriptors : Site → s.Descriptor)
    (encode : RetainedRebind s View → s.WitnessValue) :
    canonicalAnchors (canonicalAnchors original origin owners descriptors encode)
      origin owners descriptors encode = canonicalAnchors original origin owners descriptors encode := by
  funext key
  by_cases owned : key.origin = origin
  · cases formed : retainedRebind owners descriptors key <;> simp [canonicalAnchors, owned, formed]
  · simp [canonicalAnchors, owned]

/-- Fixing the strategy at the root is sufficient for every subsequent full
source telescope. Reusing the decoder theorem after this entries does not
reassign old Shared anchors or install a new strategy after seeing a result. -/
theorem canonical_prefix_already_fixed (environment : Environment (Payload s View))
    (owners : List CallOwner) (descriptors : Site → s.Descriptor)
    (encode : RetainedRebind s View → s.WitnessValue)
    (entries : List (Binder × ScopedValue (Payload s View))) :
    withCanonicalAnchors
      (extendPrefix (withCanonicalAnchors environment owners descriptors encode) entries)
      owners descriptors encode =
      extendPrefix (withCanonicalAnchors environment owners descriptors encode) entries := by
  let actual := extendPrefix (withCanonicalAnchors environment owners descriptors encode) entries
  have original := prefix_original_strategy (withCanonicalAnchors environment owners descriptors encode) entries
  have stable : canonicalAnchors actual.anchors actual.origin owners descriptors encode = actual.anchors := by
    rw [original.1, original.2]
    exact canonical_anchors_idempotent environment.anchors environment.origin owners descriptors encode
  change {actual with anchors := canonicalAnchors actual.anchors actual.origin owners descriptors encode} = actual
  rw [stable]

end YulangClosure.OriginalRecursiveClosure
