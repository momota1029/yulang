import YulangClosure.OriginalCheckingAdmission

/-!
Actual invocation events and finite observation-child transport. The event is
constructed by the original decoder using its entire retained frame prefix;
it is not identified with the event at closure creation. These results cover
actual goal-admitted raw invocations, including later histories, without a
view-token choice or an assumed event-readback equation.

The independent full-future event registry and domain-reading repair are not
constructed here. The finite discriminator below records why current-event
DomainMeaning cannot supply that missing premise.
-/
namespace YulangClosure.OriginalFunctionFuture

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceChecking OriginalCheckingAdmission

/-- Actual source readout at the incoming invocation's live configuration. -/
def invocationEvent (readout : RuntimeReadout s View) (state : Decoded s View)
    (binder : Binder) (raw : Invocation s View) : Event s :=
  readout.event state.fixedFrames state.assignment.event binder (.invocation raw)

/-- Every logical/event coordinate uses the exact original prefix and raw
invocation. Only fiber and eta0 are fixed; the witness is a fresh readout. -/
theorem invocation_event_fields (readout : RuntimeReadout s View) (state : Decoded s View)
    (binder : Binder) (raw : Invocation s View) :
    (invocationEvent readout state binder raw).fiber = state.assignment.event.fiber ∧
    (invocationEvent readout state binder raw).eta0 = state.assignment.event.eta0 ∧
    (invocationEvent readout state binder raw).history = raw.current.history ∧
    (invocationEvent readout state binder raw).current = raw.current.configuration ∧
    (invocationEvent readout state binder raw).eta =
      readout.eta state.fixedFrames state.assignment.event binder (.invocation raw) ∧
    (invocationEvent readout state binder raw).witness =
      readout.witness state.fixedFrames state.assignment.event binder (.invocation raw) ∧
    (invocationEvent readout state binder raw).scope =
      readout.scope state.fixedFrames state.assignment.event binder (.invocation raw) ∧
    (invocationEvent readout state binder raw).authority =
      readout.authority state.fixedFrames state.assignment.event binder (.invocation raw) ∧
    (invocationEvent readout state binder raw).incidence =
      readout.incidence state.fixedFrames state.assignment.event binder (.invocation raw) ∧
    (invocationEvent readout state binder raw).dictionary =
      readout.dictionary state.fixedFrames state.assignment.event binder (.invocation raw) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Decoration neither overwrites the current witness nor resets the actual
current configuration already supplied by the incoming invocation. -/
theorem invocation_event_redecoration (readout : RuntimeReadout s View)
    (state : Decoded s View) (binder : Binder) (raw : Invocation s View) :
    raw.decorate (invocationEvent readout state binder raw) =
      invocationEvent readout state binder raw := rfl

theorem event_readback_requires_original_static_scope (readout : RuntimeReadout s View)
    (state : Decoded s View) (binder : Binder) (raw : Invocation s View) (event : Event s)
    (readback : invocationEvent readout state binder raw = event) :
    event.fiber = state.assignment.event.fiber ∧ event.eta0 = state.assignment.event.eta0 := by
  rw [← readback]
  exact ⟨rfl, rfl⟩

def invocationChild (readout : RuntimeReadout s View) (state : Decoded s View)
    (environment : Environment (Payload s View)) (binder : Binder)
    (candidate : ScopedValue (Payload s View)) (raw : Invocation s View) : Decoded s View :=
  (state.runtime readout binder (.invocation raw)).retain
    ⟨binder, candidate, environment.eventPath⟩

/-- No re-rooting: the existing original prefix, including Shared witnesses
and entry paths, precedes the actual new frame. -/
theorem invocation_child_preserves_prefix (readout : RuntimeReadout s View)
    (state : Decoded s View) (environment : Environment (Payload s View)) (binder : Binder)
    (candidate : ScopedValue (Payload s View)) (raw : Invocation s View) :
    (invocationChild readout state environment binder candidate raw).fixedFrames =
      state.fixedFrames ++ [⟨binder, candidate, environment.eventPath⟩] ∧
    (invocationChild readout state environment binder candidate raw).callOwners = state.callOwners ∧
    (invocationChild readout state environment binder candidate raw).assignment.descriptor =
      state.assignment.descriptor ∧
    (invocationChild readout state environment binder candidate raw).assignment.event =
      invocationEvent readout state binder raw := ⟨rfl, rfl, rfl, rfl⟩

theorem decode_actual_invocation (readout : RuntimeReadout s View) (state : Decoded s View)
    (environment : Environment (Payload s View)) (binder : Binder)
    (candidate : ScopedValue (Payload s View)) (raw : Invocation s View)
    (decoded : decode readout environment = some state)
    (payload : candidate.data = .runtime (.invocation raw)) :
    decode readout (environment.extend binder candidate) =
      some (invocationChild readout state environment binder candidate raw) := by
  simpa only [decodeFrame, payload, invocationChild] using
    decode_extend readout environment binder candidate state decoded

/-- All descriptor retargets have the same active raw input, including the
actual later event and its complete current witness/readout. -/
theorem invocation_child_active (readout : RuntimeReadout s View) (state : Decoded s View)
    (environment : Environment (Payload s View)) (binder : Binder)
    (candidate : ScopedValue (Payload s View)) (raw : Invocation s View)
    (descriptor : s.Descriptor) :
    (invocationChild readout state environment binder candidate raw).active =
      some ((raw.challenge (invocationEvent readout state binder raw)
        descriptor state.viewMeaning).input) := rfl

/-- Semantic child action at its actual incoming event. This lemma makes no
current-event or static-fiber identification beyond the decoder itself. -/
theorem raw_observation_action (inputs : Inputs s) (Z : Family s)
    (readout : RuntimeReadout s View) (state : Decoded s View)
    (environment : Environment (Payload s View)) (binder : Binder)
    (candidate : ScopedValue (Payload s View)) (raw : Invocation s View) (observation : CheckGoal)
    (observed : ObservationMeaning inputs Z
      (invocationChild readout state environment binder candidate raw) observation) :
    ∀ output, ObservationMem inputs Z
      (raw.challenge (invocationEvent readout state binder raw)
        (state.assignment.descriptor observation.lower) state.viewMeaning) output →
      ObservationMem inputs Z
      (raw.challenge (invocationEvent readout state binder raw)
        (state.assignment.descriptor observation.upper) state.viewMeaning) output := by
  exact observed

/-- The actual finite observation Checking child supplies the action. Its
admitted raw candidate carries its own view and current event; there is no
assumed token reconstruction, eventReadback, or future GoalMeaning. -/
theorem admitted_checked_observation (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (ports : PortReadout s View)
    (original : Kernel (Payload s View)) (environment : Environment (Payload s View))
    (goal observation : CheckGoal) (binder : Binder) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (invocation : binder.kind = .invocation) (mode : observation.mode = .observation)
    (candidate : ScopedValue (Payload s View))
    (admitted : GoalAdmitted inputs readout admissions environment goal binder candidate)
    (checked : Checking (registeredKernel inputs registry declarations readout admissions ports original)
      (environment.extend binder candidate) observation) :
    ∃ raw : Invocation s View, candidate.data = .runtime (.invocation raw) ∧
      raw.value = (state.goalRow binder goal).value ∧
      raw.valueRoot = (state.goalRow binder goal).root ∧
      CheckedDomain inputs (raw.challenge (invocationEvent readout state binder raw)
        (state.assignment.descriptor goal.upper) state.viewMeaning) ∧
      ∀ output, ObservationMem inputs (Meaning inputs)
        (raw.challenge (invocationEvent readout state binder raw)
          (state.assignment.descriptor observation.lower) state.viewMeaning) output →
        ObservationMem inputs (Meaning inputs)
        (raw.challenge (invocationEvent readout state binder raw)
          (state.assignment.descriptor observation.upper) state.viewMeaning) output := by
  obtain ⟨raw, payload, value, root, domain⟩ := goal_admission_recovers_challenge
    inputs readout admissions environment goal binder state decoded candidate admitted invocation
  refine ⟨raw, payload, value, root, domain, ?_⟩
  apply raw_observation_action inputs (Meaning inputs) readout state environment binder candidate raw observation
  apply observation_action inputs readout ports (environment.extend binder candidate)
    (invocationChild readout state environment binder candidate raw)
    (decode_actual_invocation readout state environment binder candidate raw decoded payload)
    observation mode
    ((raw.challenge (invocationEvent readout state binder raw)
      (state.assignment.descriptor goal.upper) state.viewMeaning).input)
    (invocation_child_active readout state environment binder candidate raw _)
  exact checking_sound inputs registry declarations (environmentReading inputs readout ports)
    (goalFunctionKernel inputs readout admissions original) checked

/-- Direct application to the observation premise of the finite Function
constructor. The admitted domain is the enclosing goal's own domain. -/
theorem function_observation_child_at_actual_event (inputs : Inputs s)
    (registry : GuardRegistry inputs) (declarations : Declarations inputs registry)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (ports : PortReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (goal observation : CheckGoal)
    (binder : Binder) (state : Decoded s View) (decoded : decode readout environment = some state)
    (invocation : binder.kind = .invocation) (mode : observation.mode = .observation)
    (children : ∀ candidate, GoalAdmitted inputs readout admissions environment goal binder candidate →
      Checking (registeredKernel inputs registry declarations readout admissions ports original)
        (environment.extend binder candidate) observation)
    (candidate : ScopedValue (Payload s View))
    (admitted : GoalAdmitted inputs readout admissions environment goal binder candidate) :
    ∃ raw : Invocation s View, candidate.data = .runtime (.invocation raw) ∧
      CheckedDomain inputs (raw.challenge (invocationEvent readout state binder raw)
        (state.assignment.descriptor goal.upper) state.viewMeaning) ∧
      ∀ output, ObservationMem inputs (Meaning inputs)
        (raw.challenge (invocationEvent readout state binder raw)
          (state.assignment.descriptor observation.lower) state.viewMeaning) output →
        ObservationMem inputs (Meaning inputs)
        (raw.challenge (invocationEvent readout state binder raw)
          (state.assignment.descriptor observation.upper) state.viewMeaning) output := by
  obtain ⟨raw, payload, _, _, domain, action⟩ := admitted_checked_observation inputs registry declarations
    readout admissions ports original environment goal observation binder state decoded invocation mode
    candidate admitted (children candidate admitted)
  exact ⟨raw, payload, domain, action⟩

/-! A finite event-sensitive discriminator for the current formal interface.
It is not a source program and is not an alleged counterexample to original
Yulang soundness. Both domains stay nonempty; the missing future challenge
is independently admitted and uses the same immutable callable. -/
namespace EventDiscriminator

def sorts : Sorts := {OriginalCheckingAdmission.Discriminator.sorts with
  Assignment := Bool, History := Nat, Configuration := Bool, JointWitness := Bool}

def event (later : Bool) : Event sorts :=
  ⟨⟨(), (), (), (), ()⟩, false, later, if later then (1 : Nat) else (0 : Nat),
    later, later, (), (), (), ()⟩

def inputs : Inputs sorts where
  compatible := fun first second => first.fiber = second.fiber ∧ first.eta0 = second.eta0
  eventCoherent := fun _ => True
  valueForm := fun _ => .function
  ground := fun _ => True
  fixedExternal := fun _ => True
  structuralGuard := fun _ => True
  structuralFields := fun _ => .guard True
  actual := fun _ _ _ => True
  functionGuards := fun _ _ => ⟨True, True, True, True, True⟩
  capturedFields := fun _ _ => .guard True
  checkedInlet := id
  actualInlet := fun _ => true
  carrierAccepted := fun row => row.interface = false ∨ row.event.current = false ∨ row.carrier = false
  puncturedContext := fun _ => True
  otherValues := fun _ => True
  registeredHoles := fun _ => True
  checkedIncidences := fun _ => True
  receiptPrecondition := fun _ _ => True
  actualTypedPath := fun _ _ => True
  actualContext := fun _ _ => True
  execute := fun _ _ _ => True
  observationGuards := fun _ => ⟨True, True, True, True, True, True, True, True, True, True⟩
  traceForm := fun _ => .unfinished
  observationFields := fun _ => .guard True
  checkedObservation := fun _ _ => .guard True
  worldGuards := fun _ => ⟨True, True, True, True⟩
  installedCount := fun _ => 0
  installed := fun _ _ => none
  alias := fun _ a b => a = b
  capture := fun _ _ _ => none
  captureValue := fun _ _ _ => none
  sharedPosition := fun _ a b => a = b
  witnessAt := fun _ _ => ()
  carrierGuards := fun _ => ⟨True, True, True, True, True⟩
  carrierCaptures := fun _ => .guard True
  demand := fun _ _ => True
  force := fun _ _ _ => True
  forceIncidence := fun _ _ _ => True

def readout : RuntimeReadout sorts Bool where
  eta := fun _ before _ data => (data.after.getD ⟨before.history, before.current⟩).configuration
  witness := fun _ before _ data => (data.after.getD ⟨before.history, before.current⟩).configuration
  scope := fun _ _ _ _ => ()
  authority := fun _ _ _ _ => ()
  incidence := fun _ _ _ _ => ()
  dictionary := fun _ _ _ _ => ()

def admissions : LocalAdmissions sorts Bool where
  logical := fun _ _ _ _ => True
  shared := fun _ _ _ => True
  receipt := fun _ _ _ => True
  returnRebind := fun _ _ _ => True
  response := fun _ _ _ => True
  rigidOperation := fun _ _ _ => True
  oneShot := fun _ _ _ => True

def rootData : Root sorts Bool where
  assignment :=
    {event := event false
     descriptor := fun endpoint => endpoint.site != 8
     value := fun _ => false
     root := fun _ => ()
     binding := fun _ => none}
  interfaces := fun _ => false
  carriers := fun _ => false
  viewMeaning := id
  installed := fun _ => none
  callOwners := [CallOwner.application 7 [] 3 4]

def state : Decoded sorts Bool := rootData.decoded

def environment : Environment (Payload sorts Bool) where
  root := .root rootData
  anchors := fun _ => ⟨.root rootData, ⟨[], 0⟩⟩
  publications := fun _ => none
  origin := 0

def binder : Binder := ⟨7, .invocation, 0⟩

def domain : CheckGoal := ⟨.domain, 7, [], ⟨8, .descriptor⟩, ⟨9, .descriptor⟩⟩

def goal : CheckGoal := ⟨.value, 7, [], ⟨9, .descriptor⟩, ⟨8, .descriptor⟩⟩

def raw (later carrier : Bool) : Invocation sorts Bool :=
  ⟨⟨if later then (1 : Nat) else (0 : Nat), later⟩, false, (), (), (), carrier, (), false, (), (), (), ()⟩

def challenge (later descriptor carrier : Bool) :
    Challenge (⟨descriptor, false, (), event later⟩ : ValueRow sorts) :=
  ⟨(), (), carrier, (), false, (), (), (), ()⟩

theorem exact_domain (later descriptor carrier : Bool) :
    CheckedDomain inputs (challenge later descriptor carrier) ↔
      descriptor = false ∨ later = false ∨ carrier = false := by
  simp only [CheckedDomain, inputs, challenge, Challenge.carrierRow, event, true_and]
  rfl

theorem both_domains_nonempty (later descriptor : Bool) :
    CheckedDomain inputs (challenge later descriptor false) := by
  rw [exact_domain]
  exact Or.inr (Or.inr rfl)

theorem current_domain_meaning : DomainMeaning inputs state domain := by
  intro value root challenge admitted
  change True ∧ True ∧ True ∧ True ∧ True ∧
    (true = false ∨ false = false ∨ challenge.carrier = false)
  exact ⟨True.intro, True.intro, True.intro, True.intro, True.intro, Or.inr (Or.inl rfl)⟩

/-- Even the entire decoded domain GoalMeaning, not merely its extracted
current DomainMeaning, misses this later admitted challenge. -/
theorem current_goal_meaning (ports : PortReadout sorts Bool) :
    GoalMeaning inputs (environmentReading inputs readout ports) environment domain := by
  apply (goal_meaning_iff inputs readout ports environment state (by rfl) domain).mpr
  intro input atCurrent admitted
  change True ∧ True ∧ True ∧ True ∧ True ∧
    (true = false ∨ input.event.current = false ∨ input.carrier = false)
  rw [atCurrent]
  exact ⟨True.intro, True.intro, True.intro, True.intro, True.intro, Or.inr (Or.inl rfl)⟩

/-- The current reading drops the future input by its explicit event guard,
although that input belongs to the independent target domain. -/
theorem future_input_excluded_by_current_guard (ports : PortReadout sorts Bool) :
    ¬ (stateClause inputs ports state .domain 7 [] domain.lower
      (.domain (challenge true false true).input)).Holds (Meaning inputs) := by
  intro valid
  have eventEqual : event true = event false := valid.1
  have impossible : true = false := congrArg Event.current eventEqual
  cases impossible

theorem later_domain_inclusion_fails :
    CheckedDomain inputs (challenge true false true) ∧
    ¬ CheckedDomain inputs ((challenge true false true).retarget true) := by
  constructor
  · rw [exact_domain]
    exact Or.inl rfl
  · change ¬ CheckedDomain inputs (challenge true true true)
    rw [exact_domain]
    simp only [Bool.true_eq_false, or_self, not_false_eq_true]

theorem actual_later_readout :
    invocationEvent readout state binder (raw true true) = event true := rfl

theorem static_scope_same_current_fields_change :
    (event false).fiber = (event true).fiber ∧
    (event false).eta0 = (event true).eta0 ∧
    (event false).history ≠ (event true).history ∧
    (event false).current ≠ (event true).current ∧
    (event false).eta ≠ (event true).eta ∧
    (event false).witness ≠ (event true).witness := by
  refine ⟨rfl, rfl, ?_⟩
  change (0 : Nat) ≠ 1 ∧ false ≠ true ∧ false ≠ true ∧ false ≠ true
  decide

theorem later_raw_is_goal_admitted :
    GoalAdmitted inputs readout admissions environment goal binder
      (scopeCandidate environment 0 (.runtime (.invocation (raw true true)))) := by
  apply (goal_admitted_scoped_iff inputs readout admissions environment goal binder state
    (by rfl) 0 _).mpr
  change BinderKind.invocation = .invocation ∧ false = false ∧ () = () ∧ True ∧ True ∧ True ∧ True ∧ True ∧
    (false = false ∨ true = false ∨ true = false)
  exact ⟨rfl, rfl, rfl, True.intro, True.intro, True.intro, True.intro, True.intro, Or.inl rfl⟩

/-- A later independently admitted target challenge need not be covered by
the domain IH at the event where the finite check was decoded. -/
theorem current_ih_does_not_cover_admitted_future :
    DomainMeaning inputs state domain ∧
    GoalAdmitted inputs readout admissions environment goal binder
      (scopeCandidate environment 0 (.runtime (.invocation (raw true true)))) ∧
    ¬ CheckedDomain inputs ((challenge true false true).retarget true) :=
  ⟨current_domain_meaning, later_raw_is_goal_admitted, later_domain_inclusion_fails.2⟩

/-- Same fiber and eta0 do not authenticate the remaining dynamic event
fields. The actual decoder owns the current witness, not an arbitrary one. -/
theorem same_static_scope_does_not_force_event_readback :
    let unregistered := {event true with witness := false}
    unregistered.fiber = (event false).fiber ∧ unregistered.eta0 = (event false).eta0 ∧
    invocationEvent readout state binder (raw true true) ≠ unregistered := by
  refine ⟨rfl, rfl, ?_⟩
  intro equality
  have impossible : true = false := congrArg Event.witness equality
  cases impossible

end EventDiscriminator
end YulangClosure.OriginalFunctionFuture
