import YulangClosure.OriginalSourceChecking

/-!
SG §3.2(4): a finite Function check quantifies its observation child over the
current goal's complete independent checked domain. Source binders retain
their original admission. Neither a descriptor nor a checking proof enters
the raw invocation or actual event identity.

The registration equations below concern the actual goal challenge. Changing
a descriptor preserves its raw input, not arbitrary checked-incidence guards.
The Function results are current-event results; future-event registration and
general recursive L4 are separate obligations.
-/
namespace YulangClosure.OriginalCheckingAdmission

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceChecking

/-- Only the checking invocation domain changes. All other original payload
classes retain their independently declared admission and complete scope. -/
def GoalDataAdmitted (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (state : Decoded s View)
    (goal : CheckGoal) (binder : Binder) : Payload s View → Prop
  | .runtime (.invocation raw) =>
      binder.kind = .invocation ∧ raw.value = (state.goalRow binder goal).value ∧
      raw.valueRoot = (state.goalRow binder goal).root ∧
      CheckedDomain inputs (raw.challenge
        (readout.event state.fixedFrames state.assignment.event binder (.invocation raw))
        (state.assignment.descriptor goal.upper) state.viewMeaning)
  | payload => DataAdmitted inputs readout admissions state binder payload

def GoalAdmitted (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (goal : CheckGoal) (binder : Binder) (candidate : ScopedValue (Payload s View)) : Prop :=
  candidate.event.parents = environment.eventPath ∧ ∃ state,
    decode readout environment = some state ∧
      GoalDataAdmitted inputs readout admissions state goal binder candidate.data

/-- Apply this override AFTER legacy admission/function wrappers. It changes
only the checking predicate and preserves the caller's source admission. -/
def goalAdmissionKernel (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (original : Kernel (Payload s View)) :
    Kernel (Payload s View) :=
  {original with checkingAdmitted := GoalAdmitted inputs readout admissions}

/-- The order is explicit: install original source admission and Function
incidence first, then the current-goal checking domain. -/
def goalFunctionKernel (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (original : Kernel (Payload s View)) :
    Kernel (Payload s View) :=
  goalAdmissionKernel inputs readout admissions
    (OriginalSourceEnvironment.functionKernel inputs readout admissions original)

theorem goal_kernel_admissions (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (original : Kernel (Payload s View)) :
    (goalAdmissionKernel inputs readout admissions original).admitted = original.admitted ∧
    (goalAdmissionKernel inputs readout admissions original).checkingAdmitted =
      GoalAdmitted inputs readout admissions := ⟨rfl, rfl⟩

theorem function_kernel_admissions (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (original : Kernel (Payload s View)) :
    (goalFunctionKernel inputs readout admissions original).admitted =
      Admitted inputs readout admissions ∧
    (goalFunctionKernel inputs readout admissions original).checkingAdmitted =
      GoalAdmitted inputs readout admissions := ⟨rfl, rfl⟩

theorem goal_admitted_scoped_iff (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (goal : CheckGoal) (binder : Binder) (state : Decoded s View)
    (decoded : decode readout environment = some state) (occurrence : Nat) (data : Payload s View) :
    GoalAdmitted inputs readout admissions environment goal binder
      (scopeCandidate environment occurrence data) ↔
      GoalDataAdmitted inputs readout admissions state goal binder data := by
  simp only [GoalAdmitted, scopeCandidate, decoded, Option.some.injEq, true_and]
  constructor
  · rintro ⟨other, equal, valid⟩
    subst other
    exact valid
  · intro valid
    exact ⟨state, rfl, valid⟩

theorem goal_data_aligned_legacy (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (state : Decoded s View)
    (goal : CheckGoal) (binder : Binder)
    (aligned : state.assignment.descriptor goal.upper = (state.callRow binder).descriptor)
    (payload : Payload s View) :
    GoalDataAdmitted inputs readout admissions state goal binder payload ↔
      DataAdmitted inputs readout admissions state binder payload := by
  cases payload with
  | root data | logical kind data | shared data => rfl
  | runtime data =>
      cases data <;> simp only [GoalDataAdmitted, DataAdmitted, Decoded.goalRow,
        ValueRow.withDescriptor]
      rw [aligned]

theorem goal_admission_aligned_legacy (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (goal : CheckGoal) (binder : Binder) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (aligned : state.assignment.descriptor goal.upper = (state.callRow binder).descriptor)
    (candidate : ScopedValue (Payload s View)) :
    GoalAdmitted inputs readout admissions environment goal binder candidate ↔
      Admitted inputs readout admissions environment binder candidate := by
  constructor
  · rintro ⟨scope, other, otherDecoded, valid⟩
    have same : other = state := Option.some.inj (otherDecoded.symm.trans decoded)
    subst other
    exact ⟨scope, state, decoded,
      (goal_data_aligned_legacy inputs readout admissions state goal binder aligned candidate.data).mp valid⟩
  · rintro ⟨scope, other, otherDecoded, valid⟩
    have same : other = state := Option.some.inj (otherDecoded.symm.trans decoded)
    subst other
    exact ⟨scope, state, decoded,
      (goal_data_aligned_legacy inputs readout admissions state goal binder aligned candidate.data).mpr valid⟩

theorem initial_goal_admission_legacy (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (goal : CheckGoal) (binder : Binder) (upper : goal.upper = ⟨binder.site, .descriptor⟩)
    (candidate : ScopedValue (Payload s View)) :
    GoalAdmitted inputs readout admissions environment goal binder candidate ↔
      Admitted inputs readout admissions environment binder candidate := by
  constructor
  · rintro ⟨scope, state, decoded, valid⟩
    exact ⟨scope, state, decoded,
      (goal_data_aligned_legacy inputs readout admissions state goal binder
        (by simp only [upper, Decoded.callRow]) candidate.data).mp valid⟩
  · rintro ⟨scope, state, decoded, valid⟩
    exact ⟨scope, state, decoded,
      (goal_data_aligned_legacy inputs readout admissions state goal binder
        (by simp only [upper, Decoded.callRow]) candidate.data).mpr valid⟩

theorem encode_retarget {row : ValueRow s} (challenge : Challenge row)
    (descriptor : s.Descriptor) (view : View) :
    encodeInvocation (challenge.retarget descriptor) view = encodeInvocation challenge view := rfl

/-- The decoder may use any descriptor: its full actual input is unchanged. -/
theorem decode_encode_input {row : ValueRow s} (challenge : Challenge row)
    (view : View) (viewMeaning : View → s.Interface)
    (presented : viewMeaning view = challenge.carrierView) (descriptor : s.Descriptor) :
    ((encodeInvocation challenge view).challenge row.event descriptor viewMeaning).input =
      challenge.input := by
  cases row
  cases challenge
  simp_all [encodeInvocation, Invocation.challenge, Invocation.decorate, Challenge.input]

theorem encoded_scope_retarget (environment : Environment (Payload s View))
    (occurrence : Nat) {row : ValueRow s} (challenge : Challenge row)
    (descriptor : s.Descriptor) (view : View) :
    scopeCandidate environment occurrence
      (.runtime (.invocation (encodeInvocation (challenge.retarget descriptor) view))) =
    scopeCandidate environment occurrence
      (.runtime (.invocation (encodeInvocation challenge view))) := rfl

theorem encoded_event_path_retarget (environment : Environment (Payload s View))
    (binder : Binder) (occurrence : Nat) {row : ValueRow s} (challenge : Challenge row)
    (descriptor : s.Descriptor) (view : View) :
    (environment.extend binder (scopeCandidate environment occurrence
      (.runtime (.invocation (encodeInvocation (challenge.retarget descriptor) view))))).eventPath =
    (environment.extend binder (scopeCandidate environment occurrence
      (.runtime (.invocation (encodeInvocation challenge view))))).eventPath := rfl

/-- Complete target admission is supplied before provider or body acceptance.
Both readback premises are about this goal's own challenge. -/
theorem goal_challenge_supplies_admission (inputs : Inputs s)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (environment : Environment (Payload s View)) (goal : CheckGoal) (binder : Binder)
    (invocation : binder.kind = .invocation) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (challenge : Challenge (state.goalRow binder goal)) (admitted : CheckedDomain inputs challenge)
    (view : View) (presented : state.viewMeaning view = challenge.carrierView)
    (readback : readout.event state.fixedFrames state.assignment.event binder
      (.invocation (encodeInvocation challenge view)) = (state.goalRow binder goal).event)
    (occurrence : Nat) :
    GoalAdmitted inputs readout admissions environment goal binder
      (scopeCandidate environment occurrence (.runtime (.invocation (encodeInvocation challenge view)))) := by
  apply (goal_admitted_scoped_iff inputs readout admissions environment goal binder state decoded occurrence _).mpr
  refine ⟨invocation, rfl, rfl, ?_⟩
  rw [readback]
  change CheckedDomain inputs ((encodeInvocation challenge view).challenge
    (state.goalRow binder goal).event (state.goalRow binder goal).descriptor state.viewMeaning)
  rw [decode_encode_challenge challenge view state.viewMeaning presented]
  exact admitted

theorem goal_admission_recovers_challenge (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (goal : CheckGoal) (binder : Binder) (state : Decoded s View)
    (decoded : decode readout environment = some state) (candidate : ScopedValue (Payload s View))
    (admitted : GoalAdmitted inputs readout admissions environment goal binder candidate)
    (invocation : binder.kind = .invocation) :
    ∃ raw : Invocation s View, candidate.data = .runtime (.invocation raw) ∧
      raw.value = (state.goalRow binder goal).value ∧
      raw.valueRoot = (state.goalRow binder goal).root ∧
      CheckedDomain inputs (raw.challenge
        (readout.event state.fixedFrames state.assignment.event binder (.invocation raw))
        (state.assignment.descriptor goal.upper) state.viewMeaning) := by
  obtain ⟨_, other, decodedOther, valid⟩ := admitted
  have same : other = state := Option.some.inj (decodedOther.symm.trans decoded)
  subst other
  cases payload : candidate.data with
  | root data => simp only [payload, GoalDataAdmitted, DataAdmitted] at valid
  | logical kind data =>
      simp only [payload, GoalDataAdmitted, DataAdmitted, invocation] at valid
      cases kind <;> simp [LogicalKind.binderKind] at valid
  | shared data =>
      simp only [payload, GoalDataAdmitted, DataAdmitted, invocation, reduceCtorEq, false_and] at valid
  | runtime data =>
      cases data with
      | invocation raw =>
          simp only [payload, GoalDataAdmitted] at valid
          exact ⟨raw, rfl, valid.2.1, valid.2.2.1, valid.2.2.2⟩
      | receipt data | returnRebind data | response data | rigidOperation data | oneShot data =>
          simp only [payload, GoalDataAdmitted, DataAdmitted, invocation, reduceCtorEq, false_and] at valid

theorem goal_invocation_has_active (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (goal : CheckGoal) (binder : Binder) (state : Decoded s View)
    (decoded : decode readout environment = some state) (candidate : ScopedValue (Payload s View))
    (admitted : GoalAdmitted inputs readout admissions environment goal binder candidate)
    (kind : binder.kind = .invocation) :
    ∃ next input, decode readout (environment.extend binder candidate) = some next ∧
      next.active = some input := by
  obtain ⟨raw, payload, value, root, domain⟩ :=
    goal_admission_recovers_challenge inputs readout admissions environment goal binder
      state decoded candidate admitted kind
  refine ⟨decodeFrame readout state ⟨binder, candidate, environment.eventPath⟩,
    (raw.challenge (readout.event state.fixedFrames state.assignment.event binder (.invocation raw))
      (state.assignment.descriptor ⟨binder.site, .descriptor⟩) state.viewMeaning).input,
    decode_extend readout environment binder candidate state decoded, ?_⟩
  simpa only [decodeFrame, payload, Decoded.retain] using
    runtime_invocation_captures_input readout state binder raw

/-- The recursive observation child ranges over the current goal's exact D.
The binder descriptor is irrelevant to the stored CallInput. Endpoint
incidence comes from the original finite Function shape; no targetReadback
between the binder slot and the current goal is a premise. -/
theorem goal_observation_child_transport (inputs : Inputs s) (Z : Family s)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (environment : Environment (Payload s View)) (goal : CheckGoal) (binder : Binder)
    (invocation : binder.kind = .invocation) (state : Decoded s View)
    (decoded : decode readout environment = some state) (observation : CheckGoal)
    (target : observation.upper = goal.upper)
    (child : ∀ candidate,
      GoalAdmitted inputs readout admissions environment goal binder candidate →
      ∀ next, decode readout (environment.extend binder candidate) = some next →
        ObservationMeaning inputs Z next observation)
    (challenge : Challenge (state.goalRow binder goal)) (admitted : CheckedDomain inputs challenge)
    (view : View) (presented : state.viewMeaning view = challenge.carrierView)
    (readback : readout.event state.fixedFrames state.assignment.event binder
      (.invocation (encodeInvocation challenge view)) = (state.goalRow binder goal).event)
    (occurrence : Nat) :
    ∀ raw, ObservationMem inputs Z
      (challenge.retarget (state.assignment.descriptor observation.lower)) raw →
        ObservationMem inputs Z challenge raw := by
  let candidate := scopeCandidate environment occurrence
    (.runtime (.invocation (encodeInvocation challenge view)))
  have accepted : GoalAdmitted inputs readout admissions environment goal binder candidate :=
    goal_challenge_supplies_admission inputs readout admissions environment goal binder invocation
      state decoded challenge admitted view presented readback occurrence
  let next := (state.runtime readout binder (.invocation (encodeInvocation challenge view))).retain
    ⟨binder, candidate, environment.eventPath⟩
  have nextDecoded : decode readout (environment.extend binder candidate) = some next := by
    simpa only [candidate, scopeCandidate, decodeFrame, next] using
      decode_extend readout environment binder candidate state decoded
  have observed := child candidate accepted next nextDecoded
  change ObservationMeaning inputs Z
    (state.runtime readout binder (.invocation (encodeInvocation challenge view))) observation at observed
  simp only [ObservationMeaning, runtime_invocation_captures_input] at observed
  change ∀ raw, ObservationMem inputs Z
      (inputChallenge ((encodeInvocation challenge view).challenge
        (readout.event state.fixedFrames state.assignment.event binder (.invocation (encodeInvocation challenge view)))
        (state.assignment.descriptor ⟨binder.site, .descriptor⟩) state.viewMeaning).input
        (state.assignment.descriptor observation.lower)) raw →
      ObservationMem inputs Z
      (inputChallenge ((encodeInvocation challenge view).challenge
        (readout.event state.fixedFrames state.assignment.event binder (.invocation (encodeInvocation challenge view)))
        (state.assignment.descriptor ⟨binder.site, .descriptor⟩) state.viewMeaning).input
        (state.assignment.descriptor observation.upper)) raw at observed
  rw [readback, decode_encode_input challenge view state.viewMeaning presented] at observed
  change ∀ raw, ObservationMem inputs Z
      (challenge.retarget (state.assignment.descriptor observation.lower)) raw →
      ObservationMem inputs Z
      (challenge.retarget (state.assignment.descriptor observation.upper)) raw at observed
  rw [target] at observed
  exact observed

/-- Current-event Function transport from its recursive child meanings.
Every registration law is indexed by the actual current target challenge. -/
theorem goal_function_at (inputs : Inputs s) (Z : Family s)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (environment : Environment (Payload s View)) (goal domain observation : CheckGoal) (binder : Binder)
    (shape : OriginalSourceEnvironment.FunctionShape inputs readout environment goal domain binder observation)
    (state : Decoded s View) (decoded : decode readout environment = some state)
    (domainMeaning : DomainMeaning inputs state domain)
    (observationMeaning : ∀ candidate,
      GoalAdmitted inputs readout admissions environment goal binder candidate →
      ∀ next, decode readout (environment.extend binder candidate) = some next →
        ObservationMeaning inputs Z next observation)
    (token : s.Receipt → View)
    (viewReadback : ∀ challenge : Challenge (state.goalRow binder goal),
      inputs.checkedIncidences challenge → state.viewMeaning (token challenge.receipt) = challenge.carrierView)
    (eventReadback : ∀ challenge : Challenge (state.goalRow binder goal), inputs.checkedIncidences challenge →
      readout.event state.fixedFrames state.assignment.event binder
        (.invocation (encodeInvocation challenge (token challenge.receipt))) = (state.goalRow binder goal).event)
    (occurrence : Nat)
    (source : FunctionAt inputs Z ((state.goalRow binder goal).withDescriptor
      (state.assignment.descriptor goal.lower)))
    (guards : ∀ provider, inputs.actual (state.goalRow binder goal).value (state.goalRow binder goal).root provider →
      (inputs.functionGuards (state.goalRow binder goal) provider).Valid)
    (captures : ∀ provider, inputs.actual (state.goalRow binder goal).value (state.goalRow binder goal).root provider →
      (inputs.capturedFields (state.goalRow binder goal) provider).Holds Z) :
    FunctionAt inputs Z (state.goalRow binder goal) := by
  apply same_provider_function_check inputs Z (state.goalRow binder goal)
    (state.assignment.descriptor goal.lower) source guards captures
  · intro challenge admitted
    unfold DomainMeaning at domainMeaning
    rw [shape.domainLower, shape.domainUpper] at domainMeaning
    exact domainMeaning _ _ challenge admitted
  · intro challenge admitted
    have incidence := admitted.2.2.2.2.1
    have action := goal_observation_child_transport inputs Z readout admissions environment goal binder
      shape.invocationKind state decoded observation shape.observationUpper observationMeaning
      challenge admitted (token challenge.receipt) (viewReadback challenge incidence)
      (eventReadback challenge incidence) occurrence
    rw [shape.observationLower] at action
    exact action

/-- The actual finite Function constructor retains both recursively checked
children. Its semantic step consumes the explicit recursive induction
hypotheses; registered Checking supplies those in the application below. -/
theorem goal_function_checking_constructor (inputs : Inputs s) (Z : Family s)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (environment : Environment (Payload s View))
    (goal domain observation : CheckGoal) (binder : Binder)
    (shape : OriginalSourceEnvironment.FunctionShape inputs readout environment goal domain binder observation)
    (domainChecked : Checking (goalFunctionKernel inputs readout admissions original) environment domain)
    (observationChecked : ∀ candidate,
      GoalAdmitted inputs readout admissions environment goal binder candidate →
      Checking (goalFunctionKernel inputs readout admissions original)
        (environment.extend binder candidate) observation)
    (state : Decoded s View) (decoded : decode readout environment = some state)
    (domainMeaning : DomainMeaning inputs state domain)
    (observationMeaning : ∀ candidate,
      GoalAdmitted inputs readout admissions environment goal binder candidate →
      ∀ next, decode readout (environment.extend binder candidate) = some next →
        ObservationMeaning inputs Z next observation)
    (token : s.Receipt → View)
    (viewReadback : ∀ challenge : Challenge (state.goalRow binder goal),
      inputs.checkedIncidences challenge → state.viewMeaning (token challenge.receipt) = challenge.carrierView)
    (eventReadback : ∀ challenge : Challenge (state.goalRow binder goal), inputs.checkedIncidences challenge →
      readout.event state.fixedFrames state.assignment.event binder
        (.invocation (encodeInvocation challenge (token challenge.receipt))) = (state.goalRow binder goal).event)
    (occurrence : Nat)
    (source : FunctionAt inputs Z ((state.goalRow binder goal).withDescriptor
      (state.assignment.descriptor goal.lower)))
    (guards : ∀ provider, inputs.actual (state.goalRow binder goal).value (state.goalRow binder goal).root provider →
      (inputs.functionGuards (state.goalRow binder goal) provider).Valid)
    (captures : ∀ provider, inputs.actual (state.goalRow binder goal).value (state.goalRow binder goal).root provider →
      (inputs.capturedFields (state.goalRow binder goal) provider).Holds Z) :
    Checking (goalFunctionKernel inputs readout admissions original) environment goal ∧
      FunctionAt inputs Z (state.goalRow binder goal) := by
  refine ⟨Checking.function goal domain observation binder shape.domainMode shape.observationMode
    shape.invocationKind shape domainChecked observationChecked, ?_⟩
  exact goal_function_at inputs Z readout admissions environment goal domain observation binder shape
    state decoded domainMeaning observationMeaning token viewReadback eventReadback occurrence source guards captures

/-- The final registered proof kernel is composed AFTER the concrete goal
override. It preserves that exact admission predicate in its Function leaves. -/
def registeredKernel (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (ports : PortReadout s View)
    (original : Kernel (Payload s View)) : Kernel (Payload s View) :=
  OriginalSourceChecking.kernel inputs registry declarations (environmentReading inputs readout ports)
    (goalFunctionKernel inputs readout admissions original)

theorem registered_kernel_admissions (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (ports : PortReadout s View)
    (original : Kernel (Payload s View)) :
    (registeredKernel inputs registry declarations readout admissions ports original).admitted =
      Admitted inputs readout admissions ∧
    (registeredKernel inputs registry declarations readout admissions ports original).checkingAdmitted =
      GoalAdmitted inputs readout admissions ∧
    (registeredKernel inputs registry declarations readout admissions ports original).functionShape =
      OriginalSourceChecking.FunctionShape inputs registry (environmentReading inputs readout ports)
        (GoalAdmitted inputs readout admissions) := ⟨rfl, rfl, rfl⟩

/-- Domain/observation meanings here are obtained from actual finite Checking
proofs. Guard/capture consequences are finite registered proof data. The
result is the current Function core, not an all-future value membership. -/
theorem goal_function_children_at_meaning (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (ports : PortReadout s View)
    (original : Kernel (Payload s View)) (environment : Environment (Payload s View))
    (goal domain observation : CheckGoal) (binder : Binder)
    (shape : OriginalSourceEnvironment.FunctionShape inputs readout environment goal domain binder observation)
    (domainChecked : Checking (registeredKernel inputs registry declarations readout admissions ports original)
      environment domain)
    (observationChecked : ∀ candidate,
      GoalAdmitted inputs readout admissions environment goal binder candidate →
      Checking (registeredKernel inputs registry declarations readout admissions ports original)
        (environment.extend binder candidate) observation)
    (state : Decoded s View) (decoded : decode readout environment = some state)
    (token : s.Receipt → View)
    (viewReadback : ∀ challenge : Challenge (state.goalRow binder goal), inputs.checkedIncidences challenge →
      state.viewMeaning (token challenge.receipt) = challenge.carrierView)
    (eventReadback : ∀ challenge : Challenge (state.goalRow binder goal), inputs.checkedIncidences challenge →
      readout.event state.fixedFrames state.assignment.event binder
        (.invocation (encodeInvocation challenge (token challenge.receipt))) = (state.goalRow binder goal).event)
    (occurrence : Nat)
    (source : FunctionAt inputs (Meaning inputs) ((state.goalRow binder goal).withDescriptor
      (state.assignment.descriptor goal.lower)))
    (guardCode : ∀ provider, inputs.actual (state.goalRow binder goal).value (state.goalRow binder goal).root provider →
      Proof inputs registry (fun _ _ => False)
        (.guard (inputs.functionGuards ((state.goalRow binder goal).withDescriptor
          (state.assignment.descriptor goal.lower)) provider).Valid)
        (.guard (inputs.functionGuards (state.goalRow binder goal) provider).Valid))
    (captureCode : ∀ provider, inputs.actual (state.goalRow binder goal).value (state.goalRow binder goal).root provider →
      Proof inputs registry (fun _ _ => False)
        (inputs.capturedFields ((state.goalRow binder goal).withDescriptor
          (state.assignment.descriptor goal.lower)) provider)
        (inputs.capturedFields (state.goalRow binder goal) provider)) :
    FunctionAt inputs (Meaning inputs) (state.goalRow binder goal) := by
  have domainMeaning := domain_action inputs readout ports environment state decoded domain shape.domainMode
    (checking_sound inputs registry declarations (environmentReading inputs readout ports)
      (goalFunctionKernel inputs readout admissions original) domainChecked)
  have observationMeaning : ∀ candidate,
      GoalAdmitted inputs readout admissions environment goal binder candidate →
      ∀ next, decode readout (environment.extend binder candidate) = some next →
        ObservationMeaning inputs (Meaning inputs) next observation := by
    intro candidate admitted next nextDecoded
    obtain ⟨actual, input, actualDecoded, active⟩ := goal_invocation_has_active inputs readout admissions
      environment goal binder state decoded candidate admitted shape.invocationKind
    have same : actual = next := Option.some.inj (actualDecoded.symm.trans nextDecoded)
    subst actual
    exact observation_action inputs readout ports (environment.extend binder candidate) next nextDecoded
      observation shape.observationMode input active
      (checking_sound inputs registry declarations (environmentReading inputs readout ports)
        (goalFunctionKernel inputs readout admissions original) (observationChecked candidate admitted))
  apply goal_function_at inputs (Meaning inputs) readout admissions environment goal domain observation binder
    shape state decoded domainMeaning observationMeaning token viewReadback eventReadback occurrence source
  · intro provider actual
    exact (guardCode provider actual).sound inputs registry (fun _ _ impossible => False.elim impossible)
      (source.2 provider actual).1
  · intro provider actual
    exact (captureCode provider actual).sound inputs registry (fun _ _ impossible => False.elim impossible)
      (source.2 provider actual).2.1

/-- A completed source value supplies the source Function core by actual
Meaning unfolding. The finite child proofs then establish the target's
current-event core. No future target membership is inferred here. -/
theorem checked_current_function_from_meaning (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (ports : PortReadout s View)
    (original : Kernel (Payload s View)) (environment : Environment (Payload s View))
    (goal domain observation : CheckGoal) (binder : Binder)
    (shape : OriginalSourceEnvironment.FunctionShape inputs readout environment goal domain binder observation)
    (domainChecked : Checking (registeredKernel inputs registry declarations readout admissions ports original)
      environment domain)
    (observationChecked : ∀ candidate,
      GoalAdmitted inputs readout admissions environment goal binder candidate →
      Checking (registeredKernel inputs registry declarations readout admissions ports original)
        (environment.extend binder candidate) observation)
    (state : Decoded s View) (decoded : decode readout environment = some state)
    (token : s.Receipt → View)
    (viewReadback : ∀ challenge : Challenge (state.goalRow binder goal), inputs.checkedIncidences challenge →
      state.viewMeaning (token challenge.receipt) = challenge.carrierView)
    (eventReadback : ∀ challenge : Challenge (state.goalRow binder goal), inputs.checkedIncidences challenge →
      readout.event state.fixedFrames state.assignment.event binder
        (.invocation (encodeInvocation challenge (token challenge.receipt))) = (state.goalRow binder goal).event)
    (occurrence : Nat)
    (source : Meaning inputs (.value ((state.goalRow binder goal).withDescriptor
      (state.assignment.descriptor goal.lower))))
    (guardCode : ∀ provider, inputs.actual (state.goalRow binder goal).value (state.goalRow binder goal).root provider →
      Proof inputs registry (fun _ _ => False)
        (.guard (inputs.functionGuards ((state.goalRow binder goal).withDescriptor
          (state.assignment.descriptor goal.lower)) provider).Valid)
        (.guard (inputs.functionGuards (state.goalRow binder goal) provider).Valid))
    (captureCode : ∀ provider, inputs.actual (state.goalRow binder goal).value (state.goalRow binder goal).root provider →
      Proof inputs registry (fun _ _ => False)
        (inputs.capturedFields ((state.goalRow binder goal).withDescriptor
          (state.assignment.descriptor goal.lower)) provider)
        (inputs.capturedFields (state.goalRow binder goal) provider)) :
    FunctionAt inputs (Meaning inputs) (state.goalRow binder goal) := by
  obtain ⟨other, otherDecoded, owner, sourceForm, targetForm⟩ := shape.decoded
  have same : other = state := Option.some.inj (otherDecoded.symm.trans decoded)
  subst other
  have sourceCore : FunctionAt inputs (Meaning inputs) ((state.goalRow binder goal).withDescriptor
      (state.assignment.descriptor goal.lower)) := by
    have core := ((meaning_iff inputs _).mp source).1
    simpa only [ValueRow.withDescriptor, sourceForm] using core
  exact goal_function_children_at_meaning inputs registry declarations readout admissions ports original
    environment goal domain observation binder shape domainChecked observationChecked state decoded
    token viewReadback eventReadback occurrence sourceCore guardCode captureCode

theorem default_checking_admission (original : Kernel Value) :
    ({atom := original.atom, admitted := original.admitted,
      primitiveCheck := original.primitiveCheck, structuralShape := original.structuralShape,
      functionShape := original.functionShape, boundaryTag := original.boundaryTag,
      conversion := original.conversion} : Kernel Value).checkingAdmitted =
      (fun environment _ binder candidate => original.admitted environment binder candidate) := rfl

/-- A record update does not recompute a captured default. This is why the
two accepted legacy wrappers explicitly assign both admission predicates. -/
theorem admission_update_keeps_checking (original : Kernel Value)
    (replacement : Environment Value → Binder → ScopedValue Value → Prop) :
    ({original with admitted := replacement} : Kernel Value).checkingAdmitted = original.checkingAdmitted := rfl

theorem legacy_admission_kernel_fields (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (original : Kernel (Payload s View)) :
    (admissionKernel inputs readout admissions original).admitted = Admitted inputs readout admissions ∧
    (admissionKernel inputs readout admissions original).checkingAdmitted =
      (fun environment _ binder candidate => Admitted inputs readout admissions environment binder candidate) :=
  ⟨rfl, rfl⟩

theorem legacy_function_kernel_fields (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (original : Kernel (Payload s View)) :
    (OriginalSourceEnvironment.functionKernel inputs readout admissions original).admitted =
      Admitted inputs readout admissions ∧
    (OriginalSourceEnvironment.functionKernel inputs readout admissions original).checkingAdmitted =
      (fun environment _ binder candidate => Admitted inputs readout admissions environment binder candidate) :=
  ⟨rfl, rfl⟩

theorem literal_kernel_admissions (inputs : Inputs s) (declarations : LiteralDeclaration s)
    (original : Kernel (SourceAssignment s)) (site : Site) (literal : Literal) :
    (literalKernel inputs declarations original site literal).admitted = original.admitted ∧
    (literalKernel inputs declarations original site literal).checkingAdmitted = original.checkingAdmitted :=
  ⟨rfl, rfl⟩

theorem name_kernel_admissions (inputs : Inputs s) (original : Kernel (SourceAssignment s))
    (site : Site) (name : OriginalSource.Name) :
    (nameKernel inputs original site name).admitted = original.admitted ∧
    (nameKernel inputs original site name).checkingAdmitted = original.checkingAdmitted := ⟨rfl, rfl⟩

theorem folded_literal_kernel_admissions (inputs : Inputs s) (readout : RuntimeReadout s View)
    (declarations : LiteralDeclaration s) (original : Kernel (Payload s View)) (site : Site) (literal : Literal) :
    (foldedLiteralKernel inputs readout declarations original site literal).admitted = original.admitted ∧
    (foldedLiteralKernel inputs readout declarations original site literal).checkingAdmitted =
      original.checkingAdmitted := ⟨rfl, rfl⟩

theorem folded_name_kernel_admissions (inputs : Inputs s) (readout : RuntimeReadout s View)
    (original : Kernel (Payload s View)) (site : Site) (name : OriginalSource.Name) :
    (foldedNameKernel inputs readout original site name).admitted = original.admitted ∧
    (foldedNameKernel inputs readout original site name).checkingAdmitted = original.checkingAdmitted := ⟨rfl, rfl⟩

theorem checking_kernel_admissions (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (reading : Reading s Value) (original : Kernel Value) :
    (OriginalSourceChecking.kernel inputs registry declarations reading original).admitted = original.admitted ∧
    (OriginalSourceChecking.kernel inputs registry declarations reading original).checkingAdmitted =
      original.checkingAdmitted := ⟨rfl, rfl⟩

/-- Authentic App ownership supplies this exact checking occurrence. Its
initial target recovers legacy admission; composition intermediates need not. -/
theorem source_app_admission_recovery (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (context : Context) (site : Site) (callee argument : Source .expression)
    (candidate : ScopedValue (Payload s View)) :
    ∃ premises children,
      sourceRules context (.app ⟨site, none⟩ callee argument) =
        .existsE ⟨site, .viewLogic, 0⟩ (.rule .app site context premises children) ∧
      Premise.checking ⟨.value, site, context, ⟨callee.site, .returnedValue⟩,
        ⟨site, .descriptor⟩⟩ ∈ premises ∧
      (GoalAdmitted inputs readout admissions environment
        ⟨.value, site, context, ⟨callee.site, .returnedValue⟩, ⟨site, .descriptor⟩⟩
        ⟨site, .invocation, 0⟩ candidate ↔
        Admitted inputs readout admissions environment ⟨site, .invocation, 0⟩ candidate) := by
  obtain ⟨premises, children, generated, present⟩ := source_app_value_incidence context site callee argument
  refine ⟨premises, children, generated, present, ?_⟩
  exact initial_goal_admission_legacy inputs readout admissions environment _ _ rfl candidate

/-- Every intermediate goal at the registered App still uses the returned
callee, never the App's eventual result. The target endpoint is unrestricted. -/
theorem goal_app_callable (root : Root s View) (context : Context) (site : Site)
    (callee argument : Source .expression) (goal : CheckGoal) :
    let state := (root.withSource context (.app ⟨site, none⟩ callee argument)).decoded
    (state.goalRow ⟨site, .invocation, 0⟩ goal).value =
      root.assignment.value ⟨callee.site, .returnedValue⟩ ∧
    (state.goalRow ⟨site, .invocation, 0⟩ goal).root =
      root.assignment.root ⟨callee.site, .returnedValue⟩ := by
  simpa only [Decoded.goalRow, ValueRow.withDescriptor] using
    registered_app_callable root context site callee argument

theorem goal_lambda_callable (root : Root s View) (context : Context) (site : Site)
    (formal : Formal) (pattern : Source .pattern) (body : Source .expression) (goal : CheckGoal) :
    let state := (root.withSource context (.lambda ⟨site, none⟩ formal pattern body)).decoded
    (state.goalRow ⟨site, .invocation, 0⟩ goal).value = root.assignment.value ⟨site, .finalRoot⟩ ∧
    (state.goalRow ⟨site, .invocation, 0⟩ goal).root = root.assignment.root ⟨site, .finalRoot⟩ := by
  simpa only [Decoded.goalRow, ValueRow.withDescriptor] using
    registered_lambda_callable root context site formal pattern body

theorem goal_invocation_captures_subject (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (state : Decoded s View)
    (goal : CheckGoal) (binder : Binder) (raw : Invocation s View)
    (admitted : GoalDataAdmitted inputs readout admissions state goal binder (.runtime (.invocation raw))) :
    ((state.runtime readout binder (.invocation raw)).active.map
      (fun input => (input.value, input.valueRoot))) =
      some (state.assignment.value (state.callSubject binder),
        state.assignment.root (state.callSubject binder)) := by
  change some (raw.value, raw.valueRoot) = _
  rw [admitted.2.1, admitted.2.2.1]
  rfl

theorem goal_admission_ignores_stored_maps (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (anchors : AnchorKey (Payload s View) → ScopedValue (Payload s View))
    (publications : PublicationId (Payload s View) → Option (PublicationRecord (Payload s View)))
    (goal : CheckGoal) (binder : Binder) (candidate : ScopedValue (Payload s View)) :
    GoalAdmitted inputs readout admissions {environment with anchors := anchors, publications := publications}
      goal binder candidate ↔ GoalAdmitted inputs readout admissions environment goal binder candidate := Iff.rfl

/-- The actual received carrier and owned native Receipt construct the same
goal-admitted candidate. Its view/event equations refer to the current goal
challenge, and its receipt insertion is the accepted native constructor. -/
theorem native_received_supplies_goal_admission [DecidableEq Key]
    (inputs : Inputs (nativeReceiptSorts s Key SiteData))
    (readout : RuntimeReadout (nativeReceiptSorts s Key SiteData) Nat)
    (admissions : LocalAdmissions (nativeReceiptSorts s Key SiteData) Nat)
    (environment : Environment (Payload (nativeReceiptSorts s Key SiteData) Nat))
    (goal : CheckGoal) (binder : Binder) (invocation : binder.kind = .invocation)
    (state : Decoded (nativeReceiptSorts s Key SiteData) Nat)
    (decoded : decode readout environment = some state)
    (challenge : Challenge (state.goalRow binder goal)) (admitted : CheckedDomain inputs challenge)
    (receiving : SourceIdentityWorld.Receiving Key s.Carrier ViewData SiteData)
    (argument : SourceIdentityWorld.Received s.Carrier)
    (owner : SourceIdentityWorld.Owner) (site : SiteData) (formal : Option Key)
    (carrier : challenge.carrier = argument.value)
    (owned : challenge.receipt = {owner := owner, view := argument.view, site := site, formal := formal})
    (viewReadback : state.viewMeaning argument.view = challenge.carrierView)
    (eventReadback : readout.event state.fixedFrames state.assignment.event binder
      (.invocation (encodeInvocation challenge argument.view)) = (state.goalRow binder goal).event)
    (occurrence : Nat) :
    GoalAdmitted inputs readout admissions environment goal binder
      (scopeCandidate environment occurrence (.runtime (.invocation
        (nativeInvocation (encodeInvocation challenge argument.view) argument
          {owner := owner, view := argument.view, site := site, formal := formal})))) ∧
    (receiving.record owner argument.view site formal).receipts.cell receiving.receipts.size =
      some {owner := owner, view := argument.view, site := site, formal := formal} := by
  rw [native_received_encoding challenge argument _ carrier owned]
  exact ⟨goal_challenge_supplies_admission inputs readout admissions environment goal binder invocation
    state decoded challenge admitted argument.view viewReadback eventReadback occurrence,
    native_receipt_token_owned receiving owner argument.view site formal⟩

/-! A finite discriminator for admission plumbing, not a proposed complete
Yulang semantic instance. Both independent checked domains are nonempty and
distinct. All unrelated original input fields remain explicit. -/
namespace Discriminator

def sorts : Sorts where
  Valuation := Unit
  ConstructorGraph := Unit
  Dependencies := Unit
  SourceGraph := Unit
  BinderTree := Unit
  Assignment := Unit
  History := Unit
  Configuration := Unit
  JointWitness := Unit
  Scope := Unit
  Authority := Unit
  Incidence := Unit
  Dictionary := Unit
  Descriptor := Bool
  Interface := Bool
  Value := Bool
  Provider := Unit
  Root := Unit
  Carrier := Bool
  Observation := Unit
  Context := Unit
  Continuation := Unit
  Receipt := Unit
  TypedPath := Unit
  Consumer := Unit
  WitnessPosition := Unit
  WitnessValue := Unit

def event : Event sorts :=
  ⟨⟨(), (), (), (), ()⟩, (), (), (), (), (), (), (), (), ()⟩

def inputs : Inputs sorts where
  compatible := fun _ _ => True
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
  actualInlet := fun _ => false
  carrierAccepted := fun row => row.interface = false ∨ row.carrier = false
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
  eta := fun _ _ _ _ => ()
  witness := fun _ _ _ _ => ()
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

def callee : Source .expression :=
  .lambda ⟨3, none⟩ ⟨5, 11, none, false⟩ (.wild 6) (.name ⟨10, none⟩ 11)

def source : Source .expression := .app ⟨7, none⟩ callee (.literal ⟨4, none⟩ .unit)

def baseRoot (sourceDescriptor : Bool) : Root sorts Bool where
  assignment :=
    {event := event
     descriptor := fun endpoint => if endpoint.site == 7 then sourceDescriptor else endpoint.site == 9
     value := fun endpoint => endpoint.site == 7
     root := fun _ => ()
     binding := fun _ => none}
  interfaces := fun _ => false
  carriers := fun _ => false
  viewMeaning := id
  installed := fun _ => none
  callOwners := []

def rootData (sourceDescriptor : Bool) : Root sorts Bool :=
  (baseRoot sourceDescriptor).withSource [] source

def state (sourceDescriptor : Bool) : Decoded sorts Bool := (rootData sourceDescriptor).decoded

def environment (sourceDescriptor : Bool) : Environment (Payload sorts Bool) where
  root := .root (rootData sourceDescriptor)
  anchors := fun _ => ⟨.root (rootData sourceDescriptor), ⟨[], 0⟩⟩
  publications := fun _ => none
  origin := 0

def binder : Binder := ⟨7, .invocation, 0⟩

def goal (target : Bool) : CheckGoal :=
  ⟨.value, 7, [], ⟨3, .returnedValue⟩, ⟨if target then 9 else 8, .descriptor⟩⟩

def raw (carrier : Bool) : Invocation sorts Bool :=
  ⟨⟨(), ()⟩, false, (), (), (), carrier, (), false, (), (), (), ()⟩

def candidate (sourceDescriptor carrier : Bool) : ScopedValue (Payload sorts Bool) :=
  scopeCandidate (environment sourceDescriptor) 0 (.runtime (.invocation (raw carrier)))

theorem state_callable (sourceDescriptor : Bool) :
    ((state sourceDescriptor).callRow binder).value = false ∧
    ((state sourceDescriptor).callRow binder).root = () := by
  exact registered_app_callable (baseRoot sourceDescriptor) [] 7 callee (.literal ⟨4, none⟩ .unit)

theorem target_descriptor (sourceDescriptor target : Bool) :
    (state sourceDescriptor).assignment.descriptor (goal target).upper = target := by
  cases target <;> rfl

theorem binder_descriptor (sourceDescriptor : Bool) :
    ((state sourceDescriptor).callRow binder).descriptor = sourceDescriptor := rfl

theorem goal_domain (sourceDescriptor target carrier : Bool) :
    GoalAdmitted inputs readout admissions (environment sourceDescriptor) (goal target) binder
      (candidate sourceDescriptor carrier) ↔ target = false ∨ carrier = false := by
  rw [candidate, goal_admitted_scoped_iff inputs readout admissions (environment sourceDescriptor)
    (goal target) binder (state sourceDescriptor) (by rfl)]
  simp only [GoalDataAdmitted, Decoded.goalRow, ValueRow.withDescriptor,
    (state_callable sourceDescriptor).1, (state_callable sourceDescriptor).2,
    CheckedDomain, inputs, raw, Invocation.challenge, Challenge.carrierRow, target_descriptor]
  simp only [binder, true_and]
  exact ⟨fun valid => valid.2.2, fun valid => ⟨rfl, rfl, valid⟩⟩

theorem legacy_domain (sourceDescriptor carrier : Bool) :
    Admitted inputs readout admissions (environment sourceDescriptor) binder
      (candidate sourceDescriptor carrier) ↔ sourceDescriptor = false ∨ carrier = false := by
  rw [candidate, admitted_scoped_iff inputs readout admissions (environment sourceDescriptor)
    binder (state sourceDescriptor) (by rfl)]
  simp only [DataAdmitted, (state_callable sourceDescriptor).1, (state_callable sourceDescriptor).2,
    CheckedDomain, inputs, raw, Invocation.challenge, Challenge.carrierRow, binder_descriptor]
  simp only [binder, true_and]
  exact ⟨fun valid => valid.2.2, fun valid => ⟨rfl, rfl, valid⟩⟩

theorem broad_source_narrow_goal :
    Admitted inputs readout admissions (environment false) binder (candidate false true) ∧
    ¬ GoalAdmitted inputs readout admissions (environment false) (goal true) binder (candidate false true) := by
  simp only [legacy_domain, goal_domain, Bool.true_eq_false, or_self,
    true_or, not_false_eq_true, and_self]

/-- The important missing-challenge direction: a broader intermediate
checked target can admit an input absent from the original binder domain. -/
theorem narrow_source_broad_goal :
    GoalAdmitted inputs readout admissions (environment true) (goal false) binder (candidate true true) ∧
    ¬ Admitted inputs readout admissions (environment true) binder (candidate true true) := by
  simp only [legacy_domain, goal_domain, Bool.true_eq_false, or_self,
    true_or, not_false_eq_true, and_self]

theorem both_domains_nonempty (sourceDescriptor target : Bool) :
    Admitted inputs readout admissions (environment sourceDescriptor) binder (candidate sourceDescriptor false) ∧
    GoalAdmitted inputs readout admissions (environment sourceDescriptor) (goal target) binder
      (candidate sourceDescriptor false) := by
  simp only [legacy_domain, goal_domain, or_true, and_self]

def challenge (sourceDescriptor target carrier : Bool) :
    Challenge ((state sourceDescriptor).goalRow binder (goal target)) :=
  ⟨(), (), carrier, (), false, (), (), (), ()⟩

theorem same_encoded_invocation (sourceDescriptor first second carrier : Bool) :
    encodeInvocation (challenge sourceDescriptor first carrier) false =
      encodeInvocation (challenge sourceDescriptor second carrier) false := rfl

theorem same_actual_event_key (sourceDescriptor first second carrier : Bool) :
    ((environment sourceDescriptor).extend binder
      (scopeCandidate (environment sourceDescriptor) 0 (.runtime (.invocation
        (encodeInvocation (challenge sourceDescriptor first carrier) false))))).eventPath =
    ((environment sourceDescriptor).extend binder
      (scopeCandidate (environment sourceDescriptor) 0 (.runtime (.invocation
        (encodeInvocation (challenge sourceDescriptor second carrier) false))))).eventPath := rfl

theorem source_and_target_descriptors_differ :
    ((state false).callRow binder).descriptor ≠ (state false).assignment.descriptor (goal true).upper ∧
    ((state true).callRow binder).descriptor ≠ (state true).assignment.descriptor (goal false).upper := by
  change false ≠ true ∧ true ≠ false
  decide

end Discriminator

end YulangClosure.OriginalCheckingAdmission
