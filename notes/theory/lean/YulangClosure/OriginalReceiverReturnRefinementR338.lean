import YulangClosure.OriginalSourceExecutionWorldR337

/-!
R338: actual machine.rs Frame::ReceiverReturn / leave_owner(owned=true).
The boundary follows step's state take, return_value's token takes and frame pop.
Active order is
innermost first, reverse of native Vec. Failure retains partial pop mutations.
Rest projects only fields untouched by this branch, excluding State::Return
and test journals. Other frame arms / outer error driver are unrepresented.
No source provider site is identified with an original semantic Provider.
-/
namespace YulangClosure.OriginalReceiverReturnRefinementR338
open NativeClosureEnvironment SourceIdentityWorld OriginalSourceInterpretation
open OriginalParameterSemantics

inductive LeaveResult (Site : Type) where
  | invalid (control : Control Site)
  | ok (control : Control Site)

def LeaveResult.success : LeaveResult Site → Option (Control Site)
  | .invalid _ => none
  | .ok control => some control

/-- Sequential owned=true branch, including pop before validation. -/
def leaveOwned (control : Control Site) (id : Nat) (previous : Owner) : LeaveResult Site :=
  if control.current ≠ .invocation id then .invalid control else
    match control.active with
    | [] => .invalid control
    | top :: rest =>
      let popped := { control with active := rest }
      if top ≠ id then .invalid popped else
        match control.invocations.cell id with
        | none => .invalid popped
        | some invocation =>
          if invocation.active = false then .invalid popped else
            .ok ⟨deactivate control.invocations id invocation, rest, previous⟩

/-- Total successful-outcome refinement, without well-formedness premises. -/
theorem leave_owned_refines (control : Control Site) (id : Nat) (previous : Owner) :
    (leaveOwned control id previous).success = control.leave id previous := by
  by_cases current : control.current = .invocation id
  · cases stack : control.active with
    | nil => simp [leaveOwned, Control.leave, current, stack, LeaveResult.success]
    | cons top rest =>
      cases found : control.invocations.cell id with
      | none => simp [leaveOwned, Control.leave, current, stack, found, LeaveResult.success]
      | some invocation =>
        by_cases same : top = id <;> cases live : invocation.active <;>
          simp [leaveOwned, Control.leave, current, stack, found, same, live,
            LeaveResult.success]
  · simp [leaveOwned, Control.leave, current, LeaveResult.success]

/-- Construct success from independent raw input facts. -/
theorem leave_owned_construct (control : Control Site) (id : Nat) (previous : Owner)
    (rest : List Nat) (invocation : Invocation Site)
    (current : control.current = .invocation id) (stack : control.active = id :: rest)
    (found : control.invocations.cell id = some invocation) (live : invocation.active = true) :
    leaveOwned control id previous =
      .ok ⟨deactivate control.invocations id invocation, rest, previous⟩ := by
  simp [leaveOwned, current, stack, found, live]

/-- Every failure preserves owner and invocation table. Only pop can mutate. -/
theorem leave_owned_failure (control failed : Control Site) (id : Nat) (previous : Owner)
    (failure : leaveOwned control id previous = .invalid failed) :
    failed.current = control.current ∧ failed.invocations = control.invocations ∧
      (failed.active = control.active ∨
        ∃ top rest, control.active = top :: rest ∧ failed.active = rest) := by
  unfold leaveOwned at failure
  split at failure
  · cases failure; exact ⟨rfl, rfl, .inl rfl⟩
  · cases stack : control.active with
    | nil => simp only [stack] at failure; cases failure; exact ⟨rfl, rfl, .inl stack⟩
    | cons top rest =>
      simp only [stack] at failure
      split at failure
      · cases failure; exact ⟨rfl, rfl, .inr ⟨top, rest, rfl, rfl⟩⟩
      · cases found : control.invocations.cell id with
        | none =>
          simp only [found] at failure
          cases failure; exact ⟨rfl, rfl, .inr ⟨top, rest, rfl, rfl⟩⟩
        | some invocation =>
          simp only [found] at failure
          split at failure
          · cases failure; exact ⟨rfl, rfl, .inr ⟨top, rest, rfl, rfl⟩⟩
          · cases failure

theorem wrong_top_pops (control : Control Site) (id top : Nat) (previous : Owner)
    (rest : List Nat) (current : control.current = .invocation id)
    (stack : control.active = top :: rest) (wrong : top ≠ id) :
    leaveOwned control id previous = .invalid { control with active := rest } := by
  simp [leaveOwned, current, stack, wrong]

/-- Finite native vectors, retaining full source call/provider descriptors.
The stack is stored in its actual outer-to-inner Vec order. -/
structure NativeControl (Site : Type) where
  invocations : List (Invocation Site)
  activeReceivers : List Nat
  current : Owner

def vectorStore (rows : List A) : Store A := ⟨rows.length, fun id => rows[id]?⟩

def NativeControl.project (native : NativeControl Site) : Control Site :=
  ⟨vectorStore native.invocations, native.activeReceivers.reverse, native.current⟩

/-- get_mut plus assignment is precisely the existing Store deactivation. -/
theorem vector_retirement (rows : List (Invocation Site)) (id : Nat)
    (invocation : Invocation Site) (found : rows[id]? = some invocation) :
    vectorStore (rows.set id { invocation with active := false }) =
      deactivate (vectorStore rows) id invocation := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  unfold vectorStore deactivate
  simp only [List.length_set]
  apply congrArg (fun cell => Store.mk rows.length cell)
  funext other
  by_cases same : other = id
  · subst other
    simp [bound]
  · simp [same, Ne.symm same]

inductive NativeLeaveResult (Site : Type) where
  | invalid (control : NativeControl Site)
  | ok (control : NativeControl Site)

def NativeLeaveResult.project : NativeLeaveResult Site → LeaveResult Site
  | .invalid control => .invalid control.project
  | .ok control => .ok control.project

/-- Vec.pop is expressed by reversing to expose the last element; all other
updates follow the Rust statements in order, including failed partial writes. -/
def nativeLeaveOwned (native : NativeControl Site) (id : Nat) (previous : Owner) :
    NativeLeaveResult Site :=
  if native.current ≠ .invocation id then .invalid native else
    match native.activeReceivers.reverse with
    | [] => .invalid native
    | top :: rest =>
      let popped := { native with activeReceivers := rest.reverse }
      if top ≠ id then .invalid popped else
        match native.invocations[id]? with
        | none => .invalid popped
        | some invocation =>
          if invocation.active = false then .invalid popped else
            .ok { popped with
              invocations := native.invocations.set id { invocation with active := false }
              current := previous }

/-- Finite-vector native operations refine the existing Control representation,
including the exact control state retained at every failure. -/
theorem native_leave_refines (native : NativeControl Site) (id : Nat) (previous : Owner) :
    (nativeLeaveOwned native id previous).project = leaveOwned native.project id previous := by
  by_cases current : native.current = .invocation id
  · cases stack : native.activeReceivers.reverse with
    | nil => simp [nativeLeaveOwned, leaveOwned, NativeControl.project, current, stack,
        NativeLeaveResult.project]
    | cons top rest =>
      by_cases same : top = id
      · cases found : native.invocations[id]? with
        | none => simp [nativeLeaveOwned, leaveOwned, NativeControl.project, vectorStore,
            current, stack, same, found, NativeLeaveResult.project]
        | some invocation =>
          cases live : invocation.active
          · simp [nativeLeaveOwned, leaveOwned, NativeControl.project, vectorStore,
              current, stack, same, found, live, NativeLeaveResult.project]
          · simp only [nativeLeaveOwned, current, ne_eq, not_true_eq_false, ↓reduceIte,
              stack, same, found, live, Bool.true_eq_false, NativeLeaveResult.project,
              leaveOwned, NativeControl.project, vectorStore]
            congr 2
            · exact vector_retirement native.invocations id invocation found
            · exact List.reverse_reverse rest
      · simp [nativeLeaveOwned, leaveOwned, NativeControl.project, vectorStore,
          current, stack, same, NativeLeaveResult.project]
  · simp [nativeLeaveOwned, leaveOwned, NativeControl.project, current, NativeLeaveResult.project]

inductive ReturnResult (K D V ViewData Site Rest : Type) where
  /-- Retain the raw argument as evidence, not as native state. On failure the
  branch has not replaced step's Stopped(Running) sentinel; the outer driver
  then installs Stopped(Unavailable(InvalidSourceReference)). -/
  | invalid (world : World K D V ViewData Site Rest) (input : Received V)
  | returned (world : World K D V ViewData Site Rest) (output : Received V)

def ReturnResult.success : ReturnResult K D V ViewData Site Rest →
    Option (World K D V ViewData Site Rest × Received V)
  | .invalid _ _ => none
  | .returned world output => some (world, output)

/-- Normalize packet locally; assign State::Return only after exit succeeds. -/
def receiverReturn (world : World K D V ViewData Site Rest) (id : Nat)
    (previous : Owner) (input : Received V) : ReturnResult K D V ViewData Site Rest :=
  let returned : Received V := ⟨input.value, .value, input.view, input.dispatch⟩
  match leaveOwned world.control id previous with
  | .invalid failed => .invalid { world with control := failed } input
  | .ok control => .returned { world with control := control } returned

theorem receiver_return_refines (world : World K D V ViewData Site Rest) (id : Nat)
    (previous : Owner) (input : Received V) :
    (receiverReturn world id previous input).success = returnOwned world id previous input := by
  unfold receiverReturn returnOwned
  rw [← leave_owned_refines]
  cases leaveOwned world.control id previous <;> rfl

/-- Failed receiver exits retain the input argument as evidence and every represented store;
only their control stack may have the already-performed native pop. -/
theorem receiver_return_failure (world failed : World K D V ViewData Site Rest)
    (id : Nat) (previous : Owner) (input output : Received V)
    (failure : receiverReturn world id previous input = .invalid failed output) :
    output = input ∧ failed.environments = world.environments ∧
    failed.cells = world.cells ∧ failed.receiving = world.receiving ∧
    failed.rest = world.rest ∧ failed.control.current = world.control.current ∧
    failed.control.invocations = world.control.invocations ∧
    (failed.control.active = world.control.active ∨
      ∃ top rest, world.control.active = top :: rest ∧ failed.control.active = rest) := by
  unfold receiverReturn at failure
  cases left : leaveOwned world.control id previous with
  | invalid control =>
    simp only [left] at failure
    cases failure
    have shape := leave_owned_failure world.control control id previous left
    exact ⟨rfl, rfl, rfl, rfl, rfl, shape⟩
  | ok control => simp only [left] at failure; cases failure

def exited (world : World K D V ViewData Site Rest) (id : Nat) (previous : Owner)
    (rest : List Nat) (invocation : Invocation Site) : World K D V ViewData Site Rest :=
  { world with control := ⟨deactivate world.control.invocations id invocation, rest, previous⟩ }

/-- Actions, owner, stack, retirement, store preservation and every packet field
are derived from input guards; no successful desired output is assumed. -/
theorem receiver_return_construct (world : World K D V ViewData Site Rest)
    (id : Nat) (previous : Owner) (input : Received V)
    (rest : List Nat) (invocation : Invocation Site)
    (current : world.control.current = .invocation id)
    (stack : world.control.active = id :: rest)
    (found : world.control.invocations.cell id = some invocation)
    (live : invocation.active = true) :
    let after := exited world id previous rest invocation
    receiverReturn world id previous input = .returned after input.asValue ∧
    returnOwned world id previous input = some (after, input.asValue) ∧
    after.control.current = previous ∧ after.control.active = rest ∧
    after.control.invocations.size = world.control.invocations.size ∧
    after.control.invocations.cell id = some { invocation with active := false } ∧
    (∀ other, other ≠ id →
      after.control.invocations.cell other = world.control.invocations.cell other) ∧
    ¬ OwnerActive after.control (.invocation id) ∧
    after.environments = world.environments ∧ after.cells = world.cells ∧
    after.receiving = world.receiving ∧ after.rest = world.rest ∧
    input.asValue.value = input.value ∧ input.asValue.view = input.view ∧
    input.asValue.dispatch = input.dispatch ∧ input.asValue.interface = .value := by
  have native := leave_owned_construct world.control id previous rest invocation
    current stack found live
  have action : returnOwned world id previous input =
      some (exited world id previous rest invocation, input.asValue) := by
    simp only [returnOwned, leave_success current stack found live, exited,
      Option.pure_def]
    rfl
  refine ⟨?_, action, rfl, rfl, rfl, deactivate_current _ _ _, ?_,
    (OriginalSourceExecutionWorldR337.return_owned_fields action).2.2.2.2.2.2.2,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [receiverReturn, native, exited, Received.asValue]
  · intro other different
    exact deactivate_other _ _ _ _ different

/-- A snapshot supplies raw vectors and ownership, never a successful desired
world. All other projected stores stay arbitrary and are preserved by the branch. -/
theorem receiver_return_from_vectors (world : World K D V ViewData Site Rest)
    (native : NativeControl Site) (id : Nat) (previous : Owner) (input : Received V)
    (rest : List Nat) (invocation : Invocation Site)
    (current : native.current = .invocation id)
    (stack : native.activeReceivers.reverse = id :: rest)
    (found : native.invocations[id]? = some invocation)
    (live : invocation.active = true) :
    let before := { world with control := native.project }
    let after := exited before id previous rest invocation
    receiverReturn before id previous input = .returned after input.asValue ∧
    returnOwned before id previous input = some (after, input.asValue) ∧
    after.control.active = rest ∧ after.control.current = previous ∧
    after.control.invocations =
      vectorStore (native.invocations.set id { invocation with active := false }) := by
  dsimp only
  have action := receiver_return_construct { world with control := native.project }
    id previous input rest invocation current stack found live
  exact ⟨action.1, action.2.1, rfl, rfl, (vector_retirement _ _ _ found).symm⟩

/-- Replace only current.world. No semantic coherence or compatibility follows
from retaining the other original logical fields syntactically. -/
def exitEvent {b : Sorts} {D V ViewData Site Rest Body View : Type}
    (before : Event (NS b D V ViewData Site Rest Body View))
    (id : Nat) (previous : Owner) (rest : List Nat) (invocation : Invocation Site) :
    Event (NS b D V ViewData Site Rest Body View) :=
  { before with current := { before.current with world := exited before.current.world id previous rest invocation } }

/-- Same existing joint assignment interprets the exact returned native value
and root. This data readout supplies no membership or provider law. -/
def nativeResult {b : Sorts} {D V ViewData Site Rest Body View : Type}
    (before : Event (NS b D V ViewData Site Rest Body View))
    (descriptor : b.Descriptor) (input : Received V)
    (id : Nat) (previous : Owner) (rest : List Nat) (invocation : Invocation Site) :
    ValueRow (NS b D V ViewData Site Rest Body View) :=
  ⟨descriptor, before.eta.views.value input.asValue.value,
    before.eta.views.root input.asValue.value, exitEvent before id previous rest invocation⟩

theorem native_result_fields {b : Sorts} {D V ViewData Site Rest Body View : Type}
    (before : Event (NS b D V ViewData Site Rest Body View))
    (descriptor : b.Descriptor) (input : Received V)
    (id : Nat) (previous : Owner) (rest : List Nat) (invocation : Invocation Site) :
    let result := nativeResult before descriptor input id previous rest invocation
    result.descriptor = descriptor ∧ result.value = before.eta.views.value input.value ∧
    result.root = before.eta.views.root input.value ∧
    result.event.current.world = exited before.current.world id previous rest invocation ∧
    result.event.eta = before.eta ∧ result.event.witness = before.witness ∧
    result.event.current.providers = before.current.providers ∧
    result.event.current.aliases = before.current.aliases ∧
    result.event.current.residual = before.current.residual :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem exit_event_differs {b : Sorts} {D V ViewData Site Rest Body View : Type}
    (before : Event (NS b D V ViewData Site Rest Body View))
    (id : Nat) (previous : Owner) (input : Received V)
    (rest : List Nat) (invocation : Invocation Site)
    (current : before.current.world.control.current = .invocation id)
    (stack : before.current.world.control.active = id :: rest)
    (found : before.current.world.control.invocations.cell id = some invocation)
    (live : invocation.active = true) :
    exitEvent before id previous rest invocation ≠ before := by
  have action := (receiver_return_construct before.current.world id previous input
    rest invocation current stack found live).2.1
  exact OriginalSourceExecutionWorldR337.successful_return_events_differ before
    (exitEvent before id previous rest invocation) id previous input input.asValue action

/-- Original pure-Return consumer at constructed post-exit Event. Event equality
is discharged; semantic coherence, guards, world/value/field obligations remain. -/
theorem post_exit_return_iff {b : Sorts} {D V ViewData Site Rest Body View : Type}
    (inputs : Inputs (NS b D V ViewData Site Rest Body View))
    (before : Event (NS b D V ViewData Site Rest Body View))
    (id : Nat) (previous : Owner) (rest : List Nat) (invocation : Invocation Site)
    (descriptor : b.Descriptor) (input : Received V)
    (observation : b.Observation) (interface : b.Interface)
    (form : inputs.traceForm ⟨interface, observation,
      exitEvent before id previous rest invocation⟩ =
      .pureReturn (nativeResult before descriptor input id previous rest invocation)) :
    let after := exitEvent before id previous rest invocation
    let trace : TraceRow (NS b D V ViewData Site Rest Body View) :=
      ⟨interface, observation, after⟩
    Meaning inputs (.trace trace) ↔
      inputs.eventCoherent after ∧ (inputs.observationGuards trace).Valid ∧
      Meaning inputs (.world after) ∧
      Meaning inputs (.value (nativeResult before descriptor input id previous rest invocation)) ∧
      (inputs.observationFields trace).Holds (Meaning inputs) := by
  dsimp only
  rw [return_observation_iff inputs _ _ form]
  simp only [nativeResult, true_and]

/-- Apply the unchanged function_return_result falsifier using input facts,
replacing the previously assumed successful native result equation. -/
theorem function_rejects_pre_exit {b : Sorts} {D V ViewData Site Rest Body View : Type}
    (inputs : Inputs (NS b D V ViewData Site Rest Body View))
    (row : ValueRow (NS b D V ViewData Site Rest Body View))
    (functionForm : inputs.valueForm row.descriptor = .function)
    (valid : Meaning inputs (.value row)) (provider : b.Provider)
    (actual : inputs.actual row.value row.root provider)
    (challenge : Challenge row) (admitted : CheckedDomain inputs challenge)
    (raw : RawObservation (NS b D V ViewData Site Rest Body View))
    (interface : b.Interface)
    (readout : inputs.checkedObservation challenge raw = checkedTrace raw interface)
    (descriptor : b.Descriptor)
    (id : Nat) (previous : Owner) (input : Received V)
    (rest : List Nat) (invocation : Invocation Site)
    (current : raw.event.current.world.control.current = .invocation id)
    (stack : raw.event.current.world.control.active = id :: rest)
    (found : raw.event.current.world.control.invocations.cell id = some invocation)
    (live : invocation.active = true)
    (form : inputs.traceForm (raw.atInterface interface) =
      .pureReturn (nativeResult raw.event descriptor input id previous rest invocation)) :
    ¬ inputs.execute provider challenge.input raw := by
  have action := (receiver_return_construct raw.event.current.world id previous input
    rest invocation current stack found live).2.1
  exact OriginalSourceExecutionWorldR337.function_rejects_pre_exit_execution inputs row
    functionForm valid provider actual challenge admitted raw interface readout _ form
    id previous input input.asValue action

end YulangClosure.OriginalReceiverReturnRefinementR338
