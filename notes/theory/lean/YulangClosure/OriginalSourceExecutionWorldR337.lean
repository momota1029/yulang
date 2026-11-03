import YulangClosure.OriginalParameterSemantics

/-!
R337: exact successful receiver-return projection and an original-semantic
falsifier for mixing its pre-exit observation with its post-exit result.

`SourceIdentityWorld.returnOwned` is the existing successful native projection
of `Frame::ReceiverReturn` / `leave_owner`. The existing nativeSorts make its
entire World a field of Configuration. No opaque original Configuration is
silently identified with that representation, and no Inputs instance is chosen.

These theorems do not construct execute, checkedObservation, traceForm, semantic
provider ownership, world validity or lawful whole actions. In particular,
they cannot promote the finite R335 execution to universal EI semantics.
-/
namespace YulangClosure.OriginalSourceExecutionWorldR337

open NativeClosureEnvironment SourceIdentityWorld OriginalSourceInterpretation
open OriginalParameterSemantics

/-- Extract the successful native control transition, without an assumed
post-state or stack equation. Failed native paths are outside this lemma. -/
theorem leave_shape {before after : Control Site} {id : Nat} {previous : Owner}
    (executed : before.leave id previous = some after) :
    before.current = .invocation id ∧
      ∃ rest invocation,
        before.active = id :: rest ∧
        before.invocations.cell id = some invocation ∧
        invocation.active = true ∧
        after = ⟨deactivate before.invocations id invocation, rest, previous⟩ := by
  unfold Control.leave at executed
  split at executed
  next current =>
    cases stack : before.active with
    | nil => simp [stack] at executed
    | cons top rest =>
      cases found : before.invocations.cell id with
      | none => simp [stack, found] at executed
      | some invocation =>
        simp only [stack, found] at executed
        split at executed
        next valid =>
          have same := Option.some.inj executed
          exact ⟨current, rest, invocation, by simp only [valid.1],
            rfl, valid.2, same.symm⟩
        next invalid => cases executed
  next wrong => cases executed

/-- Every represented native store is preserved by ReceiverReturn; control
changes and only the received interface is normalized. This holds at every
successful world, independent of value, response, provider and future history. -/
theorem return_owned_fields
    {before after : World K D V ViewData Site Rest} {id : Nat} {previous : Owner}
    {input output : Received V}
    (executed : returnOwned before id previous input = some (after, output)) :
    before.control.current = .invocation id ∧
    after.control.current = previous ∧
    output = input.asValue ∧
    after.environments = before.environments ∧
    after.cells = before.cells ∧
    after.receiving = before.receiving ∧
    after.rest = before.rest ∧
    ¬ OwnerActive after.control (.invocation id) := by
  unfold returnOwned at executed
  cases left : before.control.leave id previous with
  | none => simp [left] at executed
  | some control =>
    simp only [left, Option.pure_def] at executed
    cases executed
    obtain ⟨current, rest, invocation, _, _, _, shape⟩ := leave_shape left
    subst control
    refine ⟨current, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rintro ⟨other, found, active⟩
    have same := Option.some.inj ((deactivate_current _ _ _).symm.trans found)
    subst other
    cases active

/-- Even a malformed saved previous owner equal to the returning owner
cannot make the successful world unchanged: the registered owner is retired. -/
theorem return_owned_changes_world
    {before after : World K D V ViewData Site Rest} {id : Nat} {previous : Owner}
    {input output : Received V}
    (executed : returnOwned before id previous input = some (after, output)) :
    after ≠ before := by
  have retired := (return_owned_fields executed).2.2.2.2.2.2.2
  intro same
  subst after
  unfold returnOwned at executed
  cases left : before.control.leave id previous with
  | none => simp [left] at executed
  | some control =>
    obtain ⟨_, rest, invocation, _, found, live, _⟩ := leave_shape left
    exact retired ⟨invocation, found, live⟩

/-- The original Event distinction follows from its existing Configuration
projection, not from an injectivity axiom for opaque original event sorts.
All other logical fields of both Events remain arbitrary. -/
theorem successful_return_events_differ
    {b : Sorts} {D V ViewData Site Rest Body View : Type}
    (before after : Event (NS b D V ViewData Site Rest Body View))
    (id : Nat) (previous : Owner) (input output : Received V)
    (executed : returnOwned before.current.world id previous input =
      some (after.current.world, output)) : after ≠ before := by
  intro same
  exact return_owned_changes_world executed
    (congrArg (fun event : Event (NS b D V ViewData Site Rest Body View) =>
      event.current.world) same)

/-- Exact original trace consumer falsifier. A genuine post-exit result
cannot be interpreted at the pre-exit raw Event.
This leaves all independent Inputs, descriptors and logical fields quantified. -/
theorem pre_exit_trace_rejected
    {b : Sorts} {D V ViewData Site Rest Body View : Type}
    (inputs : Inputs (NS b D V ViewData Site Rest Body View))
    (before : Event (NS b D V ViewData Site Rest Body View))
    (result : ValueRow (NS b D V ViewData Site Rest Body View))
    (id : Nat) (previous : Owner) (input output : Received V)
    (executed : returnOwned before.current.world id previous input =
      some (result.event.current.world, output))
    (observation : b.Observation) (interface : b.Interface)
    (form : inputs.traceForm ⟨interface, observation, before⟩ = .pureReturn result) :
    ¬ Meaning inputs (.trace ⟨interface, observation, before⟩) := by
  intro valid
  have same := ((return_observation_iff inputs _ result form).mp valid).2.2.2.1.1
  exact successful_return_events_differ before result.event id previous input output
    executed same

/-- Apply the unchanged function_return_result parent consumer: after all
its genuine function/admission/readout premises, the mixed-event observation
cannot be a claimed actual execution. No desired execute equation is assumed. -/
theorem function_rejects_pre_exit_execution
    {b : Sorts} {D V ViewData Site Rest Body View : Type}
    (inputs : Inputs (NS b D V ViewData Site Rest Body View))
    (row : ValueRow (NS b D V ViewData Site Rest Body View))
    (functionForm : inputs.valueForm row.descriptor = .function)
    (valid : Meaning inputs (.value row)) (provider : b.Provider)
    (actual : inputs.actual row.value row.root provider)
    (challenge : Challenge row) (admitted : CheckedDomain inputs challenge)
    (raw : RawObservation (NS b D V ViewData Site Rest Body View))
    (interface : b.Interface)
    (readout : inputs.checkedObservation challenge raw = checkedTrace raw interface)
    (result : ValueRow (NS b D V ViewData Site Rest Body View))
    (form : inputs.traceForm (raw.atInterface interface) = .pureReturn result)
    (id : Nat) (previous : Owner) (input output : Received V)
    (nativeReturn : returnOwned raw.event.current.world id previous input =
      some (result.event.current.world, output)) :
    ¬ inputs.execute provider challenge.input raw := by
  intro executed
  have same := (function_return_result inputs row functionForm valid provider actual
    challenge admitted raw executed interface readout result form).1
  exact successful_return_events_differ raw.event result.event id previous input output
    nativeReturn same

end YulangClosure.OriginalSourceExecutionWorldR337
