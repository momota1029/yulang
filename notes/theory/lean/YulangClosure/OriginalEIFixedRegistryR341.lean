import YulangClosure.OriginalEIUsePullbackR341

/-!
R341 review repair on a separate lease: one fixed registry BEFORE all responses.

The earlier discriminator was pointwise: its registry depended on the chosen
answer. Here a fixed abstract development relation is selected before any
answer, and one registry/resolver validates the R339 request and ALL resume
primitive hypotheses. The response/current domain remains nonempty at every
event and every Nat response, with the complete shared record retained.

This is a model of the CURRENT ABSTRACT interfaces, not an authenticated
original primitive or a source-qualified counterexample. Its development
relation returns the fixed raw row (at its independently fixed event), not a
source continuation. In particular no law tying that row to the response's
current event is supplied by ResponseSchema. No source domain is narrowed or
original continuation semantics changed. It refutes the proposed unrestricted
abstract implication with the resumed-callee premise removed, not EI itself.
-/
namespace YulangClosure.OriginalEIFixedRegistryR341

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment OriginalSourceChecking
open ComputedCallTypedFormationR310 OriginalComputedCallInterpretationR311
open OriginalSourceEIInterpretationR331 OriginalSourceEIConstructionR339
open OriginalEIUsePullbackR341.AbstractContinuationObstruction

/-- Fixed before the entire response quantifier. Typing/admission permit every
current world and every Nat response. Development is independent of Meaning. -/
def fixedSchema (resumed : RawObservation sorts) : ResponseSchema sorts Unit :=
  {schema with Develops := fun _ _ _ raw => raw = resumed}

def fixedAnswer (resumed : RawObservation sorts) (head : RequestHead sorts Unit)
    (current : Event sorts) (response witness : Nat) (names : List (Name × Nat))
    (objects : List (Nat × Installed sorts)) : ResponseAt inputs (fixedSchema resumed) head :=
  responseAt inputs (fixedSchema resumed) head current trivial response trivial trivial
    ⟨(), (), (), (), (), ⟨current.history, current.current⟩⟩ rfl rfl
    witness names objects resumed rfl

theorem resumption_exact (resumed : RawObservation sorts) (head : RequestHead sorts Unit)
    (answer : ResponseAt inputs (fixedSchema resumed) head) : answer.raw = resumed :=
  answer.development

/-- No world/response/witness is selected to make the domain empty. Actual
operation, raw handle, saved continuation and suffix remain the head's fields. -/
theorem all_worlds_responses_inhabited (resumed : RawObservation sorts)
    (head : RequestHead sorts Unit) (current : Event sorts) (response witness : Nat)
    (names : List (Name × Nat)) (objects : List (Nat × Installed sorts)) :
    ∃ answer : ResponseAt inputs (fixedSchema resumed) head,
      answer.current = current ∧ answer.response = response ∧
      answer.retainedWitness = witness ∧ answer.retainedNames = names ∧
      answer.retainedObjects = objects ∧ answer.record.operation = head.operation ∧
      answer.record.rawHandle = head.rawHandle ∧
      answer.record.continuation = head.continuation ∧ answer.record.suffix = head.suffix :=
  ⟨fixedAnswer resumed head current response witness names objects,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- One fixed resolver for the full dependent telescope, including answers
with arbitrary receipt and shared fields. It does not vary with the answer. -/
noncomputable def allResumeInputs (request : Request) (head : RequestHead sorts Unit)
    (resumed : RawObservation sorts) :
    ∀ answer : ResponseAt inputs (fixedSchema resumed) head,
      PrimitiveInput inputs (registry request head.prior resumed)
        (resolution request head.prior resumed)
        (primitiveGoal request declarations .calleeResume
          [.observation head.prior, .event head.prior.event,
           .observation answer.raw, .event answer.raw.event]) := by
  intro answer
  rw [resumption_exact resumed head answer]
  exact testInput request head.prior resumed 2

/-- The independent recursive-leaf soundness premise is also supplied, not
silently omitted from the R339 consumer. This model has no recursive leaves. -/
theorem children_sound (A B : Positive sorts) (leaf : noLeaves A B)
    (_member : A.Holds (Meaning inputs)) : B.Holds (Meaning inputs) := leaf.elim

/-- Exact goal-level obstruction after choosing the schema, registry and
resolver BEFORE all response/current-world quantifiers. Prior CalleeInputs,
request PrimitiveInput and the entire universal resume supplier are built.
The universal R311 calleeRequest conclusion is false. -/
theorem fixed_registry_obstruction (state : Decoded sorts Unit) (request : Request)
    (head : RequestHead sorts Unit) (good : head.prior.observation = false)
    (developmentEvent : Event sorts) :
    let resumed : RawObservation sorts := ⟨true, developmentEvent⟩
    let R := registry request head.prior resumed
    let Q := resolution request head.prior resumed
    Nonempty (CalleeInputs inputs R Q noLeaves state request declarations head.prior) ∧
    Nonempty (PrimitiveInput inputs R Q (primitiveGoal request declarations .calleeRequest
      [.observation head.prior, .event head.prior.event])) ∧
    Nonempty (∀ answer : ResponseAt inputs (fixedSchema resumed) head,
      PrimitiveInput inputs R Q (primitiveGoal request declarations .calleeResume
        [.observation head.prior, .event head.prior.event,
         .observation answer.raw, .event answer.raw.event])) ∧
    (∀ answer : ResponseAt inputs (fixedSchema resumed) head,
      ¬ Nonempty (CalleeInputs inputs R Q noLeaves state request declarations answer.raw)) ∧
    ¬ (∀ answer : ResponseAt inputs (fixedSchema resumed) head,
      (phaseBody inputs R Q state request declarations
        (.calleeRequest head.prior answer.raw)).Holds (Meaning inputs)) := by
  dsimp only
  refine ⟨⟨priorCallee state request head.prior _ good⟩,
    ⟨testInput request head.prior _ 1⟩, ⟨allResumeInputs request head _⟩, ?_, ?_⟩
  · intro answer
    rw [resumption_exact _ head answer]
    rintro ⟨callee⟩
    exact no_resumed_trace developmentEvent _ callee.member
  · intro all
    let result := fixedAnswer ⟨true, developmentEvent⟩ head developmentEvent 0 0 [] []
    have phase := all result
    exact no_resumed_trace developmentEvent _ ((meaning_clause inputs _).mpr phase.2.2.2.1)

def testEvent (history : Nat) (configuration : Bool) : Event sorts :=
  ⟨⟨(), (), (), (), ()⟩, (), (), history, configuration, history, (), (), (), ()⟩

def testState : Decoded sorts Unit :=
  ⟨⟨testEvent 0 false, fun _ => (), fun _ => (), fun _ => (), fun _ => none⟩,
    (fun _ => ()), (fun _ => ()), (fun _ => ()), (fun _ => none), none, none, [], []⟩

def testHead : RequestHead sorts Unit :=
  ⟨⟨false, testEvent 0 false⟩,
    ⟨⟨(0 : Nat), false⟩, (), (), (10 : Nat), (20 : Nat), (), (), (), (), (), (), ()⟩,
    (11 : Nat), 7, (21 : Nat), (22 : Nat), (23 : Nat)⟩

/-- Closed inhabited instance, using an existing scoped request DATA record.
That authentic static Key does not authenticate this artificial primitive
semantics. The development and prior events are visibly different. -/
theorem closed_fixed_registry_counterexample :
    let request := OriginalSourceViewRegistrationR330.request 7
    let resumed : RawObservation sorts := ⟨true, testEvent 1 true⟩
    let R := registry request testHead.prior resumed
    let Q := resolution request testHead.prior resumed
    Nonempty (CalleeInputs inputs R Q noLeaves testState request declarations testHead.prior) ∧
    Nonempty (PrimitiveInput inputs R Q (primitiveGoal request declarations .calleeRequest
      [.observation testHead.prior, .event testHead.prior.event])) ∧
    Nonempty (∀ answer : ResponseAt inputs (fixedSchema resumed) testHead,
      PrimitiveInput inputs R Q (primitiveGoal request declarations .calleeResume
        [.observation testHead.prior, .event testHead.prior.event,
         .observation answer.raw, .event answer.raw.event])) ∧
    Nonempty (ResponseAt inputs (fixedSchema resumed) testHead) ∧
    ¬ (∀ answer : ResponseAt inputs (fixedSchema resumed) testHead,
      (phaseBody inputs R Q testState request declarations
        (.calleeRequest testHead.prior answer.raw)).Holds (Meaning inputs)) := by
  have result := fixed_registry_obstruction testState
    (OriginalSourceViewRegistrationR330.request 7) testHead rfl (testEvent 1 true)
  exact ⟨result.1, result.2.1, result.2.2.1,
    ⟨fixedAnswer _ testHead (testEvent 2 false) 17 29 [] []⟩, result.2.2.2.2⟩

end YulangClosure.OriginalEIFixedRegistryR341
