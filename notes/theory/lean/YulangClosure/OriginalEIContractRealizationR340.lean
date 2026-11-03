import YulangClosure.OriginalSourceEIConstructionR339

/-!
R340: the primitive-evidence part of an original same-source restriction.

IF §§3.1–3.3 permits original atomic primitive laws and lawful declaration
actions as independent inputs. They do not follow from a source occurrence.
This file constructs the Guard/PrimitiveLeaf/PrimitiveInput action from those
components and applies it to the actual R339 callee-request consumer.

LIMIT: no authentic nonidentity instance of the lookup/action inputs is
constructed here. Original response-domain equivalence, continuation-to-callee
typing, and source Generated/R306/R159 remain open. In particular this is not
another purported original response schema or a completed EI interpretation.
-/
namespace YulangClosure.OriginalEIContractRealizationR340

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking ComputedCallTypedFormationR310
open OriginalComputedCallInterpretationR311 OriginalSourceEIInterpretationR331
open OriginalSourceEIConstructionR339

variable {s : Sorts} {View : Type}

/-- A same-source semantic action keeps declaration, endpoint, owner, source
context and full reference Key fixed. All dynamic operands have explicit maps.
The action is DATA; lawfulness is separately checked at atomic predicates. -/
structure Action (s : Sorts) (View : Type) where
  fields : FieldMap s View
  descriptor : s.Descriptor → s.Descriptor
  interface : s.Interface → s.Interface
  value : s.Value → s.Value
  root : s.Root → s.Root
  provider : s.Provider → s.Provider
  carrier : s.Carrier → s.Carrier
  invocation : CallInput s → CallInput s

def Action.valueRow (a : Action s View) (row : ValueRow s) : ValueRow s :=
  ⟨a.descriptor row.descriptor, a.value row.value, a.root row.root, a.fields.event row.event⟩

def Action.traceRow (a : Action s View) (row : TraceRow s) : TraceRow s :=
  ⟨a.interface row.interface, a.fields.observation row.observation, a.fields.event row.event⟩

def Action.carrierRow (a : Action s View) (row : CarrierRow s) : CarrierRow s :=
  ⟨a.interface row.interface, a.carrier row.carrier, a.root row.root, a.fields.event row.event⟩

def Action.operand (a : Action s View) : Operand s → Operand s
  | .descriptor x => .descriptor (a.descriptor x)
  | .interface x => .interface (a.interface x)
  | .value v r => .value (a.value v) (a.root r)
  | .provider x => .provider (a.provider x)
  | .event x => .event (a.fields.event x)
  | .carrier x => .carrier (a.carrierRow x)
  | .observation x => .observation (a.fields.raw x)
  | .invocation x => .invocation (a.invocation x)
  | .endpoint x => .endpoint x
  | .declaration x => .declaration x

def Action.signature (a : Action s View) (sig : Signature s) : Signature s :=
  {sig with operands := sig.operands.map a.operand}

/-- Recursive syntax action, not a supplied implication on arbitrary guards. -/
def Action.guard (a : Action s View) : Guard s → Guard s
  | .truth => .truth
  | .falsity => .falsity
  | .both first second => .both (a.guard first) (a.guard second)
  | .ground row => .ground (a.valueRow row)
  | .fixedExternal row => .fixedExternal (a.valueRow row)
  | .structural row => .structural (a.valueRow row)
  | .coherent event => .coherent (a.fields.event event)
  | .function row provider => .function (a.valueRow row) (a.provider provider)
  | .observation row => .observation (a.traceRow row)
  | .carrier row => .carrier (a.carrierRow row)
  | .world event => .world (a.fields.event event)
  | .equal first second => .equal (a.operand first) (a.operand second)
  | .registered sig => .registered (a.signature sig)

/-- Precisely the independent primitive atom actions. No Meaning, EI clause,
completed source judgment or contribution is a field. The registered case is
the original primitive relation's lawful action, not its assumed truth. -/
structure AtomicLaws (inputs : Inputs s) (registry : GuardRegistry inputs)
    (a : Action s View) : Prop where
  ground : ∀ row, inputs.ground row → inputs.ground (a.valueRow row)
  fixedExternal : ∀ row, inputs.fixedExternal row → inputs.fixedExternal (a.valueRow row)
  structural : ∀ row, inputs.structuralGuard row → inputs.structuralGuard (a.valueRow row)
  coherent : ∀ event, inputs.eventCoherent event → inputs.eventCoherent (a.fields.event event)
  function : ∀ row provider, (inputs.functionGuards row provider).Valid →
    (inputs.functionGuards (a.valueRow row) (a.provider provider)).Valid
  observation : ∀ row, (inputs.observationGuards row).Valid →
    (inputs.observationGuards (a.traceRow row)).Valid
  carrier : ∀ row, (inputs.carrierGuards row).Valid →
    (inputs.carrierGuards (a.carrierRow row)).Valid
  world : ∀ event, (inputs.worldGuards event).Valid →
    (inputs.worldGuards (a.fields.event event)).Valid
  registered : ∀ sig, registry.original sig → registry.original (a.signature sig)

theorem guard_action (inputs : Inputs s) (registry : GuardRegistry inputs)
    (a : Action s View) (laws : AtomicLaws inputs registry a)
    (guard : Guard s) (valid : guard.Holds inputs registry.original) :
    (a.guard guard).Holds inputs registry.original := by
  induction guard with
  | truth => exact valid
  | falsity => exact valid
  | both first second ih₁ ih₂ => exact ⟨ih₁ valid.1, ih₂ valid.2⟩
  | ground row => exact laws.ground row valid
  | fixedExternal row => exact laws.fixedExternal row valid
  | structural row => exact laws.structural row valid
  | coherent event => exact laws.coherent event valid
  | function row provider => exact laws.function row provider valid
  | observation row => exact laws.observation row valid
  | carrier row => exact laws.carrier row valid
  | world event => exact laws.world event valid
  | equal first second => exact congrArg a.operand valid
  | registered sig => exact laws.registered sig valid

def Action.declaration (a : Action s View) (entry : GuardDeclaration s) : GuardDeclaration s :=
  ⟨a.signature entry.signature, a.guard entry.before, a.guard entry.after⟩

/-- This is a declaration-environment equation required of the ORIGINAL
lawful action. It is not present in GuardRegistry and is not manufactured by
this module. No precondition, membership or semantic truth is assumed here. -/
structure LookupAction (inputs : Inputs s) (registry : GuardRegistry inputs)
    (a : Action s View) where
  index : Nat → Nat
  found : ∀ identifier entry, registry.declaration identifier = some entry →
    registry.declaration (index identifier) = some (a.declaration entry)

def Action.goal (a : Action s View) (goal : PrimitiveGoal s) : PrimitiveGoal s :=
  {goal with signature := a.signature goal.signature}

/-- Source reference/use authentication is preserved, never inferred from
matching signatures. In particular callee and incidence keys stay distinct. -/
theorem goal_keeps_source (a : Action s View) (goal : PrimitiveGoal s) :
    (a.goal goal).reference = goal.reference ∧ (a.goal goal).use = goal.use := ⟨rfl, rfl⟩

def actLeaf (inputs : Inputs s) (registry : GuardRegistry inputs)
    (a : Action s View) (lookup : LookupAction inputs registry a)
    {goal : PrimitiveGoal s} (leaf : PrimitiveLeaf inputs registry goal) :
    PrimitiveLeaf inputs registry (a.goal goal) where
  identifier := lookup.index leaf.identifier
  entry := a.declaration leaf.entry
  found := lookup.found leaf.identifier leaf.entry leaf.found
  signature := congrArg a.signature leaf.signature
  conclusion := by
    change a.guard leaf.entry.after = Guard.registered (a.signature goal.signature)
    rw [leaf.conclusion]
    rfl

/-- Source resolver naturality is the SECOND structural equation required of
an original action. It cannot be deduced from declaration lookup alone: the
resolver also sees the original Key/use. This field asserts no guard truth. -/
def ResolutionCommutes (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (a : Action s View)
    (lookup : LookupAction inputs registry a) : Prop :=
  ∀ goal leaf, resolution goal = some leaf →
    resolution (a.goal goal) = some (actLeaf inputs registry a lookup leaf)

/-- The target precondition is DERIVED by induction on the old guard. No
changed-world PrimitiveInput or guard precondition is supplied. -/
def actInput (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (a : Action s View)
    (laws : AtomicLaws inputs registry a) (lookup : LookupAction inputs registry a)
    (commutes : ResolutionCommutes inputs registry resolution a lookup)
    {goal : PrimitiveGoal s} (original : PrimitiveInput inputs registry resolution goal) :
    PrimitiveInput inputs registry resolution (a.goal goal) where
  leaf := actLeaf inputs registry a lookup original.leaf
  found := commutes goal original.leaf original.found
  before := guard_action inputs registry a laws original.leaf.entry.before original.before

theorem primitive_action (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (a : Action s View)
    (laws : AtomicLaws inputs registry a) (lookup : LookupAction inputs registry a)
    (commutes : ResolutionCommutes inputs registry resolution a lookup)
    {goal : PrimitiveGoal s} (original : PrimitiveInput inputs registry resolution goal)
    (Z : Family s) : (primitiveBody inputs registry resolution (a.goal goal)).Holds Z :=
  primitive_input_sound inputs registry resolution _
    (actInput inputs registry resolution a laws lookup commutes original) Z

/-- Exact application to the existing request constructor. The signature's
source prefix is retained, so there is no cast from the callee Key to the
Call incidence Key. -/
theorem goal_operands_action (a : Action s View) (request : Request)
    (declarations : PrimitiveDeclarations) (use : Use) (operands : List (Operand s)) :
    a.goal (primitiveGoal request declarations use operands) =
      primitiveGoal request declarations use (operands.map a.operand) := by
  simp only [Action.goal, Action.signature, primitiveGoal, goal, List.map_cons, Action.operand]

/-- R339's changed request/resume primitive evidence is now constructed from
the old evidence and atomic actions. The changed callee evidence is STILL an
explicit premise: no original continuation typing theorem is available in
these interfaces, and this theorem does not conceal that missing edge. All
original response records remain universally quantified, with their own raw
development and current world; no single response or Return is selected. -/
theorem restricted_response_from_primitive_actions
    (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (leaves : Positive s → Positive s → Prop)
    (children : ∀ A B, leaves A B → A.Holds (Meaning inputs) → B.Holds (Meaning inputs))
    (state : Decoded s View) (request : Request) (declarations : PrimitiveDeclarations)
    (schema : ResponseSchema s View) (head : RequestHead s View)
    (a : Action s View) (laws : AtomicLaws inputs registry a)
    (lookup : LookupAction inputs registry a)
    (commutes : ResolutionCommutes inputs registry resolution a lookup)
    (requested : PrimitiveInput inputs registry resolution
      (primitiveGoal request declarations .calleeRequest
        [.observation head.prior, .event head.prior.event]))
    (resume : ∀ answer : ResponseAt inputs schema head,
      PrimitiveInput inputs registry resolution
        (primitiveGoal request declarations .calleeResume
          [.observation head.prior, .event head.prior.event,
           .observation answer.raw, .event answer.raw.event]))
    (prior : CalleeInputs inputs registry resolution leaves state request declarations
      (a.fields.raw head.prior))
    (callee : ∀ answer : ResponseAt inputs schema head,
      CalleeInputs inputs registry resolution leaves state request declarations (a.fields.raw answer.raw)) :
    ∀ answer : ResponseAt inputs schema head,
      (phaseBody inputs registry resolution state request declarations
        (.calleeRequest (a.fields.raw head.prior) (a.fields.raw answer.raw))).Holds (Meaning inputs) := by
  intro answer
  have requested' := actInput inputs registry resolution a laws lookup commutes requested
  have resumed' := actInput inputs registry resolution a laws lookup commutes (resume answer)
  rw [goal_operands_action] at requested' resumed'
  exact ⟨callee_from_components inputs registry resolution leaves children state request declarations
      _ prior,
    primitive_input_sound inputs registry resolution _ requested' _,
    primitive_input_sound inputs registry resolution _ resumed' _,
    callee_from_components inputs registry resolution leaves children state request declarations
      _ (callee answer)⟩

/-- Whole-record application, retaining the exact shared witness, receipt,
request operation, continuation and unexecuted suffix. Coverage of all target
responses is not claimed: the action theorem concerns every original response
and its lawful image, and original-domain authentication remains independent. -/
theorem restricted_record_from_primitive_actions
    (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (leaves : Positive s → Positive s → Prop)
    (children : ∀ A B, leaves A B → A.Holds (Meaning inputs) → B.Holds (Meaning inputs))
    (state : Decoded s View) (request : Request) (declarations : PrimitiveDeclarations)
    (schema : ResponseSchema s View) (head : RequestHead s View)
    (a : Action s View) (laws : AtomicLaws inputs registry a)
    (lookup : LookupAction inputs registry a)
    (commutes : ResolutionCommutes inputs registry resolution a lookup)
    (lawful : LawfulResponseMap inputs schema a.fields)
    (requested : PrimitiveInput inputs registry resolution
      (primitiveGoal request declarations .calleeRequest
        [.observation head.prior, .event head.prior.event]))
    (resume : ∀ answer : ResponseAt inputs schema head,
      PrimitiveInput inputs registry resolution
        (primitiveGoal request declarations .calleeResume
          [.observation head.prior, .event head.prior.event,
           .observation answer.raw, .event answer.raw.event]))
    (prior : CalleeInputs inputs registry resolution leaves state request declarations
      (a.fields.raw head.prior))
    (callee : ∀ answer : ResponseAt inputs schema head,
      CalleeInputs inputs registry resolution leaves state request declarations (a.fields.raw answer.raw))
    (answer : ResponseAt inputs schema head) :
    let changed := restrictResponse a.fields lawful answer
    changed.record = a.fields.record answer.record ∧
      (phaseBody inputs registry resolution state request declarations
        (.calleeRequest (a.fields.raw head.prior) changed.raw)).Holds (Meaning inputs) := by
  exact ⟨response_restriction_natural a.fields lawful answer,
    restricted_response_from_primitive_actions inputs registry resolution leaves children state request
      declarations schema head a laws lookup commutes requested resume prior callee answer⟩

end YulangClosure.OriginalEIContractRealizationR340
