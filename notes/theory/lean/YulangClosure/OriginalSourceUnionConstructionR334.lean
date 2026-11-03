import YulangClosure.OriginalSourceGoalKernelTransportR333

/-!
R334: the exact source-owned scoped-arm resolver boundary.

EI-All §4 requires the original scoped arm family and independent laws. R330
registers the generated result expression, but its registry is not a resolver
for the references occurring inside that expression. These theorems compute
that distinction at the actual selected R315 Call and apply it to R333's
original parent witness. No source admission, empty arm list, semantic
interpretation, target Checking or licensed child is manufactured.

The two concrete references below are a falsifier of endpoint-only reference
authentication in the existing R310 grammar. They are NOT claimed to be actual
emitted whole-Call arms. The source-qualified result is the exact lookup failure
for ANY original arm reference, if present in the selected definition.
-/
namespace YulangClosure.OriginalSourceUnionConstructionR334

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment ComputedCallTypedFormationR310
open OriginalSourceViewRegistrationR330 OriginalSourcePrefixBridgeR332
open OriginalInterfacePreservationR328 OriginalSourceEnvironmentTransportR331

variable {s : Sorts} {View : Type}

/-- A constructor discriminator only; no semantic classification is added. -/
def completeResultKey (key : Key) : Bool :=
  match key with
  | ⟨_, .computation, reference⟩ => match reference.slot with
    | .completeResult => true
    | _ => false
  | _ => false

theorem original_arm_key_ne_result (origin : Declaration)
    (scope : List LocalBinder) (position : Position) (tag : Nat) (endpoint : Endpoint) :
    (Ref.mk position (.arm tag endpoint) : Ref scope .computation).key ≠
      (request origin).generatedResult.key := by
  intro equal
  have impossible := congrArg completeResultKey equal
  change false = true at impossible
  cases impossible

/-- Exact failed lookup, including arbitrary locations, rather than assuming
that the stored generated result is a resolver for all its operand references. -/
theorem unregistered_key_read_none
    {origin : Declaration} {declared : Key → Prop}
    (definition : Definition origin declared) (location : Occurrence) (key : Key)
    (different : key ≠ (request origin).generatedResult.key) :
    (register definition).read location key = none := by
  simp [register, Registry.read, Ne.symm different]

theorem original_arm_resolution_none
    {origin : Declaration} {declared : Key → Prop}
    (definition : Definition origin declared) (state : Decoded s View)
    (location : Occurrence) (scope : List LocalBinder) (position : Position)
    (tag : Nat) (endpoint : Endpoint) :
    resolve state (register definition) location
      (.inr (Ref.mk position (.arm tag endpoint) : Ref scope .computation).key) = none := by
  change Option.map (Sum.inr : Code → s.Interface ⊕ Code)
    ((register definition).read location _) = none
  rw [unregistered_key_read_none definition location _
    (original_arm_key_ne_result origin scope position tag endpoint)]
  rfl

/-- This is a concrete missing lookup, independent of whether the as-yet
unconstructed arm inventory is empty: the actual source callee operand exists.
The endpoint route succeeds, but the scoped-key route has no registered entry.
This is a boundary of the deliberately disjoint R330 API, not a claim that
its existing generated-definition resolver is buggy. -/
theorem actual_callee_resolution_boundary
    {origin : Declaration} {declared : Key → Prop}
    (definition : Definition origin declared) (state : Decoded s View) :
    resolve state (register definition) (owner origin)
        (.inr (request origin).operands.callee.key) = none ∧
    resolve state (register definition) (owner origin)
        (.inl ⟨(request origin).original.calleeSite, .synthesis⟩) =
      some (.inl (state.interfaces ⟨(request origin).original.calleeSite, .synthesis⟩)) := by
  refine ⟨?_, rfl⟩
  change Option.map (Sum.inr : Code → s.Interface ⊕ Code)
    ((register definition).read (owner origin) _) = none
  rw [unregistered_key_read_none definition (owner origin) _ ?_]
  · rfl
  · intro equal
    have impossible := congrArg completeResultKey equal
    change false = true at impossible
    cases impossible

/-- Quantifies over every supplied original arm and its complete local scope.
The slot equation is only a constructor discriminator, not a desired lookup,
source law, licence, or completeness assumption about definition.arms. -/
theorem selected_arm_resolution_none
    {origin : Declaration} {declared : Key → Prop}
    (definition : Definition origin declared) (state : Decoded s View)
    (index : Fin definition.arms.length) (tag : Nat) (endpoint : Endpoint)
    (slot : definition.arms[index].descriptor.slot = .arm tag endpoint) :
    resolve state (register definition) (owner origin)
      (.inr definition.arms[index].descriptor.key) = none := by
  apply congrArg (Option.map Sum.inr)
    (unregistered_key_read_none definition (owner origin) _ ?_)
  intro equal
  have impossible := congrArg completeResultKey equal
  change (match definition.arms[index].descriptor.slot with
    | .completeResult => true | _ => false) = true at impossible
  rw [slot] at impossible
  cases impossible

/-- Generated readback and missing original arm resolution occur together
in the SAME registry and decoded state. Old endpoint resolution still succeeds
but does not authenticate the omitted scoped Key. -/
theorem selected_result_and_arm_resolution
    {origin : Declaration} {declared : Key → Prop}
    (definition : Definition origin declared) (state : Decoded s View)
    (index : Fin definition.arms.length) (tag : Nat) (endpoint : Endpoint)
    (slot : definition.arms[index].descriptor.slot = .arm tag endpoint) :
    resolve state (register definition) (owner origin)
        (.inr (request origin).generatedResult.key) = some (.inr definition.code) ∧
    resolve state (register definition) (owner origin)
        (.inr definition.arms[index].descriptor.key) = none ∧
    resolve state (register definition) (owner origin) (.inl endpoint) =
        some (.inl (state.interfaces endpoint)) :=
  ⟨generated_resolution state definition,
    selected_arm_resolution_none definition state index tag endpoint slot, rfl⟩

/-- Exact selected source position, but different original local telescopes.
These are grammar witnesses, not an asserted arm inventory of the source. -/
def responseReference (origin : Declaration) (tag : Nat) (endpoint : Endpoint) : Key :=
  (Ref.mk (request origin).original.position (.arm tag endpoint) :
    Ref [.response (request origin).original.position] .computation).key

def futureReference (origin : Declaration) (tag : Nat) (endpoint : Endpoint) : Key :=
  (Ref.mk (request origin).original.position (.arm tag endpoint) :
    Ref [.future (request origin).original.position] .computation).key

/-- The tempting endpoint projection is explicitly partial: not every
computation reference is an original endpoint (completeResult has none). -/
def originalEndpoint (key : Key) : Option Endpoint :=
  match key with
  | ⟨_, .computation, reference⟩ => match reference.slot with
    | .originalComputation endpoint | .arm _ endpoint => some endpoint
    | _ => none
  | _ => none

theorem selected_scopes_do_not_collapse (origin : Declaration) (tag : Nat) (endpoint : Endpoint) :
    responseReference origin tag endpoint ≠ futureReference origin tag endpoint ∧
    originalEndpoint (responseReference origin tag endpoint) = some endpoint ∧
    originalEndpoint (futureReference origin tag endpoint) = some endpoint := by
  refine ⟨?_, rfl, rfl⟩
  intro equal
  have impossible := congrArg Key.scope equal
  change [LocalBinder.response _] = [LocalBinder.future _] at impossible
  cases impossible

/-- Apply the resolver boundary to the SAME actual original parent witnesses
used by the reviewed R333 construction. The original source input is retained;
no target source or Checking judgment is an added premise. This diagnoses the
remaining arm-resolution edge, and does not purport to close that edge. -/
theorem actual_parent_arm_resolution_boundary
    {origin : Declaration} {declared : Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (old : Kernel (Payload s View)) (initial reached : Environment (Payload s View))
    (parent : OriginalSourceGoalKernelTransportR333.ParentRegisteredAt
      definition base gen ro adm old initial reached) :
    OriginalSourceGoalKernelTransportR333.ParentTransportedAt
      definition base gen ro adm old initial reached ∧
    ∃ occurrence data state,
      decode ro reached = some state ∧
      adm.logical state ⟨1,.viewLogic,0⟩ .viewLogic data ∧
      RegisteredAt definition base gen ro adm initial reached data occurrence ∧
      resolve (state.logical data) (register definition) (owner origin)
        (.inr (request origin).operands.callee.key) = none ∧
      ∀ (index : Fin definition.arms.length) (tag : Nat) (endpoint : Endpoint),
        definition.arms[index].descriptor.slot = .arm tag endpoint →
        resolve (state.logical data) (register definition) (owner origin)
          (.inr (request origin).generatedResult.key) = some (.inr definition.code) ∧
        resolve (state.logical data) (register definition) (owner origin)
          (.inr definition.arms[index].descriptor.key) = none ∧
        resolve (state.logical data) (register definition) (owner origin) (.inl endpoint) =
          some (.inl ((state.logical data).interfaces endpoint)) := by
  refine ⟨OriginalSourceGoalKernelTransportR333.registered_parent_transport
    definition base gen ro adm old initial reached parent, ?_⟩
  obtain ⟨_, occurrence, data, state, found, admitted, _, _, _, _, registered, _, _⟩ := parent
  refine ⟨occurrence, data, state, found, admitted, registered,
    (actual_callee_resolution_boundary definition (state.logical data)).1, ?_⟩
  intro index tag endpoint slot
  exact selected_result_and_arm_resolution definition (state.logical data) index tag endpoint slot

end YulangClosure.OriginalSourceUnionConstructionR334
