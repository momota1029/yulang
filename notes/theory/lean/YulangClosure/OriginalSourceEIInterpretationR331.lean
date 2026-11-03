import YulangClosure.OriginalSourceViewRegistrationR330
import YulangClosure.OriginalComputedCallInterpretationR311

/-!
R331 constructive partial EI-Intro: the original CalRet, argument and live
receiver obligations, applied to R311's selected callee phase. The inputs below
are original callee membership, same-return value checking, original primitive
guard leaves, and whole argument checking. No EI membership, EI clause, finished
child contribution, generated readback or target Checking is an input.

This is NOT the full EI interpreter. In particular, R311's Phase still lacks
an authenticated typed response telescope and its result branch does not bind
the preceding receiver trace. We do not register that incomplete Phase as the
meaning of R330's Code. Actual original primitive/source instances, complete
arm-local interpretation and licensed Call contribution remain open.
-/
namespace YulangClosure.OriginalSourceEIInterpretationR331

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking
open ComputedCallTypedFormationR310 OriginalComputedCallInterpretationR311

variable {s : Sorts} {View : Type}

/-- A single independent original guard derivation, retaining the actual
registered declaration and its precondition. This is not an EI body supplier. -/
structure PrimitiveInput (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (goal : PrimitiveGoal s) where
  leaf : PrimitiveLeaf inputs registry goal
  found : resolution goal = some leaf
  before : leaf.entry.before.Holds inputs registry.original

theorem primitive_input_sound (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (goal : PrimitiveGoal s)
    (original : PrimitiveInput inputs registry resolution goal) (Z : Family s) :
    (primitiveBody inputs registry resolution goal).Holds Z :=
  primitive_introduction inputs registry resolution goal original.leaf original.found original.before Z

/-- Source argument input at its OWN actual CalRet binder. The carrier is
whole: its Meaning contains all independent demands, Force, captures and
hereditary fields, rather than only a returned value. -/
structure ArgumentInput (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (request : Request)
    (declarations : PrimitiveDeclarations)
    (returned : BoundReturn s request.original.position) (carrier : CarrierRow s) where
  reify : PrimitiveInput inputs registry resolution
    (primitiveGoal request declarations .reify (returnedOperands returned ++ [.carrier carrier]))
  checked : Meaning inputs (.carrier carrier)

/-- Genuine separately typed operands for the post-CalRet construction.
The argument domain is the ORIGINAL reify incidence, not carrier membership
or provider acceptance. No source result/check endpoint is modified. -/
structure ReturnInputs (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (leaves : Positive s → Positive s → Prop)
    (request : Request) (declarations : PrimitiveDeclarations)
    (callee : s.Interface) (function : s.Descriptor)
    (returned : BoundReturn s request.original.position) where
  calleeMember : Meaning inputs (.trace (returned.callee.atInterface callee))
  form : inputs.traceForm (returned.callee.atInterface callee) = .pureReturn returned.value
  checked : Proof inputs registry leaves (.field (.value returned.value))
    (.field (.value (returned.value.withDescriptor function)))
  functionSort : inputs.valueForm function = .function
  actual : inputs.actual returned.value.value returned.value.root returned.provider
  calRet : PrimitiveInput inputs registry resolution
    (primitiveGoal request declarations .calRet (returnedOperands returned))
  argument : ∀ carrier : CarrierRow s,
    registry.original (primitiveGoal request declarations .reify
      (returnedOperands returned ++ [.carrier carrier])).signature →
    ArgumentInput inputs registry resolution request declarations returned carrier

section Construction
variable (inputs : Inputs s) (registry : GuardRegistry inputs)
  (resolution : Resolution inputs registry) (leaves : Positive s → Positive s → Prop)
  (children : ∀ A B, leaves A B → A.Holds (Meaning inputs) → B.Holds (Meaning inputs))
  (request : Request) (declarations : PrimitiveDeclarations)
  (callee : s.Interface) (function : s.Descriptor)
  (returned : BoundReturn s request.original.position)
  (original : ReturnInputs inputs registry resolution leaves request declarations callee function returned)

include original children

/-- Extract the SAME returned value and apply only its independently checked
Function conversion. This proof is reused at all later live events. -/
theorem checked_return_from_operands :
    Meaning inputs (.value (returned.value.withDescriptor function)) := by
  have trace := (meaning_iff inputs _).mp original.calleeMember
  change PhiT inputs (Meaning inputs) (returned.callee.atInterface callee) at trace
  have result := trace.2.2.2.1
  rw [original.form] at result
  exact Proof.sound inputs registry children original.checked result.2

/-- Construct R311's actual tailBody. Its former whole-tail premise is
replaced by original callee/return, guard and whole-argument premises above. -/
theorem tail_from_original_operands :
    (tailBody inputs registry resolution request declarations callee function returned).Holds
      (Meaning inputs) := by
  have calRet := calRet_introduction inputs registry leaves children callee function returned
    original.calleeMember original.form original.checked original.functionSort original.actual
  refine ⟨calRet, primitive_input_sound inputs registry resolution _ original.calRet _, ?_, ?_⟩
  · intro carrier
    let argument := original.argument carrier.val carrier.property
    exact argument_introduction inputs registry resolution request declarations returned carrier.val
      argument.reify.leaf argument.reify.found argument.reify.before argument.checked
  · exact calRet.2.2.2.2

/-- The independent live-event quantifier is not replaced by the CalRet world.
Every checked challenge and actual execution remains under that event. -/
theorem all_live_receiver_developments :
    ∀ current : Event s, inputs.compatible returned.value.event current →
      (receiverDevelopments inputs returned function current).Holds (Meaning inputs) := by
  intro current compatible
  exact receiver_developments_from_function inputs returned function current compatible
    (checked_return_from_operands inputs registry resolution leaves children request declarations
      callee function returned original) original.functionSort original.actual

omit children in
/-- Original carrier input supplies the designated execution at EACH demand.
No designated Force is dropped, including when the formal is unused. -/
theorem argument_designated_force (carrier : CarrierRow s)
    (formed : registry.original (primitiveGoal request declarations .reify
      (returnedOperands returned ++ [.carrier carrier])).signature)
    (demand : Event s) (raw : RawObservation s)
    (demanded : inputs.demand carrier demand)
    (forced : inputs.force carrier.input demand raw) :
    inputs.compatible carrier.event demand ∧ inputs.forceIncidence carrier demand raw ∧
      (clause inputs (.trace (raw.atInterface carrier.interface))).Holds (Meaning inputs) :=
  designated_force_from_carrier inputs carrier demand raw
    (original.argument carrier formed).checked demanded forced

/-- Preserve the actual Return form, provider and every hereditary later
value field. This result does not identify receiver Return with CalRet. -/
theorem same_return_live_function (later : Event s)
    (compatible : inputs.compatible returned.value.event later) :
    Meaning inputs (.value ((returned.value.withDescriptor function).atEvent later)) ∧
    inputs.actual returned.value.value returned.value.root returned.provider := by
  have member := checked_return_from_operands inputs registry resolution leaves children request declarations
    callee function returned original
  exact ⟨((meaning_iff inputs _).mp member).2 later compatible, original.actual⟩
end Construction

/-- Step induction retains the exact earlier raw history in every later
primitive signature. It does not infer the independent primitive leaves from
a protocol label or a successful native sample. -/
def StepsInput (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (request : Request)
    (declarations : PrimitiveDeclarations) (fixed : List (Operand s)) :
    List (Use × RawObservation s) → Type
  | [] => Unit
  | (use, raw) :: rest =>
      PrimitiveInput inputs registry resolution
        (primitiveGoal request declarations use (fixed ++ [.observation raw, .event raw.event])) ×
      StepsInput inputs registry resolution request declarations
        (fixed ++ [.observation raw, .event raw.event]) rest

theorem steps_from_original_primitives (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (request : Request)
    (declarations : PrimitiveDeclarations) (fixed : List (Operand s))
    (steps : List (Use × RawObservation s))
    (original : StepsInput inputs registry resolution request declarations fixed steps) (Z : Family s) :
    (stepsBody inputs registry resolution request declarations fixed steps).Holds Z := by
  induction steps generalizing fixed with
  | nil => trivial
  | cons step rest ih =>
    exact ⟨primitive_input_sound inputs registry resolution _ original.1 Z,
      ih _ original.2⟩

/-- The original full callee proof supplies its own prefix clause. Future
CalRet values are bound by the ORIGINAL incidence domain; none is picked now.
Each tail is CONSTRUCTED from separately typed original operands. -/
theorem callee_phase_from_original_operands
    (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (leaves : Positive s → Positive s → Prop)
    (children : ∀ A B, leaves A B → A.Holds (Meaning inputs) → B.Holds (Meaning inputs))
    (state : Decoded s View) (request : Request) (declarations : PrimitiveDeclarations)
    (prior : RawObservation s)
    (calleeMember : Meaning inputs (.trace (prior.atInterface
      (state.interfaces ⟨request.original.calleeSite, .synthesis⟩))))
    (prefixInput : PrimitiveInput inputs registry resolution
      (primitiveGoal request declarations .calleePrefix [.observation prior, .event prior.event]))
    (returns : ∀ returned : BoundReturn s request.original.position,
      registry.original (primitiveGoal request declarations .calleeResume
        ([.observation prior, .event prior.event] ++ returnedOperands returned)).signature →
      ReturnInputs inputs registry resolution leaves request declarations
        (state.interfaces ⟨request.original.calleeSite, .synthesis⟩)
        (state.assignment.descriptor ⟨request.original.site, .descriptor⟩) returned) :
    (phaseBody inputs registry resolution state request declarations (.callee prior)).Holds
      (Meaning inputs) := by
  refine ⟨(meaning_clause inputs _).mp calleeMember,
    primitive_input_sound inputs registry resolution _ prefixInput _, ?_⟩
  intro returned
  exact tail_from_original_operands inputs registry resolution leaves children request declarations
    _ _ returned.val (returns returned.val returned.property)

/-- Apply the newly constructed tail at R330's ACTUAL selected source
position. This eliminates a finished phaseBody input at the R311 consumer;
it does NOT assert EI-All registration or source child licensing. -/
theorem selected_source_phase
    (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (leaves : Positive s → Positive s → Prop)
    (children : ∀ A B, leaves A B → A.Holds (Meaning inputs) → B.Holds (Meaning inputs))
    (state : Decoded s View) (origin : Declaration) (declarations : PrimitiveDeclarations)
    (prior : RawObservation s)
    (calleeMember : Meaning inputs (.trace (prior.atInterface
      (state.interfaces ⟨(OriginalSourceViewRegistrationR330.request origin).original.calleeSite, .synthesis⟩))))
    (prefixInput : PrimitiveInput inputs registry resolution
      (primitiveGoal (OriginalSourceViewRegistrationR330.request origin) declarations .calleePrefix
        [.observation prior, .event prior.event]))
    (returns : ∀ returned : BoundReturn s (OriginalSourceViewRegistrationR330.request origin).original.position,
      registry.original (primitiveGoal (OriginalSourceViewRegistrationR330.request origin) declarations .calleeResume
        ([.observation prior, .event prior.event] ++ returnedOperands returned)).signature →
      ReturnInputs inputs registry resolution leaves (OriginalSourceViewRegistrationR330.request origin) declarations
        (state.interfaces ⟨(OriginalSourceViewRegistrationR330.request origin).original.calleeSite, .synthesis⟩)
        (state.assignment.descriptor ⟨(OriginalSourceViewRegistrationR330.request origin).original.site, .descriptor⟩) returned) :
    (phaseBody inputs registry resolution state (OriginalSourceViewRegistrationR330.request origin)
      declarations (.callee prior)).Holds (Meaning inputs) ∧
    (OriginalSourceViewRegistrationR330.request origin).original.position =
      (OriginalSourceViewRegistrationR330.owner origin).position.under
        (.existsE (OriginalSourceViewRegistrationR330.owner origin).binder) :=
  ⟨callee_phase_from_original_operands inputs registry resolution leaves children state _ declarations
    prior calleeMember prefixInput returns,
    OriginalSourceViewRegistrationR330.original_description_scope origin⟩

/-- The first missing selected source leaf is necessary even for the weakest
callee prefix. Static R330 Definition/formation cannot replace this premise. -/
theorem selected_prefix_requires_original_declaration
    (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (state : Decoded s View)
    (origin : Declaration) (declarations : PrimitiveDeclarations) (prior : RawObservation s)
    (valid : (phaseBody inputs registry resolution state
      (OriginalSourceViewRegistrationR330.request origin) declarations (.callee prior)).Holds (Meaning inputs)) :
    ∃ leaf, resolution (primitiveGoal (OriginalSourceViewRegistrationR330.request origin)
      declarations .calleePrefix [.observation prior, .event prior.event]) = some leaf := by
  cases found : resolution (primitiveGoal (OriginalSourceViewRegistrationR330.request origin)
    declarations .calleePrefix [.observation prior, .event prior.event]) with
  | none => exact False.elim (missing_callee_prefix_rejected inputs registry resolution state _ declarations prior found valid)
  | some leaf => exact ⟨leaf, rfl⟩

/-- Exact limitation of R311's primitive leaf interface: the leaf authenticates
its registered SIGNATURE but not its source Key or use. A real resolver must
separately authenticate those. This constructor is a falsifier of deriving
source-key authentication merely from PrimitiveLeaf; it is not a source law. -/
def change_unchecked_reference (inputs : Inputs s) (registry : GuardRegistry inputs)
    (goal : PrimitiveGoal s) (leaf : PrimitiveLeaf inputs registry goal)
    (reference : Key) (use : Use) :
    PrimitiveLeaf inputs registry { goal with reference := reference, use := use } :=
  ⟨leaf.identifier, leaf.entry, leaf.found, leaf.signature, leaf.conclusion⟩

theorem unchecked_reference_preserves_leaf (inputs : Inputs s) (registry : GuardRegistry inputs)
    (goal : PrimitiveGoal s) (leaf : PrimitiveLeaf inputs registry goal)
    (reference : Key) (use : Use) :
    (change_unchecked_reference inputs registry goal leaf reference use).identifier = leaf.identifier ∧
    (change_unchecked_reference inputs registry goal leaf reference use).entry = leaf.entry := ⟨rfl, rfl⟩

end YulangClosure.OriginalSourceEIInterpretationR331
