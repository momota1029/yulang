import YulangClosure.ComputedCallTypedFormationR310

/-!
Partial selected EI §§3–4 clause construction over the UNCHANGED original Positive,
Inputs, Interface and Meaning. This is not registration of an EI interface.

The phase/IF/entry primitives must be resolved at their original declaration
IDs. Missing primitive resolution is interpreted as False, including inside
pending/future telescopes. The resolver returns only one original guard-law
leaf, never a Positive body, membership, Checking or a source judgment.
No instance of that resolver is manufactured here. In particular entry order
and IF maps are requirements on those original leaves, not proved machine laws.
`phaseBody` is an INCOMPLETE construction attempt: it does not yet implement
lawful whole-tuple restriction actions or typed Request response domains, and
its returned/future branch is not connected to the preceding receiver trace.
`allArmsBody` retains full old endpoint clauses, but the actual scoped-family
inventory/endpoint correspondence is missing. These gaps cannot be hidden by
supplying a completed callback. There is no EI-Intro or EI-Result theorem here.
-/
namespace YulangClosure.OriginalComputedCallInterpretationR311

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking
open ComputedCallTypedFormationR310

variable {s : Sorts} {View : Type}

/-- Required primitive occurrences. Callee and receiver Request suffixes are
separate uses. The original owner must authenticate each use and its raw data. -/
inductive Use where
  | calleePrefix | calleeRequest | calleeResume | calRet | reify
  | assemble | receipt | valueForce | valueRebind | retainedBind
  | operationNativeReturn | operationDelimiter | body | consumer
  | receiverRequest | receiverResume | result | future | restriction
  deriving DecidableEq, Repr

/-- A goal keeps the typed original reference, original owner/context, and ALL
semantic operands. The Key's Position includes its source binder telescope.
Signature has no Position operand; authentication of Key to declaration is an
explicit source-resolution duty, not inferred from equal numeric sites. -/
structure PrimitiveGoal (s : Sorts) where
  use : Use
  reference : Key
  signature : Signature s

/-- One actual original registry leaf at an exact ID. The conclusion is a
fixed original registered predicate, never the desired EI body. This does not
by itself authenticate that the source Key denotes this declaration. -/
structure PrimitiveLeaf (inputs : Inputs s) (registry : GuardRegistry inputs)
    (goal : PrimitiveGoal s) where
  identifier : Nat
  entry : GuardDeclaration s
  found : registry.declaration identifier = some entry
  signature : entry.signature = goal.signature
  conclusion : entry.after = .registered goal.signature

/-- Each source/primitive owner supplies only an optional exact guard-law leaf.
No completed interpretation, overall membership or arbitrary Positive callback
can occur in this interface. None is failure, not an absent obligation. -/
abbrev Resolution (inputs : Inputs s) (registry : GuardRegistry inputs) :=
  (goal : PrimitiveGoal s) → Option (PrimitiveLeaf inputs registry goal)

def primitiveBody (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (goal : PrimitiveGoal s) : Positive s :=
  match resolution goal with
  | none => .guard False
  | some _ => .guard (registry.original goal.signature)

def Missing (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (goal : PrimitiveGoal s) : Prop :=
  resolution goal = none

theorem missing_primitive_rejected (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (goal : PrimitiveGoal s) (Z : Family s)
    (missing : Missing inputs registry resolution goal) :
    ¬ (primitiveBody inputs registry resolution goal).Holds Z := by
  simp only [Missing] at missing
  simp only [primitiveBody, missing, Positive.Holds, not_false_eq_true]

theorem primitive_introduction (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (goal : PrimitiveGoal s)
    (leaf : PrimitiveLeaf inputs registry goal) (found : resolution goal = some leaf)
    (before : leaf.entry.before.Holds inputs registry.original) (Z : Family s) :
    (primitiveBody inputs registry resolution goal).Holds Z := by
  have after := registry.law leaf.identifier leaf.entry leaf.found before
  rw [leaf.conclusion] at after
  simpa only [primitiveBody, found, Positive.Holds, Guard.Holds] using after


/-- Original same-CalRet data is indexed by the exact Call position. No Return
or successful execution is asserted by this data constructor. -/
structure BoundReturn (s : Sorts) (call : Position) where
  callee : RawObservation s
  value : ValueRow s
  provider : s.Provider

/-- Invocation uses its LIVE current event; it does not freeze the callee's
CalRet world across Delay/reify, receipt, response or future development. -/
def receiverRow {call : Position} (returned : BoundReturn s call)
    (function : s.Descriptor) (current : Event s) : ValueRow s :=
  (returned.value.withDescriptor function).atEvent current

/-- Resolution goals are built from original typed operands. The argument use
is inside the exact CalRet binder; every other use keeps the original IF key.
No original source Program is replaced by a successful argument execution. -/
def goal (request : Request) (use : Use) (declaration : Declaration)
    (operands : List (Operand s)) : PrimitiveGoal s :=
  ⟨use, (if use = .reify then request.operands.argument.reference.key
    else request.operands.incidence.key),
    ⟨declaration, request.original.site, request.original.context,
      .declaration request.original.position.origin ::
      .endpoint request.originalResult :: operands⟩⟩

theorem argument_reference_scope (call : CallRecord) (declaration : Declaration)
    (operands : List (Operand s)) :
    (goal (prepare call) .reify declaration operands).reference.scope =
      [.calRet call.position] := by
  simp only [goal, ↓reduceIte, Ref.key, ComputedCallTypedFormationR310.prepare, List.nil_append]

theorem goal_original_owner (request : Request) (use : Use) (declaration : Declaration)
    (operands : List (Operand s)) :
    (goal request use declaration operands).signature.owner = request.original.site ∧
    (goal request use declaration operands).signature.context = request.original.context := ⟨rfl, rfl⟩

/-- IDs/declarations come from the independent original primitive inventory.
Their source resolution is not supplied by the syntax of a Call. -/
structure PrimitiveDeclarations where
  declaration : Use → Declaration

def primitiveGoal (request : Request) (declarations : PrimitiveDeclarations) (use : Use)
    (operands : List (Operand s)) : PrimitiveGoal s :=
  goal request use (declarations.declaration use) operands

def returnedOperands {call : Position} (returned : BoundReturn s call) : List (Operand s) :=
  [.observation returned.callee, .value returned.value.value returned.value.root,
   .descriptor returned.value.descriptor, .provider returned.provider, .event returned.value.event]

def calRetBody (inputs : Inputs s) (callee : s.Interface) (function : s.Descriptor)
    {call : Position} (returned : BoundReturn s call) : Positive s :=
  .both (clause inputs (.trace (returned.callee.atInterface callee)))
    (.both (.guard (inputs.traceForm (returned.callee.atInterface callee) = .pureReturn returned.value))
      (receiverBody inputs (returned.value.withDescriptor function) returned.provider))

/-- Actual original callee membership + an independently checked RETURN VALUE
transport produces the same-provider Function component. No EI body, source
Call membership, admission or overall Checking is assumed. -/
theorem calRet_introduction (inputs : Inputs s) (registry : GuardRegistry inputs)
    (leaves : Positive s → Positive s → Prop)
    (children : ∀ A B, leaves A B → A.Holds (Meaning inputs) → B.Holds (Meaning inputs))
    (callee : s.Interface) (function : s.Descriptor) {call : Position}
    (returned : BoundReturn s call)
    (member : Meaning inputs (.trace (returned.callee.atInterface callee)))
    (form : inputs.traceForm (returned.callee.atInterface callee) = .pureReturn returned.value)
    (checked : Proof inputs registry leaves (.field (.value returned.value))
      (.field (.value (returned.value.withDescriptor function))))
    (functionSort : inputs.valueForm function = .function)
    (actual : inputs.actual returned.value.value returned.value.root returned.provider) :
    (calRetBody inputs callee function returned).Holds (Meaning inputs) := by
  have trace := (meaning_iff inputs _).mp member
  change PhiT inputs (Meaning inputs) (returned.callee.atInterface callee) at trace
  have result := trace.2.2.2.1
  rw [form] at result
  have checkedMember : Meaning inputs (.value (returned.value.withDescriptor function)) :=
    Proof.sound inputs registry children checked result.2
  exact ⟨(meaning_clause inputs _).mp member, form,
    receiver_from_function inputs _ returned.provider actual functionSort checkedMember⟩

/-- The whole original carrier clause includes inert/license/captures, every
independent demand and designated Force readout, and all hereditary events. -/
def argumentBody (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (request : Request)
    (declarations : PrimitiveDeclarations)
    (returned : BoundReturn s request.original.position) (carrier : CarrierRow s) : Positive s :=
  .both (primitiveBody inputs registry resolution
    (primitiveGoal request declarations .reify (returnedOperands returned ++ [.carrier carrier])))
    (clause inputs (.carrier carrier))

theorem argument_introduction (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (request : Request)
    (declarations : PrimitiveDeclarations)
    (returned : BoundReturn s request.original.position) (carrier : CarrierRow s)
    (leaf : PrimitiveLeaf inputs registry
      (primitiveGoal request declarations .reify (returnedOperands returned ++ [.carrier carrier])))
    (found : resolution (primitiveGoal request declarations .reify
      (returnedOperands returned ++ [.carrier carrier])) = some leaf)
    (before : leaf.entry.before.Holds inputs registry.original)
    (checked : Meaning inputs (.carrier carrier)) :
    (argumentBody inputs registry resolution request declarations returned carrier).Holds (Meaning inputs) :=
  ⟨primitive_introduction inputs registry resolution _ leaf found before _,
    (meaning_clause inputs _).mp checked⟩

/-- Semantic entry modes of EI §3.3. Their primitive transition truth is still
owned by the original declaration; tags alone never certify entry order. -/
inductive EntryMode where
  | value | retained | operation
  deriving DecidableEq, Repr

/-- Original raw observation at every ordered step is retained. Value always
has a designated Force and typed Return/rebind, even for an unused formal.
Operation has native Return(MakeRequestThunk), delimiter, then consumer. -/
inductive Entry (s : Sorts) where
  | value (receipt force rebind body consumer : RawObservation s)
      (demand : Event s) (result : ValueRow s)
  | retained (receipt bound body consumer : RawObservation s)
  | operation (receipt nativeReturn delimiter consumer : RawObservation s)

def Entry.mode : Entry s → EntryMode
  | .value .. => .value | .retained .. => .retained | .operation .. => .operation

def Entry.steps : Entry s → List (Use × RawObservation s)
  | .value receipt force rebind body consumer _ _ =>
      [(.receipt, receipt), (.valueForce, force), (.valueRebind, rebind),
       (.body, body), (.consumer, consumer)]
  | .retained receipt bound body consumer =>
      [(.receipt, receipt), (.retainedBind, bound), (.body, body), (.consumer, consumer)]
  | .operation receipt nativeReturn delimiter consumer =>
      [(.receipt, receipt), (.operationNativeReturn, nativeReturn),
       (.operationDelimiter, delimiter), (.consumer, consumer)]

/-- Entry protocol labels only. Actual transition/order validity remains at
original phase declarations and checkedObservation, not this finite list. -/
def EntryMode.protocol : EntryMode → List Use
  | .value => [.receipt, .valueForce, .valueRebind, .body, .consumer]
  | .retained => [.receipt, .retainedBind, .body, .consumer]
  | .operation => [.receipt, .operationNativeReturn, .operationDelimiter, .consumer]

/-- A pending observation supplies ONLY reached raw slots, including the current
unfinished step. There is no raw value for a future Force Return/body/consumer.
The bound verifies representation shape only; it is not a machine-order law. -/
structure ReachedPrefix (s : Sorts) where
  mode : EntryMode
  observations : List (RawObservation s)
  bounded : observations.length ≤ mode.protocol.length

def ReachedPrefix.steps (reached : ReachedPrefix s) : List (Use × RawObservation s) :=
  reached.mode.protocol.zip reached.observations

theorem reached_prefix_tags (reached : ReachedPrefix s) :
    reached.steps.map Prod.fst = reached.mode.protocol.take reached.observations.length := by
  have general (uses : List Use) (raws : List (RawObservation s)) :
      (uses.zip raws).map Prod.fst = uses.take raws.length := by
    induction uses generalizing raws with
    | nil => simp
    | cons use uses ih =>
        cases raws with
        | nil => simp
        | cons raw raws => simp [ih]
  exact general _ _

theorem reached_prefix_raws (reached : ReachedPrefix s) :
    reached.steps.map Prod.snd = reached.observations := by
  exact List.map_snd_zip reached.bounded

/-- Each step leaf is checked with all reached earlier observations,
so a receiver Request cannot reinterpret the whole entry as an unexecuted tail.
No callback supplies any complete EI clause. -/
def stepsBody (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (request : Request)
    (declarations : PrimitiveDeclarations) (fixed : List (Operand s)) :
    List (Use × RawObservation s) → Positive s
  | [] => .guard True
  | (use, raw) :: rest =>
      .both (primitiveBody inputs registry resolution
        (primitiveGoal request declarations use (fixed ++ [.observation raw, .event raw.event])))
        (stepsBody inputs registry resolution request declarations
          (fixed ++ [.observation raw, .event raw.event]) rest)

def entryBody (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (request : Request)
    (declarations : PrimitiveDeclarations)
    (returned : BoundReturn s request.original.position) (carrier : CarrierRow s) (current : Event s) {function : s.Descriptor}
    (challenge : Challenge (receiverRow returned function current)) (entry : Entry s) : Positive s :=
  .both (stepsBody inputs registry resolution request declarations
    (returnedOperands returned ++ [.carrier carrier, .event current, .invocation challenge.input]) entry.steps)
    (match entry with
      | .value _ force _ _ _ demand result =>
          .both (.guard (inputs.demand carrier demand ∧ inputs.force carrier.input demand force ∧
            inputs.forceIncidence carrier demand force ∧
            inputs.traceForm (force.atInterface carrier.interface) = .pureReturn result))
            (clause inputs (.trace (force.atInterface carrier.interface)))
      | .retained .. => clause inputs (.carrier carrier)
      | .operation .. => clause inputs (.carrier carrier))

theorem value_entry_never_omits_force (receipt force rebind body consumer : RawObservation s)
    (demand : Event s) (result : ValueRow s) :
    (Entry.value receipt force rebind body consumer demand result).steps.map Prod.fst =
      [.receipt, .valueForce, .valueRebind, .body, .consumer] := rfl

theorem operation_entry_keeps_native_return (receipt nativeReturn delimiter consumer : RawObservation s) :
    (Entry.operation receipt nativeReturn delimiter consumer).steps.map Prod.fst =
      [.receipt, .operationNativeReturn, .operationDelimiter, .consumer] := rfl

/-- Whole original carrier membership supplies the designated Force checking
at every independent demand, with the SAME carrier, raw observation/current
world and full result/future clause. This is applied without executing Force. -/
theorem designated_force_from_carrier (inputs : Inputs s) (carrier : CarrierRow s)
    (demand : Event s) (raw : RawObservation s)
    (checked : Meaning inputs (.carrier carrier))
    (demanded : inputs.demand carrier demand) (forced : inputs.force carrier.input demand raw) :
    inputs.compatible carrier.event demand ∧ inputs.forceIncidence carrier demand raw ∧
      (clause inputs (.trace (raw.atInterface carrier.interface))).Holds (Meaning inputs) := by
  have body := (meaning_iff inputs (.carrier carrier)).mp checked
  have designated := body.2.2.2.2.1 demand demanded
  have result := designated.2 raw forced
  exact ⟨designated.1, result.1, (meaning_clause inputs _).mp result.2⟩

/-- The receiver contract remains the ORIGINAL complete P_F over every checked
challenge and every actual development. No provider acceptance filters D_F. -/
def receiverDevelopments (inputs : Inputs s) {call : Position}
    (returned : BoundReturn s call) (function : s.Descriptor) (current : Event s) : Positive s :=
  .all {d : Challenge (receiverRow returned function current) // CheckedDomain inputs d} fun d =>
    .both (.guard (ActualAdm inputs returned.provider d.val))
      (.all {raw : RawObservation s // inputs.execute returned.provider d.val.input raw} fun raw =>
        inputs.checkedObservation d.val raw.val)

theorem receiver_developments_from_function (inputs : Inputs s) {call : Position}
    (returned : BoundReturn s call) (function : s.Descriptor) (current : Event s)
    (compatible : inputs.compatible returned.value.event current)
    (member : Meaning inputs (.value (returned.value.withDescriptor function)))
    (form : inputs.valueForm function = .function)
    (actual : inputs.actual returned.value.value returned.value.root returned.provider) :
    (receiverDevelopments inputs returned function current).Holds (Meaning inputs) := by
  have original := (meaning_iff inputs _).mp member
  have currentMember := original.2 current compatible
  have body := (meaning_clause inputs _).mp currentMember
  have callable : FunctionAt inputs (Meaning inputs) (receiverRow returned function current) := by
    simpa only [valueCore, ValueRow.withDescriptor, ValueRow.atEvent, form, functionClause_iff,
      receiverRow] using body.1
  intro d
  have development := (callable.2 returned.provider actual).2.2 d.val d.property
  exact ⟨development.1, fun raw => development.2 raw.val raw.property⟩

/-- The post-Delay/receipt receiver uses the SAME actual provider at the LIVE
world. Hereditary transport is derived from the completed old Function value;
compatibility is an original event-action leaf, not equality to CalRet. -/
theorem live_receiver_from_function (inputs : Inputs s) {call : Position}
    (returned : BoundReturn s call) (function : s.Descriptor) (current : Event s)
    (compatible : inputs.compatible returned.value.event current)
    (member : Meaning inputs (.value (returned.value.withDescriptor function)))
    (form : inputs.valueForm function = .function)
    (actual : inputs.actual returned.value.value returned.value.root returned.provider) :
    (receiverBody inputs (receiverRow returned function current) returned.provider).Holds (Meaning inputs) := by
  have body := (meaning_iff inputs _).mp member
  exact receiver_from_function inputs _ returned.provider actual
    (show inputs.valueForm (receiverRow returned function current).descriptor = .function from form)
    (body.2 current compatible)

/-- A pending callee keeps only a dependent tail at a FUTURE CalRet binder.
Receiver pending keeps only reached entry-prefix data, and carries only
its receiver continuation. The different constructors cannot replay a callee.
Continuation domains are full original response/current-world raw tuples; their
authentication is a required original Request/resume primitive leaf. -/
inductive Phase (s : Sorts) (call : Position) where
  | callee (raw : RawObservation s)
  | calleeRequest (raw : RawObservation s) (resumed : RawObservation s)
  | calRet (returned : BoundReturn s call)
  | argument (returned : BoundReturn s call) (carrier : CarrierRow s)
  | receiver (returned : BoundReturn s call) (carrier : CarrierRow s)
      (function : s.Descriptor) (current : Event s) (challenge : Challenge (receiverRow returned function current))
      (reached : ReachedPrefix s) (raw : RawObservation s)
  | receiverRequest (returned : BoundReturn s call) (carrier : CarrierRow s) (function : s.Descriptor)
      (current : Event s) (challenge : Challenge (receiverRow returned function current))
      (reached : ReachedPrefix s) (request resumed : RawObservation s)
  | returned (returned : BoundReturn s call) (result : ValueRow s)
      (provider : s.Provider) (raw : RawObservation s)
  | future (result : ValueRow s) (provider : s.Provider) (later : Event s)

/-- Primitive guards for a fixed open tail. The future CalRet is bound here,
not fabricated at an earlier prior. The original carrier/challenge checking
obligations remain independently visible. -/
def tailBody (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (request : Request)
    (declarations : PrimitiveDeclarations) (callee : s.Interface) (function : s.Descriptor)
    (returned : BoundReturn s request.original.position) : Positive s :=
  .both (calRetBody inputs callee function returned)
    (.both (primitiveBody inputs registry resolution
      (primitiveGoal request declarations .calRet (returnedOperands returned)))
      (.both
        (.all {carrier : CarrierRow s // registry.original
          (primitiveGoal request declarations .reify (returnedOperands returned ++ [.carrier carrier])).signature}
          fun carrier => argumentBody inputs registry resolution request declarations returned carrier.val)
        (receiverDevelopments inputs returned function returned.value.event)))

/-- Callee prior retains a universal dependent post-CalRet obligation. Its
independent domain is the original declared CalRet incidence, never membership,
provider acceptance or a desired result. Authenticity/completeness of that
source-owned incidence remains unresolved; no instance is manufactured here. -/
def calleeSuffix (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (request : Request)
    (declarations : PrimitiveDeclarations) (callee : s.Interface) (function : s.Descriptor)
    (prior : RawObservation s) : Positive s :=
  .all {returned : BoundReturn s request.original.position //
    registry.original (primitiveGoal request declarations .calleeResume
      ([.observation prior, .event prior.event] ++ returnedOperands returned)).signature}
    fun returned => tailBody inputs registry resolution request declarations callee function returned.val

def calleePhaseBody (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (state : Decoded s View)
    (request : Request) (declarations : PrimitiveDeclarations) (raw : RawObservation s) : Positive s :=
      .both (clause inputs (.trace (raw.atInterface
        (state.interfaces ⟨request.original.calleeSite, .synthesis⟩))))
        (.both (primitiveBody inputs registry resolution
          (primitiveGoal request declarations .calleePrefix [.observation raw, .event raw.event]))
          (calleeSuffix inputs registry resolution request declarations
            (state.interfaces ⟨request.original.calleeSite, .synthesis⟩)
            (state.assignment.descriptor ⟨request.original.site, .descriptor⟩) raw))

def argumentPhaseBody (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (state : Decoded s View)
    (request : Request) (declarations : PrimitiveDeclarations)
    (returned : BoundReturn s request.original.position) (carrier : CarrierRow s) : Positive s :=
  .both (tailBody inputs registry resolution request declarations
    (state.interfaces ⟨request.original.calleeSite, .synthesis⟩)
    (state.assignment.descriptor ⟨request.original.site, .descriptor⟩) returned)
    (argumentBody inputs registry resolution request declarations returned carrier)

/-- Selected phase clause CONSTRUCTION. This makes no q_c or original Interface
registration. Primitive resolution is required even when the typed data exists.
The original checkedObservation and carrier clauses retain all local arms. -/
def phaseBody (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (state : Decoded s View)
    (request : Request) (declarations : PrimitiveDeclarations) :
    Phase s request.original.position → Positive s
  | .callee raw => calleePhaseBody inputs registry resolution state request declarations raw
  | .calleeRequest raw resumed =>
      .both (calleePhaseBody inputs registry resolution state request declarations raw)
        (.both (primitiveBody inputs registry resolution (primitiveGoal request declarations .calleeRequest
          [.observation raw, .event raw.event]))
          (.both (primitiveBody inputs registry resolution (primitiveGoal request declarations .calleeResume
            [.observation raw, .event raw.event, .observation resumed, .event resumed.event]))
            (calleePhaseBody inputs registry resolution state request declarations resumed)))
  | .calRet returned => tailBody inputs registry resolution request declarations
      (state.interfaces ⟨request.original.calleeSite, .synthesis⟩)
      (state.assignment.descriptor ⟨request.original.site, .descriptor⟩) returned
  | .argument returned carrier =>
      argumentPhaseBody inputs registry resolution state request declarations returned carrier
  | .receiver returned carrier function current challenge reached raw =>
      .both (argumentPhaseBody inputs registry resolution state request declarations returned carrier)
        (.both (.guard (function = state.assignment.descriptor ⟨request.original.site, .descriptor⟩))
          (.both (.guard (CheckedDomain inputs challenge ∧
            challenge.carrier = carrier.carrier ∧ challenge.carrierRoot = carrier.root ∧
            challenge.carrierView = carrier.interface))
            (.both (primitiveBody inputs registry resolution (primitiveGoal request declarations .assemble
              (returnedOperands returned ++ [.carrier carrier, .event current, .invocation challenge.input])))
              (.both (receiverBody inputs (receiverRow returned function current) returned.provider)
              (.both (stepsBody inputs registry resolution request declarations
                (returnedOperands returned ++ [.carrier carrier, .event current, .invocation challenge.input]) reached.steps)
                (inputs.checkedObservation challenge raw))))))
  | .receiverRequest returned carrier function current challenge reached raw resumed =>
      .both (argumentPhaseBody inputs registry resolution state request declarations returned carrier)
        (.both (.guard (function = state.assignment.descriptor ⟨request.original.site, .descriptor⟩ ∧
          CheckedDomain inputs challenge ∧ challenge.carrier = carrier.carrier ∧
          challenge.carrierRoot = carrier.root ∧ challenge.carrierView = carrier.interface))
          (.both (primitiveBody inputs registry resolution (primitiveGoal request declarations .assemble
            (returnedOperands returned ++ [.carrier carrier, .event current, .invocation challenge.input])))
            (.both (receiverBody inputs (receiverRow returned function current) returned.provider)
            (.both (stepsBody inputs registry resolution request declarations
              (returnedOperands returned ++ [.carrier carrier, .event current, .invocation challenge.input]) reached.steps)
        (.both (primitiveBody inputs registry resolution (primitiveGoal request declarations .receiverRequest
          (returnedOperands returned ++ [.invocation challenge.input, .observation raw, .event raw.event])))
          (.both (primitiveBody inputs registry resolution (primitiveGoal request declarations .receiverResume
            (returnedOperands returned ++ [.invocation challenge.input,
              .observation raw, .event raw.event, .observation resumed, .event resumed.event])))
            (.both (inputs.checkedObservation challenge raw)
              (inputs.checkedObservation challenge resumed))))))))
  | .returned returned result provider raw =>
      .both (primitiveBody inputs registry resolution (primitiveGoal request declarations .result
        (returnedOperands returned ++ [.value result.value result.root, .descriptor result.descriptor,
          .provider provider, .observation raw, .event raw.event])))
        (.both (.guard (result.event = raw.event ∧ inputs.actual result.value result.root provider))
          (.both (.field (.world raw.event)) (.field (.value result))))
  | .future result provider later =>
      .both (primitiveBody inputs registry resolution (primitiveGoal request declarations .future
        [.value result.value result.root, .descriptor result.descriptor, .provider provider,
         .event result.event, .event later]))
        (.both (.guard (inputs.compatible result.event later ∧
          inputs.actual result.value result.root provider))
          (.field (.value (result.atEvent later))))
/-- An absent phase primitive cannot silently validate a reached prior. -/
theorem missing_callee_prefix_rejected (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (state : Decoded s View)
    (request : Request) (declarations : PrimitiveDeclarations) (raw : RawObservation s)
    (missing : Missing inputs registry resolution
      (primitiveGoal request declarations .calleePrefix [.observation raw, .event raw.event])) :
    ¬ (phaseBody inputs registry resolution state request declarations (.callee raw)).Holds (Meaning inputs) := by
  intro valid
  change (calleePhaseBody inputs registry resolution state request declarations raw).Holds (Meaning inputs) at valid
  exact missing_primitive_rejected inputs registry resolution _ _ missing valid.2.1

/-- The returned provider's hereditary field is obtained from ORIGINAL result
membership; the original future-map primitive remains a separate required leaf.
No future observation or desired future body is assumed. -/
theorem future_introduction (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (state : Decoded s View)
    (request : Request) (declarations : PrimitiveDeclarations) (result : ValueRow s)
    (provider : s.Provider) (later : Event s)
    (member : Meaning inputs (.value result))
    (compatible : inputs.compatible result.event later)
    (actual : inputs.actual result.value result.root provider)
    (leaf : PrimitiveLeaf inputs registry (primitiveGoal request declarations .future
      [.value result.value result.root, .descriptor result.descriptor, .provider provider,
       .event result.event, .event later]))
    (found : resolution (primitiveGoal request declarations .future
      [.value result.value result.root, .descriptor result.descriptor, .provider provider,
       .event result.event, .event later]) = some leaf)
    (before : leaf.entry.before.Holds inputs registry.original) :
    (phaseBody inputs registry resolution state request declarations (.future result provider later)).Holds
      (Meaning inputs) := by
  have body := (meaning_iff inputs (.value result)).mp member
  exact ⟨primitive_introduction inputs registry resolution _ leaf found before _,
    ⟨compatible, actual⟩, body.2 later compatible⟩

/-- An entirely unresolved primitive map cannot admit any source phase.
This is an actual failure result, not a successful empty interpretation. -/
theorem unresolved_source_rejected (inputs : Inputs s) (registry : GuardRegistry inputs)
    (state : Decoded s View) (request : Request) (declarations : PrimitiveDeclarations)
    (phase : Phase s request.original.position) :
    ¬ (phaseBody inputs registry (fun _ => none) state request declarations phase).Holds (Meaning inputs) := by
  cases phase with
  | callee raw =>
      exact missing_callee_prefix_rejected inputs registry (fun _ => none) state request declarations raw rfl
  | calleeRequest raw resumed =>
      intro valid
      exact missing_callee_prefix_rejected inputs registry (fun _ => none) state request declarations raw rfl valid.1
  | calRet returned =>
      intro valid
      exact valid.2.1
  | argument returned carrier =>
      intro valid
      exact valid.1.2.1
  | receiver returned carrier function current challenge reached raw =>
      intro valid
      exact valid.1.1.2.1
  | receiverRequest returned carrier function current challenge reached raw resumed =>
      intro valid
      exact valid.1.1.2.1
  | returned returned result provider raw =>
      intro valid
      exact valid.1
  | future result provider later =>
      intro valid
      exact valid.1

/-- EI-All retains each original arm slot, including duplicates, with its FULL
old clause at the same raw tuple. The original owner must supply the complete
arm inventory; no source traversal guesses [] and no arm truth is assumed. -/
def allArmsBody (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (state : Decoded s View)
    (request : Request) (declarations : PrimitiveDeclarations)
    (arms : List Endpoint) (phase : Phase s request.original.position) (raw : RawObservation s) : Positive s :=
  .either (phaseBody inputs registry resolution state request declarations phase)
    (.existsE (Fin arms.length) fun i =>
      ComputedCallUnionRealizationR293.branchBody inputs state arms[i] raw)

/-- A genuine independent arm is injected at its exact original Fin slot into
both the new constructed EI-All clause and the EXISTING R293 Union consumer.
Neither injection registers the source phase clause at the old source endpoint. -/
theorem independent_arm_application (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (state : Decoded s View)
    (request : Request) (declarations : PrimitiveDeclarations) (arms : List Endpoint)
    (phase : Phase s request.original.position) (raw : RawObservation s) (i : Fin arms.length)
    (member : Meaning inputs (.trace (raw.atInterface (state.interfaces arms[i])))) :
    (allArmsBody inputs registry resolution state request declarations arms phase raw).Holds (Meaning inputs) ∧
    (ComputedCallUnionRealizationR293.unionBody inputs state request.originalCheck arms raw).Holds (Meaning inputs) :=
  ⟨Or.inr ⟨i, (meaning_clause inputs _).mp member⟩,
   Or.inr ⟨i, (meaning_clause inputs _).mp member⟩⟩

/-- Actual R308/R293-to-R159 application remains available only with the old
source membership and original Checking. It does not take a desired EI readback
as a hypothesis. The constructed phase clause cannot furnish those inputs. -/
theorem original_parent_application (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (declarations : Declarations inputs registry) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) (mark : Mark)
    (occurrence : Nat) (data : Logical s View) (state : Decoded s View)
    (decoded : decode readout environment = some state) (arms : List Endpoint)
    (raw : RawObservation s)
    (checked : Checking (OriginalSourceChecking.kernel inputs registry declarations
      (environmentReading inputs readout ports) original)
      (environment.extend ⟨mark.site, .viewLogic, 0⟩
        (scopeCandidate environment occurrence (.logical .viewLogic data)))
      ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩)
    (member : Meaning inputs (.trace (raw.atInterface
      ((state.logical data).interfaces ⟨mark.site, .callableImage⟩)))) :
    (ComputedCallUnionClausesR308.factoredBody inputs (state.logical data)
      ⟨mark.site, .callableImage⟩ arms raw).Holds (Meaning inputs) ∧
    Meaning inputs (.trace (raw.atInterface ((state.logical data).interfaces ⟨mark.site, .synthesis⟩))) :=
  ComputedCallUnionClausesR308.factored_app_result_pair inputs registry readout ports
    declarations original environment context mark occurrence data state decoded arms raw checked member

/-- No clause at an original opaque Interface literally registers EI-All.
Semantic equivalence would still not be an authentic q_c owner/readback. -/
theorem original_clause_ne_ei_all (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (state : Decoded s View)
    (request : Request) (declarations : PrimitiveDeclarations) (arms : List Endpoint)
    (phase : Phase s request.original.position) (raw : RawObservation s) (row : TraceRow s) :
    clause inputs (.trace row) ≠
      allArmsBody inputs registry resolution state request declarations arms phase raw := by
  intro equation
  cases equation

end YulangClosure.OriginalComputedCallInterpretationR311
