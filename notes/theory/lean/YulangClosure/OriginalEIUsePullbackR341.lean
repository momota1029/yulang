import YulangClosure.OriginalEIContractRealizationR340
import YulangClosure.SourceDeclarationRetentionR295

/-!
R341: exact IF-Use fibres and the missing original continuation producer.

IF construction §§3/6 precomposes the complete dependent catalogue with the
original scoped substitution. It needs no inverse of that substitution. This
file proves the full packet round trip and universal elimination for every use
world, not only worlds in an image. This does not authenticate a catalogue as
an original primitive's response/continuation contract.

The second part supplies an ABSTRACT Inputs discriminator: prior CalleeInputs,
resolved request/resume primitive inputs, and a nonempty full typed/admitted
response telescope coexist with a false resumed callee trace. Thus those
existing interfaces cannot supply the omitted continuation typing producer.
It is not an independently typed Yulang primitive and is NOT a counterexample
to EI §§2–5. No source-domain, R306 or R159 closure is asserted.
-/
namespace YulangClosure.OriginalEIUsePullbackR341

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking ComputedCallTypedFormationR310
open OriginalComputedCallInterpretationR311 OriginalSourceEIInterpretationR331
open OriginalSourceEIConstructionR339 SourceSignatureConstruction SourceContributionConstruction

section Pullback
variable {Joint : Type}

/-- The inverse is on the dependent PACKET fibre, not on worlds. It retains
every field, including any response, suffix, key, witness and license present
in the independently supplied original packet. -/
def declarationPacket (original : Graph Joint)
    (data : SourceDeclarationRetentionR295.DeclarationData Joint) (whole : Joint)
    (packet : Packet (SourceDeclarationRetentionR295.useCatalogue original data) whole) :
    Packet data.clause.catalogue (original.substitution data.substitution whole) :=
  ⟨packet.port, packet.value⟩

theorem declaration_use_roundtrip (original : Graph Joint)
    (data : SourceDeclarationRetentionR295.DeclarationData Joint) (whole : Joint)
    (packet : Packet data.clause.catalogue (original.substitution data.substitution whole)) :
    declarationPacket original data whole
      (SourceDeclarationRetentionR295.usePacket original data whole packet) = packet := by
  cases packet
  rfl

theorem use_declaration_roundtrip (original : Graph Joint)
    (data : SourceDeclarationRetentionR295.DeclarationData Joint) (whole : Joint)
    (packet : Packet (SourceDeclarationRetentionR295.useCatalogue original data) whole) :
    SourceDeclarationRetentionR295.usePacket original data whole
      (declarationPacket original data whole packet) = packet := by
  cases packet
  rfl

/-- All use worlds, all ports and the entire dependent evidence fibre. No
surjectivity, world inverse, source execution or membership assumption occurs.
The predicate is only an elimination principle; it supplies no semantic law. -/
theorem all_use_packets_iff (original : Graph Joint)
    (data : SourceDeclarationRetentionR295.DeclarationData Joint)
    (P : (whole : Joint) → Packet (SourceDeclarationRetentionR295.useCatalogue original data) whole → Prop) :
    (∀ whole packet, P whole packet) ↔
      (∀ whole packet, P whole (SourceDeclarationRetentionR295.usePacket original data whole packet)) := by
  constructor
  · intro all whole packet
    exact all whole _
  · intro all whole packet
    simpa only [use_declaration_roundtrip] using
      all whole (declarationPacket original data whole packet)

theorem use_scope_and_sharing (original : Graph Joint)
    (data : SourceDeclarationRetentionR295.DeclarationData Joint) :
    (SourceDeclarationRetentionR295.useCatalogue original data).scope = data.clause.catalogue.scope ∧
    (SourceDeclarationRetentionR295.useCatalogue original data).sharedSlot =
      data.clause.catalogue.sharedSlot := ⟨rfl, rfl⟩
end Pullback

namespace AbstractContinuationObstruction

/-- Infinite histories, responses and continuation/context identities; distinct
configurations and observations. These are discriminator sorts, not a source
interpretation or a replacement for the accepted primitive domains. -/
def sorts : Sorts where
  Valuation := Unit
  ConstructorGraph := Unit
  Dependencies := Unit
  SourceGraph := Unit
  BinderTree := Unit
  Assignment := Unit
  History := Nat
  Configuration := Bool
  JointWitness := Nat
  Scope := Unit
  Authority := Unit
  Incidence := Unit
  Dictionary := Unit
  Descriptor := Unit
  Interface := Unit
  Value := Unit
  Provider := Unit
  Root := Unit
  Carrier := Unit
  Observation := Bool
  Context := Nat
  Continuation := Nat
  Receipt := Unit
  TypedPath := Unit
  Consumer := Unit
  WitnessPosition := Unit
  WitnessValue := Nat

def inputs : Inputs sorts where
  compatible := fun _ _ => True
  eventCoherent := fun _ => True
  valueForm := fun _ => .ground
  ground := fun _ => True
  fixedExternal := fun _ => True
  structuralGuard := fun _ => True
  structuralFields := fun _ => .guard True
  actual := fun _ _ _ => False
  functionGuards := fun _ _ => ⟨True, True, True, True, True⟩
  capturedFields := fun _ _ => .guard True
  checkedInlet := fun _ => ()
  actualInlet := fun _ => ()
  carrierAccepted := fun _ => True
  puncturedContext := fun _ => True
  otherValues := fun _ => True
  registeredHoles := fun _ => True
  checkedIncidences := fun _ => True
  receiptPrecondition := fun _ _ => True
  actualTypedPath := fun _ _ => True
  actualContext := fun _ _ => True
  execute := fun _ _ _ => False
  observationGuards := fun row =>
    ⟨row.observation = false, True, True, True, True, True, True, True, True, True⟩
  traceForm := fun _ => .unfinished
  observationFields := fun _ => .guard True
  checkedObservation := fun _ _ => .guard True
  worldGuards := fun _ => ⟨True, True, True, True⟩
  installedCount := fun _ => 0
  installed := fun _ _ => none
  alias := fun _ _ _ => False
  capture := fun _ _ _ => none
  captureValue := fun _ _ _ => none
  sharedPosition := fun _ _ _ => False
  witnessAt := fun _ _ => (0 : Nat)
  carrierGuards := fun _ => ⟨True, True, True, True, True⟩
  carrierCaptures := fun _ => .guard True
  demand := fun _ _ => True
  force := fun _ _ _ => False
  forceIncidence := fun _ _ _ => True

def candidate : Family sorts
  | .trace row => row.observation = false
  | _ => True

theorem candidate_postfixed : candidate.Le (Phi inputs candidate) := by
  intro query member
  cases query with
  | value row => exact ⟨trivial, fun _ _ => trivial⟩
  | world event =>
    refine ⟨trivial, ⟨trivial, trivial, trivial, trivial⟩,
      (fun _ _ impossible => impossible.elim),
      (fun _ _ _ impossible => by
        change (none : Option Nat) = some _ at impossible
        cases impossible),
      (fun _ _ impossible => impossible.elim), ?_⟩
    intro i binding impossible
    change (none : Option (Installed sorts)) = some binding at impossible
    cases impossible
  | trace row =>
    exact ⟨trivial, ⟨member, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial, trivial, trivial⟩, trivial, trivial, trivial⟩
  | carrier row =>
    exact ⟨trivial, ⟨trivial, trivial, trivial, trivial, trivial⟩, trivial, trivial,
      (fun _ _ => ⟨trivial, fun _ impossible => impossible.elim⟩),
      (fun _ _ => trivial)⟩

theorem prior_trace (raw : RawObservation sorts) (good : raw.observation = false)
    (interface : sorts.Interface) : Meaning inputs (.trace (raw.atInterface interface)) :=
  greatest_coinduct (Phi inputs) candidate candidate_postfixed _ good

theorem no_resumed_trace (current : Event sorts) (interface : sorts.Interface) :
    ¬ Meaning inputs (.trace ((⟨true, current⟩ : RawObservation sorts).atInterface interface)) := by
  intro member
  have impossible : true = false := ((meaning_iff inputs _).mp member).2.1.1
  cases impossible

/-- The admitted domain is deliberately independent of trace membership.
Every original record field survives, with all Nat responses and all live
worlds and developments. This abstract schema has NO source authentication. -/
def schema : ResponseSchema sorts Unit where
  Response := fun _ => Nat
  Typed := fun _ _ _ => True
  Admitted := fun _ _ _ => True
  observe := fun _ _ _ => true
  Develops := fun _ _ _ _ => True

def answer (head : RequestHead sorts Unit) (current : Event sorts) (response : Nat)
    (witness : Nat) (names : List (Name × Nat)) (objects : List (Nat × Installed sorts)) :
    ResponseAt inputs schema head :=
  responseAt inputs schema head current trivial response trivial trivial
    ⟨(), (), (), (), (), ⟨current.history, current.current⟩⟩ rfl rfl
    witness names objects ⟨true, current⟩ trivial

def declarations : PrimitiveDeclarations := ⟨fun _ => 0⟩

/-- Exactly three abstract laws: prior prefix, request, and response step.
Their signatures retain the full source prefix. They deliberately provide no
callee-result/continuation law. They are not genuine Yulang declarations. -/
def testGoal (request : Request) (prior resumed : RawObservation sorts) (index : Nat) :
    PrimitiveGoal sorts :=
  if index = 0 then primitiveGoal request declarations .calleePrefix
    [.observation prior, .event prior.event]
  else if index = 1 then primitiveGoal request declarations .calleeRequest
    [.observation prior, .event prior.event]
  else primitiveGoal request declarations .calleeResume
    [.observation prior, .event prior.event, .observation resumed, .event resumed.event]

def entry (request : Request) (prior resumed : RawObservation sorts) (index : Nat) :
    GuardDeclaration sorts :=
  ⟨(testGoal request prior resumed index).signature, .truth,
    .registered (testGoal request prior resumed index).signature⟩

theorem test_goal_length (request : Request) (prior resumed : RawObservation sorts) (index : Nat) :
    (testGoal request prior resumed index).signature.operands.length ≤ 6 := by
  simp only [testGoal]
  split
  · simp [primitiveGoal, goal]
  · split <;> simp [primitiveGoal, goal]

def registry (request : Request) (prior resumed : RawObservation sorts) : GuardRegistry inputs where
  original := fun signature => signature.operands.length ≤ 6
  declaration := fun index => some (entry request prior resumed index)
  law := by
    intro index declaration found _
    have same := Option.some.inj found
    subst declaration
    exact test_goal_length request prior resumed index

/-- Full Key AND use AND signature matching is demanded even in this abstract
discriminator. Mere signature equality is not used as source authentication. -/
noncomputable def resolution (request : Request) (prior resumed : RawObservation sorts) :
    Resolution inputs (registry request prior resumed) := by
  classical
  intro goal
  exact if found : ∃ index, testGoal request prior resumed index = goal then
    some ⟨found.choose, entry request prior resumed found.choose, rfl,
      congrArg PrimitiveGoal.signature found.choose_spec,
      congrArg (fun goal : PrimitiveGoal sorts => Guard.registered goal.signature) found.choose_spec⟩
    else none

noncomputable def testInput (request : Request) (prior resumed : RawObservation sorts) (index : Nat) :
    PrimitiveInput inputs (registry request prior resumed) (resolution request prior resumed)
      (testGoal request prior resumed index) := by
  classical
  let found : ∃ i, testGoal request prior resumed i = testGoal request prior resumed index := ⟨index, rfl⟩
  refine ⟨⟨found.choose, entry request prior resumed found.choose, rfl,
    congrArg PrimitiveGoal.signature found.choose_spec,
    congrArg (fun goal : PrimitiveGoal sorts => Guard.registered goal.signature) found.choose_spec⟩, ?_, trivial⟩
  simp only [resolution, dite_eq_left found]

def noLeaves : Positive sorts → Positive sorts → Prop := fun _ _ => False

noncomputable def priorCallee (state : Decoded sorts Unit) (request : Request)
    (prior resumed : RawObservation sorts) (good : prior.observation = false) :
    CalleeInputs inputs (registry request prior resumed) (resolution request prior resumed)
      noLeaves state request declarations prior where
  member := prior_trace prior good _
  prefixInput := testInput request prior resumed 0
  returns := by
    intro returned registered
    change (9 : Nat) ≤ 6 at registered
    exact False.elim (by omega)

/-- Exact R339 consumer obstruction, with independently resolved request and
resume leaves and ALL prior CalleeInputs constructed. The current world and
response remain arbitrary, including changed configurations and histories.
Only the missing resumed CalleeInputs can fail. -/
theorem response_consumer_obstruction (state : Decoded sorts Unit) (request : Request)
    (head : RequestHead sorts Unit) (good : head.prior.observation = false)
    (current : Event sorts) (response witness : Nat)
    (names : List (Name × Nat)) (objects : List (Nat × Installed sorts)) :
    let result := answer head current response witness names objects
    let registry := registry request head.prior result.raw
    let resolution := resolution request head.prior result.raw
    Nonempty (CalleeInputs inputs registry resolution noLeaves state request declarations head.prior) ∧
    Nonempty (PrimitiveInput inputs registry resolution (primitiveGoal request declarations
      .calleeRequest [.observation head.prior, .event head.prior.event])) ∧
    Nonempty (PrimitiveInput inputs registry resolution (primitiveGoal request declarations
      .calleeResume [.observation head.prior, .event head.prior.event,
        .observation result.raw, .event result.raw.event])) ∧
    ¬ Nonempty (CalleeInputs inputs registry resolution noLeaves state request declarations result.raw) ∧
    ¬ (phaseBody inputs registry resolution state request declarations
      (.calleeRequest head.prior result.raw)).Holds (Meaning inputs) := by
  dsimp only
  refine ⟨⟨priorCallee state request head.prior _ good⟩,
    ⟨testInput request head.prior _ 1⟩, ⟨testInput request head.prior _ 2⟩, ?_, ?_⟩
  · rintro ⟨callee⟩
    exact no_resumed_trace current _ callee.member
  · intro phase
    exact no_resumed_trace current _ ((meaning_clause inputs _).mpr phase.2.2.2.1)

end AbstractContinuationObstruction
end YulangClosure.OriginalEIUsePullbackR341
