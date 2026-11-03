import YulangClosure.OriginalDeclaredUnionR339

/-!
R340: exact finite receiver extraction and an abstract-input obstruction.

Authority: EI (2026-10-24 computed-call-result-constructor) §§3.3–3.4
embeds the original P_F through IF's original full maps. IF (2026-10-08
call-source-interface-construction) §§3.1–3.3 retains those independently
typed maps; it does not identify an arbitrary P_F with an opaque trace.

The finite extraction below reaches the SAME provider/challenge/raw observation.
It introduces no recursive leaves. The discriminator satisfies the current Lean
ReturnInputs and all live receiver premises but refutes the requested trace.
It is an ABSTRACT Inputs instance, NOT a source-qualified Yulang counterexample.
Its primitive inventory has no reify occurrence; hence it cannot realize an
original complete source IF/EI contract. It locates the missing semantic map,
not a defect in the authoritative EI constructor. No parent gate closes here.
-/
namespace YulangClosure.OriginalReceiverProjectionR340

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking ComputedCallTypedFormationR310
open OriginalComputedCallInterpretationR311 OriginalSourceEIInterpretationR331

variable {s : Sorts}

/-- Finite original Function elimination, with every dependent operand fixed
by its actual constructor. No child soundness callback is used. -/
theorem observation_from_function (inputs : Inputs s) (registry : GuardRegistry inputs)
    (leaves : Positive s → Positive s → Prop) (row : ValueRow s)
    (provider : s.Provider) (actual : inputs.actual row.value row.root provider)
    (challenge : Challenge row) (domain : CheckedDomain inputs challenge)
    (raw : RawObservation s) (executed : inputs.execute provider challenge.input raw) :
    Proof inputs registry leaves (functionClause inputs row)
      (inputs.checkedObservation challenge raw) := by
  exact .compose (.right _ _) (.compose (.allElim _ (⟨provider, actual⟩ : {p : s.Provider // inputs.actual row.value row.root p}))
    (.compose (.right _ _) (.compose (.right _ _)
      (.compose (.allElim _ (⟨challenge, domain⟩ : {d : Challenge row // CheckedDomain inputs d}))
        (.compose (.right _ _) (.allElim _ (⟨raw, executed⟩ : {r : RawObservation s // inputs.execute provider challenge.input r})))))))

/-- Extract the original same-return value from its complete callee trace.
All remaining trace guards/world/latent fields stay in the source clause. -/
theorem value_from_return (inputs : Inputs s) (registry : GuardRegistry inputs)
    (leaves : Positive s → Positive s → Prop) (row : TraceRow s) (value : ValueRow s)
    (form : inputs.traceForm row = .pureReturn value) :
    Proof inputs registry leaves (.field (.trace row)) (.field (.value value)) := by
  apply Proof.compose (.unfold _)
  simp only [clause, form]
  exact .compose (.right _ _) (.compose (.right _ _) (.compose (.left _ _) (.right _ _)))

/-- Every compatible live event is selected from the returned value's original
hereditary field. Its world is not equated to the CalRet event. -/
theorem live_value (inputs : Inputs s) (registry : GuardRegistry inputs)
    (leaves : Positive s → Positive s → Prop) (row : ValueRow s)
    (current : Event s) (compatible : inputs.compatible row.event current) :
    Proof inputs registry leaves (.field (.value row)) (.field (.value (row.atEvent current))) :=
  .compose (.unfold _) (.compose (.right _ _) (.allElim _ (⟨current, compatible⟩ : {later : Event s // inputs.compatible row.event later})))

/-- Actual finite producer available BEFORE the missing projection. The only
recursive leaves here belong to the independent same-return Function check;
no checkedObservation-to-trace leaf or completed observation is supplied. -/
theorem return_to_observation (inputs : Inputs s) (registry : GuardRegistry inputs)
    (resolution : Resolution inputs registry) (leaves : Positive s → Positive s → Prop)
    (request : Request) (declarations : PrimitiveDeclarations)
    (callee : s.Interface) (function : s.Descriptor)
    (returned : BoundReturn s request.original.position)
    (original : ReturnInputs inputs registry resolution leaves request declarations callee function returned)
    (current : Event s) (compatible : inputs.compatible returned.value.event current)
    (challenge : Challenge (receiverRow returned function current))
    (domain : CheckedDomain inputs challenge) (raw : RawObservation s)
    (executed : inputs.execute returned.provider challenge.input raw) :
    Proof inputs registry leaves (.field (.trace (returned.callee.atInterface callee)))
      (inputs.checkedObservation challenge raw) := by
  apply Proof.compose (value_from_return inputs registry leaves _ _ original.form)
  apply Proof.compose original.checked
  apply Proof.compose (live_value inputs registry leaves (returned.value.withDescriptor function) current compatible)
  apply Proof.compose (.unfold _)
  apply Proof.compose (.left _ _)
  have form : inputs.valueForm (receiverRow returned function current).descriptor = .function :=
    original.functionSort
  change Proof inputs registry leaves (valueCore inputs (receiverRow returned function current)) _
  rw [valueCore, form]
  exact observation_from_function inputs registry leaves (receiverRow returned function current) returned.provider original.actual
    challenge domain raw executed

namespace AbstractInputObstruction

/-- Infinite histories and distinct current configurations/witnesses are kept.
Only this explicit discriminator's ordinary operand sorts are singletons. -/
def sorts : Sorts where
  Valuation := Unit
  ConstructorGraph := Unit
  Dependencies := Unit
  SourceGraph := Unit
  BinderTree := Unit
  Assignment := Bool
  History := Nat
  Configuration := Bool
  JointWitness := Bool
  Scope := Unit
  Authority := Unit
  Incidence := Unit
  Dictionary := Unit
  Descriptor := Bool
  Interface := Bool
  Value := Unit
  Provider := Unit
  Root := Unit
  Carrier := Unit
  Observation := Unit
  Context := Unit
  Continuation := Unit
  Receipt := Unit
  TypedPath := Unit
  Consumer := Unit
  WitnessPosition := Unit
  WitnessValue := Unit

def value (event : Event sorts) : ValueRow sorts := ⟨false, (), (), event⟩

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
  carrierAccepted := fun _ => True
  puncturedContext := fun _ => True
  otherValues := fun _ => True
  registeredHoles := fun _ => True
  checkedIncidences := fun _ => True
  receiptPrecondition := fun _ _ => True
  actualTypedPath := fun _ _ => True
  actualContext := fun _ _ => True
  execute := fun _ _ _ => True
  observationGuards := fun row =>
    ⟨row.interface = false, True, True, True, True, True, True, True, True, True⟩
  traceForm := fun row => .pureReturn (value row.event)
  observationFields := fun _ => .guard True
  checkedObservation := fun _ _ => .guard True
  worldGuards := fun _ => ⟨True, True, True, True⟩
  installedCount := fun _ => 0
  installed := fun _ _ => none
  alias := fun _ _ _ => False
  capture := fun _ _ _ => none
  captureValue := fun _ _ _ => none
  sharedPosition := fun _ _ _ => False
  witnessAt := fun _ _ => ()
  carrierGuards := fun _ => ⟨True, True, True, True, True⟩
  carrierCaptures := fun _ => .guard True
  demand := fun _ _ => True
  force := fun _ _ _ => False
  forceIncidence := fun _ _ _ => True

/-- A single simultaneous candidate, with ALL events, providers, admitted
challenges and executions. Bad trace membership is never put in the candidate. -/
def candidate : Family sorts
  | .trace row => row.interface = false
  | _ => True

theorem candidate_postfixed : candidate.Le (Phi inputs candidate) := by
  intro query member
  cases query with
  | value row =>
    refine ⟨⟨⟨(), trivial⟩, ?_⟩, ?_⟩
    · intro provider actual
      exact ⟨⟨trivial, trivial, trivial, trivial, trivial⟩, trivial,
        fun challenge domain => ⟨⟨trivial, trivial, trivial, trivial⟩, fun raw executed => trivial⟩⟩
    · intro later compatible
      trivial
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
      trivial, trivial, trivial⟩, trivial, ⟨rfl, trivial⟩, trivial⟩
  | carrier row =>
    exact ⟨trivial, ⟨trivial, trivial, trivial, trivial, trivial⟩, trivial, trivial,
      (fun event demand => ⟨trivial, fun raw impossible => impossible.elim⟩),
      (fun later compatible => trivial)⟩

theorem candidate_meaning : candidate.Le (Meaning inputs) :=
  greatest_coinduct (Phi inputs) candidate candidate_postfixed

theorem all_values (row : ValueRow sorts) : Meaning inputs (.value row) :=
  candidate_meaning _ trivial

theorem callee_trace (raw : RawObservation sorts) :
    Meaning inputs (.trace (raw.atInterface false)) := candidate_meaning _ rfl

theorem no_target_trace (raw : RawObservation sorts) :
    ¬ Meaning inputs (.trace (raw.atInterface true)) := by
  intro member
  have body := (meaning_iff inputs _).mp member
  have impossible : true = false := body.2.1.1
  cases impossible

def noLeaves : Positive sorts → Positive sorts → Prop := fun _ _ => False

def declarations : PrimitiveDeclarations :=
  ⟨fun use => if use = .reify then 1 else 0⟩

def returned (request : Request) (birth : Event sorts) :
    BoundReturn sorts request.original.position := ⟨⟨(), birth⟩, value birth, ()⟩

def calRetSignature (request : Request) (birth : Event sorts) : Signature sorts :=
  (primitiveGoal request declarations .calRet (returnedOperands (returned request birth))).signature

def entry (request : Request) (birth : Event sorts) : GuardDeclaration sorts :=
  ⟨calRetSignature request birth, .truth, .registered (calRetSignature request birth)⟩

/-- This registry authenticates only its single abstract CalRet law. Its source
Key has NOT been authenticated. In particular it has no reify inventory. -/
def registry (request : Request) (birth : Event sorts) : GuardRegistry inputs where
  original := fun signature => signature.declaration = 0
  declaration := fun _ => some (entry request birth)
  law := by
    intro identifier declaration found before
    have same : entry request birth = declaration := Option.some.inj found
    subst declaration
    rfl

noncomputable def resolution (request : Request) (birth : Event sorts) :
    Resolution inputs (registry request birth) := by
  classical
  intro goal
  exact if same : goal.signature = calRetSignature request birth then
    some ⟨0, entry request birth, rfl, same.symm, congrArg Guard.registered same.symm⟩
    else none

noncomputable def calRetInput (request : Request) (birth : Event sorts) :
    PrimitiveInput inputs (registry request birth) (resolution request birth)
      (primitiveGoal request declarations .calRet (returnedOperands (returned request birth))) := by
  classical
  refine ⟨⟨0, entry request birth, rfl, rfl, rfl⟩, ?_, trivial⟩
  simp only [resolution, calRetSignature, ↓reduceDIte]

/-- ALL fields of the current R331 record are constructed. Its argument
premise is empty because this ABSTRACT registry declares no reify occurrence.
That omission is stated explicitly and prevents a source-qualified claim. -/
noncomputable def returnInputs (request : Request) (birth : Event sorts) :
    ReturnInputs inputs (registry request birth) (resolution request birth) noLeaves
      request declarations false false (returned request birth) where
  calleeMember := callee_trace _
  form := rfl
  checked := .identity _
  functionSort := rfl
  actual := trivial
  calRet := calRetInput request birth
  argument := by
    intro carrier registered
    have impossible : (1 : Nat) = 0 := registered
    cases impossible

theorem return_inputs_available (request : Request) (birth : Event sorts) :
    Nonempty (ReturnInputs inputs (registry request birth) (resolution request birth) noLeaves
      request declarations false false (returned request birth)) := ⟨returnInputs request birth⟩

/-- Same returned provider at EVERY independent live world. Every actual
challenge and raw execution is admitted. This discriminator uses pureReturn
trace forms; none of these hypotheses yields the unrelated target trace. -/
theorem receiver_obstruction (request : Request) (birth current : Event sorts)
    (challenge : Challenge (receiverRow (returned request birth) false current))
    (raw : RawObservation sorts) :
    (receiverDevelopments inputs (returned request birth) false current).Holds (Meaning inputs) ∧
    CheckedDomain inputs challenge ∧ inputs.execute (returned request birth).provider challenge.input raw ∧
    (inputs.checkedObservation challenge raw).Holds (Meaning inputs) ∧
    ¬ Meaning inputs (.trace (raw.atInterface true)) := by
  refine ⟨?_, ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩, trivial, trivial,
    no_target_trace raw⟩
  exact all_live_receiver_developments inputs (registry request birth) (resolution request birth)
    noLeaves (fun _ _ impossible => impossible.elim) request declarations false false
    (returned request birth) (returnInputs request birth) current trivial

/-- In this full upstream instance no finite projection can be built using
original logical/guard/fold/function constructors and ZERO recursive leaves. -/
theorem no_finite_projection (request : Request) (birth current : Event sorts)
    (challenge : Challenge (receiverRow (returned request birth) false current))
    (raw : RawObservation sorts) :
    ¬ Proof inputs (registry request birth) noLeaves (inputs.checkedObservation challenge raw)
      (.field (.trace (raw.atInterface true))) := by
  intro projection
  exact no_target_trace raw (Proof.sound inputs (registry request birth)
    (fun _ _ impossible => impossible.elim) projection trivial)

end AbstractInputObstruction
end YulangClosure.OriginalReceiverProjectionR340
