import YulangClosure.OriginalSourceGeneration
import YulangClosure.SourceFunctionMembership
import YulangClosure.NativeDictionaryDenotation

/-!
The selected positive immutable interpretation, not a new production model.
Authority: contextual-function-membership-definition §§2–3, selecting
call-semantic-input-realization §§2–4 and simultaneous-immutable-root-
introduction §§2–5. The complete original independent domains and immediate
primitive guards remain inputs, as that selection expressly requires.

This module constructs the four-component operator and its greatest fixed
point. It never assumes monotonicity, a completed world, a source derivation,
a successful solver, or an arbitrary full-body certificate as an operator
field. Every recursive occurrence is exposed as a positive indexed premise.
No W/Z grammar, mutable State law or foreign descriptor interpretation is
invented. The final source application has its exact local clause scope.
-/
namespace YulangClosure.OriginalSourceInterpretation

/-- Original semantic sorts. They are not identified with the effect-erased
paper execution sorts or with endpoint IDs. -/
structure Sorts where
  Valuation : Type
  ConstructorGraph : Type
  Dependencies : Type
  SourceGraph : Type
  BinderTree : Type
  Assignment : Type
  History : Type
  Configuration : Type
  JointWitness : Type
  Scope : Type
  Authority : Type
  Incidence : Type
  Dictionary : Type
  Descriptor : Type
  Interface : Type
  Value : Type
  Provider : Type
  Root : Type
  Carrier : Type
  Observation : Type
  Context : Type
  Continuation : Type
  Receipt : Type
  TypedPath : Type
  Consumer : Type
  WitnessPosition : Type
  WitnessValue : Type

/-- One original xi and source binder graph. All components travel together. -/
structure Fiber (s : Sorts) where
  nu : s.Valuation
  K : s.ConstructorGraph
  D : s.Dependencies
  source : s.SourceGraph
  binders : s.BinderTree

/-- eta0 is fixed source assignment data; current configuration and current
witness are event fields, not snapshots frozen at closure creation. -/
structure Event (s : Sorts) where
  fiber : Fiber s
  eta0 : s.Assignment
  eta : s.Assignment
  history : s.History
  current : s.Configuration
  witness : s.JointWitness
  scope : s.Scope
  authority : s.Authority
  incidence : s.Incidence
  dictionary : s.Dictionary

structure ValueRow (s : Sorts) where
  descriptor : s.Descriptor
  value : s.Value
  root : s.Root
  event : Event s

structure CarrierRow (s : Sorts) where
  interface : s.Interface
  carrier : s.Carrier
  root : s.Root
  event : Event s

structure RawObservation (s : Sorts) where
  observation : s.Observation
  event : Event s

structure TraceRow (s : Sorts) where
  interface : s.Interface
  observation : s.Observation
  event : Event s

def RawObservation.atInterface (raw : RawObservation s) (interface : s.Interface) : TraceRow s :=
  ⟨interface, raw.observation, raw.event⟩

def TraceRow.raw (row : TraceRow s) : RawObservation s := ⟨row.observation, row.event⟩

theorem raw_of_checked_observation (raw : RawObservation s) (interface : s.Interface) :
    (raw.atInterface interface).raw = raw := rfl

structure CarrierInput (s : Sorts) where
  carrier : s.Carrier
  root : s.Root
  event : Event s

def CarrierRow.input (row : CarrierRow s) : CarrierInput s := ⟨row.carrier, row.root, row.event⟩

abbrev WorldRow (s : Sorts) := Event s

def ValueRow.atEvent (row : ValueRow s) (event : Event s) : ValueRow s := {row with event := event}
def ValueRow.withDescriptor (row : ValueRow s) (descriptor : s.Descriptor) : ValueRow s :=
  {row with descriptor := descriptor}
def CarrierRow.atEvent (row : CarrierRow s) (event : Event s) : CarrierRow s := {row with event := event}

/-- Every checked challenge is indexed by its actual same callable tuple.
No candidate validity or provider-output premise is stored here. -/
structure Challenge {s : Sorts} (row : ValueRow s) where
  context : s.Context
  continuation : s.Continuation
  carrier : s.Carrier
  carrierRoot : s.Root
  carrierView : s.Interface
  receipt : s.Receipt
  path : s.TypedPath
  consumer : s.Consumer
  incidence : s.Incidence

def Challenge.carrierRow {s : Sorts} {row : ValueRow s} (d : Challenge row)
    (interface : s.Interface) : CarrierRow s :=
  ⟨interface, d.carrier, d.carrierRoot, row.event⟩

/-- The complete actual invocation operands, independent of the checked
Function description. All runtime/receipt/context fields remain present. -/
structure CallInput (s : Sorts) where
  value : s.Value
  valueRoot : s.Root
  event : Event s
  context : s.Context
  continuation : s.Continuation
  carrier : s.Carrier
  carrierRoot : s.Root
  carrierView : s.Interface
  receipt : s.Receipt
  path : s.TypedPath
  consumer : s.Consumer
  incidence : s.Incidence

def Challenge.input {s : Sorts} {row : ValueRow s} (d : Challenge row) : CallInput s :=
  ⟨row.value, row.root, row.event, d.context, d.continuation, d.carrier,
    d.carrierRoot, d.carrierView, d.receipt, d.path, d.consumer, d.incidence⟩

def Challenge.retarget {s : Sorts} {row : ValueRow s} (d : Challenge row)
    (descriptor : s.Descriptor) : Challenge (row.withDescriptor descriptor) :=
  ⟨d.context, d.continuation, d.carrier, d.carrierRoot, d.carrierView,
    d.receipt, d.path, d.consumer, d.incidence⟩

theorem retarget_keeps_actual_input {s : Sorts} {row : ValueRow s}
    (d : Challenge row) (descriptor : s.Descriptor) :
    (d.retarget descriptor).input = d.input := rfl

inductive Installed (s : Sorts) where
  | value (descriptor : s.Descriptor) (value : s.Value) (root : s.Root)
  | carrier (interface : s.Interface) (carrier : s.Carrier) (root : s.Root)

inductive Query (s : Sorts) where
  | value (row : ValueRow s)
  | world (row : WorldRow s)
  | trace (row : TraceRow s)
  | carrier (row : CarrierRow s)

abbrev Family (s : Sorts) := Query s → Prop

def Family.Le (first second : Family s) : Prop := ∀ q, first q → second q

def Family.join (first second : Family s) : Family s := fun q => first q ∨ second q

/-- A positive family of original typed fields. There is no fixed finite
cardinality or bounded future-history restriction. Each field keeps its full
original tuple; this is not a test of candidate validity. -/
structure Requirements (s : Sorts) where
  value : ValueRow s → Prop
  world : WorldRow s → Prop
  trace : TraceRow s → Prop
  carrier : CarrierRow s → Prop

def Requirements.Holds (requirements : Requirements s) (Z : Family s) : Prop :=
  (∀ row, requirements.value row → Z (.value row)) ∧
  (∀ row, requirements.world row → Z (.world row)) ∧
  (∀ row, requirements.trace row → Z (.trace row)) ∧
  (∀ row, requirements.carrier row → Z (.carrier row))

def Requirements.empty : Requirements s :=
  ⟨fun _ => False, fun _ => False, fun _ => False, fun _ => False⟩

theorem requirements_mono {first second : Family s} (included : first.Le second)
    (requirements : Requirements s) (proof : requirements.Holds first) :
    requirements.Holds second := by
  rcases proof with ⟨hv, hw, ht, hc⟩
  exact ⟨fun row h => included _ (hv row h), fun row h => included _ (hw row h),
    fun row h => included _ (ht row h), fun row h => included _ (hc row h)⟩

/-- Original positive logical scopes, including existential evidence whose
choice may depend on all preceding challenge/event fields. Domains are fixed
before the candidate relation. There is no negative or inclusion-oracle case. -/
inductive Positive (s : Sorts) : Type 1 where
  | guard (fact : Prop)
  | field (query : Query s)
  | both (left right : Positive s)
  | either (left right : Positive s)
  | all (Domain : Type) (body : Domain → Positive s)
  | existsE (Domain : Type) (body : Domain → Positive s)

def Positive.Holds (clause : Positive s) (Z : Family s) : Prop :=
  match clause with
  | .guard fact => fact
  | .field query => Z query
  | .both left right => left.Holds Z ∧ right.Holds Z
  | .either left right => left.Holds Z ∨ right.Holds Z
  | .all Domain body => ∀ value : Domain, (body value).Holds Z
  | .existsE Domain body => ∃ value : Domain, (body value).Holds Z

/-- The usual descriptor-indexed observation obligation. The same actual
raw observation can be checked at distinct recursive result interfaces. -/
def checkedTrace (raw : RawObservation s) (interface : s.Interface) : Positive s :=
  .field (.trace (raw.atInterface interface))

theorem checked_trace_iff (raw : RawObservation s) (interface : s.Interface) (Z : Family s) :
    (checkedTrace raw interface).Holds Z ↔ Z (.trace (raw.atInterface interface)) := Iff.rfl

/-- A candidate validating one checked return need not validate another.
Raw execution and event identity remain identical in this separation. -/
theorem different_checked_trace_requirements (raw : RawObservation s)
    (first second : s.Interface) (different : first ≠ second) :
    ∃ Z : Family s, (checkedTrace raw first).Holds Z ∧
      ¬ (checkedTrace raw second).Holds Z := by
  refine ⟨fun query => query = .trace (raw.atInterface first), rfl, ?_⟩
  intro same
  have rows : raw.atInterface second = raw.atInterface first := Query.trace.inj same
  exact different (congrArg TraceRow.interface rows).symm

theorem positive_mono {first second : Family s} (included : first.Le second)
    (clause : Positive s) (valid : clause.Holds first) : clause.Holds second := by
  induction clause with
  | guard fact => exact valid
  | field query => exact included query valid
  | both left right leftIH rightIH => exact ⟨leftIH valid.1, rightIH valid.2⟩
  | either left right leftIH rightIH =>
      rcases valid with leftProof | rightProof
      · exact Or.inl (leftIH leftProof)
      · exact Or.inr (rightIH rightProof)
  | all Domain body ih => exact fun value => ih value (valid value)
  | existsE Domain body ih =>
      obtain ⟨value, proof⟩ := valid
      exact ⟨value, ih value proof⟩

/-- The four independent PhiW guard groups are explicit, before installed
binding validity. Alias/capture/shared-witness equations are computed below. -/
structure WorldGuards where
  registry : Prop
  scope : Prop
  currentAuthority : Prop
  incidence : Prop

def WorldGuards.Valid (guards : WorldGuards) : Prop :=
  guards.registry ∧ guards.scope ∧ guards.currentAuthority ∧ guards.incidence

structure FunctionGuards where
  formation : Prop
  roleAndEntry : Prop
  profile : Prop
  scope : Prop
  incidence : Prop

def FunctionGuards.Valid (guards : FunctionGuards) : Prop :=
  guards.formation ∧ guards.roleAndEntry ∧ guards.profile ∧ guards.scope ∧ guards.incidence

/-- All independent P_F/phase guards, including actual typed operation data,
remain visible. Positive hereditary fields are handled separately by PhiT. -/
structure ObservationGuards where
  descriptor : Prop
  guarantee : Prop
  request : Prop
  response : Prop
  rawHandle : Prop
  phase : Prop
  scope : Prop
  currentAuthority : Prop
  incidence : Prop
  jointConstraints : Prop

def ObservationGuards.Valid (guards : ObservationGuards) : Prop :=
  guards.descriptor ∧ guards.guarantee ∧ guards.request ∧ guards.response ∧
  guards.rawHandle ∧ guards.phase ∧ guards.scope ∧ guards.currentAuthority ∧
  guards.incidence ∧ guards.jointConstraints

structure CarrierGuards where
  inertFormation : Prop
  license : Prop
  view : Prop
  scope : Prop
  incidence : Prop

def CarrierGuards.Valid (guards : CarrierGuards) : Prop :=
  guards.inertFormation ∧ guards.license ∧ guards.view ∧ guards.scope ∧ guards.incidence

inductive TraceForm (s : Sorts) where
  | pureReturn (value : ValueRow s)
  | unfinished

inductive ValueForm where
  | ground | fixedExternal | structural | function
  deriving DecidableEq

/-- Independently fixed original input relations of the adopted operator.
None takes a candidate Family, source judgment, generated constraints, solver
result or Q. Ordinary Function and carrier rows cannot be disguised as fixed
external leaves: their descriptor registration selects their own case.

The original interpretation of these input sorts/relations is still required.
In particular this record does not choose an exhaustive W/Z or State model.
-/
structure Inputs (s : Sorts) where
  compatible : Event s → Event s → Prop
  eventCoherent : Event s → Prop
  valueForm : s.Descriptor → ValueForm
  ground : ValueRow s → Prop
  fixedExternal : ValueRow s → Prop
  structuralGuard : ValueRow s → Prop
  structuralFields : ValueRow s → Positive s
  actual : s.Value → s.Root → s.Provider → Prop
  functionGuards : ValueRow s → s.Provider → FunctionGuards
  capturedFields : ValueRow s → s.Provider → Positive s
  checkedInlet : s.Descriptor → s.Interface
  actualInlet : s.Provider → s.Interface
  carrierAccepted : CarrierRow s → Prop
  puncturedContext : {row : ValueRow s} → Challenge row → Prop
  otherValues : {row : ValueRow s} → Challenge row → Prop
  registeredHoles : {row : ValueRow s} → Challenge row → Prop
  checkedIncidences : {row : ValueRow s} → Challenge row → Prop
  receiptPrecondition : s.Provider → CallInput s → Prop
  actualTypedPath : s.Provider → CallInput s → Prop
  actualContext : s.Provider → CallInput s → Prop
  /-- Every raw actual zero/admin/pending/complete observation and admitted
  development; never filtered by P_F or by tested membership. -/
  execute : s.Provider → CallInput s → RawObservation s → Prop
  observationGuards : TraceRow s → ObservationGuards
  traceForm : TraceRow s → TraceForm s
  observationFields : TraceRow s → Positive s
  /-- Original complete positive P_F clause at the checked challenge and
  fixed raw observation. Its recursive descriptor obligations may change
  with F; they are not hidden in a candidate-independent incidence guard.
  All independent non-source alternatives and evidence scopes remain. -/
  checkedObservation : {row : ValueRow s} → Challenge row → RawObservation s → Positive s
  worldGuards : WorldRow s → WorldGuards
  installedCount : WorldRow s → Nat
  installed : WorldRow s → Nat → Option (Installed s)
  alias : WorldRow s → Nat → Nat → Prop
  capture : WorldRow s → s.Provider → Nat → Option Nat
  captureValue : WorldRow s → s.Provider → Nat → Option (Installed s)
  sharedPosition : WorldRow s → s.WitnessPosition → s.WitnessPosition → Prop
  witnessAt : WorldRow s → s.WitnessPosition → s.WitnessValue
  carrierGuards : CarrierRow s → CarrierGuards
  carrierCaptures : CarrierRow s → Positive s
  demand : CarrierRow s → Event s → Prop
  force : CarrierInput s → Event s → RawObservation s → Prop
  /-- Descriptor-native finite observation readout of a designated Force;
  this is incidence, not a promise that the returned row is valid. -/
  forceIncidence : CarrierRow s → Event s → RawObservation s → Prop

/-- The independent checked challenge constructor, before provider acceptance.
Its context/carrier/registration data all refer to one row and current event. -/
def CheckedDomain (inputs : Inputs s) {row : ValueRow s} (d : Challenge row) : Prop :=
  inputs.eventCoherent row.event ∧ inputs.puncturedContext d ∧ inputs.otherValues d ∧
  inputs.registeredHoles d ∧ inputs.checkedIncidences d ∧
  inputs.carrierAccepted (d.carrierRow (inputs.checkedInlet row.descriptor))

def ActualAdm (inputs : Inputs s) {row : ValueRow s}
    (provider : s.Provider) (d : Challenge row) : Prop :=
  inputs.carrierAccepted (d.carrierRow (inputs.actualInlet provider)) ∧
  inputs.receiptPrecondition provider d.input ∧ inputs.actualTypedPath provider d.input ∧
  inputs.actualContext provider d.input

def Installed.Valid (Z : Family s) (event : Event s) : Installed s → Prop
  | .value descriptor actualValue root => Z (.value ⟨descriptor, actualValue, root, event⟩)
  | .carrier interface actualCarrier root => Z (.carrier ⟨interface, actualCarrier, root, event⟩)

def AliasesAgree (inputs : Inputs s) (event : Event s) : Prop :=
  ∀ a b, inputs.alias event a b → ∃ binding,
    inputs.installed event a = some binding ∧ inputs.installed event b = some binding

def CapturesAgree (inputs : Inputs s) (event : Event s) : Prop :=
  ∀ provider name address, inputs.capture event provider name = some address →
    address < inputs.installedCount event ∧ ∃ binding,
      inputs.installed event address = some binding ∧ inputs.captureValue event provider name = some binding

def WitnessesAgree (inputs : Inputs s) (event : Event s) : Prop :=
  ∀ a b, inputs.sharedPosition event a b → inputs.witnessAt event a = inputs.witnessAt event b

/-- Complete PhiW, not merely AllInstalled: all independent joint guards,
all installed values/carriers and all alias/capture/shared-field equations. -/
def PhiW (inputs : Inputs s) (Z : Family s) (event : WorldRow s) : Prop :=
  inputs.eventCoherent event ∧ (inputs.worldGuards event).Valid ∧
  AliasesAgree inputs event ∧ CapturesAgree inputs event ∧ WitnessesAgree inputs event ∧
  ∀ i binding, inputs.installed event i = some binding → binding.Valid Z event

def PhiT (inputs : Inputs s) (Z : Family s) (row : TraceRow s) : Prop :=
  inputs.eventCoherent row.event ∧ (inputs.observationGuards row).Valid ∧
    Z (.world row.event) ∧
    (match inputs.traceForm row with
      | .pureReturn value => value.event = row.event ∧ Z (.value value)
      | .unfinished => True) ∧
    (inputs.observationFields row).Holds Z

def ObservationMem (inputs : Inputs s) (Z : Family s) {row : ValueRow s}
    (d : Challenge row) (observation : RawObservation s) : Prop :=
  (inputs.checkedObservation d observation).Holds Z

def FunctionAt (inputs : Inputs s) (Z : Family s) (row : ValueRow s) : Prop :=
  (∃ provider, inputs.actual row.value row.root provider) ∧
  ∀ provider, inputs.actual row.value row.root provider →
    (inputs.functionGuards row provider).Valid ∧
    (inputs.capturedFields row provider).Holds Z ∧
    ∀ d : Challenge row, CheckedDomain inputs d →
      ActualAdm inputs provider d ∧
        ∀ observation, inputs.execute provider d.input observation →
          ObservationMem inputs Z d observation

/-- Hereditary closure uses every unchanged independent compatible event,
with that event's live configuration. It never snapshots a maker activation. -/
def PhiV (inputs : Inputs s) (Z : Family s) (row : ValueRow s) : Prop :=
  (match inputs.valueForm row.descriptor with
    | .ground => inputs.ground row
    | .fixedExternal => inputs.fixedExternal row
    | .structural => inputs.structuralGuard row ∧ (inputs.structuralFields row).Holds Z
    | .function => FunctionAt inputs Z row) ∧
  ∀ later, inputs.compatible row.event later → Z (.value (row.atEvent later))

def PhiCar (inputs : Inputs s) (Z : Family s) (row : CarrierRow s) : Prop :=
  inputs.eventCoherent row.event ∧ (inputs.carrierGuards row).Valid ∧
  Z (.world row.event) ∧ (inputs.carrierCaptures row).Holds Z ∧
  (∀ event, inputs.demand row event → inputs.compatible row.event event ∧
    ∀ observation, inputs.force row.input event observation →
      inputs.forceIncidence row event observation ∧
        Z (.trace (observation.atInterface row.interface))) ∧
  ∀ later, inputs.compatible row.event later → Z (.carrier (row.atEvent later))

def Phi (inputs : Inputs s) (Z : Family s) : Family s
  | .value row => PhiV inputs Z row
  | .world row => PhiW inputs Z row
  | .trace row => PhiT inputs Z row
  | .carrier row => PhiCar inputs Z row

private theorem installed_mono {first second : Family s} (included : first.Le second)
    (event : Event s) (binding : Installed s) (valid : binding.Valid first event) :
    binding.Valid second event := by
  cases binding <;> exact included _ valid

theorem phiW_mono (inputs : Inputs s) {first second : Family s}
    (included : first.Le second) (event : WorldRow s) (valid : PhiW inputs first event) :
    PhiW inputs second event := by
  rcases valid with ⟨coherent, guards, aliases, captures, witnesses, bindings⟩
  exact ⟨coherent, guards, aliases, captures, witnesses,
    fun i binding found => installed_mono included event binding (bindings i binding found)⟩

theorem phiT_mono (inputs : Inputs s) {first second : Family s}
    (included : first.Le second) (row : TraceRow s) (valid : PhiT inputs first row) :
    PhiT inputs second row := by
  refine ⟨valid.1, valid.2.1, included _ valid.2.2.1, ?_,
    positive_mono included _ valid.2.2.2.2⟩
  have shape := valid.2.2.2.1
  cases form : inputs.traceForm row with
  | pureReturn value =>
      simp only [form] at shape ⊢
      exact ⟨shape.1, included _ shape.2⟩
  | unfinished => trivial

theorem functionAt_mono (inputs : Inputs s) {first second : Family s}
    (included : first.Le second) (row : ValueRow s) (valid : FunctionAt inputs first row) :
    FunctionAt inputs second row := by
  refine ⟨valid.1, ?_⟩
  intro provider actual
  rcases valid.2 provider actual with ⟨guards, captures, challenges⟩
  refine ⟨guards, positive_mono included _ captures, ?_⟩
  intro challenge admitted
  rcases challenges challenge admitted with ⟨accepted, observations⟩
  exact ⟨accepted, fun observation executed =>
    positive_mono included _ (observations observation executed)⟩

theorem phiV_mono (inputs : Inputs s) {first second : Family s}
    (included : first.Le second) (row : ValueRow s) (valid : PhiV inputs first row) :
    PhiV inputs second row := by
  refine ⟨?_, fun later compatible => included _ (valid.2 later compatible)⟩
  cases form : inputs.valueForm row.descriptor with
  | ground => simpa only [form] using valid.1
  | fixedExternal => simpa only [form] using valid.1
  | structural =>
      have old := valid.1
      simp only [form] at old ⊢
      exact ⟨old.1, positive_mono included _ old.2⟩
  | function =>
      have old := valid.1
      simp only [form] at old ⊢
      exact functionAt_mono inputs included row old

theorem phiCar_mono (inputs : Inputs s) {first second : Family s}
    (included : first.Le second) (row : CarrierRow s) (valid : PhiCar inputs first row) :
    PhiCar inputs second row := by
  rcases valid with ⟨coherent, guards, world, captures, demands, future⟩
  refine ⟨coherent, guards, included _ world, positive_mono included _ captures, ?_,
    fun later compatible => included _ (future later compatible)⟩
  intro event demand
  exact ⟨(demands event demand).1, fun observation executed =>
    ⟨((demands event demand).2 observation executed).1,
      included _ ((demands event demand).2 observation executed).2⟩⟩

theorem phi_monotone (inputs : Inputs s) {first second : Family s}
    (included : first.Le second) : (Phi inputs first).Le (Phi inputs second) := by
  intro query valid
  cases query with
  | value row => exact phiV_mono inputs included row valid
  | world row => exact phiW_mono inputs included row valid
  | trace row => exact phiT_mono inputs included row valid
  | carrier row => exact phiCar_mono inputs included row valid

/-- Union of all postfixed families. This is an actual greatest-fixed-point
construction; no fixed-point, fold/unfold or coinduction axiom is supplied. -/
def Greatest (operator : Family s → Family s) : Family s :=
  fun query => ∃ candidate : Family s, candidate.Le (operator candidate) ∧ candidate query

theorem greatest_coinduct (operator : Family s → Family s) (candidate : Family s)
    (postfixed : candidate.Le (operator candidate)) : candidate.Le (Greatest operator) :=
  fun _ proof => ⟨candidate, postfixed, proof⟩

theorem greatest_unfold (operator : Family s → Family s)
    (monotone : ∀ {first second}, first.Le second → (operator first).Le (operator second)) :
    (Greatest operator).Le (operator (Greatest operator)) := by
  rintro query ⟨candidate, postfixed, member⟩
  exact monotone (greatest_coinduct operator candidate postfixed) query (postfixed query member)

theorem greatest_fold (operator : Family s → Family s)
    (monotone : ∀ {first second}, first.Le second → (operator first).Le (operator second)) :
    (operator (Greatest operator)).Le (Greatest operator) := by
  apply greatest_coinduct
  exact monotone (greatest_unfold operator monotone)

def Meaning (inputs : Inputs s) : Family s := Greatest (Phi inputs)

theorem meaning_iff (inputs : Inputs s) (query : Query s) :
    Meaning inputs query ↔ Phi inputs (Meaning inputs) query :=
  ⟨greatest_unfold _ (phi_monotone inputs) query, greatest_fold _ (phi_monotone inputs) query⟩


/-- Fixed declared assumptions occupy only exact Value tuples. In particular
there is no world, carrier, observation, authority or guard hole. -/
def ValueHoles (holes : ValueRow s → Prop) : Family s
  | .value row => holes row
  | _ => False

def RelativePhi (inputs : Inputs s) (holes : ValueRow s → Prop) (Z : Family s) : Family s :=
  (Phi inputs Z).join (ValueHoles holes)

def Background (inputs : Inputs s) (holes : ValueRow s → Prop) : Family s :=
  Greatest (RelativePhi inputs holes)

theorem relative_monotone (inputs : Inputs s) (holes : ValueRow s → Prop)
    {first second : Family s} (included : first.Le second) :
    (RelativePhi inputs holes first).Le (RelativePhi inputs holes second) := by
  intro query valid
  rcases valid with fromPhi | hole
  · exact Or.inl (phi_monotone inputs included query fromPhi)
  · exact Or.inr hole

/-- The adopted background lift, proved from the actual four-component
unfolding. It does not assume a full background embedding or drop any fields. -/
theorem background_lift (inputs : Inputs s) (holes : ValueRow s → Prop)
    (candidate : Family s)
    (included : (Background inputs holes).Le candidate)
    (replace : ∀ row, holes row → PhiV inputs candidate row) :
    (Background inputs holes).Le (Phi inputs candidate) := by
  intro query member
  have opened := greatest_unfold (RelativePhi inputs holes) (relative_monotone inputs holes) query member
  rcases opened with original | hole
  · exact phi_monotone inputs included query original
  · cases query with
    | value row => exact replace row hole
    | world row => cases hole
    | trace row => cases hole
    | carrier row => cases hole

/-- Actual added source cases, plus exact replacement of the declared value
holes, jointly introduce all four original components. -/
theorem simultaneous_introduction (inputs : Inputs s) (holes : ValueRow s → Prop)
    (added : Family s)
    (replace : ∀ row, holes row → PhiV inputs ((Background inputs holes).join added) row)
    (sourceCases : added.Le (Phi inputs ((Background inputs holes).join added))) :
    ((Background inputs holes).join added).Le (Meaning inputs) := by
  apply greatest_coinduct
  intro query member
  rcases member with background | source
  · exact background_lift inputs holes _ (fun _ proof => Or.inl proof) replace query background
  · exact sourceCases query source

/-- Every declaration assumption is present in the independent background,
but replacing it by an original constructor remains a separate proof. -/
theorem background_value_hole (inputs : Inputs s) (holes : ValueRow s → Prop)
    (row : ValueRow s) (hole : holes row) : Background inputs holes (.value row) := by
  apply greatest_fold (RelativePhi inputs holes) (relative_monotone inputs holes)
  exact Or.inr hole

theorem world_unfold (inputs : Inputs s) (event : WorldRow s) :
    Meaning inputs (.world event) ↔ PhiW inputs (Meaning inputs) event :=
  meaning_iff inputs (.world event)

theorem world_installed (inputs : Inputs s) (event : WorldRow s)
    (valid : Meaning inputs (.world event)) (i : Nat) (binding : Installed s)
    (found : inputs.installed event i = some binding) :
    binding.Valid (Meaning inputs) event :=
  ((world_unfold inputs event).mp valid).2.2.2.2.2 i binding found

theorem value_restrict (inputs : Inputs s) (row : ValueRow s)
    (valid : Meaning inputs (.value row)) (later : Event s)
    (compatible : inputs.compatible row.event later) :
    Meaning inputs (.value (row.atEvent later)) :=
  ((meaning_iff inputs (.value row)).mp valid).2 later compatible

theorem carrier_restrict (inputs : Inputs s) (row : CarrierRow s)
    (valid : Meaning inputs (.carrier row)) (later : Event s)
    (compatible : inputs.compatible row.event later) :
    Meaning inputs (.carrier (row.atEvent later)) :=
  ((meaning_iff inputs (.carrier row)).mp valid).2.2.2.2.2 later compatible

theorem installed_restrict (inputs : Inputs s) (binding : Installed s)
    (before after : Event s) (compatible : inputs.compatible before after)
    (valid : binding.Valid (Meaning inputs) before) :
    binding.Valid (Meaning inputs) after := by
  cases binding with
  | value descriptor actualValue root =>
      exact value_restrict inputs ⟨descriptor, actualValue, root, before⟩ valid after compatible
  | carrier interface actualCarrier root =>
      exact carrier_restrict inputs ⟨interface, actualCarrier, root, before⟩ valid after compatible

/-- A real immutable append constructs full world membership from the old
world, all independent new-event guard/equality facts, and the actual new
binding certificate. A completed target world is not a premise. -/
theorem immutable_rebind_world (inputs : Inputs s) (before after : Event s)
    (oldWorld : Meaning inputs (.world before))
    (compatible : inputs.compatible before after)
    (coherent : inputs.eventCoherent after) (guards : (inputs.worldGuards after).Valid)
    (aliases : AliasesAgree inputs after) (captures : CapturesAgree inputs after)
    (witnesses : WitnessesAgree inputs after)
    (oldCells : ∀ i, i ≠ inputs.installedCount before →
      inputs.installed after i = inputs.installed before i)
    (newBinding : Installed s)
    (newCell : inputs.installed after (inputs.installedCount before) = some newBinding)
    (newCertificate : newBinding.Valid (Meaning inputs) after) :
    Meaning inputs (.world after) := by
  apply (world_unfold inputs after).mpr
  refine ⟨coherent, guards, aliases, captures, witnesses, ?_⟩
  intro i binding found
  by_cases fresh : i = inputs.installedCount before
  · subst i
    have same : newBinding = binding := Option.some.inj (newCell.symm.trans found)
    simpa only [same] using newCertificate
  · have oldFound : inputs.installed before i = some binding :=
      (oldCells i fresh).symm.trans found
    exact installed_restrict inputs binding before after compatible
      (world_installed inputs before oldWorld i binding oldFound)

/-- Actual source Name projection keeps the installed value's descriptor,
value, root and live event. No new provider is selected by its checked type. -/
theorem immutable_name_value (inputs : Inputs s) (event : Event s)
    (world : Meaning inputs (.world event)) (address : Nat)
    (descriptor : s.Descriptor) (value : s.Value) (root : s.Root)
    (found : inputs.installed event address = some (.value descriptor value root)) :
    Meaning inputs (.value ⟨descriptor, value, root, event⟩) :=
  world_installed inputs event world address _ found

theorem return_observation_iff (inputs : Inputs s) (row : TraceRow s) (value : ValueRow s)
    (form : inputs.traceForm row = .pureReturn value) :
    Meaning inputs (.trace row) ↔
      inputs.eventCoherent row.event ∧ (inputs.observationGuards row).Valid ∧
      Meaning inputs (.world row.event) ∧
      (value.event = row.event ∧ Meaning inputs (.value value)) ∧
      (inputs.observationFields row).Holds (Meaning inputs) := by
  rw [meaning_iff]
  simp only [Phi, PhiT, form]

theorem name_return_observation (inputs : Inputs s) (event : Event s)
    (world : Meaning inputs (.world event)) (address : Nat)
    (descriptor : s.Descriptor) (value : s.Value) (root : s.Root)
    (found : inputs.installed event address = some (.value descriptor value root))
    (returned : TraceRow s) (sameEvent : returned.event = event)
    (form : inputs.traceForm returned = .pureReturn ⟨descriptor, value, root, event⟩)
    (guards : (inputs.observationGuards returned).Valid)
    (fields : (inputs.observationFields returned).Holds (Meaning inputs)) :
    Meaning inputs (.trace returned) := by
  apply (return_observation_iff inputs returned _ form).mpr
  have current := ((world_unfold inputs event).mp world).1
  refine ⟨?_, guards, ?_, ⟨sameEvent.symm, immutable_name_value inputs event world address _ _ _ found⟩, fields⟩
  · simpa only [sameEvent] using current
  · simpa only [sameEvent] using world

theorem carrier_observations (inputs : Inputs s) (row : CarrierRow s)
    (valid : Meaning inputs (.carrier row)) (event : Event s) (demand : inputs.demand row event)
    (observation : RawObservation s) (executed : inputs.force row.input event observation) :
    inputs.forceIncidence row event observation ∧
      Meaning inputs (.trace (observation.atInterface row.interface)) :=
  (((meaning_iff inputs (.carrier row)).mp valid).2.2.2.2.1 event demand).2 observation executed

/-- Same-provider elimination at a complete original checked challenge. All
actual decompositions are checked; no convenient alternative is chosen. -/
theorem function_challenge (inputs : Inputs s) (row : ValueRow s)
    (form : inputs.valueForm row.descriptor = .function)
    (valid : Meaning inputs (.value row)) (provider : s.Provider)
    (actual : inputs.actual row.value row.root provider)
    (challenge : Challenge row) (admitted : CheckedDomain inputs challenge) :
    ActualAdm inputs provider challenge ∧
      ∀ observation, inputs.execute provider challenge.input observation →
        ObservationMem inputs (Meaning inputs) challenge observation := by
  have function := ((meaning_iff inputs (.value row)).mp valid).1
  simp only [form] at function
  exact (function.2 provider actual).2.2 challenge admitted

/-- The source constructor's exact inlet equality supplies ActualAdm from
the same checked carrier certificate and original receipt/path/context inputs.
No Function membership, output behavior or completed Call proof is assumed. -/
theorem source_inlet_acceptance (inputs : Inputs s) (row : ValueRow s)
    (provider : s.Provider) (challenge : Challenge row)
    (admitted : CheckedDomain inputs challenge)
    (inlet : inputs.actualInlet provider = inputs.checkedInlet row.descriptor)
    (receipt : inputs.receiptPrecondition provider challenge.input)
    (path : inputs.actualTypedPath provider challenge.input)
    (context : inputs.actualContext provider challenge.input) :
    ActualAdm inputs provider challenge := by
  refine ⟨?_, receipt, path, context⟩
  simpa only [inlet] using admitted.2.2.2.2.2

/-- The whole same-callable Function comparison of selected Theorem F.
These are full domain/observation implications at one original tuple, not
scalar port inequalities or an oracle constructor of the source checker.
The observation premise transports the entire positive P_A[Z] to P_F[Z],
including distinct recursive result descriptors at the same raw observation;
it is not supplied here by metadata inclusion or by retargeting alone. -/
theorem same_provider_function_check (inputs : Inputs s) (Z : Family s)
    (checked : ValueRow s) (sourceDescriptor : s.Descriptor)
    (source : FunctionAt inputs Z (checked.withDescriptor sourceDescriptor))
    (guards : ∀ provider, inputs.actual checked.value checked.root provider →
      (inputs.functionGuards checked provider).Valid)
    (captures : ∀ provider, inputs.actual checked.value checked.root provider →
      (inputs.capturedFields checked provider).Holds Z)
    (domain : ∀ challenge : Challenge checked, CheckedDomain inputs challenge →
      CheckedDomain inputs (challenge.retarget sourceDescriptor))
    (observations : ∀ (challenge : Challenge checked), CheckedDomain inputs challenge →
      ∀ observation, ObservationMem inputs Z (challenge.retarget sourceDescriptor) observation →
        ObservationMem inputs Z challenge observation) :
    FunctionAt inputs Z checked := by
  refine ⟨source.1, ?_⟩
  intro provider actual
  refine ⟨guards provider actual, captures provider actual, ?_⟩
  intro challenge admitted
  have sourceProof := (source.2 provider actual).2.2
    (challenge.retarget sourceDescriptor) (domain challenge admitted)
  refine ⟨?_, ?_⟩
  · exact sourceProof.1
  · intro observation executed
    have observed := sourceProof.2 observation executed
    exact observations challenge admitted observation observed

/-- Checked pure Return readout requires the result certificate at that
checked interface. Changing the Function descriptor cannot silently keep the
old result obligation merely because actual execution was unchanged. -/
theorem checked_return_result (inputs : Inputs s) {row : ValueRow s}
    (challenge : Challenge row) (raw : RawObservation s) (interface : s.Interface)
    (readout : inputs.checkedObservation challenge raw = checkedTrace raw interface)
    (result : ValueRow s)
    (form : inputs.traceForm (raw.atInterface interface) = .pureReturn result)
    (valid : ObservationMem inputs (Meaning inputs) challenge raw) :
    result.event = raw.event ∧ Meaning inputs (.value result) := by
  have trace : Meaning inputs (.trace (raw.atInterface interface)) := by
    simpa only [ObservationMem, readout, checkedTrace, Positive.Holds] using valid
  have returned := (return_observation_iff inputs _ result form).mp trace
  exact returned.2.2.2.1

/-- Elimination of the same actual provider reaches the checked result's
recursive descriptor after every original admitted challenge and actual Return. -/
theorem function_return_result (inputs : Inputs s) (row : ValueRow s)
    (functionForm : inputs.valueForm row.descriptor = .function)
    (valid : Meaning inputs (.value row)) (provider : s.Provider)
    (actual : inputs.actual row.value row.root provider)
    (challenge : Challenge row) (admitted : CheckedDomain inputs challenge)
    (raw : RawObservation s) (executed : inputs.execute provider challenge.input raw)
    (interface : s.Interface)
    (readout : inputs.checkedObservation challenge raw = checkedTrace raw interface)
    (result : ValueRow s)
    (form : inputs.traceForm (raw.atInterface interface) = .pureReturn result) :
    result.event = raw.event ∧ Meaning inputs (.value result) :=
  checked_return_result inputs challenge raw interface readout result form
    ((function_challenge inputs row functionForm valid provider actual challenge admitted).2 raw executed)


/-- A local ground primitive law, independent of the recursive candidate.
It is an L1 hereditary primitive law, not a Function/body soundness premise. -/
structure GroundLaw (inputs : Inputs s) : Prop where
  hereditary : ∀ row, inputs.ground row → ∀ later, inputs.compatible row.event later →
    inputs.ground (row.atEvent later)

theorem ground_membership (inputs : Inputs s) (law : GroundLaw inputs)
    (row : ValueRow s) (form : inputs.valueForm row.descriptor = .ground)
    (ground : inputs.ground row) : Meaning inputs (.value row) := by
  let candidate : Family s := fun query => match query with
    | .value value => inputs.valueForm value.descriptor = .ground ∧ inputs.ground value
    | _ => False
  apply greatest_coinduct (Phi inputs) candidate ?_ (.value row) ⟨form, ground⟩
  intro query member
  cases query with
  | world event => cases member
  | trace trace => cases member
  | carrier carrier => cases member
  | value value =>
      rcases member with ⟨kind, primitive⟩
      refine ⟨?_, ?_⟩
      · simpa only [kind] using primitive
      · intro later compatible
        exact ⟨kind, law.hereditary value primitive later compatible⟩

/-- Raw semantic assignment at an actual source occurrence. Endpoints and
binding addresses are data, not source typing or recursive membership proofs. -/
structure SourceAssignment (s : Sorts) where
  event : Event s
  descriptor : OriginalSource.Endpoint → s.Descriptor
  value : OriginalSource.Endpoint → s.Value
  root : OriginalSource.Endpoint → s.Root
  binding : OriginalSource.Name → Option Nat

def SourceAssignment.row (assignment : SourceAssignment s) (site : OriginalSource.Site) : ValueRow s :=
  ⟨assignment.descriptor ⟨site, .finalRoot⟩, assignment.value ⟨site, .finalRoot⟩,
    assignment.root ⟨site, .finalRoot⟩, assignment.event⟩

/-- An authentic literal declaration's local relation, before recursive
membership. It fixes the original literal, descriptor, value and root. -/
abbrev LiteralDeclaration (s : Sorts) := OriginalSource.Literal → ValueRow s → Prop

def LiteralAtom (inputs : Inputs s) (declarations : LiteralDeclaration s)
    (assignment : SourceAssignment s) (atom : OriginalSource.Atom) : Prop :=
  ∃ literal, atom.literal = some literal ∧
    declarations literal (assignment.row atom.site) ∧
    inputs.valueForm (assignment.descriptor ⟨atom.site, .finalRoot⟩) = .ground ∧
    inputs.ground (assignment.row atom.site)

/-- Only the actual literal declaration constructor is interpreted here.
Every other source clause and all six other Kernel fields remain the supplied
original ones; no unsupported source form is defined false or removed. -/
def literalKernel (inputs : Inputs s) (declarations : LiteralDeclaration s)
    (original : OriginalSource.Kernel (SourceAssignment s))
    (sourceSite : OriginalSource.Site) (sourceLiteral : OriginalSource.Literal) :
    OriginalSource.Kernel (SourceAssignment s) :=
  { original with atom := fun environment atom =>
      if atom.kind = .literalDeclaration ∧ atom.site = sourceSite ∧ atom.literal = some sourceLiteral
      then LiteralAtom inputs declarations environment.root atom
      else original.atom environment atom }

/-- The concrete raw-lookup clause for an ordinary value formal. There is no
ValueMem, Meaning, body safety or desired source judgment in this atom. -/
def ValueNameAtom (inputs : Inputs s) (assignment : SourceAssignment s)
    (atom : OriginalSource.Atom) : Prop :=
  ∃ name address,
    atom.names = [name] ∧ assignment.binding name = some address ∧
    address < inputs.installedCount assignment.event ∧
    inputs.installed assignment.event address =
      some (.value (assignment.descriptor ⟨atom.site, .finalRoot⟩) (assignment.value ⟨atom.site, .finalRoot⟩) (assignment.root ⟨atom.site, .finalRoot⟩))

def valueFormalAtom (atom : OriginalSource.Atom) : Bool :=
  match atom.binding with
  | some binding => binding.kind == .formal && binding.entry == some .value
  | none => false

/-- This installs exactly the adopted ordinary-value-formal Name case.
Retained, published, imported-family and other original cases are untouched. -/
def nameKernel (inputs : Inputs s) (original : OriginalSource.Kernel (SourceAssignment s))
    (sourceSite : OriginalSource.Site) (sourceName : OriginalSource.Name) :
    OriginalSource.Kernel (SourceAssignment s) :=
  { original with atom := fun environment atom =>
      if atom.site = sourceSite ∧ atom.names = [sourceName] ∧
        (atom.kind = .resolvedSameBinding ∨ atom.kind = .computedFetchOnce) ∧ valueFormalAtom atom = true
      then ValueNameAtom inputs environment.root atom
      else original.atom environment atom }

def formalContext (name : OriginalSource.Name) (owner : OriginalSource.Site) : OriginalSource.Context :=
  [{name := name, owner := owner, kind := .formal, entry := some .value}]

/-- Generated literal clauses now have a genuine contextual value meaning.
The checked source reconstruction is used first; the only semantic law is
the independent local ground primitive law, not an assumed source theorem. -/
theorem generated_literal_membership (inputs : Inputs s) (law : GroundLaw inputs)
    (declarations : LiteralDeclaration s) (original : OriginalSource.Kernel (SourceAssignment s))
    (environment : OriginalSource.Environment (SourceAssignment s))
    (context : OriginalSource.Context) (site : OriginalSource.Site) (literal : OriginalSource.Literal)
    (solved : OriginalSource.Satisfies (literalKernel inputs declarations original site literal) environment
      (OriginalSource.Build context (.literal ⟨site, none⟩ literal))) :
    Meaning inputs (.value (environment.root.row site)) := by
  have derivation := OriginalSource.generated_constraints_imply_source_judgment
    (literalKernel inputs declarations original site literal) environment context (.literal ⟨site, none⟩ literal) solved
  simp only [OriginalSource.SourceJudgment, OriginalSource.sourceRules] at derivation
  cases derivation with
  | rule locals children =>
      have primitive := locals _ (List.mem_cons_self)
      cases primitive with
      | atom valid =>
          simp [literalKernel, OriginalSource.atom] at valid
          obtain ⟨_, _, _, form, ground⟩ := valid
          exact ground_membership inputs law _ form ground

/-- An actual source-formal lookup supplies the generated constraints. It
contains only the raw address/result tuple, with no recursive certificate. -/
theorem name_constraints_from_binding (inputs : Inputs s)
    (original : OriginalSource.Kernel (SourceAssignment s))
    (environment : OriginalSource.Environment (SourceAssignment s))
    (site owner : OriginalSource.Site) (name : OriginalSource.Name) (address : Nat)
    (binding : environment.root.binding name = some address)
    (bound : address < inputs.installedCount environment.root.event)
    (found : inputs.installed environment.root.event address =
      some (.value (environment.root.descriptor ⟨site, .finalRoot⟩) (environment.root.value ⟨site, .finalRoot⟩) (environment.root.root ⟨site, .finalRoot⟩))) :
    OriginalSource.Satisfies (nameKernel inputs original site name) environment
      (OriginalSource.Build (formalContext name owner) (.name ⟨site, none⟩ name)) := by
  apply (OriginalSource.source_reconstruction _ _ _ _).mpr
  have lookup : OriginalSource.lookupBinding (formalContext name owner) name =
      some {name := name, owner := owner, kind := .formal, entry := some .value} := by
    simp [OriginalSource.lookupBinding, formalContext]
  simp only [OriginalSource.SourceJudgment, OriginalSource.sourceRules, lookup]
  apply OriginalSource.Judgment.rule
  · intro premise member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals
      apply OriginalSource.Local.atom
      simp only [nameKernel, OriginalSource.atom, valueFormalAtom]
      simp only [beq_self_eq_true, Bool.and_self, reduceCtorEq, true_or, or_true, and_self, ite_true]
      exact ⟨name, address, rfl, binding, bound, found⟩
  · exact .nil

/-- The ordinary value-formal Name source rule is interpreted by the
original full world projection, preserving its exact value/root/current event. -/
theorem generated_name_membership (inputs : Inputs s)
    (original : OriginalSource.Kernel (SourceAssignment s))
    (environment : OriginalSource.Environment (SourceAssignment s))
    (site owner : OriginalSource.Site) (name : OriginalSource.Name)
    (world : Meaning inputs (.world environment.root.event))
    (solved : OriginalSource.Satisfies (nameKernel inputs original site name) environment
      (OriginalSource.Build (formalContext name owner) (.name ⟨site, none⟩ name))) :
    Meaning inputs (.value (environment.root.row site)) := by
  have derivation := OriginalSource.generated_constraints_imply_source_judgment
    (nameKernel inputs original site name) environment (formalContext name owner) (.name ⟨site, none⟩ name) solved
  have lookup : OriginalSource.lookupBinding (formalContext name owner) name =
      some {name := name, owner := owner, kind := .formal, entry := some .value} := by
    simp [OriginalSource.lookupBinding, formalContext]
  simp only [OriginalSource.SourceJudgment, OriginalSource.sourceRules, lookup] at derivation
  cases derivation with
  | rule locals children =>
      have first := locals _ (List.mem_cons_self)
      cases first with
      | atom valid =>
          simp only [nameKernel, OriginalSource.atom, valueFormalAtom] at valid
          simp only [beq_self_eq_true, Bool.and_self, reduceCtorEq, true_or, and_self, ite_true] at valid
          obtain ⟨_, address, _, _, _, found⟩ := valid
          exact immutable_name_value inputs environment.root.event world address _ _ _ found

/-- Name/Return source application through the accepted source induction and
the original full Return clause. The complete independent fixed guards and
all positive observation fields remain explicit. -/
theorem generated_name_return (inputs : Inputs s)
    (original : OriginalSource.Kernel (SourceAssignment s))
    (environment : OriginalSource.Environment (SourceAssignment s))
    (site owner : OriginalSource.Site) (name : OriginalSource.Name)
    (world : Meaning inputs (.world environment.root.event))
    (solved : OriginalSource.Satisfies (nameKernel inputs original site name) environment
      (OriginalSource.Build (formalContext name owner) (.name ⟨site, none⟩ name)))
    (returned : TraceRow s) (sameEvent : returned.event = environment.root.event)
    (form : inputs.traceForm returned = .pureReturn (environment.root.row site))
    (guards : (inputs.observationGuards returned).Valid)
    (fields : (inputs.observationFields returned).Holds (Meaning inputs)) :
    Meaning inputs (.trace returned) := by
  apply (return_observation_iff inputs returned _ form).mpr
  refine ⟨?_, guards, ?_, ⟨sameEvent.symm, generated_name_membership inputs original environment site owner name world solved⟩, fields⟩
  · simpa only [sameEvent] using ((world_unfold inputs _).mp world).1
  · simpa only [sameEvent] using world

/-- The native registry projection explicitly excludes unallocated cells.
PhiW itself still checks every Some entry of that actual projection. -/
def nativeInstalled (store : NativeClosureEnvironment.Store α) (decode : α → Installed s)
    (address : Nat) : Option (Installed s) :=
  if address < store.size then (store.cell address).map decode else none

theorem native_installed_outside (store : NativeClosureEnvironment.Store α)
    (decode : α → Installed s) (address : Nat) (outside : store.size ≤ address) :
    nativeInstalled store decode address = none := by
  simp only [nativeInstalled, ite_eq_right (Nat.not_lt_of_ge outside)]

theorem native_installed_current (store : NativeClosureEnvironment.Store α)
    (decode : α → Installed s) (value : α) :
    nativeInstalled (store.push value) decode store.size = some (decode value) := by
  simp only [nativeInstalled, NativeClosureEnvironment.Store.push,
    Nat.lt_succ_self, ite_true, Option.map_some]

/-- Reuse the accepted actual pending-receipt realization, preserving every
predicate of the whole receiving record. This supplies a field map, not the
remaining full source-world or dictionary interpretation. -/
theorem native_receipt_preserves_predicate [DecidableEq K]
    (receiving : SourceIdentityWorld.Receiving K V ViewData Site)
    (owner : SourceIdentityWorld.Owner) (view : Nat) (site : Site)
    (predicate : SourceIdentityWorld.Receiving K V ViewData Site → Prop) :
    predicate (SourceFunctionMembership.ReceivingPhase.binding receiving owner view site).realize ↔
      predicate (SourceFunctionMembership.ReceivingPhase.executed (receiving.record owner view site none)).realize :=
  Iff.of_eq (SourceFunctionMembership.materialization_all_observers receiving owner view site predicate)

/-- Ordered dictionary composition is retained at the original observer.
No idempotence or source-type preservation is inferred from this equality. -/
theorem native_dictionary_order {StepData : Type}
    (first second : List (NativeDictionaryDenotation.Assignment StepData))
    (context : NativeDictionaryDenotation.Context StepData) :
    NativeDictionaryDenotation.action (first ++ second) context =
      NativeDictionaryDenotation.action second (NativeDictionaryDenotation.action first context) :=
  NativeDictionaryDenotation.action_append first second context


/-- A failing actual decomposition refutes membership even when another
provider alternative succeeds or the execution relation has no return. -/
theorem rejecting_actual_provider_excludes_membership (inputs : Inputs s) (row : ValueRow s)
    (form : inputs.valueForm row.descriptor = .function) (provider : s.Provider)
    (actual : inputs.actual row.value row.root provider) (challenge : Challenge row)
    (admitted : CheckedDomain inputs challenge) (rejected : ¬ ActualAdm inputs provider challenge) :
    ¬ Meaning inputs (.value row) := by
  intro member
  exact rejected (function_challenge inputs row form member provider actual challenge admitted).1

/-- An unfinished observation is checked in its actual world with all its
remaining positive obligations. No result or eventual Return is required. -/
theorem unfinished_observation_iff (inputs : Inputs s) (row : TraceRow s)
    (form : inputs.traceForm row = .unfinished) :
    Meaning inputs (.trace row) ↔
      inputs.eventCoherent row.event ∧ (inputs.observationGuards row).Valid ∧
      Meaning inputs (.world row.event) ∧ (inputs.observationFields row).Holds (Meaning inputs) := by
  rw [meaning_iff]
  simp only [Phi, PhiT, form, true_and]

/-- All actual complete or unfinished observations are read at the identical
input tuple. Rechecking a description does not choose another operation. -/
theorem retarget_keeps_raw_observations (inputs : Inputs s) (row : ValueRow s)
    (challenge : Challenge row) (descriptor : s.Descriptor) (provider : s.Provider)
    (observation : RawObservation s) :
    inputs.execute provider (challenge.retarget descriptor).input observation ↔
      inputs.execute provider challenge.input observation := Iff.rfl


/-- The actual native bind constructor supplies the local source Name
constraints and the actual lexical read. The explicit installed/count/result
maps are raw field correspondences, not full typing or source soundness.
The later Name receipt/dictionary action keeps its separate real interpretation. -/
theorem native_bind_supplies_name_constraints [DecidableEq Key]
    (inputs : Inputs s) (original : OriginalSource.Kernel (SourceAssignment s))
    (environment : OriginalSource.Environment (SourceAssignment s))
    (world : SourceIdentityWorld.World Key Dispatch RawValue ViewData SiteData Rest)
    (parent : Nat) (keys : OriginalSource.Name → Key)
    (site owner : OriginalSource.Site) (name : OriginalSource.Name)
    (packet : SourceIdentityWorld.Received RawValue)
    (node : NativeClosureEnvironment.Node Key Dispatch)
    (parentFound : NativeClosureEnvironment.nodeAt world.environments parent = some node)
    (decode : SourceIdentityWorld.Received RawValue → Installed s)
    (binding : environment.root.binding name = some world.cells.size)
    (count : inputs.installedCount environment.root.event = world.cells.size + 1)
    (projection : ∀ address, inputs.installed environment.root.event address =
      nativeInstalled (SourceIdentityWorld.bindValue world parent (keys name) packet node parentFound).cells decode address)
    (result : decode packet.asValue =
      .value (environment.root.descriptor ⟨site, .finalRoot⟩)
        (environment.root.value ⟨site, .finalRoot⟩) (environment.root.root ⟨site, .finalRoot⟩)) :
    OriginalSource.Satisfies (nameKernel inputs original site name) environment
      (OriginalSource.Build (formalContext name owner) (.name ⟨site, none⟩ name)) ∧
    NativeClosureEnvironment.observe (fun key => decide (key = keys name))
      (SourceIdentityWorld.bindValue world parent (keys name) packet node parentFound).environments
      world.environments.size
      (SourceIdentityWorld.bindValue world parent (keys name) packet node parentFound).cells.cell =
      some packet.asValue := by
  refine ⟨name_constraints_from_binding inputs original environment site owner name world.cells.size
    binding ?_ ?_, SourceIdentityWorld.bind_read world parent (keys name) packet node parentFound⟩
  · rw [count]
    exact Nat.lt_succ_self _
  · rw [projection]
    change nativeInstalled (world.cells.push packet.asValue) decode world.cells.size = _
    rw [native_installed_current, result]

end YulangClosure.OriginalSourceInterpretation
