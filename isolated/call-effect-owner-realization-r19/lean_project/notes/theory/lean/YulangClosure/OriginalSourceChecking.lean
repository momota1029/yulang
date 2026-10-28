import YulangClosure.OriginalSourceEnvironment

/-!
Finite checking of the completed original interpretation.  The source is
Source Generalize §3.2, with its original declaration and telescope ownership.
The positive proof language below has explicit logical constructors and the
proved fold/unfold of the selected Meaning.  It has no arbitrary inclusion
leaf.  In particular it is NOT a lifting theorem for an unproved recursive
candidate: union elimination needs completed membership unfolding.
-/
namespace YulangClosure.OriginalSourceChecking

open OriginalSource OriginalSourceInterpretation

def functionClause (inputs : Inputs s) (row : ValueRow s) : Positive s :=
  .both (.guard (∃ provider, inputs.actual row.value row.root provider))
    (.all {provider : s.Provider // inputs.actual row.value row.root provider} fun provider =>
      .both (.guard (inputs.functionGuards row provider.val).Valid)
        (.both (inputs.capturedFields row provider.val)
          (.all {challenge : Challenge row // CheckedDomain inputs challenge} fun challenge =>
            .both (.guard (ActualAdm inputs provider.val challenge.val))
              (.all {raw : RawObservation s // inputs.execute provider.val challenge.val.input raw}
                fun raw => inputs.checkedObservation challenge.val raw.val))))

def valueCore (inputs : Inputs s) (row : ValueRow s) : Positive s :=
  match inputs.valueForm row.descriptor with
  | .ground => .guard (inputs.ground row)
  | .fixedExternal => .guard (inputs.fixedExternal row)
  | .structural => .both (.guard (inputs.structuralGuard row)) (inputs.structuralFields row)
  | .function => functionClause inputs row

def installedClause (event : Event s) : Installed s → Positive s
  | .value descriptor value root => .field (.value ⟨descriptor, value, root, event⟩)
  | .carrier interface carrier root => .field (.carrier ⟨interface, carrier, root, event⟩)

/-- Reifies every recursive field of the actual four-component operator.
The quantified domains retain the original complete independent operands. -/
def clause (inputs : Inputs s) : Query s → Positive s
  | .value row => .both (valueCore inputs row)
      (.all {later : Event s // inputs.compatible row.event later} fun later =>
        .field (.value (row.atEvent later.val)))
  | .world event => .both
      (.guard (inputs.eventCoherent event ∧ (inputs.worldGuards event).Valid ∧
        AliasesAgree inputs event ∧ CapturesAgree inputs event ∧ WitnessesAgree inputs event))
      (.all {entry : Nat × Installed s // inputs.installed event entry.1 = some entry.2}
        fun entry => installedClause event entry.val.2)
  | .trace row => .both (.guard (inputs.eventCoherent row.event ∧ (inputs.observationGuards row).Valid))
      (.both (.field (.world row.event))
        (.both (match inputs.traceForm row with
          | .pureReturn value => .both (.guard (value.event = row.event)) (.field (.value value))
          | .unfinished => .guard True) (inputs.observationFields row)))
  | .carrier row => .both (.guard (inputs.eventCoherent row.event ∧ (inputs.carrierGuards row).Valid))
      (.both (.field (.world row.event))
        (.both (inputs.carrierCaptures row)
          (.both (.all {event : Event s // inputs.demand row event} fun event =>
            .both (.guard (inputs.compatible row.event event.val))
              (.all {raw : RawObservation s // inputs.force row.input event.val raw} fun raw =>
                .both (.guard (inputs.forceIncidence row event.val raw.val))
                  (.field (.trace (raw.val.atInterface row.interface)))))
            (.all {later : Event s // inputs.compatible row.event later} fun later =>
              .field (.carrier (row.atEvent later.val))))))

theorem functionClause_iff (inputs : Inputs s) (Z : Family s) (row : ValueRow s) :
    (functionClause inputs row).Holds Z ↔ FunctionAt inputs Z row := by
  simp only [functionClause, Positive.Holds, FunctionAt, ObservationMem, Subtype.forall]

theorem valueCore_iff (inputs : Inputs s) (Z : Family s) (row : ValueRow s) :
    (valueCore inputs row).Holds Z ↔
      (match inputs.valueForm row.descriptor with
      | .ground => inputs.ground row
      | .fixedExternal => inputs.fixedExternal row
      | .structural => inputs.structuralGuard row ∧ (inputs.structuralFields row).Holds Z
      | .function => FunctionAt inputs Z row) := by
  cases form : inputs.valueForm row.descriptor <;>
    simp only [valueCore, form, Positive.Holds, functionClause_iff]

theorem installedClause_iff (Z : Family s) (event : Event s) (binding : Installed s) :
    (installedClause event binding).Holds Z ↔ binding.Valid Z event := by
  cases binding <;> rfl

theorem clause_iff (inputs : Inputs s) (Z : Family s) (query : Query s) :
    (clause inputs query).Holds Z ↔ Phi inputs Z query := by
  cases query with
  | value row =>
      simp only [clause, Positive.Holds, valueCore_iff, Subtype.forall, Phi, PhiV]
      rfl
  | world event =>
      simp only [clause, Positive.Holds, installedClause_iff, Subtype.forall,
        Prod.forall, Phi, PhiW, and_assoc]
  | trace row =>
      cases form : inputs.traceForm row <;>
        simp only [clause, Positive.Holds, form, Phi, PhiT, and_assoc]
  | carrier row =>
      simp only [clause, Positive.Holds, Subtype.forall, Phi, PhiCar, and_assoc]

theorem meaning_clause (inputs : Inputs s) (query : Query s) :
    Meaning inputs query ↔ (clause inputs query).Holds (Meaning inputs) :=
  (meaning_iff inputs query).trans (clause_iff inputs _ query).symm

/-- The completed source member is retained together with its one-step
readout. Future target membership is constructed coinductively from the
source's actual hereditary future field. No candidate-closure assumption is
used, and every compatible event remains present. -/
theorem value_transport (inputs : Inputs s) (source target : s.Descriptor)
    (value : s.Value) (root : s.Root)
    (body : ∀ event,
      Meaning inputs (.value ⟨source, value, root, event⟩) →
      (valueCore inputs ⟨source, value, root, event⟩).Holds (Meaning inputs) →
      (valueCore inputs ⟨target, value, root, event⟩).Holds (Meaning inputs)) :
    ∀ event, Meaning inputs (.value ⟨source, value, root, event⟩) →
      Meaning inputs (.value ⟨target, value, root, event⟩) := by
  let candidate : Family s := fun query => Meaning inputs query ∨
    ∃ event, query = .value ⟨target, value, root, event⟩ ∧
      Meaning inputs (.value ⟨source, value, root, event⟩)
  have included : (Meaning inputs).Le candidate := fun _ member => Or.inl member
  have postfixed : candidate.Le (Phi inputs candidate) := by
    intro query member
    rcases member with ordinary | ⟨event, rfl, original⟩
    · exact phi_monotone inputs included query ((meaning_iff inputs query).mp ordinary)
    · have readout := (meaning_iff inputs (.value ⟨source, value, root, event⟩)).mp original
      change PhiV inputs candidate ⟨target, value, root, event⟩
      refine ⟨?_, ?_⟩
      · apply (valueCore_iff inputs candidate _).mp
        apply positive_mono included
        exact body event original ((valueCore_iff inputs (Meaning inputs) _).mpr readout.1)
      · intro later compatible
        exact Or.inr ⟨later, rfl, readout.2 later compatible⟩
  intro event original
  exact greatest_coinduct (Phi inputs) candidate postfixed _ (Or.inr ⟨event, rfl, original⟩)

/-- Full raw operands for an independently registered primitive relation.
There is no Family, Meaning, source judgment or successful query operand. -/
inductive Operand (s : Sorts) where
  | descriptor (value : s.Descriptor)
  | interface (value : s.Interface)
  | value (value : s.Value) (root : s.Root)
  | provider (value : s.Provider)
  | event (value : Event s)
  | carrier (value : CarrierRow s)
  | observation (value : RawObservation s)
  | invocation (value : CallInput s)
  | endpoint (value : Endpoint)
  | declaration (value : Declaration)

structure Signature (s : Sorts) where
  declaration : Declaration
  owner : Site
  context : Context
  operands : List (Operand s)

/-- Only fixed original predicates can be guard-law operands. The external
case names one original registered predicate at its full actual telescope. -/
inductive Guard (s : Sorts) where
  | truth | falsity
  | both (first second : Guard s)
  | ground (row : ValueRow s)
  | fixedExternal (row : ValueRow s)
  | structural (row : ValueRow s)
  | coherent (event : Event s)
  | function (row : ValueRow s) (provider : s.Provider)
  | observation (row : TraceRow s)
  | carrier (row : CarrierRow s)
  | world (event : Event s)
  | equal (first second : Operand s)
  | registered (signature : Signature s)

def Guard.Holds (inputs : Inputs s) (original : Signature s → Prop) : Guard s → Prop
  | .truth => True
  | .falsity => False
  | .both first second => first.Holds inputs original ∧ second.Holds inputs original
  | .ground row => inputs.ground row
  | .fixedExternal row => inputs.fixedExternal row
  | .structural row => inputs.structuralGuard row
  | .coherent event => inputs.eventCoherent event
  | .function row provider => (inputs.functionGuards row provider).Valid
  | .observation row => (inputs.observationGuards row).Valid
  | .carrier row => (inputs.carrierGuards row).Valid
  | .world event => (inputs.worldGuards event).Valid
  | .equal first second => first = second
  | .registered signature => original signature

structure GuardDeclaration (s : Sorts) where
  signature : Signature s
  before : Guard s
  after : Guard s

/-- L1/L3 input at a specific declaration, owning occurrence and complete
operand telescope. This proves a fixed guard action, never a goal inclusion. -/
structure GuardRegistry (inputs : Inputs s) where
  original : Signature s → Prop
  declaration : Nat → Option (GuardDeclaration s)
  law : ∀ identifier entry, declaration identifier = some entry →
    entry.before.Holds inputs original → entry.after.Holds inputs original

/-- Explicit finite logical proof syntax. `leaf` is exactly a recursive
source checking premise; no semantic implication is stored in a constructor.
All equation actions unfold the ACTUAL Phi/Meaning, not a supplied relation.
`all` and `existsE` preserve original domains and one existing witness. -/
inductive Proof (inputs : Inputs s) (registry : GuardRegistry inputs)
    (leaves : Positive s → Positive s → Prop) : Positive s → Positive s → Prop where
  | identity (A : Positive s) : Proof inputs registry leaves A A
  | leaf {A B} (present : leaves A B) : Proof inputs registry leaves A B
  | compose {A B C} (first : Proof inputs registry leaves A B)
      (second : Proof inputs registry leaves B C) : Proof inputs registry leaves A C
  | bothIntro {A B C} (first : Proof inputs registry leaves A B)
      (second : Proof inputs registry leaves A C) : Proof inputs registry leaves A (.both B C)
  | left (A B : Positive s) : Proof inputs registry leaves (.both A B) A
  | right (A B : Positive s) : Proof inputs registry leaves (.both A B) B
  | inLeft (A B : Positive s) : Proof inputs registry leaves A (.either A B)
  | inRight (A B : Positive s) : Proof inputs registry leaves B (.either A B)
  | cases {A B C} (first : Proof inputs registry leaves A C)
      (second : Proof inputs registry leaves B C) : Proof inputs registry leaves (.either A B) C
  | allIntro {A : Positive s} {Domain : Type} {body : Domain → Positive s}
      (each : ∀ value, Proof inputs registry leaves A (body value)) :
      Proof inputs registry leaves A (.all Domain body)
  | allElim {Domain : Type} (body : Domain → Positive s) (value : Domain) :
      Proof inputs registry leaves (.all Domain body) (body value)
  | existsIntro {Domain : Type} (body : Domain → Positive s) (value : Domain) :
      Proof inputs registry leaves (body value) (.existsE Domain body)
  | existsElim {Domain : Type} {body : Domain → Positive s} {C : Positive s}
      (each : ∀ value, Proof inputs registry leaves (body value) C) :
      Proof inputs registry leaves (.existsE Domain body) C
  | truth (A : Positive s) : Proof inputs registry leaves A (.guard True)
  | falsity (A : Positive s) : Proof inputs registry leaves (.guard False) A
  | guard (identifier : Nat) (entry : GuardDeclaration s)
      (registered : registry.declaration identifier = some entry) :
      Proof inputs registry leaves (.guard (entry.before.Holds inputs registry.original))
        (.guard (entry.after.Holds inputs registry.original))
  | unfold (query : Query s) : Proof inputs registry leaves (.field query) (clause inputs query)
  | fold (query : Query s) : Proof inputs registry leaves (clause inputs query) (.field query)
  | functionStep (checked : ValueRow s) (source : s.Descriptor)
      (guards : ∀ provider, inputs.actual checked.value checked.root provider →
        Proof inputs registry leaves
          (.guard (inputs.functionGuards (checked.withDescriptor source) provider).Valid)
          (.guard (inputs.functionGuards checked provider).Valid))
      (captures : ∀ provider, inputs.actual checked.value checked.root provider →
        Proof inputs registry leaves (inputs.capturedFields (checked.withDescriptor source) provider)
          (inputs.capturedFields checked provider))
      (domain : ∀ challenge : Challenge checked, Proof inputs registry leaves
        (.guard (CheckedDomain inputs challenge))
        (.guard (CheckedDomain inputs (challenge.retarget source))))
      (observations : ∀ challenge : Challenge checked, CheckedDomain inputs challenge →
        ∀ raw, Proof inputs registry leaves (inputs.checkedObservation (challenge.retarget source) raw)
          (inputs.checkedObservation challenge raw)) :
      Proof inputs registry leaves (functionClause inputs (checked.withDescriptor source))
        (functionClause inputs checked)
  | valueTransport (source target : s.Descriptor) (value : s.Value) (root : s.Root)
      (each : ∀ event, Proof inputs registry leaves
        (.both (.field (.value ⟨source, value, root, event⟩))
          (valueCore inputs ⟨source, value, root, event⟩))
        (valueCore inputs ⟨target, value, root, event⟩)) (event : Event s) :
      Proof inputs registry leaves (.field (.value ⟨source, value, root, event⟩))
        (.field (.value ⟨target, value, root, event⟩))

theorem Proof.sound (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop}
    (children : ∀ A B, leaves A B → A.Holds (Meaning inputs) → B.Holds (Meaning inputs))
    {A B : Positive s} (proof : Proof inputs registry leaves A B) :
    A.Holds (Meaning inputs) → B.Holds (Meaning inputs) := by
  induction proof with
  | identity => exact id
  | leaf present => exact children _ _ present
  | compose first second firstIH secondIH => exact fun valid => secondIH (firstIH valid)
  | bothIntro first second firstIH secondIH => exact fun valid => ⟨firstIH valid, secondIH valid⟩
  | left => exact And.left
  | right => exact And.right
  | inLeft => exact Or.inl
  | inRight => exact Or.inr
  | cases first second firstIH secondIH => exact fun valid => valid.elim firstIH secondIH
  | allIntro each ih => exact fun valid value => ih value valid
  | allElim body value => exact fun valid => valid value
  | existsIntro body value => exact fun valid => ⟨value, valid⟩
  | existsElim each ih => exact fun ⟨value, valid⟩ => ih value valid
  | truth => exact fun _ => True.intro
  | falsity => exact False.elim
  | guard identifier entry registered => exact registry.law identifier entry registered
  | unfold query => exact (meaning_clause inputs query).mp
  | fold query => exact (meaning_clause inputs query).mpr
  | functionStep checked source guards captures domain observations guardsIH capturesIH domainIH observationsIH =>
      intro valid
      have original := (functionClause_iff inputs (Meaning inputs) _).mp valid
      apply (functionClause_iff inputs (Meaning inputs) _).mpr
      apply same_provider_function_check inputs (Meaning inputs) checked source original
      · intro provider actual
        exact guardsIH provider actual (original.2 provider actual).1
      · intro provider actual
        exact capturesIH provider actual (original.2 provider actual).2.1
      · intro challenge admitted
        exact domainIH challenge admitted
      · intro challenge admitted raw valid
        exact observationsIH challenge admitted raw valid
  | valueTransport source target value root each event ih =>
      exact value_transport inputs source target value root (fun event member core => ih event ⟨member, core⟩) event

/-- A record selection computes its target fields from actual source fields
and exact child endpoints. Width never manufactures a field; depth retains
the selected original decorated field. -/
structure RecordPlan (s : Sorts) (leaves : Positive s → Positive s → Prop) where
  sourceCount : Nat
  targetCount : Nat
  source : Fin sourceCount → Positive s
  target : Fin targetCount → Positive s
  select : Fin targetCount → Fin sourceCount
  children : ∀ field, leaves (source (select field)) (target field)

theorem RecordPlan.proof (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop} (plan : RecordPlan s leaves) :
    Proof inputs registry leaves (.all (Fin plan.sourceCount) plan.source)
      (.all (Fin plan.targetCount) plan.target) :=
  .allIntro fun field => .compose (.allElim plan.source (plan.select field)) (.leaf (plan.children field))

theorem unionInjection (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop} {A B : Positive s} (other : Positive s)
    (child : leaves A B) : Proof inputs registry leaves A (.either B other) :=
  .compose (.leaf child) (.inLeft B other)

theorem unionCases (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop} {A B C : Positive s}
    (left : leaves A C) (right : leaves B C) : Proof inputs registry leaves (.either A B) C :=
  .cases (.leaf left) (.leaf right)

theorem intersection (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop} {A B C : Positive s}
    (left : leaves A B) (right : leaves A C) : Proof inputs registry leaves A (.both B C) :=
  .bothIntro (.leaf left) (.leaf right)

/-- The Return child changes only the completed result value field. Every
other complete observation guard, world field and latent clause is retained. -/
def resultClause (guards : Prop) (world : Query s) (event : Prop)
    (result : Query s) (latent : Positive s) : Positive s :=
  .both (.guard guards) (.both (.field world) (.both (.both (.guard event) (.field result)) latent))

theorem resultChecking (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop} (guards event : Prop)
    (world first last : Query s) (latent : Positive s)
    (child : leaves (.field first) (.field last)) :
    Proof inputs registry leaves (resultClause guards world event first latent)
      (resultClause guards world event last latent) := by
  apply Proof.bothIntro (Proof.left _ _)
  apply Proof.compose (Proof.right _ _)
  apply Proof.bothIntro (Proof.left _ _)
  apply Proof.compose (Proof.right _ _)
  apply Proof.bothIntro
  · apply Proof.compose (Proof.left _ _)
    exact .bothIntro (.left _ _) (.compose (.right _ _) (.leaf child))
  · exact .right _ _

/-- Registered equation incidence is an equality to the actual selected
operator clause. No equation is accepted because its desired inclusion holds. -/
structure EquationRegistration (inputs : Inputs s) where
  signature : Signature s
  query : Query s
  body : Positive s
  readback : clause inputs query = body

theorem EquationRegistration.unfold (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop} (equation : EquationRegistration inputs) :
    Proof inputs registry leaves (.field equation.query) equation.body := by
  rw [← equation.readback]
  exact .unfold equation.query

theorem EquationRegistration.fold (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop} (equation : EquationRegistration inputs) :
    Proof inputs registry leaves equation.body (.field equation.query) := by
  rw [← equation.readback]
  exact .fold equation.query

/-- Original record registration: labels, actual decorated selected fields,
and the defining positive clause at ALL original events. No selected field's
provider, root, scope or event is replaced by its label. -/
structure RecordRegistration (inputs : Inputs s) where
  signature : Signature s
  descriptor : s.Descriptor
  labels : List Label
  field : s.Value → s.Root → Event s → Fin labels.length → ValueRow s
  form : inputs.valueForm descriptor = .structural
  readback : ∀ value root event,
    inputs.structuralFields ⟨descriptor, value, root, event⟩ =
      .all (Fin labels.length) (fun index => .field (.value (field value root event index)))

theorem record_value_check (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop}
    (source target : RecordRegistration inputs) (value : s.Value) (root : s.Root)
    (select : Fin target.labels.length → Fin source.labels.length)
    (_labels : ∀ index, target.labels[index] = source.labels[select index])
    (guards : ∀ event, Proof inputs registry leaves
      (.guard (inputs.structuralGuard ⟨source.descriptor, value, root, event⟩))
      (.guard (inputs.structuralGuard ⟨target.descriptor, value, root, event⟩)))
    (children : ∀ event index, leaves (.field (.value (source.field value root event (select index))))
      (.field (.value (target.field value root event index)))) (event : Event s) :
    Proof inputs registry leaves (.field (.value ⟨source.descriptor, value, root, event⟩))
      (.field (.value ⟨target.descriptor, value, root, event⟩)) := by
  apply Proof.valueTransport source.descriptor target.descriptor value root
  intro later
  apply Proof.compose (Proof.right _ _)
  simp only [valueCore, source.form, target.form]
  apply Proof.bothIntro
  · exact .compose (.left _ _) (guards later)
  · rw [source.readback, target.readback]
    exact .compose (.right _ _) (RecordPlan.proof inputs registry
      ⟨source.labels.length, target.labels.length,
        (fun index => .field (.value (source.field value root later index))),
        (fun index => .field (.value (target.field value root later index))), select, children later⟩)

structure UnionRegistration (inputs : Inputs s) where
  signature : Signature s
  descriptor : s.Descriptor
  left : s.Descriptor
  right : s.Descriptor
  form : inputs.valueForm descriptor = .structural
  readback : ∀ value root event, inputs.structuralFields ⟨descriptor, value, root, event⟩ =
    .either (.field (.value ⟨left, value, root, event⟩)) (.field (.value ⟨right, value, root, event⟩))

theorem union_value_injection (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop} (union : UnionRegistration inputs)
    (value : s.Value) (root : s.Root)
    (guards : ∀ event, Proof inputs registry leaves
      (.both (.field (.value ⟨union.left, value, root, event⟩))
        (valueCore inputs ⟨union.left, value, root, event⟩))
      (.guard (inputs.structuralGuard ⟨union.descriptor, value, root, event⟩)))
    (event : Event s) : Proof inputs registry leaves (.field (.value ⟨union.left, value, root, event⟩))
      (.field (.value ⟨union.descriptor, value, root, event⟩)) := by
  apply Proof.valueTransport union.left union.descriptor value root
  intro later
  simp only [valueCore, union.form, union.readback]
  exact .bothIntro (guards later) (.compose (.left _ _) (.inLeft _ _))

/-- Union elimination actually unfolds the checked child at completed
Meaning. This is the operation missing from arbitrary-candidate closures. -/
theorem union_value_cases (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop} (union : UnionRegistration inputs)
    (target : s.Descriptor) (value : s.Value) (root : s.Root)
    (left : ∀ event, leaves (.field (.value ⟨union.left, value, root, event⟩))
      (.field (.value ⟨target, value, root, event⟩)))
    (right : ∀ event, leaves (.field (.value ⟨union.right, value, root, event⟩))
      (.field (.value ⟨target, value, root, event⟩))) (event : Event s) :
    Proof inputs registry leaves (.field (.value ⟨union.descriptor, value, root, event⟩))
      (.field (.value ⟨target, value, root, event⟩)) := by
  apply Proof.valueTransport union.descriptor target value root
  intro later
  apply Proof.compose (Proof.right _ _)
  simp only [valueCore, union.form, union.readback]
  apply Proof.compose (Proof.right _ _)
  apply Proof.compose (unionCases inputs registry (left later) (right later))
  exact .compose (.unfold (.value ⟨target, value, root, later⟩)) (.left _ _)

structure FiniteUnionRegistration (inputs : Inputs s) where
  signature : Signature s
  descriptor : s.Descriptor
  alternatives : List s.Descriptor
  form : inputs.valueForm descriptor = .structural
  readback : ∀ value root event, inputs.structuralFields ⟨descriptor, value, root, event⟩ =
    .existsE (Fin alternatives.length) (fun index => .field (.value ⟨alternatives[index], value, root, event⟩))

theorem finite_union_injection (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop} (union : FiniteUnionRegistration inputs)
    (selected : Fin union.alternatives.length) (value : s.Value) (root : s.Root)
    (guards : ∀ event, Proof inputs registry leaves
      (.both (.field (.value ⟨union.alternatives[selected], value, root, event⟩))
        (valueCore inputs ⟨union.alternatives[selected], value, root, event⟩))
      (.guard (inputs.structuralGuard ⟨union.descriptor, value, root, event⟩)))
    (event : Event s) : Proof inputs registry leaves
      (.field (.value ⟨union.alternatives[selected], value, root, event⟩))
      (.field (.value ⟨union.descriptor, value, root, event⟩)) := by
  apply Proof.valueTransport union.alternatives[selected] union.descriptor value root
  intro later
  simp only [valueCore, union.form, union.readback]
  exact .bothIntro (guards later) (.compose (.left _ _) (.existsIntro (fun index : Fin union.alternatives.length =>
    .field (.value ⟨union.alternatives[index], value, root, later⟩)) selected))

theorem finite_union_cases (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop} (union : FiniteUnionRegistration inputs)
    (target : s.Descriptor) (value : s.Value) (root : s.Root)
    (children : ∀ event (index : Fin union.alternatives.length), leaves (.field (.value ⟨union.alternatives[index], value, root, event⟩))
      (.field (.value ⟨target, value, root, event⟩))) (event : Event s) :
    Proof inputs registry leaves (.field (.value ⟨union.descriptor, value, root, event⟩))
      (.field (.value ⟨target, value, root, event⟩)) := by
  apply Proof.valueTransport union.descriptor target value root
  intro later
  apply Proof.compose (Proof.right _ _)
  simp only [valueCore, union.form, union.readback]
  apply Proof.compose (Proof.right _ _)
  apply Proof.compose (B := .field (.value ⟨target, value, root, later⟩))
  · exact .existsElim (fun index => .leaf (children later index))
  · exact .compose (.unfold (.value ⟨target, value, root, later⟩)) (.left _ _)

structure IntersectionRegistration (inputs : Inputs s) where
  signature : Signature s
  descriptor : s.Descriptor
  left : s.Descriptor
  right : s.Descriptor
  form : inputs.valueForm descriptor = .structural
  readback : ∀ value root event, inputs.structuralFields ⟨descriptor, value, root, event⟩ =
    .both (.field (.value ⟨left, value, root, event⟩)) (.field (.value ⟨right, value, root, event⟩))

theorem intersection_value_check (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop} (target : IntersectionRegistration inputs)
    (source : s.Descriptor) (value : s.Value) (root : s.Root)
    (guards : ∀ event, Proof inputs registry leaves
      (.both (.field (.value ⟨source, value, root, event⟩)) (valueCore inputs ⟨source, value, root, event⟩))
      (.guard (inputs.structuralGuard ⟨target.descriptor, value, root, event⟩)))
    (left : ∀ event, leaves (.field (.value ⟨source, value, root, event⟩))
      (.field (.value ⟨target.left, value, root, event⟩)))
    (right : ∀ event, leaves (.field (.value ⟨source, value, root, event⟩))
      (.field (.value ⟨target.right, value, root, event⟩))) (event : Event s) :
    Proof inputs registry leaves (.field (.value ⟨source, value, root, event⟩))
      (.field (.value ⟨target.descriptor, value, root, event⟩)) := by
  apply Proof.valueTransport source target.descriptor value root
  intro later
  simp only [valueCore, target.form, target.readback]
  exact .bothIntro (guards later) (.compose (.left _ _) (intersection inputs registry (left later) (right later)))

theorem return_clause (inputs : Inputs s) (row : TraceRow s) (result : ValueRow s)
    (form : inputs.traceForm row = .pureReturn result) :
    clause inputs (.trace row) = resultClause
      (inputs.eventCoherent row.event ∧ (inputs.observationGuards row).Valid)
      (.world row.event) (result.event = row.event) (.value result) (inputs.observationFields row) := by
  simp only [clause, form, resultClause]

theorem registered_result_check (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop}
    (source target : TraceRow s) (first last : ValueRow s)
    (sourceForm : inputs.traceForm source = .pureReturn first)
    (targetForm : inputs.traceForm target = .pureReturn last)
    (sameEvent : source.event = target.event)
    (resultEvent : first.event = last.event)
    (guards : inputs.observationGuards source = inputs.observationGuards target)
    (latent : inputs.observationFields source = inputs.observationFields target)
    (child : leaves (.field (.value first)) (.field (.value last))) :
    Proof inputs registry leaves (.field (.trace source)) (.field (.trace target)) := by
  apply Proof.compose (.unfold (.trace source))
  apply Proof.compose (B := clause inputs (.trace target))
  · rw [return_clause inputs source first sourceForm, return_clause inputs target last targetForm,
      sameEvent, resultEvent, guards, latent]
    exact resultChecking inputs registry _ _ _ _ _ _ child
  · exact .fold (.trace target)

theorem unfinished_result_check (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop} (source target : TraceRow s)
    (sourceForm : inputs.traceForm source = .unfinished)
    (targetForm : inputs.traceForm target = .unfinished)
    (sameRaw : source.raw = target.raw)
    (guards : inputs.observationGuards source = inputs.observationGuards target)
    (latent : inputs.observationFields source = inputs.observationFields target) :
    Proof inputs registry leaves (.field (.trace source)) (.field (.trace target)) := by
  have sameEvent : source.event = target.event := congrArg RawObservation.event sameRaw
  apply Proof.compose (.unfold (.trace source))
  have sameClause : clause inputs (.trace source) = clause inputs (.trace target) := by
    simp only [clause, sourceForm, targetForm, sameEvent, guards, latent]
  rw [sameClause]
  exact .fold (.trace target)

/-- The original Top declaration keeps its own full immediate guard. It is
not redefined as True, and its hereditary event field is still constructed. -/
structure TopRegistration (inputs : Inputs s) (registry : GuardRegistry inputs) where
  signature : Signature s
  descriptor : s.Descriptor
  guard : s.Value → s.Root → Event s → Guard s
  readback : ∀ value root event, valueCore inputs ⟨descriptor, value, root, event⟩ =
    .guard ((guard value root event).Holds inputs registry.original)

theorem top_value_check (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop} (top : TopRegistration inputs registry)
    (source : s.Descriptor) (value : s.Value) (root : s.Root)
    (guards : ∀ event, Proof inputs registry leaves
      (.both (.field (.value ⟨source, value, root, event⟩)) (valueCore inputs ⟨source, value, root, event⟩))
      (.guard ((top.guard value root event).Holds inputs registry.original))) (event : Event s) :
    Proof inputs registry leaves (.field (.value ⟨source, value, root, event⟩))
      (.field (.value ⟨top.descriptor, value, root, event⟩)) := by
  apply Proof.valueTransport source top.descriptor value root
  intro later
  rw [top.readback]
  exact guards later

/-- Complete same-callable Function checking at every original event, with
actual finite domain/observation proofs and explicit raw guard/capture code.
The new value theorem constructs its hereditary future membership itself. -/
theorem function_value_check (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop} (source target : s.Descriptor)
    (sourceForm : inputs.valueForm source = .function)
    (targetForm : inputs.valueForm target = .function)
    (value : s.Value) (root : s.Root)
    (guards : ∀ event provider, inputs.actual value root provider →
      Proof inputs registry leaves (.guard (inputs.functionGuards ⟨source, value, root, event⟩ provider).Valid)
        (.guard (inputs.functionGuards ⟨target, value, root, event⟩ provider).Valid))
    (captures : ∀ event provider, inputs.actual value root provider →
      Proof inputs registry leaves (inputs.capturedFields ⟨source, value, root, event⟩ provider)
        (inputs.capturedFields ⟨target, value, root, event⟩ provider))
    (domain : ∀ event (challenge : Challenge (⟨target, value, root, event⟩ : ValueRow s)),
      Proof inputs registry leaves (.guard (CheckedDomain inputs challenge))
        (.guard (CheckedDomain inputs (challenge.retarget source))))
    (observations : ∀ event (challenge : Challenge (⟨target, value, root, event⟩ : ValueRow s)),
      CheckedDomain inputs challenge → ∀ raw, Proof inputs registry leaves
        (inputs.checkedObservation (challenge.retarget source) raw) (inputs.checkedObservation challenge raw))
    (event : Event s) : Proof inputs registry leaves (.field (.value ⟨source, value, root, event⟩))
      (.field (.value ⟨target, value, root, event⟩)) := by
  apply Proof.valueTransport source target value root
  intro later
  apply Proof.compose (Proof.right _ _)
  simp only [valueCore, sourceForm, targetForm]
  exact .functionStep ⟨target, value, root, later⟩ source (guards later) (captures later)
    (domain later) (observations later)

inductive Probe (s : Sorts) where
  | value (event : Event s)
  | computation (raw : RawObservation s)
  | domain (input : CallInput s)
  | observation (raw : RawObservation s)
  | equality (operand : Operand s)

/-- Source structural constructor evidence. The tag is an INDEX of the raw
constructor, rather than a freely supplied tag next to an arbitrary proof.
Record labels, selected fields and equation identities survive in this data.
The remaining finite congruence/same-interface cases retain their explicit
proof syntax; they are not extensional semantic inclusion leaves. -/
inductive Schema (inputs : Inputs s) (registry : GuardRegistry inputs)
    (leaves : Positive s → Positive s → Prop) : StructuralCheck → Positive s → Positive s → Prop where
  | inactive (rule : StructuralCheck) : Schema inputs registry leaves rule (.guard False) (.guard False)
  | record (source target : RecordRegistration inputs) (value : s.Value) (root : s.Root)
      (select : Fin target.labels.length → Fin source.labels.length)
      (labels : ∀ index, target.labels[index] = source.labels[select index])
      (actual : ∀ event index,
        (source.field value root event (select index)).value = (target.field value root event index).value ∧
        (source.field value root event (select index)).root = (target.field value root event index).root ∧
        (source.field value root event (select index)).event = (target.field value root event index).event)
      (guards : ∀ event, Proof inputs registry leaves
        (.guard (inputs.structuralGuard ⟨source.descriptor, value, root, event⟩))
        (.guard (inputs.structuralGuard ⟨target.descriptor, value, root, event⟩)))
      (children : ∀ event index, leaves (.field (.value (source.field value root event (select index))))
        (.field (.value (target.field value root event index)))) (event : Event s) :
      Schema inputs registry leaves .recordWidthDepth
        (.field (.value ⟨source.descriptor, value, root, event⟩))
        (.field (.value ⟨target.descriptor, value, root, event⟩))
  | unionInjection (union : UnionRegistration inputs) (value : s.Value) (root : s.Root)
      (guards : ∀ event, Proof inputs registry leaves
        (.both (.field (.value ⟨union.left, value, root, event⟩)) (valueCore inputs ⟨union.left, value, root, event⟩))
        (.guard (inputs.structuralGuard ⟨union.descriptor, value, root, event⟩))) (event : Event s) :
      Schema inputs registry leaves .unionInjection (.field (.value ⟨union.left, value, root, event⟩))
        (.field (.value ⟨union.descriptor, value, root, event⟩))
  | unionCases (union : UnionRegistration inputs) (target : s.Descriptor) (value : s.Value) (root : s.Root)
      (left : ∀ event, leaves (.field (.value ⟨union.left, value, root, event⟩))
        (.field (.value ⟨target, value, root, event⟩)))
      (right : ∀ event, leaves (.field (.value ⟨union.right, value, root, event⟩))
        (.field (.value ⟨target, value, root, event⟩))) (event : Event s) :
      Schema inputs registry leaves .unionCases (.field (.value ⟨union.descriptor, value, root, event⟩))
        (.field (.value ⟨target, value, root, event⟩))
  | finiteUnionInjection (union : FiniteUnionRegistration inputs) (selected : Fin union.alternatives.length)
      (value : s.Value) (root : s.Root)
      (guards : ∀ event, Proof inputs registry leaves
        (.both (.field (.value ⟨union.alternatives[selected], value, root, event⟩))
          (valueCore inputs ⟨union.alternatives[selected], value, root, event⟩))
        (.guard (inputs.structuralGuard ⟨union.descriptor, value, root, event⟩))) (event : Event s) :
      Schema inputs registry leaves .unionInjection
        (.field (.value ⟨union.alternatives[selected], value, root, event⟩))
        (.field (.value ⟨union.descriptor, value, root, event⟩))
  | finiteUnionCases (union : FiniteUnionRegistration inputs) (target : s.Descriptor)
      (value : s.Value) (root : s.Root)
      (children : ∀ event (index : Fin union.alternatives.length), leaves (.field (.value ⟨union.alternatives[index], value, root, event⟩))
        (.field (.value ⟨target, value, root, event⟩))) (event : Event s) :
      Schema inputs registry leaves .unionCases (.field (.value ⟨union.descriptor, value, root, event⟩))
        (.field (.value ⟨target, value, root, event⟩))
  | intersection (target : IntersectionRegistration inputs) (source : s.Descriptor)
      (value : s.Value) (root : s.Root)
      (guards : ∀ event, Proof inputs registry leaves
        (.both (.field (.value ⟨source, value, root, event⟩)) (valueCore inputs ⟨source, value, root, event⟩))
        (.guard (inputs.structuralGuard ⟨target.descriptor, value, root, event⟩)))
      (left : ∀ event, leaves (.field (.value ⟨source, value, root, event⟩))
        (.field (.value ⟨target.left, value, root, event⟩)))
      (right : ∀ event, leaves (.field (.value ⟨source, value, root, event⟩))
        (.field (.value ⟨target.right, value, root, event⟩))) (event : Event s) :
      Schema inputs registry leaves .intersection (.field (.value ⟨source, value, root, event⟩))
        (.field (.value ⟨target.descriptor, value, root, event⟩))
  | top (A : Positive s) : Schema inputs registry leaves .top A (.guard True)
  | topValue (top : TopRegistration inputs registry) (source : s.Descriptor) (value : s.Value) (root : s.Root)
      (guards : ∀ event, Proof inputs registry leaves
        (.both (.field (.value ⟨source, value, root, event⟩)) (valueCore inputs ⟨source, value, root, event⟩))
        (.guard ((top.guard value root event).Holds inputs registry.original))) (event : Event s) :
      Schema inputs registry leaves .top (.field (.value ⟨source, value, root, event⟩))
        (.field (.value ⟨top.descriptor, value, root, event⟩))
  | sameValue {A B : Positive s} (proof : Proof inputs registry leaves A B) :
      Schema inputs registry leaves .sameValue A B
  | sameComputation {A B : Positive s} (proof : Proof inputs registry leaves A B) :
      Schema inputs registry leaves .sameComputation A B
  | result (source target : TraceRow s) (first last : ValueRow s)
      (sourceForm : inputs.traceForm source = .pureReturn first)
      (targetForm : inputs.traceForm target = .pureReturn last)
      (sameRaw : source.raw = target.raw) (sameValue : first.value = last.value)
      (sameRoot : first.root = last.root) (sameEvent : first.event = last.event)
      (guards : inputs.observationGuards source = inputs.observationGuards target)
      (latent : inputs.observationFields source = inputs.observationFields target)
      (child : leaves (.field (.value first)) (.field (.value last))) :
      Schema inputs registry leaves .result (.field (.trace source)) (.field (.trace target))
  | unfinished (source target : TraceRow s)
      (sourceForm : inputs.traceForm source = .unfinished) (targetForm : inputs.traceForm target = .unfinished)
      (sameRaw : source.raw = target.raw)
      (guards : inputs.observationGuards source = inputs.observationGuards target)
      (latent : inputs.observationFields source = inputs.observationFields target) :
      Schema inputs registry leaves .result (.field (.trace source)) (.field (.trace target))
  | guarantee (identifier : Nat) (entry : GuardDeclaration s)
      (registered : registry.declaration identifier = some entry) (latent : Positive s) :
      Schema inputs registry leaves .guaranteeWeakening
        (.both (.guard (entry.before.Holds inputs registry.original)) latent)
        (.both (.guard (entry.after.Holds inputs registry.original)) latent)
  | congruence {A B : Positive s} (proof : Proof inputs registry leaves A B) :
      Schema inputs registry leaves .constructorCongruence A B
  | equationPair (source target : EquationRegistration inputs)
      (proof : Proof inputs registry leaves source.body target.body) :
      Schema inputs registry leaves .recursiveEquationPair (.field source.query) (.field target.query)
  | registered {rule : StructuralCheck} (source target : EquationRegistration inputs)
      (body : Schema inputs registry leaves rule source.body target.body) :
      Schema inputs registry leaves rule (.field source.query) (.field target.query)

theorem Schema.proof (inputs : Inputs s) (registry : GuardRegistry inputs)
    {leaves : Positive s → Positive s → Prop} {rule : StructuralCheck} {A B : Positive s}
    (schema : Schema inputs registry leaves rule A B) : Proof inputs registry leaves A B := by
  induction schema with
  | inactive => exact .identity _
  | record source target value root select labels actual guards children event =>
      exact record_value_check inputs registry source target value root select labels guards children event
  | unionInjection union value root guards event => exact union_value_injection inputs registry union value root guards event
  | unionCases union target value root left right event => exact union_value_cases inputs registry union target value root left right event
  | finiteUnionInjection union selected value root guards event =>
      exact finite_union_injection inputs registry union selected value root guards event
  | finiteUnionCases union target value root children event =>
      exact finite_union_cases inputs registry union target value root children event
  | intersection target source value root guards left right event =>
      exact intersection_value_check inputs registry target source value root guards left right event
  | top => exact .truth _
  | topValue top source value root guards event => exact top_value_check inputs registry top source value root guards event
  | sameValue proof | sameComputation proof | congruence proof => exact proof
  | result source target first last sourceForm targetForm sameRaw sameValue sameRoot sameEvent guards latent child =>
      exact registered_result_check inputs registry source target first last sourceForm targetForm
        (congrArg RawObservation.event sameRaw) sameEvent guards latent child
  | unfinished source target sourceForm targetForm sameRaw guards latent =>
      exact unfinished_result_check inputs registry source target sourceForm targetForm sameRaw guards latent
  | guarantee identifier entry registered latent =>
      exact .bothIntro (.compose (.left _ _) (.guard identifier entry registered)) (.right _ _)
  | equationPair source target proof =>
      exact .compose (source.unfold inputs registry) (.compose proof (target.fold inputs registry))
  | registered source target body ih =>
      exact .compose (source.unfold inputs registry) (.compose ih (target.fold inputs registry))

/-- A source-occurrence reading is indexed by the ORIGINAL mode, site and
context. Thus composition uses one tuple and never changes Value/Computation
tags by inspecting a solved descriptor. Concrete readings are supplied below.
This is data, not a semantic implication or a predicate of checking success. -/
abbrev Reading (s : Sorts) (Value : Type) :=
  Environment Value → CheckMode → Site → Context → Endpoint → Probe s → Positive s

def lower (reading : Reading s Value) (environment : Environment Value) (goal : CheckGoal) : Probe s → Positive s :=
  reading environment goal.mode goal.site goal.context goal.lower

def upper (reading : Reading s Value) (environment : Environment Value) (goal : CheckGoal) : Probe s → Positive s :=
  reading environment goal.mode goal.site goal.context goal.upper

def GoalMeaning (inputs : Inputs s) (reading : Reading s Value)
    (environment : Environment Value) (goal : CheckGoal) : Prop :=
  ∀ probe, (lower reading environment goal probe).Holds (Meaning inputs) →
    (upper reading environment goal probe).Holds (Meaning inputs)

def ChildLeaves (reading : Reading s Value) (environment : Environment Value)
    (children : List CheckGoal) (A B : Positive s) : Prop :=
  ∃ child, child ∈ children ∧ ∃ probe,
    A = lower reading environment child probe ∧ B = upper reading environment child probe

/-- A declaration is selected by its actual source identity, occurrence,
context and operand list. Its proof is syntax in the finite original local
calculus; the ONLY nonlogical leaves are fixed guard declarations above. -/
structure CheckDeclaration (inputs : Inputs s) (registry : GuardRegistry inputs) where
  signature : Signature s
  before : Probe s → Positive s
  after : Probe s → Positive s
  proof : ∀ probe, Proof inputs registry (fun _ _ => False) (before probe) (after probe)

structure Declarations (inputs : Inputs s) (registry : GuardRegistry inputs) where
  check : Declaration → Option (CheckDeclaration inputs registry)

structure PrimitiveShape (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (reading : Reading s Value)
    (environment : Environment Value) (declaration : Declaration) (goal : CheckGoal) where
  entry : CheckDeclaration inputs registry
  registered : declarations.check declaration = some entry
  identity : entry.signature.declaration = declaration
  owner : entry.signature.owner = goal.site
  context : entry.signature.context = goal.context
  operands : Operand.endpoint goal.lower ∈ entry.signature.operands ∧
    Operand.endpoint goal.upper ∈ entry.signature.operands
  source : entry.before = lower reading environment goal
  target : entry.after = upper reading environment goal

/-- Every structural tag retains its source-owned raw certificate. The
certificate is finite proof DATA, not the implication it is meant to prove.
The concrete record/union/intersection/result/equation suppliers above create
this data from their real field incidences and child goals. -/
structure StructuralShape (inputs : Inputs s) (registry : GuardRegistry inputs)
    (reading : Reading s Value) (environment : Environment Value)
    (rule : StructuralCheck) (goal : CheckGoal) (children : List CheckGoal) where
  signature : Signature s
  owner : signature.owner = goal.site
  context : signature.context = goal.context
  operands : Operand.endpoint goal.lower ∈ signature.operands ∧ Operand.endpoint goal.upper ∈ signature.operands
  originalMode : CheckMode
  modeReadback : originalMode = goal.mode
  schema : ∀ probe, Schema inputs registry (ChildLeaves reading environment children) rule
    (lower reading environment goal probe) (upper reading environment goal probe)

inductive FunctionLeaves (reading : Reading s Value)
    (admitted : Environment Value → CheckGoal → Binder → ScopedValue Value → Prop)
    (environment : Environment Value) (goal domain : CheckGoal) (binder : Binder) (observation : CheckGoal) :
    Positive s → Positive s → Prop where
  | domain (probe : Probe s) : FunctionLeaves reading admitted environment goal domain binder observation
      (lower reading environment domain probe) (upper reading environment domain probe)
  | observation (candidate : ScopedValue Value) (valid : admitted environment goal binder candidate) (probe : Probe s) :
      FunctionLeaves reading admitted environment goal domain binder observation
        (lower reading (environment.extend binder candidate) observation probe)
        (upper reading (environment.extend binder candidate) observation probe)

/-- The complete finite Function proof retains the contravariant domain,
covariant observation endpoints and every independently admitted invocation.
Its code must be constructed from actual descriptor/guard/capture/readback
registrations. Supplying this syntax is a remaining source application task
where those registrations have not yet been constructed. -/
structure FunctionShape (inputs : Inputs s) (registry : GuardRegistry inputs)
    (reading : Reading s Value)
    (admitted : Environment Value → CheckGoal → Binder → ScopedValue Value → Prop)
    (environment : Environment Value) (goal domain : CheckGoal) (binder : Binder)
    (observation : CheckGoal) : Prop where
  valueMode : goal.mode = .value
  owner : binder.site = goal.site
  domainLower : domain.lower = goal.upper
  domainUpper : domain.upper = goal.lower
  observationLower : observation.lower = goal.lower
  observationUpper : observation.upper = goal.upper
  domainContext : domain.context = goal.context
  observationContext : observation.context = goal.context
  proof : ∀ probe, Proof inputs registry (FunctionLeaves reading admitted environment goal domain binder observation)
    (lower reading environment goal probe) (upper reading environment goal probe)

/-- All seven original Kernel fields remain present. Atom/admission/tag and
DIRECT actual conversion meanings retain their original owning predicates.
The three checking fields are now finite registered proof constructions. -/
def kernel (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (reading : Reading s Value)
    (original : Kernel Value) : Kernel Value :=
  {original with
    primitiveCheck := fun environment declaration goal =>
      Nonempty (PrimitiveShape inputs registry declarations reading environment declaration goal)
    structuralShape := fun environment rule goal children =>
      Nonempty (StructuralShape inputs registry reading environment rule goal children)
    functionShape := FunctionShape inputs registry reading original.checkingAdmitted}

theorem primitive_sound (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (reading : Reading s Value)
    (environment : Environment Value) (declaration : Declaration) (goal : CheckGoal)
    (shape : PrimitiveShape inputs registry declarations reading environment declaration goal) :
    GoalMeaning inputs reading environment goal := by
  intro probe
  have action := (shape.entry.proof probe).sound inputs registry (fun _ _ impossible => False.elim impossible)
  rw [shape.source, shape.target] at action
  exact action

theorem structural_sound (inputs : Inputs s) (registry : GuardRegistry inputs)
    (reading : Reading s Value) (environment : Environment Value)
    (rule : StructuralCheck) (goal : CheckGoal) (children : List CheckGoal)
    (shape : StructuralShape inputs registry reading environment rule goal children)
    (childMeaning : ∀ child ∈ children, GoalMeaning inputs reading environment child) :
    GoalMeaning inputs reading environment goal := by
  intro probe
  apply (Schema.proof inputs registry (shape.schema probe)).sound inputs registry
  intro A B present
  obtain ⟨child, member, childProbe, rfl, rfl⟩ := present
  exact childMeaning child member childProbe

theorem function_sound (inputs : Inputs s) (registry : GuardRegistry inputs)
    (reading : Reading s Value) (original : Kernel Value)
    (environment : Environment Value) (goal domain : CheckGoal) (binder : Binder) (observation : CheckGoal)
    (shape : FunctionShape inputs registry reading original.checkingAdmitted environment goal domain binder observation)
    (domainMeaning : GoalMeaning inputs reading environment domain)
    (observationMeaning : ∀ candidate, original.checkingAdmitted environment goal binder candidate →
      GoalMeaning inputs reading (environment.extend binder candidate) observation) :
    GoalMeaning inputs reading environment goal := by
  intro probe
  apply (shape.proof probe).sound inputs registry
  intro A B present
  cases present with
  | domain childProbe => exact domainMeaning childProbe
  | observation candidate valid childProbe => exact observationMeaning candidate valid childProbe

theorem checking_sound (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (reading : Reading s Value)
    (original : Kernel Value) {environment : Environment Value} {goal : CheckGoal}
    (checked : Checking (kernel inputs registry declarations reading original) environment goal) :
    GoalMeaning inputs reading environment goal := by
  refine Checking.rec
    (motive_1 := fun environment goal _ => GoalMeaning inputs reading environment goal)
    (motive_2 := fun environment children _ => ∀ child ∈ children, GoalMeaning inputs reading environment child)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ checked
  · intro environment goal same
    simp only [GoalMeaning, lower, upper, same]
    exact fun _ => id
  · intro environment goal declaration valid
    obtain ⟨shape⟩ := valid
    exact primitive_sound inputs registry declarations reading _ declaration goal shape
  · intro environment mode site context first middle last left right leftIH rightIH
    exact fun probe valid => rightIH probe (leftIH probe valid)
  · intro environment rule goal children shape checked childIH
    obtain ⟨shape⟩ := shape
    exact structural_sound inputs registry reading _ rule goal children shape childIH
  · intro environment goal domain observation binder domainMode observationMode invocation shape domainProof observationProof domainIH observationIH
    exact function_sound inputs registry reading original _ goal domain binder observation shape domainIH observationIH
  · intro environment child member
    exact False.elim (List.not_mem_nil member)
  · intro environment head tail first rest firstIH restIH child member
    rcases List.mem_cons.mp member with same | later
    · subst child
      exact firstIH
    · exact restIH child later

theorem checkings_sound (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (reading : Reading s Value)
    (original : Kernel Value) {environment : Environment Value} {children : List CheckGoal}
    (checked : Checkings (kernel inputs registry declarations reading original) environment children) :
    ∀ child ∈ children, GoalMeaning inputs reading environment child := by
  have all : ∀ children, Checkings (kernel inputs registry declarations reading original) environment children →
      ∀ child ∈ children, GoalMeaning inputs reading environment child := by
    intro children
    induction children with
    | nil => intro checked child member; exact False.elim (List.not_mem_nil member)
    | cons head tail ih =>
        intro checked child member
        cases checked with
        | cons first rest =>
            rcases List.mem_cons.mp member with same | later
            · subst child
              exact checking_sound inputs registry declarations reading original first
            · exact ih rest child later
  exact all children checked

/-- The actual App inventory selects callee.returnedValue, never the
application's result. This equation is obtained from the original generator. -/
theorem generated_application_ports (context : Context) (site : Site)
    (callee argument : Source .expression) :
    ∃ atoms, sourceRules context (.app ⟨site, none⟩ callee argument) =
      .existsE ⟨site, .viewLogic, 0⟩
        (.rule .app site context
          (atoms ++ [.checking ⟨.value, site, context, ⟨callee.site, .returnedValue⟩, ⟨site, .descriptor⟩⟩,
            .checking ⟨.computation, site, context, ⟨site, .callableImage⟩, ⟨site, .synthesis⟩⟩])
          (.two (sourceRules context callee) (sourceRules context argument))) := by
  refine ⟨(([AtomKind.descriptorFormation, .wholeArgumentCompatibility,
    .completeCallCertificate, .sourceCallIncidence, .callableImage] ++
    if singletonFormalCall context callee argument then [AtomKind.roleAndInitialCallOrigin] else []).map
      (fun kind => Premise.atom (atom kind site context [callee.site, argument.site]))), ?_⟩
  simp only [sourceRules]
  rfl

theorem generated_application_checking (original : Kernel Value) (environment : Environment Value)
    (context : Context) (site : Site) (callee argument : Source .expression)
    (solved : Satisfies original environment (Build context (.app ⟨site, none⟩ callee argument))) :
    ∃ candidate, original.admitted environment ⟨site, .viewLogic, 0⟩ candidate ∧
      Checking original (environment.extend ⟨site, .viewLogic, 0⟩ candidate)
        ⟨.value, site, context, ⟨callee.site, .returnedValue⟩, ⟨site, .descriptor⟩⟩ := by
  have derivation := generated_constraints_imply_source_judgment original environment context
    (.app ⟨site, none⟩ callee argument) solved
  obtain ⟨atoms, inventory⟩ := generated_application_ports context site callee argument
  change Judgment original environment (sourceRules context (.app ⟨site, none⟩ callee argument)) at derivation
  rw [inventory] at derivation
  cases derivation with
  | existsE candidate admitted proof =>
      cases proof with
      | rule locals children =>
          have checked := locals (.checking ⟨.value, site, context, ⟨callee.site, .returnedValue⟩, ⟨site, .descriptor⟩⟩)
            (List.mem_append.mpr (Or.inr List.mem_cons_self))
          cases checked with
          | checking checked => exact ⟨candidate, admitted, checked⟩


open OriginalSourceEnvironment

/-- Raw source occurrence port ownership, independent of inferred membership.
App selects callee.returnedValue; the application result is a different port. -/
structure PortReadout (s : Sorts) (View : Type) where
  subject : Decoded s View → Site → Context → Endpoint
  equality : Decoded s View → Endpoint → Operand s

/-- Concrete endpoint reading from the ORIGINAL heterogeneous frame fold.
The equality operand readout is a typed original declaration-slot readout;
it does not infer a Value/Computation tag from a solved descriptor. -/
def stateClause (inputs : Inputs s) (ports : PortReadout s View)
    (state : Decoded s View) (mode : CheckMode) (site : Site) (context : Context) (endpoint : Endpoint) : Probe s → Positive s
  | .value event => match mode with
      | .value => .field (.value ⟨state.assignment.descriptor endpoint,
          state.assignment.value (ports.subject state site context), state.assignment.root (ports.subject state site context), event⟩)
      | _ => .guard False
  | .computation raw => match mode with
      | .computation => .field (.trace (raw.atInterface (state.interfaces endpoint)))
      | _ => .guard False
  | .domain input => match mode with
      | .domain => .both (.guard (input.event = state.assignment.event))
          (.guard (CheckedDomain inputs (inputChallenge input (state.assignment.descriptor endpoint))))
      | _ => .guard False
  | .observation raw => match mode with
      | .observation => match state.active with
          | none => .guard False
          | some input => inputs.checkedObservation (inputChallenge input (state.assignment.descriptor endpoint)) raw
      | _ => .guard False
  | .equality operand => match mode with
      | .equality => .guard (ports.equality state endpoint = operand)
      | _ => .guard False

def environmentReading (inputs : Inputs s) (readout : RuntimeReadout s View)
    (ports : PortReadout s View) : Reading s (Payload s View) :=
  fun environment mode site context endpoint probe =>
    match decode readout environment with
    | none => .guard False
    | some state => stateClause inputs ports state mode site context endpoint probe

theorem value_action (inputs : Inputs s) (readout : RuntimeReadout s View)
    (ports : PortReadout s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (goal : CheckGoal) (mode : goal.mode = .value)
    (action : GoalMeaning inputs (environmentReading inputs readout ports) environment goal)
    (event : Event s) :
    Meaning inputs (.value ⟨state.assignment.descriptor goal.lower,
      state.assignment.value (ports.subject state goal.site goal.context), state.assignment.root (ports.subject state goal.site goal.context), event⟩) →
    Meaning inputs (.value ⟨state.assignment.descriptor goal.upper,
      state.assignment.value (ports.subject state goal.site goal.context), state.assignment.root (ports.subject state goal.site goal.context), event⟩) := by
  simpa only [lower, upper, environmentReading, decoded, stateClause, mode, Positive.Holds] using action (.value event)

theorem computation_action (inputs : Inputs s) (readout : RuntimeReadout s View)
    (ports : PortReadout s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (goal : CheckGoal) (mode : goal.mode = .computation)
    (action : GoalMeaning inputs (environmentReading inputs readout ports) environment goal)
    (raw : RawObservation s) :
    Meaning inputs (.trace (raw.atInterface (state.interfaces goal.lower))) →
      Meaning inputs (.trace (raw.atInterface (state.interfaces goal.upper))) := by
  simpa only [lower, upper, environmentReading, decoded, stateClause, mode, Positive.Holds] using action (.computation raw)

theorem domain_action (inputs : Inputs s) (readout : RuntimeReadout s View)
    (ports : PortReadout s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (goal : CheckGoal) (mode : goal.mode = .domain)
    (action : GoalMeaning inputs (environmentReading inputs readout ports) environment goal) :
    DomainMeaning inputs state goal := by
  intro value root challenge admitted
  have result := action (.domain challenge.input)
  simp only [lower, upper, environmentReading, decoded, stateClause, mode, Positive.Holds] at result
  exact (result ⟨rfl, admitted⟩).2

theorem observation_action (inputs : Inputs s) (readout : RuntimeReadout s View)
    (ports : PortReadout s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (goal : CheckGoal) (mode : goal.mode = .observation)
    (input : CallInput s) (active : state.active = some input)
    (action : GoalMeaning inputs (environmentReading inputs readout ports) environment goal) :
    ObservationMeaning inputs (Meaning inputs) state goal := by
  rw [ObservationMeaning, active]
  intro raw
  simpa only [lower, upper, environmentReading, decoded, stateClause, mode, active, ObservationMem]
    using action (.observation raw)

theorem equality_action (inputs : Inputs s) (readout : RuntimeReadout s View)
    (ports : PortReadout s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (goal : CheckGoal) (mode : goal.mode = .equality)
    (action : GoalMeaning inputs (environmentReading inputs readout ports) environment goal) :
    ports.equality state goal.lower = ports.equality state goal.upper := by
  have result := action (.equality (ports.equality state goal.lower))
  simp only [lower, upper, environmentReading, decoded, stateClause, mode, Positive.Holds] at result
  exact (result True.intro).symm

def ModeMeaning (inputs : Inputs s) (ports : PortReadout s View) (state : Decoded s View)
    (goal : CheckGoal) : Prop :=
  match goal.mode with
  | .value => ∀ event,
      Meaning inputs (.value ⟨state.assignment.descriptor goal.lower,
        state.assignment.value (ports.subject state goal.site goal.context),
        state.assignment.root (ports.subject state goal.site goal.context), event⟩) →
      Meaning inputs (.value ⟨state.assignment.descriptor goal.upper,
        state.assignment.value (ports.subject state goal.site goal.context),
        state.assignment.root (ports.subject state goal.site goal.context), event⟩)
  | .computation => ∀ raw : RawObservation s,
      Meaning inputs (.trace (raw.atInterface (state.interfaces goal.lower))) →
      Meaning inputs (.trace (raw.atInterface (state.interfaces goal.upper)))
  | .domain => ∀ input : CallInput s, input.event = state.assignment.event →
      CheckedDomain inputs (inputChallenge input (state.assignment.descriptor goal.lower)) →
      CheckedDomain inputs (inputChallenge input (state.assignment.descriptor goal.upper))
  | .observation => match state.active with
      | none => True
      | some input => ∀ raw, ObservationMem inputs (Meaning inputs)
          (inputChallenge input (state.assignment.descriptor goal.lower)) raw →
        ObservationMem inputs (Meaning inputs) (inputChallenge input (state.assignment.descriptor goal.upper)) raw
  | .equality => ports.equality state goal.lower = ports.equality state goal.upper

/-- Identifies all five concrete mode readings. The no-active observation
case is explicitly a conditional action only; its nonvacuous original use is
proved by admitted_invocation_has_active and observation_action below. -/
theorem goal_meaning_iff (inputs : Inputs s) (readout : RuntimeReadout s View)
    (ports : PortReadout s View) (environment : Environment (Payload s View))
    (state : Decoded s View) (decoded : decode readout environment = some state) (goal : CheckGoal) :
    GoalMeaning inputs (environmentReading inputs readout ports) environment goal ↔
      ModeMeaning inputs ports state goal := by
  unfold ModeMeaning
  cases mode : goal.mode with
  | value =>
      constructor
      · exact fun action => value_action inputs readout ports environment state decoded goal mode action
      · intro action probe
        cases probe <;> simp only [lower, upper, environmentReading, decoded, stateClause, mode, Positive.Holds]
        · exact action _
        all_goals exact id
  | computation =>
      constructor
      · exact fun action => computation_action inputs readout ports environment state decoded goal mode action
      · intro action probe
        cases probe <;> simp only [lower, upper, environmentReading, decoded, stateClause, mode, Positive.Holds]
        · exact id
        · exact action _
        all_goals exact id
  | domain =>
      constructor
      · intro action input event valid
        have result := action (.domain input)
        simp only [lower, upper, environmentReading, decoded, stateClause, mode, Positive.Holds] at result
        exact (result ⟨event, valid⟩).2
      · intro action probe
        cases probe <;> simp only [lower, upper, environmentReading, decoded, stateClause, mode, Positive.Holds]
        · exact id
        · exact id
        · exact fun ⟨event, valid⟩ => ⟨event, action _ event valid⟩
        all_goals exact id
  | observation =>
      cases active : state.active with
      | none =>
          constructor
          · exact fun _ => True.intro
          · intro action probe
            cases probe <;> simp only [lower, upper, environmentReading, decoded, stateClause, mode, active, Positive.Holds]
            all_goals exact id
      | some input =>
          constructor
          · intro action raw
            simpa only [lower, upper, environmentReading, decoded, stateClause, mode, active, ObservationMem]
              using action (.observation raw)
          · intro action probe
            cases probe <;> simp only [lower, upper, environmentReading, decoded, stateClause, mode, active, Positive.Holds]
            · exact id
            · exact id
            · exact id
            · exact action _
            · exact id
  | equality =>
      constructor
      · exact fun action => equality_action inputs readout ports environment state decoded goal mode action
      · intro action probe
        have same : ports.equality state goal.lower = ports.equality state goal.upper := action
        cases probe <;> simp only [lower, upper, environmentReading, decoded, stateClause, mode, Positive.Holds]
        all_goals simpa only [same] using (id : _ → _)

/-- Nonvacuity comes from the ACTUAL admitted invocation constructor.
Every such candidate decodes and contains its actual active CallInput; no
observation identity outside an invocation is promoted to observation safety. -/
theorem admitted_invocation_has_active (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (binder : Binder) (state : Decoded s View) (decoded : decode readout environment = some state)
    (candidate : ScopedValue (Payload s View))
    (admitted : Admitted inputs readout admissions environment binder candidate)
    (kind : binder.kind = .invocation) :
    ∃ next input, decode readout (environment.extend binder candidate) = some next ∧ next.active = some input := by
  obtain ⟨raw, payload, value, root, domain⟩ :=
    admission_recovers_challenge inputs readout admissions environment binder state decoded candidate admitted kind
  refine ⟨decodeFrame readout state ⟨binder, candidate, environment.eventPath⟩,
    (raw.challenge (readout.event state.fixedFrames state.assignment.event binder (.invocation raw))
      (state.assignment.descriptor ⟨binder.site, .descriptor⟩) state.viewMeaning).input,
    decode_extend readout environment binder candidate state decoded, ?_⟩
  simpa only [decodeFrame, payload, Decoded.retain] using runtime_invocation_captures_input readout state binder raw

theorem value_shape (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (rule : StructuralCheck)
    (goal : CheckGoal) (children : List CheckGoal) (mode : goal.mode = .value)
    (signature : Signature s) (owner : signature.owner = goal.site)
    (context : signature.context = goal.context)
    (operands : Operand.endpoint goal.lower ∈ signature.operands ∧ Operand.endpoint goal.upper ∈ signature.operands)
    (family : ∀ event, Schema inputs registry
      (ChildLeaves (environmentReading inputs readout ports) environment children) rule
        (.field (.value ⟨state.assignment.descriptor goal.lower,
          state.assignment.value (ports.subject state goal.site goal.context),
          state.assignment.root (ports.subject state goal.site goal.context), event⟩))
        (.field (.value ⟨state.assignment.descriptor goal.upper,
          state.assignment.value (ports.subject state goal.site goal.context),
          state.assignment.root (ports.subject state goal.site goal.context), event⟩))) :
    Nonempty (StructuralShape inputs registry (environmentReading inputs readout ports)
      environment rule goal children) := by
  refine ⟨⟨signature, owner, context, operands, .value, mode.symm, ?_⟩⟩
  intro probe
  cases probe with
  | value event =>
      simpa only [lower, upper, environmentReading, decoded, stateClause, mode] using family event
  | computation raw | domain input | observation raw | equality operand =>
      simp only [lower, upper, environmentReading, decoded, stateClause, mode]
      exact .inactive rule

/-- Concrete source-owned record shape. This constructor checks the actual
descriptor slots, label-preserving field selection, full decorated child
incidence and source mode. Its proof is built, not passed as a shape field. -/
theorem record_shape (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (goal : CheckGoal) (children : List CheckGoal)
    (mode : goal.mode = .value) (signature : Signature s) (owner : signature.owner = goal.site)
    (context : signature.context = goal.context)
    (operands : Operand.endpoint goal.lower ∈ signature.operands ∧ Operand.endpoint goal.upper ∈ signature.operands)
    (source target : RecordRegistration inputs)
    (sourceSlot : state.assignment.descriptor goal.lower = source.descriptor)
    (targetSlot : state.assignment.descriptor goal.upper = target.descriptor)
    (select : Fin target.labels.length → Fin source.labels.length)
    (labels : ∀ index, target.labels[index] = source.labels[select index])
    (actual : ∀ event index,
      (source.field (state.assignment.value (ports.subject state goal.site goal.context))
        (state.assignment.root (ports.subject state goal.site goal.context)) event (select index)).value =
      (target.field (state.assignment.value (ports.subject state goal.site goal.context))
        (state.assignment.root (ports.subject state goal.site goal.context)) event index).value ∧
      (source.field (state.assignment.value (ports.subject state goal.site goal.context))
        (state.assignment.root (ports.subject state goal.site goal.context)) event (select index)).root =
      (target.field (state.assignment.value (ports.subject state goal.site goal.context))
        (state.assignment.root (ports.subject state goal.site goal.context)) event index).root ∧
      (source.field (state.assignment.value (ports.subject state goal.site goal.context))
        (state.assignment.root (ports.subject state goal.site goal.context)) event (select index)).event =
      (target.field (state.assignment.value (ports.subject state goal.site goal.context))
        (state.assignment.root (ports.subject state goal.site goal.context)) event index).event)
    (guards : ∀ event, Proof inputs registry
      (ChildLeaves (environmentReading inputs readout ports) environment children)
      (.guard (inputs.structuralGuard ⟨source.descriptor,
        state.assignment.value (ports.subject state goal.site goal.context),
        state.assignment.root (ports.subject state goal.site goal.context), event⟩))
      (.guard (inputs.structuralGuard ⟨target.descriptor,
        state.assignment.value (ports.subject state goal.site goal.context),
        state.assignment.root (ports.subject state goal.site goal.context), event⟩)))
    (fields : ∀ event index, ChildLeaves (environmentReading inputs readout ports) environment children
      (.field (.value (source.field (state.assignment.value (ports.subject state goal.site goal.context))
        (state.assignment.root (ports.subject state goal.site goal.context)) event (select index))))
      (.field (.value (target.field (state.assignment.value (ports.subject state goal.site goal.context))
        (state.assignment.root (ports.subject state goal.site goal.context)) event index)))) :
    Nonempty (StructuralShape inputs registry (environmentReading inputs readout ports)
      environment .recordWidthDepth goal children) := by
  apply value_shape inputs registry readout ports environment state decoded .recordWidthDepth
    goal children mode signature owner context operands
  intro event
  rw [sourceSlot, targetSlot]
  exact .record source target _ _ select labels actual guards fields event


def PortReadout.application (base : PortReadout s View) (site : Site) (context : Context)
    (callee : Site) : PortReadout s View :=
  {base with subject := fun state occurrence scope =>
    if occurrence = site ∧ scope = context then ⟨callee, .returnedValue⟩ else base.subject state occurrence scope}

theorem application_subject (base : PortReadout s View) (state : Decoded s View)
    (site : Site) (context : Context) (callee : Site) :
    (base.application site context callee).subject state site context = ⟨callee, .returnedValue⟩ := by
  simp only [PortReadout.application, and_self, ite_true]

/-- Application of the finite checking induction to an ACTUAL generated
source check and its actual ViewLogic witness. Decoding the successor is
constructed from the original predecessor; the callable endpoint is the
callee's returnedValue, distinct from the application result. -/
theorem generated_application_value_action (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (readout : RuntimeReadout s View)
    (ports : PortReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (context : Context) (site : Site)
    (callee argument : Source .expression)
    (solved : Satisfies (kernel inputs registry declarations
      (environmentReading inputs readout (ports.application site context callee.site)) original)
      environment (Build context (.app ⟨site, none⟩ callee argument))) :
    ∃ candidate next,
      original.admitted environment ⟨site, .viewLogic, 0⟩ candidate ∧
      decode readout (environment.extend ⟨site, .viewLogic, 0⟩ candidate) = some next ∧
      (Meaning inputs (.value ⟨next.assignment.descriptor ⟨callee.site, .returnedValue⟩,
        next.assignment.value ⟨callee.site, .returnedValue⟩, next.assignment.root ⟨callee.site, .returnedValue⟩,
        next.assignment.event⟩) →
       Meaning inputs (.value ⟨next.assignment.descriptor ⟨site, .descriptor⟩,
        next.assignment.value ⟨callee.site, .returnedValue⟩, next.assignment.root ⟨callee.site, .returnedValue⟩,
        next.assignment.event⟩)) := by
  obtain ⟨candidate, admitted, checked⟩ := generated_application_checking
    (kernel inputs registry declarations (environmentReading inputs readout (ports.application site context callee.site)) original)
    environment context site callee argument solved
  let next := decodeFrame readout state ⟨⟨site, .viewLogic, 0⟩, candidate, environment.eventPath⟩
  have nextDecoded := decode_extend readout environment ⟨site, .viewLogic, 0⟩ candidate state decoded
  refine ⟨candidate, next, admitted, nextDecoded, ?_⟩
  have action := checking_sound inputs registry declarations
    (environmentReading inputs readout (ports.application site context callee.site)) original checked
  have result := value_action inputs readout (ports.application site context callee.site)
    (environment.extend ⟨site, .viewLogic, 0⟩ candidate) next nextDecoded _ rfl action next.assignment.event
  simpa only [application_subject] using result

theorem boundary_cases (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (reading : Reading s Value) (original : Kernel Value)
    (environment : Environment Value) (site : Site) (context : Context) (first last : Endpoint)
    (boundary : Boundary (kernel inputs registry declarations reading original) environment site context first last) :
    (∃ mode, original.boundaryTag environment site context first last mode ∧
      GoalMeaning inputs reading environment ⟨mode, site, context, first, last⟩) ∨
      ∃ declaration, original.conversion environment site context first last declaration := by
  cases boundary with
  | proofOnly mode tag proof =>
      exact Or.inl ⟨mode, tag, checking_sound inputs registry declarations reading original proof⟩
  | actual declaration valid => exact Or.inr ⟨declaration, valid⟩

structure ValueOccurrence (s : Sorts) (View : Type) (readout : RuntimeReadout s View)
    (environment : Environment (Payload s View)) (goal : CheckGoal) where
  state : Decoded s View
  decoded : decode readout environment = some state
  mode : goal.mode = .value
  signature : Signature s
  owner : signature.owner = goal.site
  context : signature.context = goal.context
  operands : Operand.endpoint goal.lower ∈ signature.operands ∧ Operand.endpoint goal.upper ∈ signature.operands

def ValueOccurrence.value (ports : PortReadout s View)
    (occurrence : ValueOccurrence s View readout environment goal) : s.Value :=
  occurrence.state.assignment.value (ports.subject occurrence.state goal.site goal.context)

def ValueOccurrence.root (ports : PortReadout s View)
    (occurrence : ValueOccurrence s View readout environment goal) : s.Root :=
  occurrence.state.assignment.root (ports.subject occurrence.state goal.site goal.context)

theorem union_cases_shape (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (environment : Environment (Payload s View)) (goal : CheckGoal) (children : List CheckGoal)
    (occurrence : ValueOccurrence s View readout environment goal) (union : UnionRegistration inputs)
    (sourceSlot : occurrence.state.assignment.descriptor goal.lower = union.descriptor)
    (left : ∀ event, ChildLeaves (environmentReading inputs readout ports) environment children
      (.field (.value ⟨union.left, occurrence.value ports, occurrence.root ports, event⟩))
      (.field (.value ⟨occurrence.state.assignment.descriptor goal.upper, occurrence.value ports, occurrence.root ports, event⟩)))
    (right : ∀ event, ChildLeaves (environmentReading inputs readout ports) environment children
      (.field (.value ⟨union.right, occurrence.value ports, occurrence.root ports, event⟩))
      (.field (.value ⟨occurrence.state.assignment.descriptor goal.upper, occurrence.value ports, occurrence.root ports, event⟩))) :
    Nonempty (StructuralShape inputs registry (environmentReading inputs readout ports)
      environment .unionCases goal children) := by
  apply value_shape inputs registry readout ports environment occurrence.state occurrence.decoded
    .unionCases goal children occurrence.mode occurrence.signature occurrence.owner occurrence.context occurrence.operands
  intro event
  rw [sourceSlot]
  exact .unionCases union _ (occurrence.value ports) (occurrence.root ports) left right event

theorem union_injection_shape (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (environment : Environment (Payload s View)) (goal : CheckGoal) (children : List CheckGoal)
    (occurrence : ValueOccurrence s View readout environment goal) (union : UnionRegistration inputs)
    (sourceSlot : occurrence.state.assignment.descriptor goal.lower = union.left)
    (targetSlot : occurrence.state.assignment.descriptor goal.upper = union.descriptor)
    (guards : ∀ event, Proof inputs registry (ChildLeaves (environmentReading inputs readout ports) environment children)
      (.both (.field (.value ⟨union.left, occurrence.value ports, occurrence.root ports, event⟩))
        (valueCore inputs ⟨union.left, occurrence.value ports, occurrence.root ports, event⟩))
      (.guard (inputs.structuralGuard ⟨union.descriptor, occurrence.value ports, occurrence.root ports, event⟩))) :
    Nonempty (StructuralShape inputs registry (environmentReading inputs readout ports)
      environment .unionInjection goal children) := by
  apply value_shape inputs registry readout ports environment occurrence.state occurrence.decoded
    .unionInjection goal children occurrence.mode occurrence.signature occurrence.owner occurrence.context occurrence.operands
  intro event
  rw [sourceSlot, targetSlot]
  exact .unionInjection union (occurrence.value ports) (occurrence.root ports) guards event

theorem intersection_shape (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (environment : Environment (Payload s View)) (goal : CheckGoal) (children : List CheckGoal)
    (occurrence : ValueOccurrence s View readout environment goal) (target : IntersectionRegistration inputs)
    (targetSlot : occurrence.state.assignment.descriptor goal.upper = target.descriptor)
    (guards : ∀ event, Proof inputs registry (ChildLeaves (environmentReading inputs readout ports) environment children)
      (.both (.field (.value ⟨occurrence.state.assignment.descriptor goal.lower, occurrence.value ports, occurrence.root ports, event⟩))
        (valueCore inputs ⟨occurrence.state.assignment.descriptor goal.lower, occurrence.value ports, occurrence.root ports, event⟩))
      (.guard (inputs.structuralGuard ⟨target.descriptor, occurrence.value ports, occurrence.root ports, event⟩)))
    (left : ∀ event, ChildLeaves (environmentReading inputs readout ports) environment children
      (.field (.value ⟨occurrence.state.assignment.descriptor goal.lower, occurrence.value ports, occurrence.root ports, event⟩))
      (.field (.value ⟨target.left, occurrence.value ports, occurrence.root ports, event⟩)))
    (right : ∀ event, ChildLeaves (environmentReading inputs readout ports) environment children
      (.field (.value ⟨occurrence.state.assignment.descriptor goal.lower, occurrence.value ports, occurrence.root ports, event⟩))
      (.field (.value ⟨target.right, occurrence.value ports, occurrence.root ports, event⟩))) :
    Nonempty (StructuralShape inputs registry (environmentReading inputs readout ports)
      environment .intersection goal children) := by
  apply value_shape inputs registry readout ports environment occurrence.state occurrence.decoded
    .intersection goal children occurrence.mode occurrence.signature occurrence.owner occurrence.context occurrence.operands
  intro event
  rw [targetSlot]
  exact .intersection target _ (occurrence.value ports) (occurrence.root ports) guards left right event

theorem top_shape (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (environment : Environment (Payload s View)) (goal : CheckGoal) (children : List CheckGoal)
    (occurrence : ValueOccurrence s View readout environment goal) (top : TopRegistration inputs registry)
    (targetSlot : occurrence.state.assignment.descriptor goal.upper = top.descriptor)
    (guards : ∀ event, Proof inputs registry (ChildLeaves (environmentReading inputs readout ports) environment children)
      (.both (.field (.value ⟨occurrence.state.assignment.descriptor goal.lower, occurrence.value ports, occurrence.root ports, event⟩))
        (valueCore inputs ⟨occurrence.state.assignment.descriptor goal.lower, occurrence.value ports, occurrence.root ports, event⟩))
      (.guard ((top.guard (occurrence.value ports) (occurrence.root ports) event).Holds inputs registry.original))) :
    Nonempty (StructuralShape inputs registry (environmentReading inputs readout ports)
      environment .top goal children) := by
  apply value_shape inputs registry readout ports environment occurrence.state occurrence.decoded
    .top goal children occurrence.mode occurrence.signature occurrence.owner occurrence.context occurrence.operands
  intro event
  rw [targetSlot]
  exact .topValue top _ (occurrence.value ports) (occurrence.root ports) guards event

theorem computation_shape (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (rule : StructuralCheck)
    (goal : CheckGoal) (children : List CheckGoal) (mode : goal.mode = .computation)
    (signature : Signature s) (owner : signature.owner = goal.site) (context : signature.context = goal.context)
    (operands : Operand.endpoint goal.lower ∈ signature.operands ∧ Operand.endpoint goal.upper ∈ signature.operands)
    (family : ∀ raw : RawObservation s, Schema inputs registry
      (ChildLeaves (environmentReading inputs readout ports) environment children) rule
      (.field (.trace (raw.atInterface (state.interfaces goal.lower))))
      (.field (.trace (raw.atInterface (state.interfaces goal.upper))))) :
    Nonempty (StructuralShape inputs registry (environmentReading inputs readout ports)
      environment rule goal children) := by
  refine ⟨⟨signature, owner, context, operands, .computation, mode.symm, ?_⟩⟩
  intro probe
  cases probe with
  | computation raw =>
      simpa only [lower, upper, environmentReading, decoded, stateClause, mode] using family raw
  | value event | domain input | observation raw | equality operand =>
      simp only [lower, upper, environmentReading, decoded, stateClause, mode]
      exact .inactive rule

/-- Complete Result phase readback, covering both a Return and every
unfinished/pending original observation. The same raw observation is an
index; it is never replaced with a completed result. -/
inductive ResultPair (inputs : Inputs s) (leaves : Positive s → Positive s → Prop)
    (raw : RawObservation s) (source target : s.Interface) : Prop where
  | returned (first last : ValueRow s)
      (sourceForm : inputs.traceForm (raw.atInterface source) = .pureReturn first)
      (targetForm : inputs.traceForm (raw.atInterface target) = .pureReturn last)
      (sameValue : first.value = last.value) (sameRoot : first.root = last.root) (sameEvent : first.event = last.event)
      (guards : inputs.observationGuards (raw.atInterface source) = inputs.observationGuards (raw.atInterface target))
      (latent : inputs.observationFields (raw.atInterface source) = inputs.observationFields (raw.atInterface target))
      (child : leaves (.field (.value first)) (.field (.value last))) : ResultPair inputs leaves raw source target
  | unfinished
      (sourceForm : inputs.traceForm (raw.atInterface source) = .unfinished)
      (targetForm : inputs.traceForm (raw.atInterface target) = .unfinished)
      (guards : inputs.observationGuards (raw.atInterface source) = inputs.observationGuards (raw.atInterface target))
      (latent : inputs.observationFields (raw.atInterface source) = inputs.observationFields (raw.atInterface target)) :
      ResultPair inputs leaves raw source target

theorem result_shape (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (goal : CheckGoal) (children : List CheckGoal)
    (mode : goal.mode = .computation) (signature : Signature s) (owner : signature.owner = goal.site)
    (context : signature.context = goal.context)
    (operands : Operand.endpoint goal.lower ∈ signature.operands ∧ Operand.endpoint goal.upper ∈ signature.operands)
    (phases : ∀ raw, ResultPair inputs (ChildLeaves (environmentReading inputs readout ports) environment children)
      raw (state.interfaces goal.lower) (state.interfaces goal.upper)) :
    Nonempty (StructuralShape inputs registry (environmentReading inputs readout ports)
      environment .result goal children) := by
  apply computation_shape inputs registry readout ports environment state decoded .result goal children
    mode signature owner context operands
  intro raw
  cases phases raw with
  | returned first last sourceForm targetForm sameValue sameRoot sameEvent guards latent child =>
      exact .result _ _ first last sourceForm targetForm rfl sameValue sameRoot sameEvent guards latent child
  | unfinished sourceForm targetForm guards latent =>
      exact .unfinished _ _ sourceForm targetForm rfl guards latent

structure GuaranteePair (inputs : Inputs s) (registry : GuardRegistry inputs)
    (raw : RawObservation s) (source target : s.Interface) where
  identifier : Nat
  entry : GuardDeclaration s
  registered : registry.declaration identifier = some entry
  latent : Positive s
  sourceReadback : clause inputs (.trace (raw.atInterface source)) =
    .both (.guard (entry.before.Holds inputs registry.original)) latent
  targetReadback : clause inputs (.trace (raw.atInterface target)) =
    .both (.guard (entry.after.Holds inputs registry.original)) latent

theorem guarantee_shape (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (goal : CheckGoal) (children : List CheckGoal)
    (mode : goal.mode = .computation) (signature : Signature s) (owner : signature.owner = goal.site)
    (context : signature.context = goal.context)
    (operands : Operand.endpoint goal.lower ∈ signature.operands ∧ Operand.endpoint goal.upper ∈ signature.operands)
    (registered : ∀ raw, GuaranteePair inputs registry raw (state.interfaces goal.lower) (state.interfaces goal.upper)) :
    Nonempty (StructuralShape inputs registry (environmentReading inputs readout ports)
      environment .guaranteeWeakening goal children) := by
  apply computation_shape inputs registry readout ports environment state decoded .guaranteeWeakening goal children
    mode signature owner context operands
  intro raw
  let pair := registered raw
  exact .registered
    ⟨pair.entry.signature, .trace (raw.atInterface (state.interfaces goal.lower)), _, pair.sourceReadback⟩
    ⟨pair.entry.signature, .trace (raw.atInterface (state.interfaces goal.upper)), _, pair.targetReadback⟩
    (.guarantee pair.identifier pair.entry pair.registered pair.latent)

/-- An observation structural rule is read at its actual admitted input,
not at an invented body event or at an independently selected observation.
The full positive P clause is retained, including its original binders. -/
theorem observation_shape (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (rule : StructuralCheck)
    (goal : CheckGoal) (children : List CheckGoal) (mode : goal.mode = .observation)
    (input : CallInput s) (active : state.active = some input)
    (signature : Signature s) (owner : signature.owner = goal.site) (context : signature.context = goal.context)
    (operands : Operand.endpoint goal.lower ∈ signature.operands ∧ Operand.endpoint goal.upper ∈ signature.operands)
    (family : ∀ raw, Schema inputs registry
      (ChildLeaves (environmentReading inputs readout ports) environment children) rule
      (inputs.checkedObservation (inputChallenge input (state.assignment.descriptor goal.lower)) raw)
      (inputs.checkedObservation (inputChallenge input (state.assignment.descriptor goal.upper)) raw)) :
    Nonempty (StructuralShape inputs registry (environmentReading inputs readout ports)
      environment rule goal children) := by
  refine ⟨⟨signature, owner, context, operands, .observation, mode.symm, ?_⟩⟩
  intro probe
  cases probe with
  | observation raw =>
      simpa only [lower, upper, environmentReading, decoded, stateClause, mode, active] using family raw
  | value event | computation raw | domain input | equality operand =>
      simp only [lower, upper, environmentReading, decoded, stateClause, mode]
      exact .inactive rule

/-- Actual original invocation application of the completed finite checking
induction. The domain and observation implications are DERIVED from the two
recursive Checking proofs. The actual view/event/target-slot equations and
the independent guard/capture proof codes remain visibly owned inputs.

This is the current-event Function readout, not a general recursive L4 rule.
The target-slot equation is not hidden in the raw shape: the original
goal-indexed admission telescope for arbitrary compose intermediates remains
a separate original source-registration obligation. -/
theorem function_children_at_meaning (inputs : Inputs s) (registry : GuardRegistry inputs)
    (declarations : Declarations inputs registry) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (ports : PortReadout s View)
    (original : Kernel (Payload s View)) (environment : Environment (Payload s View))
    (goal domain observation : CheckGoal) (binder : Binder)
    (shape : OriginalSourceEnvironment.FunctionShape inputs readout environment goal domain binder observation)
    (domainChecked : Checking (kernel inputs registry declarations (environmentReading inputs readout ports) original)
      environment domain)
    (observationChecked : ∀ candidate, Admitted inputs readout admissions environment binder candidate →
      Checking (kernel inputs registry declarations (environmentReading inputs readout ports) original)
        (environment.extend binder candidate) observation)
    (state : Decoded s View) (decoded : decode readout environment = some state)
    (targetReadback : (state.callRow binder).descriptor = state.assignment.descriptor goal.upper)
    (token : s.Receipt → View)
    (viewReadback : ∀ challenge : Challenge (state.callRow binder), inputs.checkedIncidences challenge →
      state.viewMeaning (token challenge.receipt) = challenge.carrierView)
    (eventReadback : ∀ challenge : Challenge (state.callRow binder), inputs.checkedIncidences challenge →
      readout.event state.fixedFrames state.assignment.event binder (.invocation (encodeInvocation challenge (token challenge.receipt))) =
        (state.callRow binder).event)
    (occurrence : Nat)
    (source : FunctionAt inputs (Meaning inputs) ((state.goalRow binder goal).withDescriptor
      (state.assignment.descriptor goal.lower)))
    (guardCode : ∀ provider, inputs.actual (state.goalRow binder goal).value (state.goalRow binder goal).root provider →
      Proof inputs registry (fun _ _ => False)
        (.guard (inputs.functionGuards ((state.goalRow binder goal).withDescriptor
          (state.assignment.descriptor goal.lower)) provider).Valid)
        (.guard (inputs.functionGuards (state.goalRow binder goal) provider).Valid))
    (captureCode : ∀ provider, inputs.actual (state.goalRow binder goal).value (state.goalRow binder goal).root provider →
      Proof inputs registry (fun _ _ => False)
        (inputs.capturedFields ((state.goalRow binder goal).withDescriptor
          (state.assignment.descriptor goal.lower)) provider)
        (inputs.capturedFields (state.goalRow binder goal) provider)) :
    FunctionAt inputs (Meaning inputs) (state.goalRow binder goal) := by
  have domainMeaning := domain_action inputs readout ports environment state decoded domain shape.domainMode
    (checking_sound inputs registry declarations (environmentReading inputs readout ports) original domainChecked)
  have observationMeaning : ∀ candidate, Admitted inputs readout admissions environment binder candidate →
      ∀ next, decode readout (environment.extend binder candidate) = some next →
        ObservationMeaning inputs (Meaning inputs) next observation := by
    intro candidate admitted next nextDecoded
    obtain ⟨actual, input, actualDecoded, active⟩ := admitted_invocation_has_active inputs readout admissions
      environment binder state decoded candidate admitted shape.invocationKind
    have same : actual = next := Option.some.inj (actualDecoded.symm.trans nextDecoded)
    subst actual
    exact observation_action inputs readout ports (environment.extend binder candidate) next nextDecoded
      observation shape.observationMode input active
      (checking_sound inputs registry declarations (environmentReading inputs readout ports) original
        (observationChecked candidate admitted))
  have rowSame : state.goalRow binder goal = state.callRow binder := by
    simp only [Decoded.goalRow, Decoded.callRow, ValueRow.withDescriptor] at targetReadback ⊢
    rw [targetReadback]
  rw [rowSame] at source guardCode captureCode ⊢
  apply same_provider_function_check inputs (Meaning inputs) (state.callRow binder)
    (state.assignment.descriptor goal.lower) source
  · intro provider actual
    exact (guardCode provider actual).sound inputs registry (fun _ _ impossible => False.elim impossible)
      (source.2 provider actual).1
  · intro provider actual
    exact (captureCode provider actual).sound inputs registry (fun _ _ impossible => False.elim impossible)
      (source.2 provider actual).2.1
  · intro challenge admitted
    unfold DomainMeaning at domainMeaning
    rw [shape.domainLower, shape.domainUpper, ← targetReadback] at domainMeaning
    exact domainMeaning _ _ challenge admitted
  · intro challenge admitted raw valid
    have incidence := admitted.2.2.2.2.1
    have action := observation_child_transport inputs (Meaning inputs) readout admissions environment binder
      shape.invocationKind state decoded observation
      (by simpa only [shape.observationUpper] using targetReadback.symm)
      observationMeaning challenge admitted (token challenge.receipt)
      (viewReadback challenge incidence) (eventReadback challenge incidence) occurrence
    rw [shape.observationLower] at action
    exact action raw valid

end YulangClosure.OriginalSourceChecking
