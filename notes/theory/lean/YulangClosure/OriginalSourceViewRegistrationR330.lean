import YulangClosure.OriginalInterfacePreservationR328

/-!
R330: source-owned STATIC definition registration at the actual R315 ViewLogic.
Authority: generated-computed-result-correspondence §§2–3 (GR1), EI §§2,4.

The registry adds a separate address space and retains the entire original
source program. Its consumer reads typed constructor expressions, not semantic
membership. It is not a Decoded environment and does not reinterpret any old
endpoint. Full EI phase interpretation, dependent arm interpretation, actual
result/future incidence and the semantic R293 catalogue remain OPEN.
-/
namespace YulangClosure.OriginalSourceViewRegistrationR330

open OriginalSource OriginalScopedClosure OriginalSourceEnvironment
open OriginalSourceInterpretation ComputedCallTypedFormationR310
open OriginalInterfacePreservationR328

abbrev request := Selected.request
abbrev Code := Selected.Code

/-- The real logical binder, immediately outside the selected Call row. -/
def owner (origin : Declaration) : Occurrence :=
  atBinder (OriginalScopedSourceEventMapR314.Fixture.position origin) ⟨1, .viewLogic, 0⟩

def viewOwner : Program → Option Occurrence
  | .existsE occurrence _ =>
      if occurrence.binder.kind == .viewLogic then some occurrence else none
  | _ => none

theorem original_owner_computed (origin : Declaration) :
    ((SourceGraphRegistrationR297.sourceInventory origin
      OriginalModuleContextBindingR315.externalContext
      OriginalScopedSourceEventMapR314.Fixture.root)[12]?).bind
        (fun row => viewOwner row.program) = some (owner origin) := by
  run_tac Lean.Meta.withTransparency .all <| Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))

theorem original_call_computed (origin : Declaration) :
    ((SourceGraphRegistrationR297.sourceInventory origin
      OriginalModuleContextBindingR315.externalContext
      OriginalScopedSourceEventMapR314.Fixture.root)[13]?).bind callRecord =
        some (request origin).original := Selected.actual_request origin

theorem original_description_scope (origin : Declaration) :
    (request origin).original.position =
      (owner origin).position.under (.existsE (owner origin).binder) := by
  rfl

/-- An owning record stores the definition, not an independently selected
Interface inhabitant. Formation refers to independent original declarations. -/
structure Definition (origin : Declaration) (declared : Key → Prop) where
  arms : List (Arm [])
  operands : StaticFormation declared (request origin).operands
  armFormation : ∀ arm ∈ arms, declared arm.descriptor.key

def Definition.code {origin : Declaration} {declared : Key → Prop}
    (definition : Definition origin declared) : Code :=
  Selected.resultCode origin definition.arms

theorem definition_formed {origin : Declaration} {declared : Key → Prop}
    (definition : Definition origin declared) : Formed declared definition.code.2 :=
  form declared (request origin) definition.arms definition.operands definition.armFormation

/-- Original source and generated keys are disjoint by construction. -/
abbrev Address := Sum Endpoint Key

/-- One new definition in its actual original description region. The entire
original program is carried alongside it; no ordinary source node is replaced. -/
structure Registry (origin : Declaration) (declared : Key → Prop) where
  original : Program
  definitions : List (Occurrence × Key × Code)

def register {origin : Declaration} {declared : Key → Prop}
    (definition : Definition origin declared) : Registry origin declared :=
  ⟨source origin OriginalModuleContextBindingR315.externalContext
      OriginalScopedSourceEventMapR314.Fixture.root,
    [(owner origin, (request origin).generatedResult.key, definition.code)]⟩

def Registry.read {origin : Declaration} {declared : Key → Prop}
    (registry : Registry origin declared) (location : Occurrence) (key : Key) : Option Code :=
  ((registry.definitions.find? fun entry => entry.1 == location && entry.2.1 == key)).map
    (fun entry => entry.2.2)

theorem registered_readback {origin : Declaration} {declared : Key → Prop}
    (definition : Definition origin declared) :
    (register definition).read (owner origin) (request origin).generatedResult.key =
      some (Selected.resultCode origin definition.arms) := by
  simp [register, Registry.read, Definition.code]

theorem original_program_retained {origin : Declaration} {declared : Key → Prop}
    (definition : Definition origin declared) :
    (register definition).original = source origin
      OriginalModuleContextBindingR315.externalContext
      OriginalScopedSourceEventMapR314.Fixture.root := rfl

theorem original_erasure_retained {origin : Declaration} {declared : Key → Prop}
    (definition : Definition origin declared) :
    (register definition).original.erase = sourceRules
      OriginalModuleContextBindingR315.externalContext
      OriginalScopedSourceEventMapR314.Fixture.root := erase_allocate _ _

/-- Consumer adapter for the separate source-owned registry. This is only a
static reference resolver. In particular it supplies no generated Inputs case. -/
def resolve {s : Sorts} {View : Type} {origin : Declaration} {declared : Key → Prop}
    (old : Decoded s View) (registry : Registry origin declared)
    (location : Occurrence) : Address → Option (extended s Code).Interface
  | .inl endpoint => some (.inl (old.interfaces endpoint))
  | .inr key => (registry.read location key).map Sum.inr

theorem generated_resolution {s : Sorts} {View : Type}
    {origin : Declaration} {declared : Key → Prop}
    (old : Decoded s View) (definition : Definition origin declared) :
    resolve old (register definition) (owner origin)
      (.inr (request origin).generatedResult.key) =
        some (.inr (Selected.resultCode origin definition.arms)) := by
  change Option.map Sum.inr ((register definition).read _ _) = _
  rw [registered_readback]
  rfl

theorem every_old_resolution_retained {s : Sorts} {View : Type}
    {origin : Declaration} {declared : Key → Prop}
    (old : Decoded s View) (registry : Registry origin declared)
    (location : Occurrence) (endpoint : Endpoint) :
    resolve old registry location (.inl endpoint) =
      some (.inl (old.interfaces endpoint)) := rfl

/-- The original ViewLogic payload is extended with a disjoint presentation
token. Every old descriptor/interface update and the SAME eta/witness remain.
The token resolves the stored expression; it does not assert its membership. -/
def definedLogical {s : Sorts} {View : Type}
    {origin : Declaration} {declared : Key → Prop}
    (old : Logical s View) (definition : Definition origin declared) :
    Logical (extended s Code) (Sum View Unit) where
  descriptors := old.descriptors
  interfaces := old.interfaces.map (fun entry => (entry.1, .inl entry.2))
  viewMeaning := fun view => match view with
    | .inl view => .inl (old.viewMeaning view)
    | .inr _ => .inr definition.code
  eta := old.eta
  witness := old.witness

def definedPayload {s : Sorts} {View : Type}
    {origin : Declaration} {declared : Key → Prop}
    (old : Logical s View) (definition : Definition origin declared) :
    Payload (extended s Code) (Sum View Unit) :=
  .logical .viewLogic (definedLogical old definition)

theorem payload_at_original_kind {s : Sorts} {View : Type}
    {origin : Declaration} {declared : Key → Prop}
    (old : Logical s View) (definition : Definition origin declared) :
    (definedPayload old definition).atKind (owner origin).binder.kind := rfl

theorem logical_old_views_retained {s : Sorts} {View : Type}
    {origin : Declaration} {declared : Key → Prop}
    (old : Logical s View) (definition : Definition origin declared) (view : View) :
    (definedLogical old definition).viewMeaning (.inl view) =
      .inl (old.viewMeaning view) := rfl

theorem logical_generated_readback {s : Sorts} {View : Type}
    {origin : Declaration} {declared : Key → Prop}
    (old : Logical s View) (definition : Definition origin declared) :
    (definedLogical old definition).viewMeaning (.inr ()) =
      .inr (Selected.resultCode origin definition.arms) := rfl

theorem logical_registry_correspondence {s : Sorts} {View : Type}
    {origin : Declaration} {declared : Key → Prop}
    (old : Logical s View) (state : Decoded s View)
    (definition : Definition origin declared) :
    some ((definedLogical old definition).viewMeaning (.inr ())) =
      resolve state (register definition) (owner origin)
        (.inr (request origin).generatedResult.key) :=
  (generated_resolution state definition).symm

/-- Apply the ACTUAL original environment decoder at the computed original
owner. The environment is explicitly over the enlarged presentation type;
this theorem does not pretend to transport an arbitrary old environment.
Only ordinary successful prefix decoding is required, never desired readback. -/
theorem actual_decoder_registration {s : Sorts} {View : Type}
    {origin : Declaration} {declared : Key → Prop}
    (readout : RuntimeReadout (extended s Code) (Sum View Unit))
    (environment : Environment (Payload (extended s Code) (Sum View Unit)))
    (state : Decoded (extended s Code) (Sum View Unit))
    (decoded : decode readout environment = some state)
    (old : Logical s View) (definition : Definition origin declared)
    (occurrence : Nat) :
    decode readout (environment.extend (owner origin).binder
      (scopeCandidate environment occurrence (definedPayload old definition))) =
        some (state.logical (definedLogical old definition)) := by
  exact decode_extend readout environment (owner origin).binder
    (scopeCandidate environment occurrence (definedPayload old definition)) state decoded

/-- Readback is derived through the original decoder, rather than supplied
as an equality premise. The same original prefix/environment is used. -/
theorem actual_decoder_generated_view {s : Sorts} {View : Type}
    {origin : Declaration} {declared : Key → Prop}
    (readout : RuntimeReadout (extended s Code) (Sum View Unit))
    (environment : Environment (Payload (extended s Code) (Sum View Unit)))
    (state : Decoded (extended s Code) (Sum View Unit))
    (decoded : decode readout environment = some state)
    (old : Logical s View) (definition : Definition origin declared)
    (occurrence : Nat) :
    (decode readout (environment.extend (owner origin).binder
      (scopeCandidate environment occurrence (definedPayload old definition)))).map
        (fun after => after.viewMeaning (.inr ())) =
          some (.inr (Selected.resultCode origin definition.arms)) := by
  rw [actual_decoder_registration readout environment state decoded old definition occurrence]
  rfl

/-- Apply original source admission to THIS stored expression and source
owner. Decoder readback is settled above; independent logical admission is
precisely the first remaining original R159 premise. No instance is invented. -/
theorem parent_admission_obligation {s : Sorts} {View : Type}
    {origin : Declaration} {declared : Key → Prop}
    (inputs : Inputs (extended s Code))
    (readout : RuntimeReadout (extended s Code) (Sum View Unit))
    (admissions : LocalAdmissions (extended s Code) (Sum View Unit))
    (environment : Environment (Payload (extended s Code) (Sum View Unit)))
    (state : Decoded (extended s Code) (Sum View Unit))
    (decoded : decode readout environment = some state)
    (old : Logical s View) (definition : Definition origin declared) (occurrence : Nat) :
    Admitted inputs readout admissions environment (owner origin).binder
      (scopeCandidate environment occurrence (definedPayload old definition)) ↔
        admissions.logical state (owner origin).binder .viewLogic
          (definedLogical old definition) := by
  rw [admitted_scoped_iff inputs readout admissions environment
    (owner origin).binder state decoded occurrence (definedPayload old definition)]
  exact ⟨fun valid => valid.2, fun valid => ⟨rfl, valid⟩⟩

theorem logical_original_updates_retained {s : Sorts} {View : Type}
    {origin : Declaration} {declared : Key → Prop}
    (old : Logical s View) (definition : Definition origin declared) :
    (definedLogical old definition).descriptors = old.descriptors ∧
    (definedLogical old definition).interfaces =
      old.interfaces.map (fun entry => (entry.1, Sum.inl entry.2)) ∧
    (definedLogical old definition).eta = old.eta ∧
    (definedLogical old definition).witness = old.witness := ⟨rfl, rfl, rfl, rfl⟩

/-- Every arm keeps its original location, local binders and typed reference.
This is a syntactic case table, NOT a semantic contribution Catalogue. -/
def branchCode {origin : Declaration} {declared : Key → Prop}
    (definition : Definition origin declared) :
    Sum Unit (Fin definition.arms.length) → Code
  | .inl _ => Selected.sourceCode origin
  | .inr i => ⟨[] ++ definition.arms[i].localBinders,
      .reference definition.arms[i].descriptor⟩

theorem source_branch_readback {origin : Declaration} {declared : Key → Prop}
    (definition : Definition origin declared) :
    branchCode definition (.inl ()) =
      ⟨[], .evalInvoke (request origin).original.position (request origin).operands⟩ := rfl

theorem arm_branch_readback {origin : Declaration} {declared : Key → Prop}
    (definition : Definition origin declared) (i : Fin definition.arms.length) :
    branchCode definition (.inr i) =
      ⟨[] ++ definition.arms[i].localBinders,
        .reference definition.arms[i].descriptor⟩ := rfl

theorem all_arm_declarations_retained {origin : Declaration} {declared : Key → Prop}
    (definition : Definition origin declared) :
    definition.code.2 = .allArms
      (.evalInvoke (request origin).original.position (request origin).operands)
      definition.arms := rfl

theorem original_references_retained (origin : Declaration) :
    (request origin).originalResult = ⟨1, .synthesis⟩ ∧
    (request origin).originalCheck = ⟨1, .callableImage⟩ ∧
    (request origin).operands.argument.original = (request origin).original.argument ∧
    (request origin).operands.argument.reference.key.scope =
      [.calRet (request origin).original.position] ∧
    (request origin).operands.incidence.key.reference.position =
      (request origin).original.position := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The old R293 source endpoint cannot read the generated label through
R328's genuine environment transport. No private interfaces-only Decoded is
presented as a source environment to circumvent this obstruction. -/
theorem old_endpoint_cannot_read_generated {s : Sorts} {View : Type}
    (old : Decoded s View) (endpoint : Endpoint) (code : Code) :
    (upDecoded (G := Code) old).interfaces endpoint ≠ .inr code := by
  intro same
  cases same

theorem old_meaning_retained {s : Sorts} (base : Inputs s)
    (generated : Generated s Code) (query : Query s) :
    Meaning (inputs base generated) (upQuery query) ↔ Meaning base query :=
  old_meaning_iff base generated query

end YulangClosure.OriginalSourceViewRegistrationR330
