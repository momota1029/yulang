import YulangClosure.InternalPermissionIncidenceR45
import YulangClosure.OwnedResidualProjectionR54

/-!
R116: CONSTRUCTED / UNCHECKED. No Lean, Lake or axiom audit was executed.
Conditional finite constructor algebra for the successful Suppress branch only.
Id denotes a complete branded source identity, including resolved arguments;
it is never a spelling or an erased arena ordinal. Native decoding is OPEN.

Authority: annotation-effect-hygiene-integration §§1--1.2. The annotation grants
subtraction on open input; it does not bound every incoming effect. R39 supplies
exact retained copy and registration/Lambda/owner facts. The selected source
annotation must be the SAME row as the R39 action; equal family names alone do
not join rows. R45/R54 applications below retain their original hypotheses.
- Paper/source inference soundness and complete hygiene remain OPEN.
- Singleton annotation, selected arm and native provider decoding are explicit
  correspondence premises, not inferred from the name Suppress.
- No membership hypothesis or LocalLaw supplies the conclusion.
-/
namespace YulangClosure.SuppressionPermissionR116

variable {Id : Type} [DecidableEq Id]

/-- Named facts about the SAME retained record, derived from the producer. -/
structure ProducerFacts (e : ComputationPermissionEntryR39.Inputs Id) (a : ComputationPermissionEntryR39.Action Id)
    (f : ComputationPermissionEntryR39.Registration Id) (r : ComputationPermissionEntryR39.Row Id) (port : Id)
    (p : ComputationPermissionEntryR39.Permission Id) : Prop where
  registered : e.formals[a.registration]? = some f
  sourceRow : a.annotation.row = some r
  registration : p.registration = a.registration
  formal : p.formalIdentity = f.parameter
  occurrence : p.occurrence = a.occurrence
  annotationOwner : p.owner = a.annotation.owner
  formalOwner : p.owner = f.owner
  sourceOwner : ComputationPermissionEntryR39.ownerLookup e.owners a.occurrence = some f.owner
  sourceLambda : ComputationPermissionEntryR39.sourceLambda e f = some (a.occurrence, f.parameter)
  scope : p.scope = f.scope
  annotationPosition : p.annotationPosition = a.annotation.position
  rowPosition : p.rowPosition = r.position
  entry : p.entry = port
  concreteCopy : p.concrete = r.concrete

/-- Inversion of actual R39 constructor equations; no producer law parameter. -/
theorem producer_facts (e : ComputationPermissionEntryR39.Inputs Id) (a : ComputationPermissionEntryR39.Action Id)
    (f : ComputationPermissionEntryR39.Registration Id) (r : ComputationPermissionEntryR39.Row Id) (port : Id)
    (p : ComputationPermissionEntryR39.Permission Id)
    (prepared : ComputationPermissionEntryR39.prepare e a = some (f, r, port))
    (retained : ComputationPermissionEntryR39.permissionFor a f r port = some p) :
    ProducerFacts e a f r port p := by
  obtain ⟨registered, row, _, valid, _, registration, _, formal, occurrence,
    owner, scope, annotationPosition, rowPosition, entry, concrete⟩ :=
    ComputationPermissionEntryR39.exact_row_retained e a p f r port prepared retained
  obtain ⟨formalOwner, _, formalScope, _, sourceOwner, sourceLambda, _⟩ := valid
  exact ⟨registered, row, registration, formal, occurrence, owner,
    owner.trans formalOwner.symm, sourceOwner, sourceLambda,
    scope.trans formalScope.symm, annotationPosition, rowPosition, entry, concrete⟩

/-- Operation declaration identity and family stay separate from spelling.
Occurrence identifies the selected provider/handler occurrence, not the family. -/
structure Operation (Id : Type) where
  occurrence : Id
  identity : Id
  declaration : Id
  family : Id
  spelling : String
  deriving DecidableEq

/-- This is a narrow comparison transcription, NOT the full Rust decision.
Exact source_operation_match/native decoding remains a correspondence gate. -/
def operationMatch (provider arm : Operation Id) : Bool :=
  decide (provider.identity = arm.identity ∧
    provider.declaration = arm.declaration ∧ provider.family = arm.family)

theorem operation_match_identity (provider arm : Operation Id)
    (matched : operationMatch provider arm = true) :
    provider.identity = arm.identity ∧
      provider.declaration = arm.declaration ∧ provider.family = arm.family := by
  exact of_decide_eq_true matched

/-- Selected assembly row is linked by exact annotation owner, position and row
identity. It cannot be exchanged for an equal-looking different formal's row.
`singleton` mirrors the successful assembly singleton/family guard; it is not a
permission membership hypothesis. Its instantiation from Rust stays OPEN. -/
structure SelectedSource (a : ComputationPermissionEntryR39.Action Id) (r : ComputationPermissionEntryR39.Row Id)
    (arm : Operation Id) : Prop where
  row : a.annotation.row = some r
  singleton : r.concrete = [arm.family]

/-- Source row -> retained vector -> selected provider member. This is the
local successful-Suppress consequence, not a theorem about every inflow member.
The actual Rust Suppress -> selected/operationMatch premises are not proved. -/
theorem selected_provider_member (e : ComputationPermissionEntryR39.Inputs Id) (a : ComputationPermissionEntryR39.Action Id)
    (f : ComputationPermissionEntryR39.Registration Id) (r : ComputationPermissionEntryR39.Row Id) (port : Id)
    (p : ComputationPermissionEntryR39.Permission Id) (provider arm : Operation Id)
    (prepared : ComputationPermissionEntryR39.prepare e a = some (f, r, port))
    (retained : ComputationPermissionEntryR39.permissionFor a f r port = some p)
    (selected : SelectedSource a r arm)
    (matched : operationMatch provider arm = true) :
    ProducerFacts e a f r port p ∧ provider.family ∈ p.concrete := by
  have facts := producer_facts e a f r port p prepared retained
  have family := (operation_match_identity provider arm matched).2.2
  refine ⟨facts, ?_⟩
  rw [facts.concreteCopy, selected.singleton, family]
  simp

/-- The native endpoint-to-provider-family equality is kept explicit. It
mirrors the provider-origin member check, but has no authenticated Rust decoder
here. This concludes membership of the actual selected endpoint, not merely a
possibly unrelated source name. -/
theorem selected_endpoint_member (e : ComputationPermissionEntryR39.Inputs Id)
    (a : ComputationPermissionEntryR39.Action Id)
    (f : ComputationPermissionEntryR39.Registration Id)
    (r : ComputationPermissionEntryR39.Row Id) (port endpoint : Id)
    (p : ComputationPermissionEntryR39.Permission Id) (provider arm : Operation Id)
    (prepared : ComputationPermissionEntryR39.prepare e a = some (f, r, port))
    (retained : ComputationPermissionEntryR39.permissionFor a f r port = some p)
    (selected : SelectedSource a r arm)
    (matched : operationMatch provider arm = true)
    (providerEndpoint : endpoint = provider.family) : endpoint ∈ p.concrete := by
  rw [providerEndpoint]
  exact (selected_provider_member e a f r port p provider arm
    prepared retained selected matched).2

/-- Same row selection is mandatory: two actual row reads of the same action
agree by Option injectivity, with no spelling/canonical-image premise. -/
theorem same_source_row (a : ComputationPermissionEntryR39.Action Id) (r other : ComputationPermissionEntryR39.Row Id)
    (first : a.annotation.row = some r)
    (second : a.annotation.row = some other) : r = other :=
  Option.some.inj (first.symm.trans second)

/-- Apply the membership result to the SAME R45 certificate permission.
All R45 owning reads, native observations and identity checks remain explicit
through extract; this theorem does not fabricate those inputs. -/
theorem internal_certificate_member {Artifact Term Fact : Type}
    [DecidableEq Artifact] [DecidableEq Term] [DecidableEq Fact]
    (e : InternalPermissionIncidenceR45.Inputs Artifact Id Term Fact) (a : ComputationPermissionEntryR39.Action Id)
    (f : ComputationPermissionEntryR39.Registration Id) (r : ComputationPermissionEntryR39.Row Id) (port : Id)
    (q : InternalPermissionIncidenceR45.Query Artifact Id) (probe : InternalPermissionIncidenceR45.Probe Artifact Id Term Fact)
    (out : InternalPermissionIncidenceR45.Certificate Artifact Id Term Fact) (provider arm : Operation Id)
    (prepared : ComputationPermissionEntryR39.prepare e.source a = some (f, r, port))
    (retained : ComputationPermissionEntryR39.permissionFor a f r port = some probe.permission)
    (accepted : InternalPermissionIncidenceR45.extract e q probe = some out)
    (selected : SelectedSource a r arm)
    (matched : operationMatch provider arm = true) :
    out.permission.registration = a.registration ∧
      out.permission.occurrence = a.occurrence ∧
      out.permission.owner = f.owner ∧ provider.family ∈ out.permission.concrete := by
  have result := selected_provider_member e.source a f r port probe.permission
    provider arm prepared retained selected matched
  have same := (InternalPermissionIncidenceR45.accepted_payload e q probe out accepted).1
  rw [same]
  exact ⟨result.1.registration, result.1.occurrence, result.1.formalOwner, result.2⟩

/-- R54 same-owner composition transports the actual two values. Equal payload
or batch labels cannot replace equality of state AND batch owners. The owner
read/extraction from Rust remains an independent premise. -/
theorem same_owner_selected_join {State Batch : Type}
    [DecidableEq State] [DecidableEq Batch]
    (permission : OwnedResidualProjectionR54.Owned State Batch (ComputationPermissionEntryR39.Permission Id))
    (arm : OwnedResidualProjectionR54.Owned State Batch (Operation Id))
    (same : permission.owner = arm.owner) :
    OwnedResidualProjectionR54.join permission arm =
      some ⟨permission.owner, (permission.value, arm.value)⟩ :=
  OwnedResidualProjectionR54.same_owner_composition permission arm same

theorem empty_concrete_no_retained (a : ComputationPermissionEntryR39.Action Id)
    (f : ComputationPermissionEntryR39.Registration Id) (r : ComputationPermissionEntryR39.Row Id) (port : Id)
    (empty : r.concrete = []) : ComputationPermissionEntryR39.permissionFor a f r port = none := by
  simp [ComputationPermissionEntryR39.permissionFor, empty]

theorem different_formal_not_same_permission (p : ComputationPermissionEntryR39.Permission Id)
    (a : ComputationPermissionEntryR39.Action Id) (different : p.registration ≠ a.registration)
    (e : ComputationPermissionEntryR39.Inputs Id) (f : ComputationPermissionEntryR39.Registration Id) (r : ComputationPermissionEntryR39.Row Id) (port : Id) :
    ¬ ProducerFacts e a f r port p := by
  intro facts
  exact different facts.registration

/-- Name equality grants no complete operation-identity equality. -/
theorem same_spelling_different_operation_rejected (provider arm : Operation Id)
    (spelling : provider.spelling = arm.spelling)
    (different : provider.identity ≠ arm.identity) :
    provider.spelling = arm.spelling ∧ operationMatch provider arm = false := by
  exact ⟨spelling, by simp [operationMatch, different]⟩

theorem provider_handler_family_mismatch (provider arm : Operation Id)
    (different : provider.family ≠ arm.family) :
    operationMatch provider arm = false := by
  simp [operationMatch, different]

/-- Extra write is allowed in the incoming row; the permission does not
manufacture it, close the input, or authorize subtracting it. This is finite
list algebra only, not the Rust propagation/residual theorem. -/
theorem open_input_write_boundary (signal write : Id) (different : write ≠ signal) :
    signal ∈ [signal] ∧ write ∈ [signal, write] ∧ write ∉ [signal] ∧
      ([signal, write].filter (fun member => member != signal)) = [write] := by
  simp [different, Ne.symm different]

end YulangClosure.SuppressionPermissionR116

-- Pending audit commands only. None of these commands has been executed.
#check @YulangClosure.SuppressionPermissionR116.producer_facts
#print axioms YulangClosure.SuppressionPermissionR116.producer_facts
#check @YulangClosure.SuppressionPermissionR116.operation_match_identity
#print axioms YulangClosure.SuppressionPermissionR116.operation_match_identity
#check @YulangClosure.SuppressionPermissionR116.selected_provider_member
#print axioms YulangClosure.SuppressionPermissionR116.selected_provider_member
#check @YulangClosure.SuppressionPermissionR116.selected_endpoint_member
#print axioms YulangClosure.SuppressionPermissionR116.selected_endpoint_member
#check @YulangClosure.SuppressionPermissionR116.same_source_row
#print axioms YulangClosure.SuppressionPermissionR116.same_source_row
#check @YulangClosure.SuppressionPermissionR116.internal_certificate_member
#print axioms YulangClosure.SuppressionPermissionR116.internal_certificate_member
#check @YulangClosure.SuppressionPermissionR116.same_owner_selected_join
#print axioms YulangClosure.SuppressionPermissionR116.same_owner_selected_join
#check @YulangClosure.SuppressionPermissionR116.empty_concrete_no_retained
#print axioms YulangClosure.SuppressionPermissionR116.empty_concrete_no_retained
#check @YulangClosure.SuppressionPermissionR116.different_formal_not_same_permission
#print axioms YulangClosure.SuppressionPermissionR116.different_formal_not_same_permission
#check @YulangClosure.SuppressionPermissionR116.same_spelling_different_operation_rejected
#print axioms YulangClosure.SuppressionPermissionR116.same_spelling_different_operation_rejected
#check @YulangClosure.SuppressionPermissionR116.provider_handler_family_mismatch
#print axioms YulangClosure.SuppressionPermissionR116.provider_handler_family_mismatch
#check @YulangClosure.SuppressionPermissionR116.open_input_write_boundary
#print axioms YulangClosure.SuppressionPermissionR116.open_input_write_boundary
