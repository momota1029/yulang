import YulangClosure.ComputedCallTypedFormationR310
import YulangClosure.OriginalAppConstructionR160

/-!
R311: resolution evidence actually available from the original source table.

Sources: selected EI §§2,4; IF §§2,3.1–3.2,6. The R297 table is a
source-occurrence inventory, not the independently typed declaration inventory
required by IF. Below every issued source reference has an actual source row;
no `declared` predicate, arbitrary catalogue or empty arm list is introduced.
The final parent equation exposes the first original formation leaf at the
same ViewLogic extension, rather than replacing it by nominal EI formation.
-/
namespace YulangClosure.OriginalSourceContractResolutionR311

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking SourceGraphRegistrationR297
open ComputedCallTypedFormationR310

/-- Each emitted request has an actual original R297 row. The lookup is an
output; it is not supplied by a desired registration equation. -/
theorem request_source_row (origin : Declaration) (context : Context)
    (raw : Source category) (request : Request)
    (present : request ∈ requests origin context raw) :
    ∃ (index : Nat) (row : Row), (sourceInventory origin context raw)[index]? = some row ∧
      callRecord row = some request.original ∧ prepare request.original = request := by
  obtain ⟨call, member, same⟩ := List.mem_map.mp present
  subst request
  obtain ⟨row, member, found⟩ := List.mem_filterMap.mp member
  obtain ⟨index, bound, equal⟩ := List.getElem_of_mem member
  exact ⟨index, row, List.getElem?_eq_some_iff.mpr ⟨bound, equal⟩, found, rfl⟩

/-- Original child, original scopes and original check endpoints read directly
from an authentic request. These are syntax/obligation references; the checked
Function sort and the independent challenge/inlet remain semantic inputs. -/
theorem request_source_references (origin : Declaration) (context : Context)
    (raw : Source category) (request : Request)
    (present : request ∈ requests origin context raw) :
    request.operands.callee =
      ⟨programPosition request.original.callee,
        .originalComputation ⟨request.original.calleeSite, .synthesis⟩⟩ ∧
    request.operands.function =
      ⟨request.original.position, .checkedFunction ⟨request.original.site, .descriptor⟩⟩ ∧
    request.operands.argument.original = request.original.argument ∧
    request.operands.argument.reference.key.scope = [.calRet request.original.position] ∧
    request.originalCheck = ⟨request.original.site, .callableImage⟩ ∧
    request.originalResult = ⟨request.original.site, .synthesis⟩ := by
  obtain ⟨_, _, _, _, same⟩ := request_source_row origin context raw request present
  rw [← same]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Reading the original name atom preserves the actual optional resolved
binding. `none` is unresolved source evidence, not an empty arm declaration. -/
def nameBinding (row : Row) : Option (Position × Site × Name × Option Binding) :=
  match row.program with
  | .rule position .name site _ (.atom data :: _) .nil =>
      match data.names with
      | [name] => some (position, site, name, data.binding)
      | _ => none
  | _ => none

structure NameReference where
  position : Position
  site : Site
  context : Context
  name : Name
  binding : Binding

/-- Reads the actual original binding attached to the source Name atom. -/
def nameReference (row : Row) : Option NameReference :=
  match row.program with
  | .rule position .name site context (.atom data :: _) .nil => do
      let binding ← data.binding
      match data.names with
      | [name] => some ⟨position, site, context, name, binding⟩
      | _ => none
  | _ => none

/-- The actual R310/R297 computed fixture contains three unbound original
names. In particular its empty Context supplies no declaration of f, x or y.
This is an exact source equation, not a refutation of the EI rule. -/
theorem computed_name_bindings :
    (sourceInventory 7 [] computedFixture).filterMap nameBinding =
      [(⟨7, [0, 0, 0, 0],
          [.existsE ⟨4, .viewLogic, 0⟩, .existsE ⟨2, .viewLogic, 0⟩], []⟩, 0, 10, none),
       (⟨7, [0, 0, 0, 0, 1],
          [.existsE ⟨4, .viewLogic, 0⟩, .existsE ⟨2, .viewLogic, 0⟩], []⟩, 1, 11, none),
       (⟨7, [0, 0, 1], [.existsE ⟨4, .viewLogic, 0⟩], []⟩, 3, 12, none)] := by
  simp only [sourceInventory, source, computedFixture,
    ComputedCallSourceSupplierR294.computedSource, source_app_equation,
    LogicalOccurrencesR104.appRule, source_name_equation]
  rfl

theorem computed_no_resolved_binding (name : Name) :
    ¬ ∃ binding, lookupBinding ([] : Context) name = some binding := by
  simp [lookupBinding]

/-- Every actual request, including BOTH computed calls, has a source row.
There is no request-specific assumption or caller-supplied desired lookup. -/
theorem computed_requests_located :
    ∀ request ∈ requests 7 [] computedFixture,
      ∃ (index : Nat) (row : Row), (sourceInventory 7 [] computedFixture)[index]? = some row ∧
        callRecord row = some request.original ∧ prepare request.original = request :=
  fun request member => request_source_row 7 [] computedFixture request member

/-- Genuine source binders around the SAME computed expression. The contexts
below are emitted by the existing Lambda generator, not supplied declaration
predicates. Wild patterns introduce no competing binding. -/
def boundSource : Source .expression :=
  .lambda ⟨20, none⟩ ⟨30, 10, none, false⟩ (.wild 40)
    (.lambda ⟨21, none⟩ ⟨31, 11, none, false⟩ (.wild 41)
      (.lambda ⟨22, none⟩ ⟨32, 12, none, false⟩ (.wild 42) computedFixture))

/-- Authentic lexical resolution at actual source Name rows. All three
bindings come from original formal introduction; no root owner is guessed
from a returned Function shape. Full scoped rows remain in the inventory.
This supplies lexical ownership, not independent semantic Function typing.
-/
theorem bound_source_name_owners :
    ((sourceInventory 7 [] boundSource).filterMap nameBinding).map
      (fun row => (row.2.1, row.2.2.1, row.2.2.2)) =
    [(0, 10, some {name := 10, owner := 30, kind := .formal, entry := some .value, singleUse := true}),
     (1, 11, some {name := 11, owner := 31, kind := .formal, entry := some .value, singleUse := true}),
     (3, 12, some {name := 12, owner := 32, kind := .formal, entry := some .value, singleUse := true})] := by
  simp only [sourceInventory, source, boundSource, computedFixture,
    ComputedCallSourceSupplierR294.computedSource, sourceRules]
  rfl

/-- Both bound computed Apps are actually emitted. No semantic arm count is
inferred from this syntactic count. -/
theorem bound_source_call_count : (requests 7 [] boundSource).length = 2 := by
  simp only [requests, callTable, sourceInventory, source, boundSource, computedFixture,
    ComputedCallSourceSupplierR294.computedSource, sourceRules]
  rfl

theorem bound_source_requests_located :
    ∀ request ∈ requests 7 [] boundSource,
      ∃ (index : Nat) (row : Row), (sourceInventory 7 [] boundSource)[index]? = some row ∧
        callRecord row = some request.original ∧ prepare request.original = request :=
  fun request member => request_source_row 7 [] boundSource request member

theorem bound_reference_count :
    ((sourceInventory 7 [] boundSource).filterMap nameReference).length = 3 := by
  simp only [sourceInventory, source, boundSource, computedFixture,
    ComputedCallSourceSupplierR294.computedSource, sourceRules]
  rfl

/-- A finite check against the actual Name context at each actual source row;
not a declaration oracle and not a claim about independent semantic arms. -/
theorem bound_references_resolved_check :
    ((sourceInventory 7 [] boundSource).filterMap nameReference).all
      (fun reference => lookupBinding reference.context reference.name == some reference.binding &&
        reference.binding.kind == .formal && reference.binding.entry == some .value) = true := by
  simp only [sourceInventory, source, boundSource, computedFixture,
    ComputedCallSourceSupplierR294.computedSource, sourceRules]
  rfl

theorem bound_reference_resolved (reference : NameReference)
    (present : reference ∈ (sourceInventory 7 [] boundSource).filterMap nameReference) :
    lookupBinding reference.context reference.name = some reference.binding ∧
      reference.binding.kind = .formal ∧ reference.binding.entry = some .value := by
  have checked := List.all_eq_true.mp bound_references_resolved_check reference present
  simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using checked

/-- Construct the original Name source rule from its raw installed binding,
for an arbitrary actual formal context, including additional captured names.
No source judgment, Value membership or desired checking is assumed. -/
theorem formal_name_from_raw_binding (inputs : Inputs s)
    (readout : RuntimeReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (context : Context) (site : Site) (name : Name) (binding : Binding)
    (resolved : lookupBinding context name = some binding)
    (formal : binding.kind = .formal) (entry : binding.entry = some .value)
    (address : Nat) (atName : state.assignment.binding name = some address)
    (bound : address < inputs.installedCount state.assignment.event)
    (found : inputs.installed state.assignment.event address =
      some (.value (state.assignment.descriptor ⟨site, .finalRoot⟩)
        (state.assignment.value ⟨site, .finalRoot⟩) (state.assignment.root ⟨site, .finalRoot⟩))) :
    Satisfies (foldedNameKernel inputs readout original site name) environment
      (Build context (.name ⟨site, none⟩ name)) := by
  apply (source_reconstruction _ _ _ _).mpr
  simp only [SourceJudgment, sourceRules, resolved, Option.map_some, formal]
  apply Judgment.rule
  · intro premise member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals
      apply Local.atom
      simp only [foldedNameKernel, atom, valueFormalAtom, formal, entry]
      simp only [beq_self_eq_true, Bool.and_self, reduceCtorEq, true_or,
        or_true, and_self, ite_true]
      exact ⟨state, decoded, name, address, rfl, atName, bound, found⟩
  · exact .nil

/-- The original whole-world certificate supplies the actual value at the
SAME raw Name binding. This is the independent immutable-name theorem, not a
Function-shape or arbitrary declaration predicate standing for membership. -/
theorem formal_name_value_from_raw_binding (inputs : Inputs s)
    (state : Decoded s View) (site : Site) (address : Nat)
    (world : Meaning inputs (.world state.assignment.event))
    (found : inputs.installed state.assignment.event address =
      some (.value (state.assignment.descriptor ⟨site, .finalRoot⟩)
        (state.assignment.value ⟨site, .finalRoot⟩) (state.assignment.root ⟨site, .finalRoot⟩))) :
    Meaning inputs (.value (state.assignment.row site)) :=
  immutable_name_value inputs state.assignment.event world address _ _ _ found

/-- Applied to ALL three actual bound-source Name rows. The returned source
proof and semantic value use the SAME decoded state, address and whole-world
certificate. Missing raw original binding/world leaves remain explicit, but
no desired source judgment, full body or descriptor membership is assumed.
-/
theorem bound_reference_source_and_value (inputs : Inputs s)
    (readout : RuntimeReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (reference : NameReference)
    (present : reference ∈ (sourceInventory 7 [] boundSource).filterMap nameReference)
    (address : Nat) (atName : state.assignment.binding reference.name = some address)
    (bound : address < inputs.installedCount state.assignment.event)
    (found : inputs.installed state.assignment.event address =
      some (.value (state.assignment.descriptor ⟨reference.site, .finalRoot⟩)
        (state.assignment.value ⟨reference.site, .finalRoot⟩)
        (state.assignment.root ⟨reference.site, .finalRoot⟩)))
    (world : Meaning inputs (.world state.assignment.event)) :
    Satisfies (foldedNameKernel inputs readout original reference.site reference.name) environment
      (Build reference.context (.name ⟨reference.site, none⟩ reference.name)) ∧
      Meaning inputs (.value (state.assignment.row reference.site)) := by
  obtain ⟨resolved, formal, entry⟩ := bound_reference_resolved reference present
  exact ⟨formal_name_from_raw_binding inputs readout original environment state decoded
    reference.context reference.site reference.name reference.binding resolved formal entry
    address atName bound found,
    formal_name_value_from_raw_binding inputs state reference.site address world found⟩

/-- Catalogue binder projection only. The complete source position (including
publication/choice/initializer anchors) remains in `NameReference.position`.
No equality of projected telescopes is used to identify source occurrences. -/
def binderTelescope (position : Position) : List Binder :=
  position.telescope.filterMap fun step => match step with
    | .existsE binder | .forallE binder | .executionE binder | .sharedE binder => some binder
    | _ => none

/-- A genuine source-Name leaf supplies R293's REAL complete branch catalogue.
All observation guards/fields are the original independent Return leaves,
not an assumed whole desired clause. This constructs only the Name/Return
leaf; it supplies neither computed-App EI phases nor independent arm laws.
-/
theorem bound_reference_return_packet (inputs : Inputs s)
    (readout : RuntimeReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (reference : NameReference)
    (present : reference ∈ (sourceInventory 7 [] boundSource).filterMap nameReference)
    (address : Nat) (atName : state.assignment.binding reference.name = some address)
    (bound : address < inputs.installedCount state.assignment.event)
    (found : inputs.installed state.assignment.event address =
      some (.value (state.assignment.descriptor ⟨reference.site, .finalRoot⟩)
        (state.assignment.value ⟨reference.site, .finalRoot⟩)
        (state.assignment.root ⟨reference.site, .finalRoot⟩)))
    (world : Meaning inputs (.world state.assignment.event))
    (raw : RawObservation s)
    (sameEvent : raw.event = state.assignment.event)
    (form : inputs.traceForm (raw.atInterface (state.interfaces ⟨reference.site, .synthesis⟩)) =
      .pureReturn (state.assignment.row reference.site))
    (guards : (inputs.observationGuards
      (raw.atInterface (state.interfaces ⟨reference.site, .synthesis⟩))).Valid)
    (fields : (inputs.observationFields
      (raw.atInterface (state.interfaces ⟨reference.site, .synthesis⟩))).Holds (Meaning inputs)) :
    Satisfies (foldedNameKernel inputs readout original reference.site reference.name) environment
      (Build reference.context (.name ⟨reference.site, none⟩ reference.name)) ∧
    Nonempty (SourceContributionConstruction.Packet
      (ComputedCallUnionRealizationR293.branchCatalogue inputs state
        (binderTelescope reference.position) ⟨reference.site, .synthesis⟩) raw) := by
  obtain ⟨source, value⟩ := bound_reference_source_and_value inputs readout original
    environment state decoded reference present address atName bound found world
  have member : Meaning inputs
      (.trace (raw.atInterface (state.interfaces ⟨reference.site, .synthesis⟩))) := by
    apply (return_observation_iff inputs _ _ form).mpr
    refine ⟨?_, guards, ?_, ⟨sameEvent.symm, value⟩, fields⟩
    · simpa only [RawObservation.atInterface, sameEvent] using ((world_unfold inputs _).mp world).1
    · simpa only [RawObservation.atInterface, sameEvent] using world
  exact ⟨source, ⟨⟨(), ComputedCallUnionClausesR308.evidenceOfHolds _ _
    ((meaning_clause inputs _).mp member)⟩⟩⟩

/-- Keep the remaining original list verbatim, including conditional formal
origin, whole-argument compatibility, Call certificate, incidence and checks. -/
def remainingPremises (context : Context) (mark : Mark)
    (callee argument : Source .expression) : List Premise :=
  (SourceAppAdmissionR159.appPremises context mark callee argument).tail

theorem original_premises_cons (context : Context) (mark : Mark)
    (callee argument : Source .expression) :
    SourceAppAdmissionR159.appPremises context mark callee argument =
      .atom (atom .descriptorFormation mark.site context [callee.site, argument.site]) ::
        remainingPremises context mark callee argument := rfl

/-- Applied directly to unchanged R159, for all original operands and both
annotation alternatives. The first missing independent source-owned premise
is now the precise `original.atom after descriptorFormation`; this theorem
does not prove it. One candidate/data/extension is shared by every premise.
-/
theorem app_parent_formation_iff (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) (mark : Mark)
    (callee argument : Source .expression) :
    let kernel := admissionKernel inputs readout admissions original
    SourceJudgment kernel environment context (.app mark callee argument) ↔
      (∀ premise ∈ SourceAppAdmissionR159.annotationPremises context mark,
        Local kernel environment premise) ∧
      ∃ occurrence data state,
        decode readout environment = some state ∧
        admissions.logical state ⟨mark.site, .viewLogic, 0⟩ .viewLogic data ∧
        let candidate := scopeCandidate environment occurrence (.logical .viewLogic data)
        let after := environment.extend ⟨mark.site, .viewLogic, 0⟩ candidate
        original.atom after
          (atom .descriptorFormation mark.site context [callee.site, argument.site]) ∧
        (∀ premise ∈ remainingPremises context mark callee argument, Local kernel after premise) ∧
        SourceJudgment kernel after context callee ∧
        SourceJudgment kernel after context argument := by
  dsimp only
  have parent := SourceAppAdmissionR159.app_admission_iff inputs readout admissions original
    environment context mark callee argument
  dsimp only at parent
  rw [parent]
  simp only [original_premises_cons, List.mem_cons, forall_eq_or_imp]
  constructor
  · rintro ⟨annotations, occurrence, data, state, decoded, admitted, locals, first, second⟩
    exact ⟨annotations, occurrence, data, state, decoded, admitted,
      (OriginalAppConstructionR160.formation_consumer_iff inputs readout admissions original
        environment context mark callee argument occurrence data).mp locals.1,
      locals.2, first, second⟩
  · rintro ⟨annotations, occurrence, data, state, decoded, admitted, formed, locals, first, second⟩
    exact ⟨annotations, occurrence, data, state, decoded, admitted,
      ⟨(OriginalAppConstructionR160.formation_consumer_iff inputs readout admissions original
        environment context mark callee argument occurrence data).mpr formed, locals⟩,
      first, second⟩

end YulangClosure.OriginalSourceContractResolutionR311
