import YulangClosure.OriginalFullIFArmInterpretationR343
import YulangClosure.OriginalUnionOwnerR292

/-!
R344: separation of full scoped-slot identity, lawful primitive actions, and
original endpoint result interpretation. This is an ABSTRACT INTERFACE MODEL,
not an emitted source ArmDecl and not a counterexample to original semantics.

The stronger boundary than R334 is a nonempty, licensed, finite R318 arm child
with the exact .arm tag/endpoint, a nonidentity involutive primitive action,
its field/license/projection naturality, and retained infinite witness family.
Even these do not produce the R306 endpoint packet. The independent
Decoded.interfaces interpretation has not been related to the scoped use.
No new source semantics, primitive license or original arm inventory is adopted.
-/
namespace YulangClosure.OriginalAuthenticatedArmTransportR344

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking
open SourceSignatureConstruction SourceContributionConstruction
open ComputedCallTypedFormationR310 ComputedCallUnionRealizationR293
open OriginalFullIFArmInterpretationR343

namespace Separation

def sorts : Sorts where
  Valuation := Unit
  ConstructorGraph := Unit
  Dependencies := Unit
  SourceGraph := Unit
  BinderTree := Unit
  Assignment := Unit
  History := Unit
  Configuration := Unit
  JointWitness := Unit
  Scope := Bool
  Authority := Unit
  Incidence := Unit
  Dictionary := Unit
  Descriptor := Unit
  Interface := Bool
  Value := Unit
  Provider := Unit
  Root := Unit
  Carrier := Unit
  Observation := Bool
  Context := Unit
  Continuation := Unit
  Receipt := Unit
  TypedPath := Unit
  Consumer := Unit
  WitnessPosition := Unit
  WitnessValue := Unit

/-- A whole independent Nat-indexed family, retained as data rather than
reconstructed from an existential proposition. -/
abbrev FutureFamily := Nat → Bool

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
  checkedInlet := fun _ => false
  actualInlet := fun _ => false
  carrierAccepted := fun _ => True
  puncturedContext := fun _ => True
  otherValues := fun _ => True
  registeredHoles := fun _ => True
  checkedIncidences := fun _ => True
  receiptPrecondition := fun _ _ => True
  actualTypedPath := fun _ _ => True
  actualContext := fun _ _ => True
  execute := fun _ _ _ => False
  observationGuards := fun _ => ⟨True, True, True, True, True, True, True, True, True, True⟩
  traceForm := fun _ => .unfinished
  observationFields := fun row =>
    .both (.guard (row.interface = row.observation))
      (.existsE FutureFamily fun _ => .all Nat fun _ => .guard True)
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

def candidate : Family sorts
  | .trace row => row.interface = row.observation
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
    exact ⟨trivial, ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial, trivial, trivial⟩, trivial, trivial, member, ⟨fun _ => false, fun _ => trivial⟩⟩
  | carrier row =>
    exact ⟨trivial, ⟨trivial, trivial, trivial, trivial, trivial⟩, trivial, trivial,
      (fun _ _ => ⟨trivial, fun _ impossible => impossible.elim⟩),
      (fun _ _ => trivial)⟩

theorem world_meaning (event : Event sorts) : Meaning inputs (.world event) :=
  greatest_coinduct (Phi inputs) candidate candidate_postfixed _ trivial

theorem trace_iff (raw : RawObservation sorts) (interface : Bool) :
    Meaning inputs (.trace (raw.atInterface interface)) ↔ interface = raw.observation := by
  constructor
  · intro member
    exact ((meaning_iff inputs _).mp member).2.2.2.2.1
  · intro equal
    exact greatest_coinduct (Phi inputs) candidate candidate_postfixed _ equal

def primitive : Primitive inputs where
  owner := 17
  occurrence := 23
  scope := [⟨23, .viewLogic, 0⟩]
  parameters := .field Bool (fun _ => .done)
  fields := fun _ _ => .field FutureFamily (fun _ => .done)
  interface := fun p => p.1
  License := fun p raw _ => PLift (p.1 = raw.observation)
  projections := fun _ raw data license => {
    coherent := trivial
    guards := ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    world := world_meaning raw.event
    returned := trivial
    observations := ⟨license, ⟨data.1, fun _ => ⟨trivial⟩⟩⟩ }

/-- The whole tuple changes its actual observation AND its scope. It is not
an identity action disguised by endpoint equality. This action is lawful for
THIS independently defined primitive, not claimed legal for native source. -/
def flip (raw : RawObservation sorts) : RawObservation sorts :=
  ⟨!raw.observation, {raw.event with scope := !raw.event.scope}⟩

def action : PrimitiveAction primitive where
  whole := flip
  mapParameter := fun p => ⟨!p.1, ()⟩
  mapFields := fun _ _ data => data
  mapLicense := fun _ _ _ license => ⟨congrArg Bool.not license.down⟩
  mapProjection := fun _ _ fields => {
    coherent := trivial
    guards := ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
    world := world_meaning _
    returned := trivial
    observations := ⟨⟨congrArg Bool.not fields.observations.1.down⟩, fields.observations.2⟩ }
  natural := fun _ _ _ _ => rfl

theorem flip_involution (raw : RawObservation sorts) : flip (flip raw) = raw := by
  cases raw with
  | mk observation event =>
    cases event
    simp only [flip]
    congr 2 <;> exact Bool.not_not _

theorem flip_not_identity (raw : RawObservation sorts) : flip raw ≠ raw := by
  intro same
  have impossible := congrArg RawObservation.observation same
  change (!raw.observation) = raw.observation at impossible
  have casesBool (b : Bool) : (!b) ≠ b := by cases b <;> decide
  exact casesBool raw.observation impossible

theorem scope_changes (raw : RawObservation sorts) : (flip raw).event.scope ≠ raw.event.scope := by
  change (!raw.event.scope) ≠ raw.event.scope
  have casesBool (b : Bool) : (!b) ≠ b := by cases b <;> decide
  exact casesBool raw.event.scope

theorem complete_action_natural (raw : RawObservation sorts) (data : primitive.Data raw)
    (license : primitive.License data.1 raw data.2) :
    action.mapResult raw ⟨data.1, (primitive.projections data.1 raw data.2 license).evidence⟩ =
      ⟨action.mapParameter data.1, (primitive.projections _ _
        (action.mapFields data.1 raw data.2) (action.mapLicense data.1 raw data.2 license)).evidence⟩ :=
  primitive_emission_natural action raw data license

theorem future_family_retained (raw : RawObservation sorts) (data : primitive.Data raw) :
    (action.mapData data).2.1 = data.2.1 := rfl

def position : Position := ⟨17, [2, 1], [.existsE ⟨23, .viewLogic, 0⟩], []⟩
def endpoint : Endpoint := ⟨23, .synthesis⟩
def originalArm : Arm [] :=
  ⟨7, position, [.response position, .future position],
    ⟨position, .arm 7 endpoint⟩⟩

def arm : ScopedArm inputs [] := ⟨originalArm, primitive, action.whole, 29⟩

theorem full_arm_slot : arm.original.descriptor.slot = .arm arm.original.tag endpoint := rfl

theorem complete_local_scope : arm.original.descriptor.key.scope =
    [.response position, .future position] ∧
    arm.original.descriptor.position = position ∧
    arm.original.originalScope = position := ⟨rfl, rfl, rfl⟩

/-- Exact-key registration can even be present. This test registry is supplied
by the abstract model, NOT derived from R297 or any actual source declaration. -/
def registry (key : Key) : Option (Primitive inputs) :=
  if key = originalArm.descriptor.key then some primitive else none

theorem exact_key_registered : registry arm.original.descriptor.key = some arm.primitive := by
  simp [registry, arm]

def event : Event sorts :=
  ⟨⟨(), (), (), (), ()⟩, (), (), (), (), (), false, (), (), ()⟩
def raw : RawObservation sorts := ⟨false, event⟩

def data (family : FutureFamily) : arm.data raw := ⟨⟨true, ()⟩, ⟨family, ()⟩⟩
def license (family : FutureFamily) : primitive.License (data family).1 (arm.action raw)
    (data family).2 := ⟨rfl⟩

def state : Decoded sorts Unit where
  assignment := ⟨event, fun _ => (), fun _ => (), fun _ => (), fun _ => none⟩
  interfaces := fun ep => match ep.port with | .callableImage => false | _ => true
  carriers := fun _ => ()
  viewMeaning := fun _ => false
  installed := fun _ => none
  active := none
  activeRaw := none
  fixedFrames := []
  callOwners := []

def arms : Fin 1 → ScopedArm inputs [] := fun _ => arm

def scopedPacket (family : FutureFamily) : Packet (scopedCatalogue inputs arms primitive.scope) raw :=
  ⟨⟨0, by decide⟩, arm.emit raw (data family) (license family)⟩

theorem scoped_evidence_family (family : FutureFamily) :
    (scopedPacket family).value.evidence.2.2.2.2.1 = family := rfl

/-- The independent licensed child exists, built by the exact R343/R318
compiler; no finished Graph, contribution or catalogue equation is supplied. -/
noncomputable def scopedChild (family : FutureFamily) :=
  OriginalClauseCompilerR318.Local.compileLegacy (armTable inputs arms primitive.scope)
    (ArmCompiler.aggregate inputs arms primitive.scope ⟨0, by decide⟩ raw
      (data family) (license family) ⟨0, by decide⟩ (Nat.zero_le _))

/-- Explicit finite-child type at its computed table/root/packet. -/
theorem scoped_child_exists (family : FutureFamily) :
    let table := armTable inputs arms primitive.scope
    let key := joinKey (⟨0, by decide⟩ : Fin 1)
    Nonempty (DeclContribution (OriginalClauseCompilerR318.Local.graph table)
      (OriginalClauseCompilerR318.Local.legacyRelations table)
      (OriginalClauseCompilerR318.Local.operators table) key.val raw
      (OriginalClauseCompilerR318.Local.node table key)
      (OriginalClauseCompilerR318.Local.compiledPacket table key
        (ArmCompiler.joinPacket inputs arms primitive.scope ⟨0, by decide⟩ raw (scopedPacket family)))) :=
  ⟨scopedChild family⟩

theorem no_legacy_packet : ¬ Nonempty (Packet (armsCatalogue inputs state primitive.scope [endpoint]) raw) := by
  rintro ⟨packet⟩
  have i : packet.port = ⟨0, by decide⟩ := by apply Fin.ext; exact Nat.eq_zero_of_le_zero (by have h := packet.port.isLt; change packet.port.val < 1 at h; omega)
  have fields := packet.value
  rw [i] at fields
  have invalid := (evidence_sound _ _ fields).2.2.2.1
  change true = false at invalid
  cases invalid

/-- Thus the exact R306 packet premise is impossible even though its proposed
scoped antecedent, whole license and nonidentity lawful action exist. -/
theorem no_endpoint_projection :
    ¬ Nonempty (Packet (scopedCatalogue inputs arms primitive.scope) raw →
      Packet (armsCatalogue inputs state primitive.scope [endpoint]) raw) := by
  rintro ⟨project⟩
  exact no_legacy_packet ⟨project (scopedPacket (fun _ => false))⟩

/-- The model also makes the original endpoint check observable at its exact
R159 local. This fixed-state reading is a model instance, not an asserted
interpretation of a source-generated environment. -/
def reading (ports : PortReadout sorts Unit) : Reading sorts Value :=
  fun _ mode site context endpoint => stateClause inputs ports state mode site context endpoint

theorem no_original_result_check (guards : GuardRegistry inputs)
    (declarations : Declarations inputs guards) (ports : PortReadout sorts Unit)
    (original : Kernel Value) (environment : Environment Value)
    (context : Context) (mark : Mark) :
    ¬ Checking (OriginalSourceChecking.kernel inputs guards declarations (reading ports) original)
      environment ⟨.computation, mark.site, context,
        ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩ := by
  intro checked
  have sound := checking_sound inputs guards declarations (reading ports) original checked
  have source : Meaning inputs (.trace (raw.atInterface false)) := (trace_iff raw false).mpr rfl
  have target := sound (.computation raw) source
  have impossible := (trace_iff raw true).mp target
  cases impossible

/-- Application to BOTH annotation alternatives, arbitrary children and the
SAME admitted candidate extension of R159. This refutes only the inference
that the authenticated-looking arm model supplies the missing original parent
check; it is not a counterexample to authentic source semantics. -/
theorem no_parent_in_this_model (guards : GuardRegistry inputs)
    (declarations : Declarations inputs guards) (ports : PortReadout sorts Unit)
    (original : Kernel Value) (environment : Environment Value)
    (context : Context) (mark : Mark) (callee argument : Source .expression) :
    ¬ SourceJudgment
      (OriginalSourceChecking.kernel inputs guards declarations (reading ports) original)
      environment context (.app mark callee argument) := by
  intro parent
  obtain ⟨_, candidate, _, continuation⟩ :=
    (SourceAppAdmissionR159.app_source_iff _ _ _ _ _ _).mp parent
  have locals := (SourceAppAdmissionR159.app_continuation_iff _ _ _ _ _ _).mp continuation
  have checked := locals.1 _
    (OriginalUnionOwnerR292.app_computation_premise context mark callee argument)
  cases checked with
  | checking checked =>
    exact no_original_result_check guards declarations ports original
      (environment.extend ⟨mark.site, .viewLogic, 0⟩ candidate) context mark checked

end Separation
end YulangClosure.OriginalAuthenticatedArmTransportR344
