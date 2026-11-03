import YulangClosure.OriginalClauseCompilerR318
import YulangClosure.ComputedCallTypedFormationR310

/-!
R343. Original IF §§3–7 and EI-All §4.

This file separates a full dependent field telescope from its result view.
Primitive typing and primitive license are independent inputs. Neither a
DeclContribution nor a catalogue equation is a primitive-contract field.
The scoped construction retains the actual R310 Arm, including duplicate
endpoint occurrences, rather than resolving its endpoint and discarding scope.

This is a research construction, not an extraction of original ArmDecl from
native code and not a claim that static IF formation proves semantic membership.
-/
namespace YulangClosure.OriginalFullIFArmInterpretationR343

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceChecking SourceSignatureConstruction SourceContributionConstruction
open ComputedCallUnionRealizationR293 ComputedCallPhaseDescriptorR306

variable {s : Sorts} {View : Type}

/-- An ordinary dependent telescope. A field may itself be an unrestricted
indexed family; its domain is not enumerated by the finite field spine. -/
inductive Telescope : Type 1 where
  | done
  | field (A : Type) (rest : A → Telescope)

def Telescope.Values : Telescope → Type
  | .done => Unit
  | .field A rest => (a : A) × (rest a).Values

def Telescope.append : (first : Telescope) → (first.Values → Telescope) → Telescope
  | .done, next => next ()
  | .field A rest, next => .field A fun a => (rest a).append (fun tail => next ⟨a, tail⟩)

def Telescope.join : (first : Telescope) → (next : first.Values → Telescope) →
    (value : first.Values) → (next value).Values → (first.append next).Values
  | .done, _, (), second => second
  | .field _ rest, next, ⟨a, tail⟩, second =>
      ⟨a, (rest a).join (fun tail => next ⟨a, tail⟩) tail second⟩

def Telescope.split : (first : Telescope) → (next : first.Values → Telescope) →
    (first.append next).Values → (value : first.Values) × (next value).Values
  | .done, _, value => ⟨(), value⟩
  | .field _ rest, next, ⟨a, value⟩ =>
      let parts := (rest a).split (fun tail => next ⟨a, tail⟩) value
      ⟨⟨a, parts.1⟩, parts.2⟩

theorem Telescope.split_join (first : Telescope) (next : first.Values → Telescope)
    (value : first.Values) (second : (next value).Values) :
    first.split next (first.join next value second) = ⟨value, second⟩ := by
  induction first with
  | done => cases value; rfl
  | field A rest ih =>
      rcases value with ⟨a, tail⟩
      simp only [split, join]
      rw [ih a]

theorem Telescope.join_split (first : Telescope) (next : first.Values → Telescope)
    (value : (first.append next).Values) :
    first.join next (first.split next value).1 (first.split next value).2 = value := by
  induction first with
  | done => rfl
  | field A rest ih =>
      rcases value with ⟨a, tail⟩
      simp only [split, join, ih]
      rfl

/-- Independent original primitive projections at its own trace interface.
The returned row is read from the original trace constructor. Observation
fields carry actual witnesses, including existential providers/futures; the
compiler never chooses a different witness from propositional membership. -/
structure PrimitiveFields (inputs : Inputs s) (row : TraceRow s) where
  coherent : inputs.eventCoherent row.event
  guards : (inputs.observationGuards row).Valid
  world : Meaning inputs (.world row.event)
  returned : match inputs.traceForm row with
    | .pureReturn value => (value.event = row.event) ∧ Meaning inputs (.value value)
    | .unfinished => True
  observations : Evidence (Meaning inputs) (inputs.observationFields row)

def PrimitiveFields.evidence {inputs : Inputs s} {row : TraceRow s}
    (fields : PrimitiveFields inputs row) : Evidence (Meaning inputs) (clause inputs (.trace row)) :=
  ⟨⟨fields.coherent, fields.guards⟩, ⟨fields.world⟩,
    (by cases formed : inputs.traceForm row with
        | pureReturn value =>
            have returned := fields.returned
            rw [formed] at returned
            exact ⟨⟨returned.1⟩, ⟨returned.2⟩⟩
        | unfinished => exact ⟨True.intro⟩), fields.observations⟩

theorem PrimitiveFields.meaning {inputs : Inputs s} {row : TraceRow s}
    (fields : PrimitiveFields inputs row) : Meaning inputs (.trace row) :=
  (meaning_clause inputs _).mpr (evidence_sound _ _ fields.evidence)

def PrimitiveFields.ofEvidence {inputs : Inputs s} {row : TraceRow s}
    (evidence : Evidence (Meaning inputs) (clause inputs (.trace row))) : PrimitiveFields inputs row where
  coherent := evidence.1.down.1
  guards := evidence.1.down.2
  world := evidence.2.1.down
  returned := by
    cases formed : inputs.traceForm row with
    | pureReturn value =>
        have returned := evidence.2.2.1
        change Evidence (Meaning inputs)
          (match inputs.traceForm row with
            | .pureReturn value => .both (.guard (value.event = row.event)) (.field (.value value))
            | .unfinished => .guard True) at returned
        rw [formed] at returned
        exact ⟨returned.1.down, returned.2.down⟩
    | unfinished => exact True.intro
  observations := evidence.2.2.2

theorem PrimitiveFields.roundtrip {inputs : Inputs s} {row : TraceRow s}
    (fields : PrimitiveFields inputs row) : PrimitiveFields.ofEvidence fields.evidence = fields := by
  cases fields
  rfl

/-- Complete ordinary parameters, dependent fields and the SAME license.
`projections` is the original primitive's independent field typing contract,
not a full IF/Call law, graph contribution or target Checking premise. -/
structure Primitive (inputs : Inputs s) where
  owner : Declaration
  occurrence : Site
  scope : List Binder
  parameters : Telescope
  fields : parameters.Values → RawObservation s → Telescope
  interface : parameters.Values → s.Interface
  License : (parameter : parameters.Values) → (raw : RawObservation s) →
    (fields parameter raw).Values → Type
  projections : ∀ parameter raw data, License parameter raw data →
    PrimitiveFields inputs (raw.atInterface (interface parameter))

def Primitive.Data {inputs : Inputs s} (primitive : Primitive inputs) (raw : RawObservation s) :=
  (parameter : primitive.parameters.Values) × (primitive.fields parameter raw).Values

def Primitive.completeTelescope {inputs : Inputs s} (primitive : Primitive inputs)
    (raw : RawObservation s) : Telescope :=
  primitive.parameters.append (fun parameter => primitive.fields parameter raw)

def Primitive.pack {inputs : Inputs s} (primitive : Primitive inputs)
    (raw : RawObservation s) (data : primitive.Data raw) : (primitive.completeTelescope raw).Values :=
  primitive.parameters.join _ data.1 data.2

def Primitive.unpack {inputs : Inputs s} (primitive : Primitive inputs)
    (raw : RawObservation s) (data : (primitive.completeTelescope raw).Values) : primitive.Data raw :=
  primitive.parameters.split _ data

theorem primitive_all_fields_roundtrip {inputs : Inputs s} (primitive : Primitive inputs)
    (raw : RawObservation s) (data : primitive.Data raw) :
    primitive.unpack raw (primitive.pack raw data) = data := by
  rcases data with ⟨parameter, fields⟩
  exact primitive.parameters.split_join (fun parameter => primitive.fields parameter raw) parameter fields

/-- Only the independent ORIGINAL primitive action is input here. No global
arm/table/Call action, target coverage or result contribution occurs in it. -/
structure PrimitiveAction {inputs : Inputs s} (primitive : Primitive inputs) where
  whole : RawObservation s → RawObservation s
  mapParameter : primitive.parameters.Values → primitive.parameters.Values
  mapFields : ∀ parameter raw, (primitive.fields parameter raw).Values →
    (primitive.fields (mapParameter parameter) (whole raw)).Values
  mapLicense : ∀ parameter raw data, primitive.License parameter raw data →
    primitive.License (mapParameter parameter) (whole raw)
      (mapFields parameter raw data)
  mapProjection : ∀ parameter raw,
    PrimitiveFields inputs (raw.atInterface (primitive.interface parameter)) →
    PrimitiveFields inputs ((whole raw).atInterface (primitive.interface (mapParameter parameter)))
  natural : ∀ parameter raw data license,
    mapProjection parameter raw (primitive.projections parameter raw data license) =
      primitive.projections (mapParameter parameter) (whole raw)
        (mapFields parameter raw data) (mapLicense parameter raw data license)

def PrimitiveAction.mapData {inputs : Inputs s} {primitive : Primitive inputs}
    (action : PrimitiveAction primitive) {raw : RawObservation s} (data : primitive.Data raw) :
    primitive.Data (action.whole raw) := ⟨action.mapParameter data.1, action.mapFields data.1 raw data.2⟩

def PrimitiveAction.mapResult {inputs : Inputs s} {primitive : Primitive inputs}
    (action : PrimitiveAction primitive) (raw : RawObservation s)
    (packet : (parameter : primitive.parameters.Values) × Evidence (Meaning inputs)
      (clause inputs (.trace (raw.atInterface (primitive.interface parameter))))) :
    (parameter : primitive.parameters.Values) × Evidence (Meaning inputs)
      (clause inputs (.trace ((action.whole raw).atInterface (primitive.interface parameter)))) :=
  ⟨action.mapParameter packet.1, (action.mapProjection packet.1 raw
    (PrimitiveFields.ofEvidence packet.2)).evidence⟩

/-- The field/parameter injection commutes with the original lawful action.
This uses only the primitive's local field law, not a supplied composite map. -/
theorem primitive_emission_natural {inputs : Inputs s} {primitive : Primitive inputs}
    (action : PrimitiveAction primitive) (raw : RawObservation s) (data : primitive.Data raw)
    (license : primitive.License data.1 raw data.2) :
    action.mapResult raw ⟨data.1, (primitive.projections data.1 raw data.2 license).evidence⟩ =
      ⟨action.mapParameter data.1, (primitive.projections _ _
        (action.mapFields data.1 raw data.2) (action.mapLicense data.1 raw data.2 license)).evidence⟩ := by
  simp only [PrimitiveAction.mapResult, PrimitiveFields.roundtrip, action.natural]

def Primitive.catalogue {inputs : Inputs s} (primitive : Primitive inputs) : Catalogue (RawObservation s) :=
  ⟨Unit, fun raw _ => primitive.Data raw, primitive.scope, fun _ => primitive.occurrence⟩

def Primitive.introduction {inputs : Inputs s} (primitive : Primitive inputs) : Introduction (RawObservation s) :=
  ⟨primitive.owner, primitive.occurrence, .primitive, primitive.catalogue,
    fun raw _ data => primitive.License data.1 raw data.2⟩

/-- A use of the original declaration. The parameter family is retained in
the primitive telescope; `action` is the original whole scoped substitution.
It is not inferred from an endpoint or from equality of descriptor meanings. -/
structure ScopedArm (inputs : Inputs s) (scope : List ComputedCallTypedFormationR310.LocalBinder) where
  original : ComputedCallTypedFormationR310.Arm scope
  primitive : Primitive inputs
  action : RawObservation s → RawObservation s
  useSite : Site

def ScopedArm.data {inputs : Inputs s} {scope} (arm : ScopedArm inputs scope)
    (raw : RawObservation s) := arm.primitive.Data (arm.action raw)

def ScopedArm.body {inputs : Inputs s} {scope} (arm : ScopedArm inputs scope)
    (raw : RawObservation s) (parameter : arm.primitive.parameters.Values) : Positive s :=
  clause inputs (.trace ((arm.action raw).atInterface (arm.primitive.interface parameter)))

structure ArmResult {inputs : Inputs s} {scope} (arm : ScopedArm inputs scope)
    (raw : RawObservation s) where
  original : ComputedCallTypedFormationR310.Arm scope
  sameOriginal : original = arm.original
  parameter : arm.primitive.parameters.Values
  evidence : Evidence (Meaning inputs) (arm.body raw parameter)

abbrev ScopedArm.result {inputs : Inputs s} {scope} (arm : ScopedArm inputs scope)
    (raw : RawObservation s) := ArmResult arm raw

def ScopedArm.emit {inputs : Inputs s} {scope} (arm : ScopedArm inputs scope)
    (raw : RawObservation s) (data : arm.data raw)
    (license : arm.primitive.License data.1 (arm.action raw) data.2) : arm.result raw :=
  ⟨arm.original, rfl, data.1, (arm.primitive.projections _ _ _ license).evidence⟩

theorem scoped_original_retained {inputs : Inputs s} {scope} (arm : ScopedArm inputs scope)
    (raw : RawObservation s) (data : arm.data raw)
    (license : arm.primitive.License data.1 (arm.action raw) data.2) :
    (arm.emit raw data license).original = arm.original := rfl

theorem scoped_parameter_retained {inputs : Inputs s} {scope} (arm : ScopedArm inputs scope)
    (raw : RawObservation s) (data : arm.data raw)
    (license : arm.primitive.License data.1 (arm.action raw) data.2) :
    (arm.emit raw data license).parameter = data.1 := rfl

theorem scoped_observation_fields_retained {inputs : Inputs s} {scope} (arm : ScopedArm inputs scope)
    (raw : RawObservation s) (data : arm.data raw)
    (license : arm.primitive.License data.1 (arm.action raw) data.2) :
    (arm.emit raw data license).evidence.2.2.2 =
      (arm.primitive.projections data.1 (arm.action raw) data.2 license).observations := rfl

/-- Scoped substitution is applied to the whole original row, in order.
No equality of individual endpoint images is used to justify this equation. -/
theorem scoped_substitution_composition {inputs : Inputs s} {scope} (arm : ScopedArm inputs scope)
    (first second : RawObservation s → RawObservation s) (raw : RawObservation s) :
    arm.data ((first ∘ second) raw) = arm.primitive.Data (arm.action (first (second raw))) := rfl

def scopedCatalogue (inputs : Inputs s) {scope} {n : Nat}
    (arms : Fin n → ScopedArm inputs scope) (binders : List Binder) : Catalogue (RawObservation s) :=
  ⟨Fin n, fun raw i => (arms i).result raw, binders, fun i => i.val⟩

/-- The output view is separate from the retained original field interface.
Every original parameter and field remains at its primitive node. -/
def interfaces (inputs : Inputs s) {scope} {n : Nat}
    (arms : Fin n → ScopedArm inputs scope) (binders : List Binder)
    (key : Fin (3*n)) : Catalogue (RawObservation s) :=
  if h : key.val < n then (arms ⟨key.val,h⟩).primitive.catalogue
  else scopedCatalogue inputs arms binders

def substitution (inputs : Inputs s) {scope} {n : Nat}
    (arms : Fin n → ScopedArm inputs scope) (sub : Nat) (raw : RawObservation s) : RawObservation s :=
  if h : sub < n then (arms ⟨sub,h⟩).action raw else raw

theorem substitution_at (inputs : Inputs s) {scope} {n : Nat}
    (arms : Fin n → ScopedArm inputs scope) (i : Fin n) (raw : RawObservation s) :
    substitution inputs arms i.val raw = (arms i).action raw := by
  simp [substitution, i.isLt]

theorem substitution_identity (inputs : Inputs s) {scope} {n : Nat}
    (arms : Fin n → ScopedArm inputs scope) (raw : RawObservation s) :
    substitution inputs arms n raw = raw := by simp [substitution]


/-- Complete original data and the same primitive license determine the result
view. The relation records both packets; it is not a membership oracle. -/
def useRelation (inputs : Inputs s) {scope} {n : Nat}
    (arms : Fin n → ScopedArm inputs scope) (binders : List Binder) (i : Fin n)
    (raw : RawObservation s) {a b : Catalogue (RawObservation s)}
    (child : Packet a (substitution inputs arms i.val raw)) (output : Packet b raw) : Type :=
  Σ data : (arms i).data raw,
  Σ license : (arms i).primitive.License data.1 ((arms i).action raw) data.2,
    PLift (HEq child (⟨(), data⟩ : Packet (arms i).primitive.catalogue ((arms i).action raw)) ∧
      HEq output (⟨i, (arms i).emit raw data license⟩ :
        Packet (scopedCatalogue inputs arms binders) raw))

def samePacket {Joint : Type} {a b : Catalogue Joint} {x y : Joint}
    (first : Packet a x) (second : Packet b y) : Type := PLift (HEq first second)

def leafKey {n : Nat} (i : Fin n) : Fin (3*n) := ⟨i.val, by omega⟩
def useKey {n : Nat} (i : Fin n) : Fin (3*n) := ⟨n+i.val, by omega⟩
def joinKey {n : Nat} (i : Fin n) : Fin (3*n) := ⟨2*n+i.val, by omega⟩

theorem leaf_interface (inputs : Inputs s) {scope} {n : Nat}
    (arms : Fin n → ScopedArm inputs scope) (binders : List Binder) (i : Fin n) :
    interfaces inputs arms binders (leafKey i) = (arms i).primitive.catalogue := by
  simp [interfaces, leafKey, i.isLt]

theorem use_interface (inputs : Inputs s) {scope} {n : Nat}
    (arms : Fin n → ScopedArm inputs scope) (binders : List Binder) (i : Fin n) :
    interfaces inputs arms binders (useKey i) = scopedCatalogue inputs arms binders := by
  simp [interfaces, useKey, show ¬ n+i.val < n by omega]

theorem join_interface (inputs : Inputs s) {scope} {n : Nat}
    (arms : Fin n → ScopedArm inputs scope) (binders : List Binder) (i : Fin n) :
    interfaces inputs arms binders (joinKey i) = scopedCatalogue inputs arms binders := by
  simp [interfaces, joinKey, show ¬ 2*n+i.val < n by omega]

def transportLicense {Joint : Type} {a b : Catalogue Joint} (same : a = b)
    (license : (raw : Joint) → (port : a.Port) → a.Packet raw port → Type)
    (raw : Joint) (port : b.Port) (value : b.Packet raw port) : Type :=
  let packet : Packet a raw := same.symm ▸ (⟨port, value⟩ : Packet b raw)
  license raw packet.port packet.value

theorem transport_license_cancel {Joint : Type} {a b : Catalogue Joint} (same : a = b)
    (license : (raw : Joint) → (port : a.Port) → a.Packet raw port → Type)
    (raw : Joint) (packet : Packet a raw) :
    transportLicense same license raw (same ▸ packet).port (same ▸ packet).value =
      license raw packet.port packet.value := by cases same; rfl

def joinClause (inputs : Inputs s) {scope} {n : Nat}
    (arms : Fin n → ScopedArm inputs scope) (binders : List Binder)
    (key : Fin (3*n)) (i : Fin n) :
    OriginalClauseCompilerR318.Local.Clause (interfaces inputs arms binders)
      (substitution inputs arms) (interfaces inputs arms binders key) :=
  if next : i.val+1 < n then
    .union (useKey i) (joinKey ⟨i.val+1,next⟩)
      (fun _ child output => samePacket child output)
      (fun _ child output => samePacket child output)
  else .reference n (useKey i) (fun _ child output => samePacket child output)

/-- All leaves, all original scoped uses and the full ordered alternative
spine are allocated before choosing an observation or a licensed arm. -/
def armTable (inputs : Inputs s) {scope} {n : Nat}
    (arms : Fin n → ScopedArm inputs scope) (binders : List Binder) :
    OriginalClauseCompilerR318.Local.Table (RawObservation s) (3*n) where
  interfaces := interfaces inputs arms binders
  substitution := substitution inputs arms
  identity := fun key =>
    if h : key.val < n then
      let p := (arms ⟨key.val,h⟩).primitive
      ⟨p.owner, p.owner, key.val, p.occurrence, p.scope⟩
    else if use : key.val < 2*n then
      let arm := arms ⟨key.val-n, by omega⟩
      ⟨arm.primitive.owner, arm.original.originalScope.origin, key.val, arm.useSite, binders⟩
    else ⟨0, 0, key.val, key.val, binders⟩
  clauses := fun key => by
    by_cases leaf : key.val < n
    · let i : Fin n := ⟨key.val,leaf⟩
      have eqn : interfaces inputs arms binders key = (arms i).primitive.catalogue := by
        simp [interfaces, leaf, i]
      exact .primitive .primitive (transportLicense eqn.symm (fun raw _ data =>
        (arms i).primitive.License data.1 raw data.2))
    · by_cases use : key.val < 2*n
      · let i : Fin n := ⟨key.val-n, by omega⟩
        exact .reference i.val (leafKey i) (fun raw child output =>
          useRelation inputs arms binders i raw child output)
      · let i : Fin n := ⟨key.val-2*n, by omega⟩
        exact joinClause inputs arms binders key i
  scopeAgreement := by
    intro key
    by_cases h : key.val < n
    · simp [interfaces, h, Primitive.catalogue]
    · simp only [interfaces, h, ↓reduceDIte, scopedCatalogue]
      split <;> rfl


namespace ArmCompiler
open OriginalClauseCompilerR318.Local
variable (inputs : Inputs s) {scope} {n : Nat}
  (arms : Fin n → ScopedArm inputs scope) (binders : List Binder)

def leafPacket (i : Fin n) (raw : RawObservation s) (data : (arms i).primitive.Data raw) :
    Packet ((armTable inputs arms binders).interfaces (leafKey i)) raw :=
  show Packet (interfaces inputs arms binders (leafKey i)) raw from
    (leaf_interface inputs arms binders i).symm ▸ (⟨(), data⟩ : Packet (arms i).primitive.catalogue raw)

def usePacket (i : Fin n) (raw : RawObservation s)
    (packet : Packet (scopedCatalogue inputs arms binders) raw) :
    Packet ((armTable inputs arms binders).interfaces (useKey i)) raw :=
  show Packet (interfaces inputs arms binders (useKey i)) raw from
    (use_interface inputs arms binders i).symm ▸ packet

def joinPacket (i : Fin n) (raw : RawObservation s)
    (packet : Packet (scopedCatalogue inputs arms binders) raw) :
    Packet ((armTable inputs arms binders).interfaces (joinKey i)) raw :=
  show Packet (interfaces inputs arms binders (joinKey i)) raw from
    (join_interface inputs arms binders i).symm ▸ packet

def leafLicense (i : Fin n) :=
  transportLicense (leaf_interface inputs arms binders i).symm
    (fun raw _ data => (arms i).primitive.License data.1 raw data.2)

def leafDerivation (i : Fin n) (raw : RawObservation s) (data : (arms i).primitive.Data raw)
    (license : (arms i).primitive.License data.1 raw data.2) :
    Derivation (armTable inputs arms binders) (leafKey i) raw
      (leafPacket inputs arms binders i raw data) := by
  refine .primitive _ .primitive (leafLicense inputs arms binders i) ?_ _ _ ?_
  · simp only [armTable, leafKey, dite_eq_left i.isLt]
    rfl
  · change transportLicense _ _ raw ((leaf_interface inputs arms binders i).symm ▸
        (⟨(), data⟩ : Packet (arms i).primitive.catalogue raw)).port
      ((leaf_interface inputs arms binders i).symm ▸
        (⟨(), data⟩ : Packet (arms i).primitive.catalogue raw)).value
    rw [transport_license_cancel]
    exact license

theorem row_cast_heq {cat : Catalogue (RawObservation s)} {a b : RawObservation s}
    (h : a = b) (p : Packet cat a) : HEq (h ▸ p) p := by cases h; rfl

def row_cast_derivation {table : Table (RawObservation s) n} {key : Fin n}
    {a b : RawObservation s} (h : a = b) {p : Packet (table.interfaces key) a}
    (d : Derivation table key a p) : Derivation table key b (h ▸ p) := by cases h; exact d

theorem dependent_congr {A : Sort u} {B : A → Sort v} (f : (a : A) → B a)
    {a b : A} (same : a = b) : HEq (f a) (f b) := by cases same; rfl

noncomputable def useDerivation (i : Fin n) (raw : RawObservation s)
    (data : (arms i).data raw)
    (license : (arms i).primitive.License data.1 ((arms i).action raw) data.2) :
    Derivation (armTable inputs arms binders) (useKey i) raw
      (usePacket inputs arms binders i raw ⟨i, (arms i).emit raw data license⟩) := by
  have action := substitution_at inputs arms i raw
  let originalPacket : Packet ((armTable inputs arms binders).interfaces (leafKey i))
      (substitution inputs arms i.val raw) := action.symm ▸ leafPacket inputs arms binders i _ data
  have original : Derivation (armTable inputs arms binders) (leafKey i)
      (substitution inputs arms i.val raw) originalPacket := by
    exact row_cast_derivation action.symm (leafDerivation inputs arms binders i _ data license)
  refine .reference (useKey i) (leafKey i) i.val
    (fun raw child output => useRelation inputs arms binders i raw child output)
    ?_ original _ ?_
  · simp [armTable, useKey, show ¬ n+i.val < n by omega,
      show n+i.val < 2*n by omega]
    exact dependent_congr
      (fun j : Fin n => fun raw
        (child : Packet (interfaces inputs arms binders (leafKey j))
          (substitution inputs arms j.val raw))
        (output : Packet (interfaces inputs arms binders (useKey i)) raw) =>
          useRelation inputs arms binders j raw child output)
      (by apply Fin.ext; dsimp; omega)
  · refine ⟨data, license, ⟨?_, ?_⟩⟩
    · exact HEq.trans (row_cast_heq action.symm _) (transported_packet_heq _ _)
    · exact transported_packet_heq _ _


theorem join_clause (i : Fin n) :
    (armTable inputs arms binders).clauses (joinKey i) =
      joinClause inputs arms binders (joinKey i) i := by
  simp only [armTable, joinKey, dite_eq_right (show ¬ 2*n+i.val < n by omega),
    dite_eq_right (show ¬ 2*n+i.val < 2*n by omega)]
  exact congrArg (joinClause inputs arms binders (joinKey i))
    (by apply Fin.ext; dsimp; omega)

theorem join_packet_heq (i : Fin n) (raw : RawObservation s)
    (packet : Packet (scopedCatalogue inputs arms binders) raw) :
    HEq (joinPacket inputs arms binders i raw packet) packet := transported_packet_heq _ _

theorem use_packet_heq (i : Fin n) (raw : RawObservation s)
    (packet : Packet (scopedCatalogue inputs arms binders) raw) :
    HEq (usePacket inputs arms binders i raw packet) packet := transported_packet_heq _ _

noncomputable def joinSelected (i : Fin n) (raw : RawObservation s)
    (data : (arms i).data raw)
    (license : (arms i).primitive.License data.1 ((arms i).action raw) data.2) :
    Derivation (armTable inputs arms binders) (joinKey i) raw
      (joinPacket inputs arms binders i raw ⟨i, (arms i).emit raw data license⟩) := by
  let packet : Packet (scopedCatalogue inputs arms binders) raw := ⟨i, (arms i).emit raw data license⟩
  have child := useDerivation inputs arms binders i raw data license
  have formed := join_clause inputs arms binders i
  by_cases next : i.val+1 < n
  · rw [joinClause, dite_eq_left next] at formed
    exact .unionLeft _ _ _ _ _ formed child _
      ⟨HEq.trans (use_packet_heq inputs arms binders i raw packet)
        (join_packet_heq inputs arms binders i raw packet).symm⟩
  · rw [joinClause, dite_eq_right next] at formed
    have action := substitution_identity inputs arms raw
    exact .reference _ _ _ _ formed (row_cast_derivation action.symm child) _
      ⟨HEq.trans (row_cast_heq action.symm _) (HEq.trans
        (use_packet_heq inputs arms binders i raw packet)
        (join_packet_heq inputs arms binders i raw packet).symm)⟩

/-- Every original arm reaches the SAME fixed aggregate root. Neither the
finite graph nor its right child is selected after seeing a license. -/
noncomputable def aggregate (selected : Fin n) (raw : RawObservation s)
    (data : (arms selected).data raw)
    (license : (arms selected).primitive.License data.1 ((arms selected).action raw) data.2)
    (start : Fin n) (before : start.val ≤ selected.val) :
    Derivation (armTable inputs arms binders) (joinKey start) raw
      (joinPacket inputs arms binders start raw ⟨selected, (arms selected).emit raw data license⟩) := by
  let packet : Packet (scopedCatalogue inputs arms binders) raw :=
    ⟨selected, (arms selected).emit raw data license⟩
  generalize distance : selected.val-start.val = gap
  induction gap generalizing start with
  | zero =>
      have same : start = selected := by apply Fin.ext; omega
      subst start
      exact joinSelected inputs arms binders selected raw data license
  | succ gap ih =>
      have next : start.val+1 < n := by omega
      let following : Fin n := ⟨start.val+1,next⟩
      have child := ih following (by dsimp [following]; omega) (by dsimp [following]; omega)
      have formed := join_clause inputs arms binders start
      rw [joinClause, dite_eq_left next] at formed
      exact .unionRight _ _ _ _ _ formed child _
        ⟨HEq.trans (join_packet_heq inputs arms binders following raw packet)
          (join_packet_heq inputs arms binders start raw packet).symm⟩

end ArmCompiler


/-- Exact legacy specialization. This is intentionally stronger than equality
of numeric endpoints: the original scoped whole action must be identity, and
EVERY ordinary parameter must denote the endpoint's same interface. Scope and
primitive fields remain retained in the pre-projection graph. -/
structure LegacySpecialization (inputs : Inputs s) (state : Decoded s View)
    {scope} (ends : List Endpoint) (arms : Fin ends.length → ScopedArm inputs scope) : Prop where
  slot : ∀ i, (arms i).original.descriptor.slot =
    .arm (arms i).original.tag ends[i]
  action : ∀ i raw, (arms i).action raw = raw
  interface : ∀ i parameter, (arms i).primitive.interface parameter = state.interfaces ends[i]

noncomputable def legacyPacket (inputs : Inputs s) (state : Decoded s View)
    {scope} (ends : List Endpoint) (arms : Fin ends.length → ScopedArm inputs scope)
    (binders : List Binder) (special : LegacySpecialization inputs state ends arms)
    {raw : RawObservation s} (packet : Packet (scopedCatalogue inputs arms binders) raw) :
    Packet (armsCatalogue inputs state binders ends) raw := by
  rcases packet with ⟨i, original, sameOriginal, parameter, evidence⟩
  refine ⟨i, ?_⟩
  change Evidence (Meaning inputs) (clause inputs (.trace
    ((arms i).action raw |>.atInterface ((arms i).primitive.interface parameter)))) at evidence
  rw [special.action i raw, special.interface i parameter] at evidence
  exact evidence

/-- A typed contextual result projection, keeping the antecedent proof and
all of its complete primitive fields in the graph. No new license is issued. -/
inductive ViewRelation (graph : Graph Joint) (site target sub : Nat)
    (source result : Catalogue Joint) (project : ∀ raw, Packet source raw → Packet result raw)
    (identityAction : ∀ raw, graph.substitution sub raw = raw) :
    (step : SourceSignatureConstruction.Step) → (raw : Joint) →
    {a b : Catalogue Joint} → Packet a (step.action graph raw) → Packet b raw → Type where
  | view (raw : Joint) (packet : Packet source raw) :
      ViewRelation graph site target sub source result project identityAction
        (.reference site target sub) raw (identityAction raw |>.symm ▸ packet) (project raw packet)

def viewRelations (graph : Graph Joint) (old : Relations graph) (site target sub : Nat)
    (source result : Catalogue Joint) (project : ∀ raw, Packet source raw → Packet result raw)
    (identityAction : ∀ raw, graph.substitution sub raw = raw) : Relations graph :=
  { old with forward := fun step raw {_ _} child output =>
      (Sum (old.forward step raw child output)
        (ViewRelation graph site target sub source result project identityAction step raw child output)) }

def retainView {graph : Graph Joint} (old : Relations graph) (ops : Operators graph)
    (site target sub : Nat) (source result : Catalogue Joint)
    (project : ∀ raw, Packet source raw → Packet result raw)
    (identityAction : ∀ raw, graph.substitution sub raw = raw)
    {index raw node packet} (proof : DeclContribution graph old ops index raw node packet) :
    DeclContribution graph (viewRelations graph old site target sub source result project identityAction)
      ops index raw node packet :=
  SourceDeclarationNoninterferenceR296.erase
    (SourceDeclarationNoninterferenceR296.map
      (a := fun _ => old)
      (b := fun _ => viewRelations graph old site target sub source result project identityAction)
      (fun _ => ⟨fun _ _ _ {_ _} _ _ h => h, fun _ _ {_ _ _} _ _ _ h => h,
        fun _ _ {_ _} _ _ h => Sum.inl h⟩)
      (SourceDeclarationNoninterferenceR296.embed proof))

def moveContribution {graph : Graph Joint} {relations : Relations graph} {ops : Operators graph}
    {index : Nat} {a b : Joint} {node : Node Joint} {packet : Packet node.catalogue a}
    (same : a = b) (proof : DeclContribution graph relations ops index a node packet) :
    DeclContribution graph relations ops index b node (same ▸ packet) := by
  cases same
  exact proof

namespace Legacy
open OriginalClauseCompilerR318.Local
variable (inputs : Inputs s) (state : Decoded s View) {scope}
  (ends : List Endpoint) (arms : Fin ends.length → ScopedArm inputs scope)
  (binders : List Binder) (special : LegacySpecialization inputs state ends arms)
  (inhabited : 0 < ends.length) (viewSite : Nat)

def originalGraph := graph (armTable inputs arms binders)
def root : Fin ends.length := ⟨0,inhabited⟩
def target : Nat := (joinKey (root ends inhabited)).val

def viewNode : Node (RawObservation s) :=
  .reference viewSite (target ends inhabited) ends.length (armsCatalogue inputs state binders ends)

def installed : Graph (RawObservation s) :=
  appendNode (originalGraph inputs ends arms binders) (viewNode inputs state ends binders inhabited viewSite)

def oldRelations : Relations (installed inputs state ends arms binders inhabited viewSite) :=
  appendRelations _ _ (legacyRelations (armTable inputs arms binders))

def ops : Operators (installed inputs state ends arms binders inhabited viewSite) :=
  appendOperators _ _ (operators (armTable inputs arms binders))

theorem identityAction (raw : RawObservation s) :
    (installed inputs state ends arms binders inhabited viewSite).substitution ends.length raw = raw :=
  substitution_identity inputs arms raw

noncomputable def relation : Relations (installed inputs state ends arms binders inhabited viewSite) :=
  viewRelations _ (oldRelations inputs state ends arms binders inhabited viewSite)
    viewSite (target ends inhabited) ends.length (scopedCatalogue inputs arms binders)
    (armsCatalogue inputs state binders ends)
    (fun _ packet => legacyPacket inputs state ends arms binders special packet)
    (identityAction inputs state ends arms binders inhabited viewSite)

/-- Both the catalogue and the original finite arm child are constructed.
Only independent primitive data/license enters this function. -/
noncomputable def child (selected : Fin ends.length) (raw : RawObservation s)
    (data : (arms selected).data raw)
    (license : (arms selected).primitive.License data.1 ((arms selected).action raw) data.2) :
    DeclContribution (installed inputs state ends arms binders inhabited viewSite)
      (relation inputs state ends arms binders special inhabited viewSite)
      (ops inputs state ends arms binders inhabited viewSite)
      (originalGraph inputs ends arms binders).nodes.length raw
      (viewNode inputs state ends binders inhabited viewSite)
      (legacyPacket inputs state ends arms binders special
        ⟨selected, (arms selected).emit raw data license⟩) := by
  let table := armTable inputs arms binders
  let packet : Packet (scopedCatalogue inputs arms binders) raw :=
    ⟨selected, (arms selected).emit raw data license⟩
  let derivation := ArmCompiler.aggregate inputs arms binders selected raw data license
    (root ends inhabited) (Nat.zero_le _)
  have original := compileLegacy table derivation
  have appended := appendContribution (originalGraph inputs ends arms binders)
    (viewNode inputs state ends binders inhabited viewSite) (legacyRelations table) (operators table) original
  have retained := retainView (oldRelations inputs state ends arms binders inhabited viewSite)
    (ops inputs state ends arms binders inhabited viewSite) viewSite (target ends inhabited) ends.length
    (scopedCatalogue inputs arms binders) (armsCatalogue inputs state binders ends)
    (fun _ packet => legacyPacket inputs state ends arms binders special packet)
    (identityAction inputs state ends arms binders inhabited viewSite) appended
  have sameCatalogue : (node table (joinKey (root ends inhabited))).catalogue =
      scopedCatalogue inputs arms binders :=
    (catalogue_retained table _).trans (join_interface inputs arms binders _)
  have packetEq : sameCatalogue ▸ compiledPacket table (joinKey (root ends inhabited))
      (ArmCompiler.joinPacket inputs arms binders (root ends inhabited) raw packet) = packet := by
    apply eq_of_heq
    exact HEq.trans (transported_packet_heq _ _) (HEq.trans (packet_heq table _ _)
      (ArmCompiler.join_packet_heq inputs arms binders _ raw packet))
  have action := identityAction inputs state ends arms binders inhabited viewSite raw
  have childAt : DeclContribution _ _ _ (target ends inhabited)
      ((installed inputs state ends arms binders inhabited viewSite).substitution ends.length raw)
      (node table (joinKey (root ends inhabited)))
      (action.symm ▸ compiledPacket table (joinKey (root ends inhabited))
        (ArmCompiler.joinPacket inputs arms binders (root ends inhabited) raw packet)) :=
    moveContribution action.symm retained
  refine .forward (appended_node _ _) .reference childAt _ (Sum.inr ?_)
  have result := ViewRelation.view
    (graph := installed inputs state ends arms binders inhabited viewSite)
    (site := viewSite) (target := target ends inhabited) (sub := ends.length)
    (project := fun _ packet => legacyPacket inputs state ends arms binders special packet)
    (identityAction := identityAction inputs state ends arms binders inhabited viewSite) raw packet
  -- The two transports only align catalogue and row types, never field values.
  have align {cat : Catalogue (RawObservation s)} (same : cat = scopedCatalogue inputs arms binders)
      (p : Packet cat raw) (equal : HEq p packet) :
      ViewRelation (installed inputs state ends arms binders inhabited viewSite)
        viewSite (target ends inhabited) ends.length (scopedCatalogue inputs arms binders)
        (armsCatalogue inputs state binders ends)
        (fun _ packet => legacyPacket inputs state ends arms binders special packet)
        (identityAction inputs state ends arms binders inhabited viewSite)
        (.reference viewSite (target ends inhabited) ends.length) raw (action.symm ▸ p)
        (legacyPacket inputs state ends arms binders special packet) := by
    cases same
    have equality := eq_of_heq equal
    subst p
    exact result
  exact align sameCatalogue _ (HEq.trans (packet_heq table _ _)
    (ArmCompiler.join_packet_heq inputs arms binders _ raw packet))


/-- Application to the unchanged R306 consumer. Its `childNode`,
`sameCatalogue`, graph lookup and finite `child` are all computed outputs.
The legacy specialization and the independently typed primitive license remain
explicit; source Checking/admission and the original R159 goal are unchanged. -/
theorem arm_registered (callSite left : Nat) (source : Endpoint)
    (selected : Fin ends.length) (raw : RawObservation s)
    (data : (arms selected).data raw)
    (license : (arms selected).primitive.License data.1 ((arms selected).action raw) data.2) :
    let g := installed inputs state ends arms binders inhabited viewSite
    let old := relation inputs state ends arms binders special inhabited viewSite
    let operators := ops inputs state ends arms binders inhabited viewSite
    let right := (originalGraph inputs ends arms binders).nodes.length
    let packet := legacyPacket inputs state ends arms binders special
      (⟨selected, (arms selected).emit raw data license⟩ : Packet (scopedCatalogue inputs arms binders) raw)
    let added := unionNode inputs state binders callSite left right source ends
    let result := installUnion inputs state binders g callSite left right source ends
    Nonempty (DeclContribution result
      (ComputedCallUnionRealizationR293.relations result (appendRelations g added old)
        inputs state binders callSite source ends)
      (appendOperators g added operators) g.nodes.length raw added
      (injectArm inputs state binders source ends packet)) := by
  exact arm_contribution_registered inputs state binders
    (installed inputs state ends arms binders inhabited viewSite)
    (relation inputs state ends arms binders special inhabited viewSite)
    (ops inputs state ends arms binders inhabited viewSite) callSite left
    (originalGraph inputs ends arms binders).nodes.length source ends raw
    (viewNode inputs state ends binders inhabited viewSite) rfl
    (legacyPacket inputs state ends arms binders special
      ⟨selected, (arms selected).emit raw data license⟩)
    (child inputs state ends arms binders special inhabited viewSite selected raw data license)

end Legacy

end YulangClosure.OriginalFullIFArmInterpretationR343
