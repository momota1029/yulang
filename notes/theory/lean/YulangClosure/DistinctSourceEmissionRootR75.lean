import YulangClosure.CurrentEmissionOwnershipR47

/-!
R75: a completed Value source root and an Effect-bound emission occupy distinct
relation-table entries. R47 already keeps Query.rootRelation and Probe.relation
separate and checks ancestry between them. The old native inventory guard
identified those entries, making the represented mixed case impossible.

This module proves the relation-role distinction and supplies a finite R47
certificate. LocalOwnership still requires RootMatches and physical readbacks;
no actual Rust extraction, R66 Root, original A/B or production closure follows.
-/
namespace YulangClosure.DistinctSourceEmissionRootR75

open CurrentEmissionOwnershipR47

variable {Artifact Id Fact : Type}

def IsValue : Endpoint Id → Prop
  | .valueRow _ | .valueAtom _ => True
  | .effectRow _ | .effectAtom _ => False

def IsEffect : Endpoint Id → Prop
  | .effectRow _ | .effectAtom _ => True
  | .valueRow _ | .valueAtom _ => False

def ValuePair (pair : Endpoint Id × Endpoint Id) : Prop :=
  IsValue pair.1 ∧ IsValue pair.2

def EffectPair (pair : Endpoint Id × Endpoint Id) : Prop :=
  IsEffect pair.1 ∧ IsEffect pair.2

theorem value_effect_disjoint (v e : Endpoint Id)
    (value : IsValue v) (effect : IsEffect e) : v ≠ e := by
  cases v <;> cases e <;> simp_all [IsValue, IsEffect]

/-- Functionality is enough: equal IDs would read equal endpoint constructors.
Both row and atom endpoints are represented, without an Id equality instance. -/
theorem typed_relation_ids_distinct
    (read : Nat → Option (Endpoint Id × Endpoint Id))
    (source emission : Nat) (sourcePair emissionPair : Endpoint Id × Endpoint Id)
    (sourceRead : read source = some sourcePair)
    (emissionRead : read emission = some emissionPair)
    (sourceTyped : ValuePair sourcePair) (emissionTyped : EffectPair emissionPair) :
    source ≠ emission := by
  intro equal
  cases equal
  have pairs : sourcePair = emissionPair := Option.some.inj (sourceRead.symm.trans emissionRead)
  exact value_effect_disjoint sourcePair.1 emissionPair.1 sourceTyped.1 emissionTyped.1
    (congrArg Prod.fst pairs)

/-- The old receiver equality, with its actual optional admission relation. -/
def OldEqualityGuard (q : Query Artifact Id Fact) (p : Probe Id) : Prop :=
  p.admission.relation = some q.rootRelation

/-- Retain two relation IDs from the original query/probe, without renumbering.
Ancestry has exactly R47's root-to-emission argument order. -/
structure RelationRoles (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact)
    (p : Probe Id) (sourcePair : Endpoint Id × Endpoint Id) : Prop where
  sourceTyped : ValuePair sourcePair
  sourceRead : e.relationPair q.rootRelation = some sourcePair
  emissionTyped : EffectPair (boundPair p.admission.bound)
  emissionRead : e.relationPair p.relation = some (boundPair p.admission.bound)
  admissionRead : p.admission.relation = some p.relation
  ancestry : ancestryCheck e q.rootRelation p.ancestry p.relation = true

theorem roles_distinct (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact)
    (p : Probe Id) (sourcePair : Endpoint Id × Endpoint Id)
    (roles : RelationRoles e q p sourcePair) : q.rootRelation ≠ p.relation :=
  typed_relation_ids_distinct e.relationPair q.rootRelation p.relation sourcePair
    (boundPair p.admission.bound) roles.sourceRead roles.emissionRead
    roles.sourceTyped roles.emissionTyped

theorem old_guard_rejected (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact)
    (p : Probe Id) (sourcePair : Endpoint Id × Endpoint Id)
    (roles : RelationRoles e q p sourcePair) : ¬ OldEqualityGuard q p := by
  intro old
  have equal : p.relation = q.rootRelation := Option.some.inj (roles.admissionRead.symm.trans old)
  exact roles_distinct e q p sourcePair roles equal.symm

theorem roles_preserve_ancestry (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact)
    (p : Probe Id) (sourcePair : Endpoint Id × Endpoint Id)
    (roles : RelationRoles e q p sourcePair) : RelationPath e q.rootRelation p.relation :=
  ancestry_sound e q.rootRelation p.relation p.ancestry roles.ancestry

variable [DecidableEq Id]

/-- Exactly the remaining R47 Matches conjuncts after the relation/admission/
ancestry conjuncts supplied by RelationRoles. These are explicit obligations,
not constructed source/native evidence. In particular RootMatches is retained. -/
def LocalOwnership (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact)
    (p : Probe Id) : Prop :=
  e.admissions[p.admissionIndex]? = some p.admission ∧
  e.emissions[p.emissionIndex]? = some p.emission ∧
  p.emission.admission = p.admissionIndex ∧
  emissionsForSlot e p.emission.physical = [p.emission] ∧
  p.emission.bound = p.admission.bound ∧ p.emission.readback.slot = p.emission.physical ∧
  p.emission.readback.bound = p.admission.bound ∧
  currentBound e p.emission.physical = some p.admission.bound ∧
  RootMatches e q ∧
  p.emission.physical.owner = .effect q.rawEntry ∧
  p.admission.bound.owner = .effect q.rawEntry ∧ p.admission.bound.polarity = .positive

theorem matches_from_local_ownership_and_roles
    (e : Inputs Artifact Id Fact) (q : Query Artifact Id Fact)
    (p : Probe Id) (sourcePair : Endpoint Id × Endpoint Id)
    (ownership : LocalOwnership e q p) (roles : RelationRoles e q p sourcePair) : Matches e q p := by
  rcases ownership with ⟨admission, emission, index, unique, bound, slot, readback, current,
    root, physicalOwner, admissionOwner, polarity⟩
  exact ⟨admission, emission, index, unique, bound, slot, readback, current,
    roles.admissionRead, roles.emissionRead, roles.ancestry, root,
    physicalOwner, admissionOwner, polarity⟩

/-! A finite witness for all R47 Matches obligations. This fixture is a finite
model, not an actual Rust run or the R66 source/native construction. -/
def mixedSourcePair : Endpoint Nat × Endpoint Nat := (.valueRow 30, .valueRow 31)

def mixedBound : Bound Nat := ⟨.effect 20, .positive, .effectRow 21⟩

def mixedSlot : Slot Nat := ⟨.effect 20, .effectLowerRow, 0⟩

def mixedAdmission : Admission Nat := ⟨mixedBound, some 1⟩

def mixedEmission : Emission Nat :=
  ⟨0, mixedBound, mixedSlot, ⟨mixedSlot, mixedBound⟩⟩

def mixedInputs : Inputs Nat Nat Nat where
  artifact := 0
  admissions := [mixedAdmission]
  emissions := [mixedEmission]
  valueRows := fun _ => none
  effectRows := fun row => if row = 20 then some ⟨[21], [], [], []⟩ else none
  liveRelations := [0, 1]
  dependencies := [(0, 1)]
  relationPair := fun relation =>
    if relation = 0 then some mixedSourcePair
    else if relation = 1 then some (boundPair mixedBound) else none
  rootSource := fun relation => if relation = 0 then some (10, 0) else none
  sourceFact := fun source => if source = (10, 0) then some 99 else none
  rootCandidates := fun use fact => if use = ⟨0, 10⟩ ∧ fact = 99 then [0] else []
  rootCause := fun relation => if relation = 0 then some (10, 0) else none
  rootTask := fun relation => if relation = 0 then some 99 else none
  rootCompleted := fun relation => decide (relation = 0)

def mixedQuery : Query Nat Nat Nat := ⟨⟨0, 10⟩, 99, 20, 0⟩

def mixedProbe : Probe Nat := ⟨0, 0, mixedAdmission, mixedEmission, 1, [1]⟩

theorem mixed_roles : RelationRoles mixedInputs mixedQuery mixedProbe mixedSourcePair := by
  constructor
  · exact ⟨True.intro, True.intro⟩
  · rfl
  · exact ⟨True.intro, True.intro⟩
  · rfl
  · rfl
  · decide

theorem mixed_local_ownership : LocalOwnership mixedInputs mixedQuery mixedProbe := by
  unfold LocalOwnership
  decide

theorem mixed_matches : Matches mixedInputs mixedQuery mixedProbe :=
  matches_from_local_ownership_and_roles mixedInputs mixedQuery mixedProbe mixedSourcePair
    mixed_local_ownership mixed_roles

theorem mixed_ancestry : RelationPath mixedInputs mixedQuery.rootRelation mixedProbe.relation :=
  roles_preserve_ancestry mixedInputs mixedQuery mixedProbe mixedSourcePair mixed_roles

theorem mixed_old_guard_rejected : ¬ OldEqualityGuard mixedQuery mixedProbe :=
  old_guard_rejected mixedInputs mixedQuery mixedProbe mixedSourcePair mixed_roles

theorem mixed_accepted : extract mixedInputs mixedQuery mixedProbe =
    some ⟨mixedQuery, mixedProbe⟩ :=
  (accepted_iff mixedInputs mixedQuery mixedProbe ⟨mixedQuery, mixedProbe⟩).mpr ⟨mixed_matches, rfl⟩

theorem mixed_discriminates :
    extract mixedInputs mixedQuery mixedProbe = some ⟨mixedQuery, mixedProbe⟩ ∧
      ¬ OldEqualityGuard mixedQuery mixedProbe :=
  ⟨mixed_accepted, mixed_old_guard_rejected⟩

end YulangClosure.DistinctSourceEmissionRootR75
