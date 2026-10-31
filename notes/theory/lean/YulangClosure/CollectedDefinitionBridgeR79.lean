import YulangClosure.IntegratedSourceAlignmentR78

/-!
R79 models the nominal HIR-definition/collected-definition boundary. HIR bindings
are scanned in their retained HIR order. Exact identity, rather than spelling,
selects one binding; its root and retained indexes authenticate the solver ID.
The collection-time map synthesizes IDs independently from admitted-binding
order. Its agreement theorem exposes the collection-order invariant explicitly.
This is a finite record model, not Rust extraction or whole-language closure.
-/
namespace YulangClosure.CollectedDefinitionBridgeR79

structure HirDef where
  moduleId : Nat
  spelling : Nat
  sameNameOrdinal : Nat
  deriving DecidableEq, Repr

structure CollectedDef where
  artifact : Nat
  ordinal : Nat
  deriving DecidableEq, Repr

structure Root where
  artifact : Nat
  ordinal : Nat
  deriving DecidableEq, Repr

structure Binding where
  id : HirDef
  root : Root
  deriving DecidableEq, Repr

structure Hir where
  artifact : Nat
  bindings : List Binding
  deriving DecidableEq, Repr

structure DefinitionRecord where
  definition : CollectedDef
  root : Root
  deriving DecidableEq, Repr

structure Batch where
  artifact : Nat
  hirs : List Hir
  definitions : List DefinitionRecord
  rootHirPositions : List Nat
  rootPositions : List (Root × Nat)
  definitionPositions : List (CollectedDef × Nat)
  deriving DecidableEq, Repr

structure LocatedBinding where
  hirPosition : Nat
  hirArtifact : Nat
  binding : Binding
  deriving DecidableEq, Repr

/-- Imported/member/expression items do not allocate an admitted-binding ordinal.
Their exclusion from this inventory models the actual collection loop only;
the source language and the R78 call inventory are not restricted. -/
def locatedBindings (b : Batch) : List LocatedBinding :=
  b.hirs.zipIdx.flatMap fun hp =>
    hp.1.bindings.map fun binding => ⟨hp.2, hp.1.artifact, binding⟩

def singleton? {A : Type} : List A → Option A
  | [a] => some a
  | _ => none

theorem singleton_eq_some {A : Type} (xs : List A) (a : A) :
    singleton? xs = some a ↔ xs = [a] := by
  cases xs with
  | nil => simp [singleton?]
  | cons x xs =>
    cases xs with
    | nil => simp [singleton?]
    | cons y ys => simp [singleton?]

/-- Lists represent finite maps; rejecting duplicate keys also models the
uniqueness guaranteed by a real HashMap's representation. -/
def assoc {A : Type} [DecidableEq A] (key : A) (entries : List (A × Nat)) : Option Nat :=
  (singleton? (entries.filter fun p => decide (p.1 = key))).map Prod.snd

def candidates (b : Batch) (query : HirDef) : List LocatedBinding :=
  (locatedBindings b).filter fun loc => decide (loc.binding.id = query)

def RowChecks (b : Batch) (loc : LocatedBinding) (position : Nat)
    (record : DefinitionRecord) : Prop :=
  loc.binding.root.artifact = loc.hirArtifact ∧
  b.rootHirPositions[position]? = some loc.hirPosition ∧
  record.root = loc.binding.root ∧
  record.definition = ⟨b.artifact, position⟩ ∧
  assoc record.definition b.definitionPositions = some position

instance (b : Batch) (loc : LocatedBinding) (position : Nat) (record : DefinitionRecord) :
    Decidable (RowChecks b loc position record) := by
  unfold RowChecks
  infer_instance

def checkRow (b : Batch) (loc : LocatedBinding) : Option CollectedDef := do
  let position ← assoc loc.binding.root b.rootPositions
  let record ← b.definitions[position]?
  if RowChecks b loc position record then some record.definition else none

/-- All exact-ID competitors are counted before validating the unique match.
Malformed unrelated bindings are not a reason to reject a valid lookup. -/
def lookup (b : Batch) (query : HirDef) : Option CollectedDef := do
  let loc ← singleton? (candidates b query)
  checkRow b loc

def Authenticated (b : Batch) (loc : LocatedBinding) (d : CollectedDef) : Prop :=
  ∃ position record,
    assoc loc.binding.root b.rootPositions = some position ∧
    b.definitions[position]? = some record ∧
    RowChecks b loc position record ∧ record.definition = d

theorem check_row_sound (b : Batch) (loc : LocatedBinding) (d : CollectedDef)
    (success : checkRow b loc = some d) : Authenticated b loc d := by
  unfold checkRow at success
  cases hp : assoc loc.binding.root b.rootPositions with
  | none => simp [hp] at success
  | some position =>
    cases hr : b.definitions[position]? with
    | none => simp [hp, hr] at success
    | some record =>
      by_cases hc : RowChecks b loc position record
      · have hd : record.definition = d := by simpa [hp, hr, hc] using success
        exact ⟨position, record, hp, hr, hc, hd⟩
      · simp [hp, hr, hc] at success

theorem lookup_sound_and_unique (b : Batch) (query : HirDef) (d : CollectedDef)
    (success : lookup b query = some d) :
    ∃ loc, candidates b query = [loc] ∧ Authenticated b loc d := by
  unfold lookup at success
  cases hs : singleton? (candidates b query) with
  | none => simp [hs] at success
  | some loc =>
    exact ⟨loc, (singleton_eq_some _ _).mp hs,
      check_row_sound b loc d (by simpa [hs] using success)⟩

theorem located_provenance (b : Batch) (loc : LocatedBinding)
    (member : loc ∈ locatedBindings b) :
    ∃ hir, b.hirs[loc.hirPosition]? = some hir ∧
      loc.hirArtifact = hir.artifact ∧
      loc.binding ∈ hir.bindings := by
  simp only [locatedBindings, List.mem_flatMap, List.mem_map] at member
  rcases member with ⟨⟨hir, position⟩, hm, binding, bm, he⟩
  cases he
  exact ⟨hir, List.mk_mem_zipIdx_iff_getElem?.mp hm, rfl, bm⟩

theorem lookup_preserves_exact_coordinates (b : Batch) (query : HirDef) (d : CollectedDef)
    (success : lookup b query = some d) :
    ∃ loc hir position record,
      candidates b query = [loc] ∧ loc.binding.id = query ∧
      b.hirs[loc.hirPosition]? = some hir ∧ loc.binding ∈ hir.bindings ∧
      loc.binding.root.artifact = hir.artifact ∧
      assoc loc.binding.root b.rootPositions = some position ∧
      b.rootHirPositions[position]? = some loc.hirPosition ∧
      b.definitions[position]? = some record ∧ record.root = loc.binding.root ∧
      d = ⟨b.artifact, position⟩ ∧
      assoc d b.definitionPositions = some position := by
  rcases lookup_sound_and_unique b query d success with ⟨loc, unique, position, record, hp, hr, hc, hd⟩
  have mem : loc ∈ candidates b query := by rw [unique]; simp
  have filtered := List.mem_filter.mp mem
  have idEq : loc.binding.id = query := of_decide_eq_true filtered.2
  rcases located_provenance b loc filtered.1 with ⟨hir, hh, ha, hb⟩
  rcases hc with ⟨owned, positionEq, rootEq, definitionEq, reverseEq⟩
  exact ⟨loc, hir, position, record, unique, idEq, hh, hb,
    owned.trans ha, hp, positionEq, hr, rootEq,
    hd.symm.trans definitionEq, hd ▸ reverseEq⟩

/-- This is the collection-time temporary map: the ID is synthesized from the
admitted-binding order, independently of the retained DefinitionRecord IDs. -/
def collectionMap (b : Batch) : List (HirDef × CollectedDef) :=
  (locatedBindings b).zipIdx.map fun p => (p.1.binding.id, ⟨b.artifact, p.2⟩)

/-- Collection's root-position table must be the actual admitted-binding order.
This is an explicit construction invariant, not an assumed target equality or
an assumed agreement of the two lookup functions. Rust extraction must prove it. -/
def OrderedRoots (b : Batch) : Prop :=
  ∀ p ∈ (locatedBindings b).zipIdx,
    assoc p.1.binding.root b.rootPositions = some p.2

theorem lookup_agrees_with_collection_map (b : Batch) (ordered : OrderedRoots b)
    (query : HirDef) (d : CollectedDef) (success : lookup b query = some d) :
    (query, d) ∈ collectionMap b := by
  rcases lookup_sound_and_unique b query d success with ⟨loc, unique, position, record, hp, hr, hc, hd⟩
  have mem : loc ∈ candidates b query := by rw [unique]; simp
  have filtered := List.mem_filter.mp mem
  have idEq : loc.binding.id = query := of_decide_eq_true filtered.2
  rcases List.mem_iff_getElem?.mp filtered.1 with ⟨index, hi⟩
  have indexed : (loc, index) ∈ (locatedBindings b).zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr hi
  have posEq : position = index := Option.some.inj (hp.symm.trans (ordered _ indexed))
  have defEq : d = (⟨b.artifact, index⟩ : CollectedDef) :=
    hd.symm.trans (hc.2.2.2.1.trans (congrArg (fun n => (⟨b.artifact, n⟩ : CollectedDef)) posEq))
  exact List.mem_map.mpr ⟨(loc, index), indexed, by simp [idEq, defEq]⟩

theorem collection_map_target_unique (b : Batch) (ordered : OrderedRoots b)
    (query : HirDef) (d : CollectedDef) (success : lookup b query = some d)
    (other : CollectedDef) (member : (query, other) ∈ collectionMap b) : other = d := by
  rcases lookup_sound_and_unique b query d success with ⟨loc, unique, position, record, hp, hr, hc, hd⟩
  rcases List.mem_map.mp member with ⟨⟨otherLoc, index⟩, indexed, imageEq⟩
  have idEq : otherLoc.binding.id = query := congrArg Prod.fst imageEq
  have otherEq : (⟨b.artifact, index⟩ : CollectedDef) = other := congrArg Prod.snd imageEq
  have otherMem : otherLoc ∈ candidates b query :=
    List.mem_filter.mpr ⟨List.fst_mem_of_mem_zipIdx indexed, by simp [idEq]⟩
  have locEq : otherLoc = loc := by simpa [unique] using otherMem
  subst otherLoc
  have posEq : position = index := Option.some.inj (hp.symm.trans (ordered _ indexed))
  exact otherEq.symm.trans ((congrArg (fun n => (⟨b.artifact, n⟩ : CollectedDef)) posEq).symm.trans
    (hc.2.2.2.1.symm.trans hd))

theorem duplicate_exact_bindings_reject (b : Batch) (query : HirDef)
    (first second : LocatedBinding) (rest : List LocatedBinding)
    (duplicates : candidates b query = first :: second :: rest) :
    lookup b query = none := by simp [lookup, duplicates, singleton?]

theorem absent_exact_identity_rejects (b : Batch) (query : HirDef)
    (absent : candidates b query = []) : lookup b query = none := by
  simp [lookup, absent, singleton?]

theorem wrong_collection_artifact_rejects (b : Batch) (query : HirDef) (d : CollectedDef)
    (foreign : d.artifact ≠ b.artifact) : lookup b query ≠ some d := by
  intro success
  rcases lookup_sound_and_unique b query d success with ⟨loc, unique, position, record, hp, hr, hc, hd⟩
  have equal : d = (⟨b.artifact, position⟩ : CollectedDef) := hd.symm.trans hc.2.2.2.1
  exact foreign (congrArg CollectedDef.artifact equal)

open SourceInternalContextR55 ProviderNativeContextR57 SourceInternalChoiceR77

/-- R78 now receives a solver key containing the entire collected identity.
HirDef never becomes a Key by a cast or a spelling/ordinal comparison. -/
structure BridgedCapture (b : Batch) (query : HirDef) (s : Source CollectedDef Nat)
    (source : OwnerSource (Key CollectedDef Nat)) (calls : List (SourceCall (Key CollectedDef Nat)))
    (callIndex : Nat) (u : Use Nat (Key CollectedDef Nat)) (receiving : Key CollectedDef Nat) where
  target : CollectedDef
  translated : lookup b query = some target
  captured : IntegratedSourceAlignmentR78.Captured s source calls callIndex u receiving (.source target)

def bridgeCapture (b : Batch) (query : HirDef) (s : Source CollectedDef Nat)
    (source : OwnerSource (Key CollectedDef Nat)) (calls : List (SourceCall (Key CollectedDef Nat)))
    (callIndex : Nat) (u : Use Nat (Key CollectedDef Nat)) (receiving : Key CollectedDef Nat) :
    Option (BridgedCapture b query s source calls callIndex u receiving) :=
  match translated : lookup b query with
  | none => none
  | some target => do
    let captured ← IntegratedSourceAlignmentR78.capture s source calls callIndex u receiving (.source target)
    pure ⟨target, translated, captured⟩

theorem bridged_capture_applies_r78 (b : Batch) (ordered : OrderedRoots b)
    (query : HirDef) (s : Source CollectedDef Nat)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory CollectedDef Nat)
    (source : OwnerSource (Key CollectedDef Nat)) (calls : List (SourceCall (Key CollectedDef Nat)))
    (callIndex : Nat) (u : Use Nat (Key CollectedDef Nat)) (receiving : Key CollectedDef Nat)
    (c : BridgedCapture b query s source calls callIndex u receiving) :
    (query, c.target) ∈ collectionMap b ∧
    IntegratedSourceAlignmentR78.rootCoordinates source calls callIndex u receiving (.source c.target) = true ∧
    c.captured.aligned.selectedUse.use = u ∧
    (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence).plan (use u) =
      some (SourceInternalContextR55.plan c.captured.aligned.choice.plan) ∧
    OccurrenceQualifiedConsumerR66.ownerSelection s (.source c.target)
      c.captured.aligned.choice.plan.targetRootComponent = some c.captured.aligned.choice.origin ∧
    s.parameterRecipes[c.captured.aligned.choice.formal.recipePosition]? =
      some c.captured.aligned.choice.formal.parameter := by
  exact ⟨lookup_agrees_with_collection_map b ordered query c.target c.translated,
    IntegratedSourceAlignmentR78.capture_root_coordinates s source calls callIndex u receiving (.source c.target) c.captured,
    IntegratedSourceAlignmentR78.capture_applies_r66 s inventory source calls callIndex u receiving (.source c.target) c.captured⟩

def firstId : HirDef := ⟨7, 40, 0⟩
def sameNameId : HirDef := ⟨7, 40, 1⟩
def foreignModuleId : HirDef := ⟨8, 40, 0⟩
def firstRoot : Root := ⟨100, 0⟩
def secondRoot : Root := ⟨100, 1⟩
def fixture : Batch :=
  { artifact := 900
    hirs := [⟨100, [⟨firstId, firstRoot⟩, ⟨sameNameId, secondRoot⟩]⟩]
    definitions := [⟨⟨900, 0⟩, firstRoot⟩, ⟨⟨900, 1⟩, secondRoot⟩]
    rootHirPositions := [0, 0]
    rootPositions := [(firstRoot, 0), (secondRoot, 1)]
    definitionPositions := [(⟨900, 0⟩, 0), (⟨900, 1⟩, 1)] }

theorem fixture_ordered_roots : OrderedRoots fixture := by
  intro p member
  simp [locatedBindings, fixture] at member
  rcases member with rfl | rfl <;> decide

theorem finite_constructed_bridge :
    lookup fixture firstId = some ⟨900, 0⟩ ∧
    lookup fixture sameNameId = some ⟨900, 1⟩ ∧
    lookup fixture foreignModuleId = none ∧
    firstId.spelling = sameNameId.spelling ∧ firstId ≠ sameNameId ∧
    (firstId, (⟨900, 0⟩ : CollectedDef)) ∈ collectionMap fixture ∧
    (sameNameId, (⟨900, 1⟩ : CollectedDef)) ∈ collectionMap fixture := by decide

theorem finite_rejects_corrupt_coordinates :
    lookup {fixture with artifact := 901} firstId = none ∧
    lookup {fixture with rootHirPositions := [1, 0]} firstId = none ∧
    lookup {fixture with definitions := [⟨⟨901, 0⟩, firstRoot⟩]} firstId = none ∧
    lookup {fixture with definitions := [⟨⟨900, 1⟩, firstRoot⟩]} firstId = none ∧
    lookup {fixture with definitions := [⟨⟨900, 0⟩, secondRoot⟩]} firstId = none ∧
    lookup {fixture with hirs := [⟨101, [⟨firstId, firstRoot⟩]⟩]} firstId = none ∧
    lookup {fixture with definitionPositions := [(⟨900, 0⟩, 1)]} firstId = none ∧
    lookup {fixture with rootPositions := [(firstRoot, 0), (firstRoot, 1)]} firstId = none ∧
    lookup {fixture with hirs := [⟨100, [⟨firstId, firstRoot⟩, ⟨firstId, secondRoot⟩]⟩]} firstId = none ∧
    lookup {fixture with hirs := fixture.hirs ++ fixture.hirs} firstId = none ∧
    (lookup fixture firstId == some (⟨901, 0⟩ : CollectedDef)) = false := by decide

theorem finite_unrelated_malformed_binding_retained :
    lookup {fixture with hirs := [⟨100,
      [⟨firstId, firstRoot⟩, ⟨sameNameId, ⟨999, 15⟩⟩]⟩]} firstId = some ⟨900, 0⟩ := by decide

end YulangClosure.CollectedDefinitionBridgeR79
