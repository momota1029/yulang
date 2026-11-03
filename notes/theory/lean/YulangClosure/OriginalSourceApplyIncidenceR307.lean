import YulangClosure.OriginalSourceOwnerReificationInstance
import YulangClosure.SourceAppAdmissionR159

/-!
R307: finite, exact source Apply incidence. This extends the use of the
unchanged owner reification relation; it does not repair that relation globally.
Raw occurrence ordinals and LocalSource indices are not OriginalSource sites.
Source-key IDs are meaningful only within the one emitted extraction.
SG §§3.1–3.3 and EI-All §4 retain their original semantic premises.
-/
namespace YulangClosure.OriginalSourceApplyIncidenceR307

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceOwnerReification

/-- Exact frozen R307 extractor schema. -/
structure ApplyNodeRef where
  localSourceIndex : Nat
  occurrenceOrdinal : Nat
  sourceKeyId : Nat
  sourcePositionOrdinal : Nat
  byteRange : Nat × Nat
  sourceForm : String
  deriving DecidableEq, Repr

structure ApplyOccurrenceRow where
  ownerDefinitionSourceKeyId : Nat
  ownerLocalSourceIndex : Nat
  application : ApplyNodeRef
  rawCallee : ApplyNodeRef
  argument : ApplyNodeRef
  rawCalleeGroupProjection : List ApplyNodeRef
  applySourceForm : String
  deriving DecidableEq, Repr

/-- The same execution's JSON key table, retaining its full ID and locators. -/
structure SourceKeyRow where
  id : Nat
  position : Nat
  byteRange : Nat × Nat
  kind : String
  deriving DecidableEq, Repr

/-- All fields of each edge are compared; source-key equality alone cannot
identify an occurrence, including the implicit Unit at an empty call. -/
def ExactApply (rows : List ApplyOccurrenceRow) (row : ApplyOccurrenceRow)
    (parent callee argument : ApplyNodeRef) : Prop :=
  row ∈ rows ∧ row.application = parent ∧ row.rawCallee = callee ∧ row.argument = argument

def PhysicalJoin (table : OriginTable) (keys : List SourceKeyRow)
    (key : PhysicalKey) (node : ApplyNodeRef) : Prop :=
  ∃ physical ∈ table.physical, physical.key = key ∧
    physical.sourceLocator = ⟨node.sourcePositionOrdinal, node.byteRange⟩ ∧
    physical.localSourceIndex = some node.localSourceIndex ∧
    physical.occurrenceOrdinal = some node.occurrenceOrdinal ∧
    ∃ raw ∈ keys, raw.id = node.sourceKeyId ∧ raw.position = node.sourcePositionOrdinal ∧
      raw.byteRange = node.byteRange

/-- A definition-owned LocalSource root, joined through its actual key table.
This does not turn the declaration ordinal into an OriginalSource Context. -/
def OwnerJoin (table : OriginTable) (keys : List SourceKeyRow)
    (row : ApplyOccurrenceRow) (root : PhysicalKey) : Prop :=
  (∃ definition ∈ table.physical, definition.key = .definition ∧
    ∃ raw ∈ keys, raw.id = row.ownerDefinitionSourceKeyId ∧
      definition.sourceLocator = ⟨raw.position, raw.byteRange⟩) ∧
  (∃ physical ∈ table.physical, physical.key = root ∧
    physical.localSourceIndex = some row.ownerLocalSourceIndex)

/-- The list excludes rawCallee and contains every successive Group.inner,
including the final non-Group. Each physical Group is retained in the tree. -/
inductive GroupPath (table : OriginTable) (keys : List SourceKeyRow) :
    ApplyNodeRef → List ApplyNodeRef → LocatedExpression → Prop where
  | stop {raw expression}
      (terminal : raw.sourceForm ≠ "Group")
      (root : PhysicalJoin table keys expression.root raw) :
      GroupPath table keys raw [] expression
  | group {raw inner rest site projected body}
      (isGroup : raw.sourceForm = "Group")
      (root : PhysicalJoin table keys site raw)
      (edge : GroupRow) (present : edge ∈ table.groups)
      (atGroup : edge.group = site) (toChild : edge.projected = projected)
      (childRoot : body.root = projected)
      (child : GroupPath table keys inner rest body) :
      GroupPath table keys raw (inner :: rest) (.group site projected body)

/-- No source judgment, desired descriptor, EI interpretation or admission is
an incidence field. Child table-to-source derivations are separate premises. -/
structure AppIncidence (table : OriginTable) (keys : List SourceKeyRow)
    (rows : List ApplyOccurrenceRow) (row : ApplyOccurrenceRow)
    (ownerRoot site : PhysicalKey) (callee argument : LocatedExpression) : Prop where
  exactRow : ExactApply rows row row.application row.rawCallee row.argument
  owner : OwnerJoin table keys row ownerRoot
  applicationForm : row.application.sourceForm = "Apply"
  parent : PhysicalJoin table keys site row.application
  calleePath : GroupPath table keys row.rawCallee row.rawCalleeGroupProjection callee
  argumentRoot : PhysicalJoin table keys argument.root row.argument

theorem group_path_retains_group {table : OriginTable} {keys : List SourceKeyRow}
    {raw : ApplyNodeRef} {path : List ApplyNodeRef} {expression : LocatedExpression}
    (isGroup : raw.sourceForm = "Group")
    (proof : GroupPath table keys raw path expression) :
    ∃ site projected body inner rest,
      expression = .group site projected body ∧ path = inner :: rest := by
  cases proof with
  | stop terminal _ => exact False.elim (terminal isGroup)
  | group _ _ _ _ _ _ _ _ => exact ⟨_, _, _, _, _, rfl, rfl⟩

theorem app_table_to_source {table : OriginTable} {keys : List SourceKeyRow}
    {rows : List ApplyOccurrenceRow} {row : ApplyOccurrenceRow}
    {ownerRoot site : PhysicalKey} {callee argument : LocatedExpression}
    {coordinates : OriginalCoordinates} {calleeSource argumentSource : Source .expression}
    (incidence : AppIncidence table keys rows row ownerRoot site callee argument)
    (left : TableToSource table coordinates callee calleeSource)
    (right : TableToSource table coordinates argument argumentSource) :
    TableToSource table coordinates (.app site callee argument)
      (.app ⟨coordinates.physical site, none⟩ calleeSource argumentSource) := by
  obtain ⟨physical, present, atSite, _⟩ := incidence.parent
  exact TableToSource.app site callee argument calleeSource argumentSource physical
    present atSite left right

/-- Apply the unchanged R159 consumer to a reified App. All semantic inputs
remain visible, and both children share the very same candidate extension. -/
theorem table_app_admission_iff {s : Sorts} {View : Type}
    {table : OriginTable} {coordinates : OriginalCoordinates}
    {site : PhysicalKey} {callee argument : LocatedExpression} {source : Source .expression}
    (derived : TableToSource table coordinates (.app site callee argument) source)
    (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) :
    let kernel := admissionKernel inputs readout admissions original
    let mark : Mark := ⟨coordinates.physical site, none⟩
    SourceJudgment kernel environment context source ↔
      (∀ premise ∈ SourceAppAdmissionR159.annotationPremises context mark,
        Local kernel environment premise) ∧
      ∃ occurrence data state,
        decode readout environment = some state ∧
        admissions.logical state ⟨mark.site, .viewLogic, 0⟩ .viewLogic data ∧
        let candidate := scopeCandidate environment occurrence (.logical .viewLogic data)
        let after := environment.extend ⟨mark.site, .viewLogic, 0⟩ candidate
        (∀ premise ∈ SourceAppAdmissionR159.appPremises context mark
          (callee.erase coordinates) (argument.erase coordinates), Local kernel after premise) ∧
        SourceJudgment kernel after context (callee.erase coordinates) ∧
        SourceJudgment kernel after context (argument.erase coordinates) := by
  rw [table_to_source_erasure derived]
  exact SourceAppAdmissionR159.app_admission_iff inputs readout admissions original
    environment context ⟨coordinates.physical site, none⟩
      (callee.erase coordinates) (argument.erase coordinates)


/- Frozen emitted owner.lean SHA-256: 27fb71cb057980f32c827ddc591cf72846dd646649452f554abf322291ca116d.
The declaration below is copied verbatim; key rows are projected from the same-run JSON. -/
namespace OwnerExtract
def source : String := "my value = \\x -> { (\\x -> x) x; x }"
def applyIncidences : List ApplyOccurrenceRow := [{ ownerDefinitionSourceKeyId := 0, ownerLocalSourceIndex := 0, application := { localSourceIndex := 3, occurrenceOrdinal := 3, sourceKeyId := 1, sourcePositionOrdinal := 39, byteRange := (29, 30), sourceForm := "Apply" }, rawCallee := { localSourceIndex := 4, occurrenceOrdinal := 4, sourceKeyId := 2, sourcePositionOrdinal := 25, byteRange := (19, 28), sourceForm := "Group" }, argument := { localSourceIndex := 5, occurrenceOrdinal := 7, sourceKeyId := 3, sourcePositionOrdinal := 41, byteRange := (29, 30), sourceForm := "Name" }, rawCalleeGroupProjection := [{ localSourceIndex := 6, occurrenceOrdinal := 5, sourceKeyId := 4, sourcePositionOrdinal := 28, byteRange := (20, 27), sourceForm := "Lambda" }], applySourceForm := "MlArgument" }]
def keys : List SourceKeyRow := [
  { id := 0, position := 1, byteRange := (0, 35), kind := "BindingStatement" },
  { id := 1, position := 39, byteRange := (29, 30), kind := "MlArgument" },
  { id := 2, position := 25, byteRange := (19, 28), kind := "ParenthesizedExpression" },
  { id := 3, position := 41, byteRange := (29, 30), kind := "IdentifierExpression" },
  { id := 4, position := 28, byteRange := (20, 27), kind := "LambdaExpression" }
]
def row : ApplyOccurrenceRow := applyIncidences[0]
end OwnerExtract

/- Frozen emitted nested.lean SHA-256: c4d12693cc0b53f2a16ef43f63091e640ae2a2b3aecb23f584aab07ae2ba7733.
The declaration below is copied verbatim; key rows are projected from the same-run JSON. -/
namespace NestedExtract
def source : String := "my value f = f() (f())\n"
def applyIncidences : List ApplyOccurrenceRow := [{ ownerDefinitionSourceKeyId := 0, ownerLocalSourceIndex := 0, application := { localSourceIndex := 1, occurrenceOrdinal := 2, sourceKeyId := 1, sourcePositionOrdinal := 24, byteRange := (17, 22), sourceForm := "Apply" }, rawCallee := { localSourceIndex := 2, occurrenceOrdinal := 3, sourceKeyId := 2, sourcePositionOrdinal := 20, byteRange := (14, 16), sourceForm := "Apply" }, argument := { localSourceIndex := 3, occurrenceOrdinal := 6, sourceKeyId := 3, sourcePositionOrdinal := 26, byteRange := (17, 22), sourceForm := "Group" }, rawCalleeGroupProjection := [], applySourceForm := "MlArgument" },{ ownerDefinitionSourceKeyId := 0, ownerLocalSourceIndex := 0, application := { localSourceIndex := 2, occurrenceOrdinal := 3, sourceKeyId := 2, sourcePositionOrdinal := 20, byteRange := (14, 16), sourceForm := "Apply" }, rawCallee := { localSourceIndex := 4, occurrenceOrdinal := 5, sourceKeyId := 4, sourcePositionOrdinal := 18, byteRange := (13, 14), sourceForm := "Name" }, argument := { localSourceIndex := 5, occurrenceOrdinal := 4, sourceKeyId := 2, sourcePositionOrdinal := 20, byteRange := (14, 16), sourceForm := "Unit" }, rawCalleeGroupProjection := [], applySourceForm := "CallTail" },{ ownerDefinitionSourceKeyId := 0, ownerLocalSourceIndex := 0, application := { localSourceIndex := 6, occurrenceOrdinal := 7, sourceKeyId := 5, sourcePositionOrdinal := 31, byteRange := (19, 21), sourceForm := "Apply" }, rawCallee := { localSourceIndex := 7, occurrenceOrdinal := 9, sourceKeyId := 6, sourcePositionOrdinal := 29, byteRange := (18, 19), sourceForm := "Name" }, argument := { localSourceIndex := 8, occurrenceOrdinal := 8, sourceKeyId := 5, sourcePositionOrdinal := 31, byteRange := (19, 21), sourceForm := "Unit" }, rawCalleeGroupProjection := [], applySourceForm := "CallTail" }]
def keys : List SourceKeyRow := [
  { id := 0, position := 1, byteRange := (0, 22), kind := "BindingStatement" },
  { id := 1, position := 24, byteRange := (17, 22), kind := "MlArgument" },
  { id := 2, position := 20, byteRange := (14, 16), kind := "CallTail" },
  { id := 3, position := 26, byteRange := (17, 22), kind := "ParenthesizedExpression" },
  { id := 4, position := 18, byteRange := (13, 14), kind := "IdentifierExpression" },
  { id := 5, position := 31, byteRange := (19, 21), kind := "CallTail" },
  { id := 6, position := 29, byteRange := (18, 19), kind := "IdentifierExpression" }
]
def row : ApplyOccurrenceRow := applyIncidences[0]
end NestedExtract

/- Frozen emitted empty.lean SHA-256: d52bbe0f26bbba7f4a3a3a0e3b0840d9e97f7845f7ee772666ff55819be69f60.
The declaration below is copied verbatim; key rows are projected from the same-run JSON. -/
namespace EmptyExtract
def source : String := "my invoke f = f()\n"
def applyIncidences : List ApplyOccurrenceRow := [{ ownerDefinitionSourceKeyId := 0, ownerLocalSourceIndex := 0, application := { localSourceIndex := 1, occurrenceOrdinal := 2, sourceKeyId := 1, sourcePositionOrdinal := 20, byteRange := (15, 17), sourceForm := "Apply" }, rawCallee := { localSourceIndex := 2, occurrenceOrdinal := 4, sourceKeyId := 2, sourcePositionOrdinal := 18, byteRange := (14, 15), sourceForm := "Name" }, argument := { localSourceIndex := 3, occurrenceOrdinal := 3, sourceKeyId := 1, sourcePositionOrdinal := 20, byteRange := (15, 17), sourceForm := "Unit" }, rawCalleeGroupProjection := [], applySourceForm := "CallTail" }]
def keys : List SourceKeyRow := [
  { id := 0, position := 1, byteRange := (0, 17), kind := "BindingStatement" },
  { id := 1, position := 20, byteRange := (15, 17), kind := "CallTail" },
  { id := 2, position := 18, byteRange := (14, 15), kind := "IdentifierExpression" }
]
def row : ApplyOccurrenceRow := applyIncidences[0]
end EmptyExtract

open OriginalSourceOwnerReificationTrace
open OriginalSourceOwnerReificationInstance (coordinates)

theorem owner_input_exact : OwnerExtract.source = originTable.inputUtf8 := rfl

theorem owner_parent_join : PhysicalJoin originTable OwnerExtract.keys .application
    OwnerExtract.row.application := by
  refine ⟨originTable.physical[3], by decide, rfl, rfl, rfl, rfl, ?_⟩
  exact ⟨OwnerExtract.keys[1], by decide, rfl, rfl, rfl⟩

theorem owner_callee_join : PhysicalJoin originTable OwnerExtract.keys .rawCallee
    OwnerExtract.row.rawCallee := by
  refine ⟨originTable.physical[4], by decide, rfl, rfl, rfl, rfl, ?_⟩
  exact ⟨OwnerExtract.keys[2], by decide, rfl, rfl, rfl⟩

theorem owner_projection_join : PhysicalJoin originTable OwnerExtract.keys .innerLambda
    OwnerExtract.row.rawCalleeGroupProjection[0] := by
  refine ⟨originTable.physical[6], by decide, rfl, rfl, rfl, rfl, ?_⟩
  exact ⟨OwnerExtract.keys[4], by decide, rfl, rfl, rfl⟩

theorem owner_argument_join : PhysicalJoin originTable OwnerExtract.keys .argument
    OwnerExtract.row.argument := by
  refine ⟨originTable.physical[5], by decide, rfl, rfl, rfl, rfl, ?_⟩
  exact ⟨OwnerExtract.keys[3], by decide, rfl, rfl, rfl⟩

theorem owner_incidence :
    AppIncidence originTable OwnerExtract.keys OwnerExtract.applyIncidences OwnerExtract.row
      .outerLambda .application (.group .rawCallee .innerLambda innerTerm) argumentTerm := by
  refine ⟨by unfold ExactApply; decide, ?_, rfl, owner_parent_join, ?_, owner_argument_join⟩
  · constructor
    · refine ⟨originTable.physical[0], by decide, rfl, ?_⟩
      exact ⟨OwnerExtract.keys[0], by decide, rfl, rfl⟩
    · exact ⟨originTable.physical[1], by decide, rfl, rfl⟩
  · exact .group rfl owner_callee_join originTable.groups[0] (by decide) rfl rfl rfl
      (.stop (by decide) owner_projection_join)

/-- Original constructor application with both existing independent child
reifications, now attached to the actual emitted Apply edges. -/
theorem owner_application :
    TableToSource originTable coordinates applicationTerm (applicationTerm.erase coordinates) :=
  app_table_to_source owner_incidence
    OriginalSourceOwnerReificationInstance.grouped_inner_source
    OriginalSourceOwnerReificationInstance.argument_source

theorem owner_swapped_children_rejected :
    ¬ ExactApply OwnerExtract.applyIncidences OwnerExtract.row OwnerExtract.row.application
      OwnerExtract.row.argument OwnerExtract.row.rawCallee := by unfold ExactApply; decide

theorem owner_missing_group_rejected :
    ¬ GroupPath originTable OwnerExtract.keys OwnerExtract.row.rawCallee [] innerTerm := by
  intro proof
  obtain ⟨_, _, _, _, _, _, impossible⟩ := group_path_retains_group rfl proof
  cases impossible

theorem owner_swapped_reification_rejected :
    ¬ AppIncidence originTable OwnerExtract.keys OwnerExtract.applyIncidences OwnerExtract.row
      .outerLambda .application argumentTerm (.group .rawCallee .innerLambda innerTerm) := by
  intro incidence
  obtain ⟨_, _, _, _, _, impossible, _⟩ :=
    group_path_retains_group rfl incidence.calleePath
  cases impossible

theorem owner_ungrouped_reification_rejected :
    ¬ AppIncidence originTable OwnerExtract.keys OwnerExtract.applyIncidences OwnerExtract.row
      .outerLambda .application innerTerm argumentTerm := by
  intro incidence
  obtain ⟨_, _, _, _, _, impossible, _⟩ :=
    group_path_retains_group rfl incidence.calleePath
  cases impossible

/-- A nested computed callee is precisely the other emitted Apply occurrence,
with all occurrence, local-index, key, locator and form fields retained. -/
theorem nested_computed_callee :
    NestedExtract.row.rawCallee = NestedExtract.applyIncidences[1].application ∧
    NestedExtract.row.rawCallee.sourceForm = "Apply" ∧
    NestedExtract.applyIncidences.length = 3 := by decide

theorem empty_shared_key_distinct_occurrences :
    EmptyExtract.row.application.sourceKeyId = EmptyExtract.row.argument.sourceKeyId ∧
    EmptyExtract.row.application.sourcePositionOrdinal =
      EmptyExtract.row.argument.sourcePositionOrdinal ∧
    EmptyExtract.row.application.byteRange = EmptyExtract.row.argument.byteRange ∧
    EmptyExtract.row.application.occurrenceOrdinal ≠ EmptyExtract.row.argument.occurrenceOrdinal ∧
    EmptyExtract.row.application.localSourceIndex ≠ EmptyExtract.row.argument.localSourceIndex := by decide

theorem empty_conflation_rejected :
    ¬ ExactApply EmptyExtract.applyIncidences EmptyExtract.row EmptyExtract.row.application
      EmptyExtract.row.rawCallee
      { EmptyExtract.row.argument with
        occurrenceOrdinal := EmptyExtract.row.application.occurrenceOrdinal } := by
  unfold ExactApply
  decide

/-- Unchanged R159 at the actual fixture's parent and both actual children.
Nothing here chooses the incoming state, original admission or child judgments. -/
theorem owner_parent_edge {s : Sorts} {View : Type}
    (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) :
    let kernel := admissionKernel inputs readout admissions original
    let mark : Mark := ⟨coordinates.physical .application, none⟩
    let callee := (.group .rawCallee .innerLambda innerTerm : LocatedExpression).erase coordinates
    let argument := argumentTerm.erase coordinates
    SourceJudgment kernel environment context (applicationTerm.erase coordinates) ↔
      (∀ premise ∈ SourceAppAdmissionR159.annotationPremises context mark,
        Local kernel environment premise) ∧
      ∃ occurrence data state,
        decode readout environment = some state ∧
        admissions.logical state ⟨mark.site, .viewLogic, 0⟩ .viewLogic data ∧
        let candidate := scopeCandidate environment occurrence (.logical .viewLogic data)
        let after := environment.extend ⟨mark.site, .viewLogic, 0⟩ candidate
        (∀ premise ∈ SourceAppAdmissionR159.appPremises context mark callee argument,
          Local kernel after premise) ∧
        SourceJudgment kernel after context callee ∧
        SourceJudgment kernel after context argument :=
  table_app_admission_iff owner_application inputs readout admissions original environment context

end YulangClosure.OriginalSourceApplyIncidenceR307
