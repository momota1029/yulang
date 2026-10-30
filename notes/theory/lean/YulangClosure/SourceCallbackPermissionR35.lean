import YulangClosure.NativeSnapshotOwnerR34

/-!
R35 candidate source projection, pinned to the source-row R35 manifest.
SourceNodeKey uses R31's parse/green/start identity, not spelling or a span.
The arena is indexed by the retained R34 owner, then by actual source root and
expression. Witness construction traverses Lambda -> formal -> annotation ->
structural type path -> effect row. No caller supplies a replacement row.
This is a formal model of the source constructors; Rust extraction/simulation,
permission polarity, runtime Grant, and original all-source A/B remain open.
-/
namespace YulangClosure.SourceCallbackPermissionR35
open NativeCallbackGrantBridgeR31 NativeCallbackGrantBridgeR32
open NativeCallbackCoordinatesR33 NativeSnapshotOwnerR34

inductive MemberKind where
  | role | implementation
  deriving DecidableEq

/-- Exact native identity fields; Artifact/Definition represent their existing
identity types. HIR allocation identity is separately the R34 owner index. -/
inductive RootId (Artifact Definition Module Parse Green : Type) where
  | definition (artifact : Artifact) (definition : Definition)
  | expression (artifact : Artifact) (occurrence : Nat)
  | member (artifact : Artifact) (moduleIdentity : Module)
      (declaration member : SourceNodeKey Parse Green) (kind : MemberKind)
  deriving DecidableEq

structure ParameterId (Artifact Definition Module Parse Green : Type) where
  owner : RootId Artifact Definition Module Parse Green
  ordinal : Nat
  deriving DecidableEq

structure EffectRow (Module Parse Green : Type) where
  position : SourceNodeKey Parse Green
  concrete : List (SourceEffectId Module Parse Green)
  variables : List String
  deriving DecidableEq

mutual
  inductive AnnotationType (Module Parse Green : Type) where
    | mk (effects : Option (EffectRow Module Parse Green))
        (value : AnnotationValue Module Parse Green)
  inductive AnnotationValue (Module Parse Green : Type) where
    | unit | int | bool | str
    | variable (name : String)
    | hole (position : SourceNodeKey Parse Green)
    | tuple (elements : List (AnnotationType Module Parse Green))
    | function (argument result : AnnotationType Module Parse Green)
end

structure SourceAnnotation (Artifact Definition Module Parse Green : Type) where
  owner : RootId Artifact Definition Module Parse Green
  position : SourceNodeKey Parse Green
  ty : AnnotationType Module Parse Green

structure Parameter (Artifact Definition Module Parse Green : Type) where
  id : ParameterId Artifact Definition Module Parse Green
  source : SourceNodeKey Parse Green
  startByte : Nat
  endByte : Nat
  annotation : Option (SourceAnnotation Artifact Definition Module Parse Green)

/-- Projection keeps every other source form as an opaque non-Lambda payload;
no typing/simulation theorem for those forms is claimed or needed to reject. -/
inductive Form (Artifact Definition Module Parse Green : Type) where
  | lambda (formal : Parameter Artifact Definition Module Parse Green) (body : Nat)
  | other (sourceConstructor : Nat)

structure Expression (Artifact Definition Module Parse Green : Type) where
  occurrence : Nat
  source : SourceNodeKey Parse Green
  startByte : Nat
  endByte : Nat
  form : Form Artifact Definition Module Parse Green

structure SourceRoot (Artifact Definition Module Parse Green : Type) where
  id : RootId Artifact Definition Module Parse Green
  expressions : List (Expression Artifact Definition Module Parse Green)

structure SourcePool (history : AllocationHistory)
    (Artifact Definition Module Parse Green : Type) where
  roots : OwnerId history → List (SourceRoot Artifact Definition Module Parse Green)
  effects : OwnerId history → List (HirEffect Module Parse Green)

inductive TypeStep where
  | argument | result | tuple (index : Nat)
  deriving DecidableEq

/-- Path lookup uses actual nested annotation constructors. In particular,
cb : () -> [E] int selects [.result], not the formal's outer effects. -/
def selectRow (ty : AnnotationType Module Parse Green) :
    List TypeStep → Option (EffectRow Module Parse Green)
  | [] => match ty with | .mk effects _ => effects
  | step :: rest => match ty with
    | .mk _ (.function argument result) => match step with
      | .argument => selectRow argument rest
      | .result => selectRow result rest
      | .tuple _ => none
    | .mk _ (.tuple elements) => match step with
      | .tuple index => do
        let element ← elements[index]?
        selectRow element rest
      | _ => none
    | _ => none

structure SelectedFormal (Artifact Definition Module Parse Green : Type) where
  root : RootId Artifact Definition Module Parse Green
  lambdaOccurrence : Nat
  lambdaSource : SourceNodeKey Parse Green
  lambdaStart : Nat
  lambdaEnd : Nat
  formal : Parameter Artifact Definition Module Parse Green
  annotation : SourceAnnotation Artifact Definition Module Parse Green

/-- This function is the source-origin construction, not a supplied LocalLaw. -/
def selectFormal (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (rootIndex expressionIndex : Nat) :
    Option (SelectedFormal Artifact Definition Module Parse Green) := do
  let root ← (pool.roots owner.hirOwner)[rootIndex]?
  let expression ← root.expressions[expressionIndex]?
  match expression.form with
  | .other _ => none
  | .lambda formal _ => do
    let annotation ← formal.annotation
    pure ⟨root.id, expression.occurrence, expression.source,
      expression.startByte, expression.endByte, formal, annotation⟩

structure Binding (history : AllocationHistory)
    (Artifact Definition Module Parse Green : Type) where
  snapshotOwner : OwnerId history
  root : RootId Artifact Definition Module Parse Green
  lambdaOccurrence : Nat
  lambdaSource : SourceNodeKey Parse Green
  lambdaStart : Nat
  lambdaEnd : Nat
  formal : ParameterId Artifact Definition Module Parse Green
  formalSource : SourceNodeKey Parse Green
  formalStart : Nat
  formalEnd : Nat
  annotationOwner : RootId Artifact Definition Module Parse Green
  annotationPosition : SourceNodeKey Parse Green
  rowPath : List TypeStep
  rowContravariant : Bool
  deriving DecidableEq

structure Witness (history : AllocationHistory)
    (Artifact Definition Module Parse Green : Type) where
  binding : Binding history Artifact Definition Module Parse Green
  row : EffectRow Module Parse Green
  deriving DecidableEq

/-- The formal begins contravariant; only Function.argument flips polarity. -/
def pathPolarity : Bool → List TypeStep → Bool
  | polarity, [] => polarity
  | polarity, .argument :: rest => pathPolarity (!polarity) rest
  | polarity, _ :: rest => pathPolarity polarity rest

variable {history : AllocationHistory} {Artifact Definition Module Parse Green : Type}
variable [DecidableEq Artifact] [DecidableEq Definition] [DecidableEq Module]
variable [DecidableEq Parse] [DecidableEq Green]

def fromSelection (owner : RuntimeOwner history)
    (s : SelectedFormal Artifact Definition Module Parse Green) (path : List TypeStep)
    (row : EffectRow Module Parse Green) : Witness history Artifact Definition Module Parse Green :=
  ⟨⟨owner.hirOwner, s.root, s.lambdaOccurrence, s.lambdaSource, s.lambdaStart, s.lambdaEnd,
    s.formal.id, s.formal.source, s.formal.startByte, s.formal.endByte,
    s.annotation.owner, s.annotation.position, path, pathPolarity true path⟩, row⟩

def issueSelected (owner : RuntimeOwner history)
    (s : SelectedFormal Artifact Definition Module Parse Green) (path : List TypeStep) :
    Option (Witness history Artifact Definition Module Parse Green) := do
  if s.formal.id.owner = s.root ∧ s.annotation.owner = s.root then
    let row ← selectRow s.annotation.ty path
    pure (fromSelection owner s path row)
  else none

def issue (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (rootIndex expressionIndex : Nat) (path : List TypeStep) :
    Option (Witness history Artifact Definition Module Parse Green) := do
  let selected ← selectFormal pool owner rootIndex expressionIndex
  issueSelected owner selected path

/-- Authentication recomputes from the same owner/arena/path. -/
def authenticate (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (rootIndex expressionIndex : Nat) (path : List TypeStep)
    (candidate : Witness history Artifact Definition Module Parse Green) : Prop :=
  issue pool owner rootIndex expressionIndex path = some candidate

instance (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat) (path : List TypeStep)
    (w : Witness history Artifact Definition Module Parse Green) :
    Decidable (authenticate pool owner ri ei path w) :=
  inferInstanceAs (Decidable (issue pool owner ri ei path = some w))

theorem issueSelected_exact (owner : RuntimeOwner history)
    (s : SelectedFormal Artifact Definition Module Parse Green) (path : List TypeStep)
    (w : Witness history Artifact Definition Module Parse Green) :
    issueSelected owner s path = some w ↔
      s.formal.id.owner = s.root ∧ s.annotation.owner = s.root ∧
      ∃ row, selectRow s.annotation.ty path = some row ∧
        w = fromSelection owner s path row := by
  unfold issueSelected
  by_cases owners : s.formal.id.owner = s.root ∧ s.annotation.owner = s.root
  · simp only [owners]
    cases found : selectRow s.annotation.ty path with
    | none => simp
    | some row => simp [eq_comm]
  · simp only [owners, ↓reduceIte, reduceCtorEq, false_iff]
    intro h
    exact owners ⟨h.1, h.2.1⟩

theorem source_origin (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat) (path : List TypeStep)
    (w : Witness history Artifact Definition Module Parse Green)
    (authentic : authenticate pool owner ri ei path w) :
    ∃ s, selectFormal pool owner ri ei = some s ∧
      s.formal.id.owner = s.root ∧ s.annotation.owner = s.root ∧
      ∃ row, selectRow s.annotation.ty path = some row ∧
        w = fromSelection owner s path row := by
  unfold authenticate issue at authentic
  cases selected : selectFormal pool owner ri ei with
  | none => simp [selected] at authentic
  | some s =>
    simp only [selected] at authentic
    exact ⟨s, rfl, (issueSelected_exact owner s path w).mp authentic⟩

omit [DecidableEq Artifact] [DecidableEq Definition] [DecidableEq Module]
  [DecidableEq Parse] [DecidableEq Green] in
/-- Success has an actual root/expression/Lambda/formal/annotation lookup chain. -/
theorem selection_is_lambda (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat)
    (s : SelectedFormal Artifact Definition Module Parse Green)
    (selected : selectFormal pool owner ri ei = some s) :
    ∃ root expression formal body annotation,
      (pool.roots owner.hirOwner)[ri]? = some root ∧
      root.expressions[ei]? = some expression ∧
      expression.form = .lambda formal body ∧ formal.annotation = some annotation ∧
      s = ⟨root.id, expression.occurrence, expression.source,
        expression.startByte, expression.endByte, formal, annotation⟩ := by
  unfold selectFormal at selected
  cases r : (pool.roots owner.hirOwner)[ri]? with
  | none => simp [r] at selected
  | some root =>
    cases e : root.expressions[ei]? with
    | none => simp [r, e] at selected
    | some expression =>
      cases f : expression.form with
      | other tag => simp [r, e, f] at selected
      | lambda formal body =>
        cases a : formal.annotation with
        | none => simp [r, e, f, a] at selected
        | some annotation =>
          have h : s = ⟨root.id, expression.occurrence, expression.source,
              expression.startByte, expression.endByte, formal, annotation⟩ := by
            simpa [r, e, f, a] using selected.symm
          exact ⟨root, expression, formal, body, annotation, rfl, e, f, a, h⟩

theorem selected_owner_rejects (owner : RuntimeOwner history)
    (s : SelectedFormal Artifact Definition Module Parse Green) (path : List TypeStep)
    (foreign : s.formal.id.owner ≠ s.root ∨ s.annotation.owner ≠ s.root) :
    issueSelected owner s path = none := by
  unfold issueSelected
  have bad : ¬(s.formal.id.owner = s.root ∧ s.annotation.owner = s.root) := by
    intro h
    cases foreign with
    | inl h' => exact h' h.1
    | inr h' => exact h' h.2
  simp [bad]

omit [DecidableEq Artifact] [DecidableEq Definition] [DecidableEq Module]
  [DecidableEq Parse] [DecidableEq Green] in
theorem row_payload_exact (owner : RuntimeOwner history)
    (s : SelectedFormal Artifact Definition Module Parse Green) (path : List TypeStep)
    (row : EffectRow Module Parse Green) :
    (fromSelection owner s path row).row = row := rfl

omit [DecidableEq Artifact] [DecidableEq Definition] [DecidableEq Module]
  [DecidableEq Parse] [DecidableEq Green] in
theorem concrete_order_multiplicity (owner : RuntimeOwner history)
    (s : SelectedFormal Artifact Definition Module Parse Green) (path : List TypeStep)
    (row : EffectRow Module Parse Green) (index : Nat) :
    (fromSelection owner s path row).row.concrete[index]? = row.concrete[index]? := rfl

omit [DecidableEq Artifact] [DecidableEq Definition] [DecidableEq Module]
  [DecidableEq Parse] [DecidableEq Green] in
theorem symbolic_variables_exact (owner : RuntimeOwner history)
    (s : SelectedFormal Artifact Definition Module Parse Green) (path : List TypeStep)
    (row : EffectRow Module Parse Green) :
    (fromSelection owner s path row).row.variables = row.variables := rfl

/-- Any identity/position/payload substitution is rejected, without comparing
family sets. The supplied equality is a computation result, not authenticity law. -/
theorem reject_changed_projection {α : Type}
    (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat) (path : List TypeStep)
    (issued candidate : Witness history Artifact Definition Module Parse Green)
    (computed : issue pool owner ri ei path = some issued)
    (projection : Witness history Artifact Definition Module Parse Green → α)
    (changed : projection candidate ≠ projection issued) :
    ¬ authenticate pool owner ri ei path candidate := by
  intro accepted
  have same : issued = candidate := Option.some.inj (computed.symm.trans accepted)
  exact changed (congrArg projection same.symm)

/-- The complete inventory is a path-indexed view of every source row. It
selects no preferred callback row and preserves absent rows as absent. -/
def inventory (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat) :
    List TypeStep → Option (Witness history Artifact Definition Module Parse Green) :=
  issue pool owner ri ei

theorem inventory_complete
    (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat)
    (s : SelectedFormal Artifact Definition Module Parse Green)
    (selected : selectFormal pool owner ri ei = some s)
    (formalOwner : s.formal.id.owner = s.root)
    (annotationOwner : s.annotation.owner = s.root) :
    ∀ path, inventory pool owner ri ei path =
      (selectRow s.annotation.ty path).map (fromSelection owner s path) := by
  intro path
  unfold inventory issue
  rw [selected]
  change issueSelected owner s path = _
  unfold issueSelected
  simp only [formalOwner, annotationOwner, and_self, ↓reduceIte]
  cases selectRow s.annotation.ty path <;> rfl

theorem authenticated_row_preservation
    (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat) (path : List TypeStep)
    (w : Witness history Artifact Definition Module Parse Green)
    (authentic : authenticate pool owner ri ei path w) :
    ∃ s row, selectFormal pool owner ri ei = some s ∧
      selectRow s.annotation.ty path = some row ∧
      w.row = row ∧ w.row.concrete = row.concrete ∧
      w.row.variables = row.variables ∧
      w.binding.snapshotOwner = owner.hirOwner ∧
      w.binding.formal = s.formal.id ∧
      w.binding.annotationPosition = s.annotation.position ∧
      w.binding.rowPath = path ∧ w.binding.rowContravariant = pathPolarity true path := by
  obtain ⟨s, selected, _, _, row, found, same⟩ :=
    source_origin pool owner ri ei path w authentic
  subst w
  exact ⟨s, row, selected, found, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem authenticated_binding_unique
    (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat) (path : List TypeStep)
    (issued candidate : Witness history Artifact Definition Module Parse Green)
    (first : authenticate pool owner ri ei path issued)
    (second : authenticate pool owner ri ei path candidate) :
    issued = candidate := Option.some.inj (first.symm.trans second)

/-- Same concrete and symbolic row content cannot authorize a different formal. -/
theorem foreign_formal_same_row_rejected
    (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat) (path : List TypeStep)
    (issued : Witness history Artifact Definition Module Parse Green)
    (computed : issue pool owner ri ei path = some issued)
    (foreign : ParameterId Artifact Definition Module Parse Green)
    (different : foreign ≠ issued.binding.formal) :
    ¬ authenticate pool owner ri ei path
      { issued with binding := { issued.binding with formal := foreign } } :=
  reject_changed_projection pool owner ri ei path issued _ computed
    (fun w => w.binding.formal) different

/-- Every identity and position belongs to the same issued witness. Differences
are checked even when candidate.row is definitionally unchanged. -/
theorem foreign_binding_rejected
    (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat) (path : List TypeStep)
    (issued candidate : Witness history Artifact Definition Module Parse Green)
    (computed : issue pool owner ri ei path = some issued)
    (different : candidate.binding ≠ issued.binding) :
    ¬ authenticate pool owner ri ei path candidate :=
  reject_changed_projection pool owner ri ei path issued candidate computed
    Witness.binding different

theorem foreign_row_position_rejected
    (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat) (path : List TypeStep)
    (issued candidate : Witness history Artifact Definition Module Parse Green)
    (computed : issue pool owner ri ei path = some issued)
    (different : candidate.row.position ≠ issued.row.position) :
    ¬ authenticate pool owner ri ei path candidate :=
  reject_changed_projection pool owner ri ei path issued candidate computed
    (fun w => w.row.position) different

omit [DecidableEq Artifact] [DecidableEq Definition] [DecidableEq Module]
  [DecidableEq Parse] [DecidableEq Green] in
theorem callback_result_row (effects : Option (EffectRow Module Parse Green))
    (argument result : AnnotationType Module Parse Green) :
    selectRow (.mk effects (.function argument result)) [.result] =
      selectRow result [] := rfl

omit [DecidableEq Artifact] [DecidableEq Definition] [DecidableEq Module]
  [DecidableEq Parse] [DecidableEq Green] in
theorem path_polarity_append (polarity : Bool) (left right : List TypeStep) :
    pathPolarity polarity (left ++ right) =
      pathPolarity (pathPolarity polarity left) right := by
  induction left generalizing polarity with
  | nil => rfl
  | cons step rest ih => cases step <;> exact ih _

theorem authenticated_owner_bound
    (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat) (path : List TypeStep)
    (w : Witness history Artifact Definition Module Parse Green)
    (authentic : authenticate pool owner ri ei path w) :
    w.binding.snapshotOwner = owner.hirOwner := by
  obtain ⟨s, _, _, _, row, _, same⟩ := source_origin pool owner ri ei path w authentic
  rw [same]
  rfl

theorem foreign_owner_rejected
    (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat) (path : List TypeStep)
    (w : Witness history Artifact Definition Module Parse Green)
    (foreign : w.binding.snapshotOwner ≠ owner.hirOwner) :
    ¬ authenticate pool owner ri ei path w :=
  fun authentic => foreign (authenticated_owner_bound pool owner ri ei path w authentic)

/-- A selected source row supplies R34's permissionRow; it is not independent
caller data. Missing selection has an empty projection and never authenticates. -/
def selectedPool (pool : SourcePool history Artifact Definition Module Parse Green)
    (ri ei : Nat) (path : List TypeStep) : RetainedPool history Module Parse Green :=
  ⟨fun id => ⟨pool.effects id,
    ((issue pool ⟨id⟩ ri ei path).map (fun w => w.row.concrete)).getD []⟩⟩

def translate (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat) (path : List TypeStep)
    (w : Witness history Artifact Definition Module Parse Green)
    (request consumer arm : OperationCoordinate (OwnerId history))
    (row : List (FamilyCoordinate (OwnerId history))) :
    Option (DecodedCoordinates Module Parse Green) :=
  if authenticate pool owner ri ei path w ∧ w.row.variables = [] then
    translateCoordinates (issuedSnapshot (selectedPool pool ri ei path) owner)
      request consumer arm row
  else none

theorem selected_pool_row (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat) (path : List TypeStep)
    (w : Witness history Artifact Definition Module Parse Green)
    (authentic : authenticate pool owner ri ei path w) :
    ((selectedPool pool ri ei path).data owner.hirOwner).permissionRow = w.row.concrete := by
  change ((issue pool owner ri ei path).map (fun w => w.row.concrete)).getD [] = _
  rw [authentic]
  rfl

theorem translate_exact (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat) (path : List TypeStep)
    (w : Witness history Artifact Definition Module Parse Green)
    (request consumer arm : OperationCoordinate (OwnerId history))
    (row : List (FamilyCoordinate (OwnerId history)))
    (out : DecodedCoordinates Module Parse Green)
    (success : translate pool owner ri ei path w request consumer arm row = some out) :
    authenticate pool owner ri ei path w ∧ w.row.variables = [] ∧
    translateCoordinates (issuedSnapshot (selectedPool pool ri ei path) owner)
      request consumer arm row = some out := by
  unfold translate at success
  split at success
  · rename_i h
    exact ⟨h.1, h.2, success⟩
  · cases success

theorem symbolic_row_rejected (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat) (path : List TypeStep)
    (w : Witness history Artifact Definition Module Parse Green)
    (request consumer arm : OperationCoordinate (OwnerId history))
    (row : List (FamilyCoordinate (OwnerId history)))
    (symbolic : w.row.variables ≠ []) :
    translate pool owner ri ei path w request consumer arm row = none := by
  unfold translate
  have bad : ¬(authenticate pool owner ri ei path w ∧ w.row.variables = []) :=
    fun h => symbolic h.2
  simp [bad]

/-- Application to the actual source-selected R34/R33/R32 computation, retaining
all ordered concrete entries. This supplies finite table facts, not a Grant. -/
theorem concrete_translation_to_r32
    (pool : SourcePool history Artifact Definition Module Parse Green)
    (owner : RuntimeOwner history) (ri ei : Nat) (path : List TypeStep)
    (w : Witness history Artifact Definition Module Parse Green)
    (request consumer arm : OperationCoordinate (OwnerId history))
    (row : List (FamilyCoordinate (OwnerId history)))
    (out : DecodedCoordinates Module Parse Green)
    (success : translate pool owner ri ei path w request consumer arm row = some out) :
    let table := coveringTable out.request out.consumer out.arm out.families
    authenticate pool owner ri ei path w ∧ w.row.variables = [] ∧
    out.families = w.row.concrete ∧ out.families.length = row.length ∧
    request.family.snapshotToken = ownerToken owner ∧
    consumer.family.snapshotToken = ownerToken owner ∧ arm.family.snapshotToken = ownerToken owner ∧
    decodeOperation table (operationKey table out.request) = some out.request ∧
    decodeOperation table (operationKey table out.consumer) = some out.consumer ∧
    decodeOperation table (operationKey table out.arm) = some out.arm ∧
    (∀ family ∈ w.row.concrete, family ∈ table.families) := by
  obtain ⟨authentic, concrete, decoded⟩ :=
    translate_exact pool owner ri ei path w request consumer arm row out success
  have bridge := owner_translation_to_r32 (selectedPool pool ri ei path) owner
    request consumer arm row decoded
  have exactRow := selected_pool_row pool owner ri ei path w authentic
  dsimp only at bridge ⊢
  rw [exactRow] at bridge
  exact ⟨authentic, concrete, bridge.1, bridge.2.1, bridge.2.2.1,
    bridge.2.2.2.1, bridge.2.2.2.2.1,
    bridge.2.2.2.2.2.2.2.2.2.2.1,
    bridge.2.2.2.2.2.2.2.2.2.2.2.1,
    bridge.2.2.2.2.2.2.2.2.2.2.2.2.1,
    bridge.2.2.2.2.2.2.2.2.2.1⟩

end YulangClosure.SourceCallbackPermissionR35
