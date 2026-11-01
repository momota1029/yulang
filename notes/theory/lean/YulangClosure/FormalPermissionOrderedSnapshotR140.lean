import Std

/-!
R140 constructed, UNCHECKED ordered projection. No executable verification is
authorized by this packet. No theorem below asserts Rust/native correspondence.
The eight identity tags retain their distinct payload types; FormalPosition is
owner/index, separately from Formal. All raw codes refer to one supplied table.
idxOf on an unregistered key is a length sentinel, not authenticated identity.
The order/filter theorems do not assume code injectivity or native equality.
-/
namespace YulangClosure.FormalPermissionOrderedSnapshotR140

inductive TaggedKey (Owner Occurrence Formal Scope Node Effect Symbol : Type) where
  | owner : Owner → TaggedKey Owner Occurrence Formal Scope Node Effect Symbol
  | occurrence : Occurrence → TaggedKey Owner Occurrence Formal Scope Node Effect Symbol
  | formal : Formal → TaggedKey Owner Occurrence Formal Scope Node Effect Symbol
  | formalPosition : Owner → Nat → TaggedKey Owner Occurrence Formal Scope Node Effect Symbol
  | scope : Scope → TaggedKey Owner Occurrence Formal Scope Node Effect Symbol
  | node : Node → TaggedKey Owner Occurrence Formal Scope Node Effect Symbol
  | effect : Effect → TaggedKey Owner Occurrence Formal Scope Node Effect Symbol
  | symbol : Scope → Symbol → TaggedKey Owner Occurrence Formal Scope Node Effect Symbol
  deriving DecidableEq

inductive Step where
  | argument | result | element (index : Nat)
  deriving DecidableEq, Repr

structure Context (Owner Occurrence Scope : Type) where
  parameter : Nat
  occurrence : Occurrence
  owner : Owner
  scope : Scope

structure Row (Node Effect Symbol : Type) where
  position : Node
  concrete : List Effect
  variables : List Symbol

inductive Leaf (Node Symbol : Type) where
  | unit | int | bool | str
  | variableRef : Symbol → Leaf Node Symbol
  | hole : Node → Leaf Node Symbol

mutual
  inductive Value (Node Effect Symbol : Type) where
    | leaf : Leaf Node Symbol → Value Node Effect Symbol
    | function (argument : Value Node Effect Symbol) (argumentRow : Option (Row Node Effect Symbol))
        (result : Value Node Effect Symbol) (resultRow : Option (Row Node Effect Symbol))
    | tuple : Elements Node Effect Symbol → Value Node Effect Symbol
  inductive Elements (Node Effect Symbol : Type) where
    | nil
    | cons (value : Value Node Effect Symbol) (row : Option (Row Node Effect Symbol))
        (rest : Elements Node Effect Symbol)
end

structure Port (Node Effect Symbol : Type) where
  positive : Bool
  path : List Step
  row : Option (Row Node Effect Symbol)

structure PermissionImage where
  parameter : Nat
  formalPosition : Nat
  occurrence : Nat
  owner : Nat
  scope : Nat
  path : List Step
  sourceRow : Nat
  concrete : List Nat
  deriving DecidableEq

/-- Kept in a separate vector; never included in the nested permission list. -/
structure EntryImage where
  registration : Nat
  parameter : Nat
  formal : Nat
  formalPosition : Nat
  occurrence : Nat
  owner : Nat
  scope : Nat
  annotationPosition : Nat
  sourceRow : Nat
  entryEffect : Nat
  concrete : List Nat
  deriving DecidableEq

variable {Owner Occurrence Formal Scope Node Effect Symbol : Type}
variable [DecidableEq Owner] [DecidableEq Occurrence] [DecidableEq Formal]
variable [DecidableEq Scope] [DecidableEq Node] [DecidableEq Effect] [DecidableEq Symbol]

abbrev Table := List (TaggedKey Owner Occurrence Formal Scope Node Effect Symbol)

def record (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (path : List Step)
    (row : Row Node Effect Symbol) : PermissionImage :=
  ⟨context.parameter, table.idxOf (.formalPosition context.owner context.parameter),
    table.idxOf (.occurrence context.occurrence), table.idxOf (.owner context.owner),
    table.idxOf (.scope context.scope), path, table.idxOf (.node row.position),
    row.concrete.map (fun effect => table.idxOf (.effect effect))⟩

def emit (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (port : Port Node Effect Symbol) : List PermissionImage :=
  match port.row with
  | none => []
  | some row =>
      if port.positive = false ∧ row.concrete ≠ [] ∧ row.variables = [] then
        [record table context port.path row]
      else []

/-- Native recursive pair admission; root annotation row is handled separately. -/
def rowAllowed (positive : Bool) : Option (Row Node Effect Symbol) → Bool
  | none => true
  | some row =>
      decide (row.variables.length ≤ 1) &&
        (positive || ((row.concrete.isEmpty && row.variables.length == 1) ||
          (!row.concrete.isEmpty && row.variables.isEmpty)))

mutual
  def supported : Value Node Effect Symbol → Bool → Bool
    | .leaf _, _ => true
    | .function argument ar result rr, positive =>
        rowAllowed (!positive) ar && supported argument (!positive) &&
          rowAllowed positive rr && supported result positive
    | .tuple .nil, _ => false
    | .tuple elements@(.cons _ _ _), positive => supportedElements elements positive
  def supportedElements : Elements Node Effect Symbol → Bool → Bool
    | .nil, _ => true
    | .cons value row rest, positive =>
        row.isNone && supported value positive && supportedElements rest positive
end

mutual
  def ports : Value Node Effect Symbol → Bool → List Step → List (Port Node Effect Symbol)
    | .leaf _, _, _ => []
    | .function argument ar result rr, positive, path =>
        ports argument (!positive) (path ++ [.argument]) ++
          ports result positive (path ++ [.result]) ++
          [⟨!positive, path ++ [.argument], ar⟩, ⟨positive, path ++ [.result], rr⟩]
    | .tuple elements, positive, path => elementPorts elements positive path 0
  def elementPorts : Elements Node Effect Symbol → Bool → List Step → Nat → List (Port Node Effect Symbol)
    | .nil, _, _, _ => []
    | .cons value _ rest, positive, path, index =>
        ports value positive (path ++ [.element index]) ++
          elementPorts rest positive path (index + 1)
end

mutual
  def inventory (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
      (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
      (context : Context Owner Occurrence Scope) :
      Value Node Effect Symbol → Bool → List Step → List PermissionImage
    | .leaf _, _, _ => []
    | .function argument ar result rr, positive, path =>
        inventory table context argument (!positive) (path ++ [.argument]) ++
          inventory table context result positive (path ++ [.result]) ++
          emit table context ⟨!positive, path ++ [.argument], ar⟩ ++
          emit table context ⟨positive, path ++ [.result], rr⟩
    | .tuple elements, positive, path => elementInventory table context elements positive path 0
  def elementInventory (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
      (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
      (context : Context Owner Occurrence Scope) :
      Elements Node Effect Symbol → Bool → List Step → Nat → List PermissionImage
    | .nil, _, _, _ => []
    | .cons value _ rest, positive, path, index =>
        inventory table context value positive (path ++ [.element index]) ++
          elementInventory table context rest positive path (index + 1)
end

section Theorems
variable (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
  (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
variable (context : Context Owner Occurrence Scope)

mutual
  theorem inventory_order_filter (value : Value Node Effect Symbol) (positive : Bool) (path : List Step) :
      inventory table context value positive path = (ports value positive path).flatMap (emit table context) := by
    cases value with
    | leaf _ => rfl
    | function argument ar result rr =>
        simp only [inventory, ports, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil,
          inventory_order_filter table context argument (!positive) (path ++ [.argument]),
          inventory_order_filter table context result positive (path ++ [.result]), List.append_assoc]
    | tuple elements => exact element_order_filter table context elements positive path 0
  theorem element_order_filter (elements : Elements Node Effect Symbol) (positive : Bool)
      (path : List Step) (index : Nat) :
      elementInventory table context elements positive path index =
        (elementPorts elements positive path index).flatMap (emit table context) := by
    cases elements with
    | nil => rfl
    | cons value row rest =>
        simp only [elementInventory, elementPorts, List.flatMap_append,
          inventory_order_filter table context value positive (path ++ [.element index]),
          element_order_filter table context rest positive path (index + 1)]
end

theorem record_fields (path : List Step) (row : Row Node Effect Symbol) :
    (record table context path row).parameter = context.parameter ∧
    (record table context path row).formalPosition = table.idxOf (.formalPosition context.owner context.parameter) ∧
    (record table context path row).occurrence = table.idxOf (.occurrence context.occurrence) ∧
    (record table context path row).owner = table.idxOf (.owner context.owner) ∧
    (record table context path row).scope = table.idxOf (.scope context.scope) ∧
    (record table context path row).path = path ∧
    (record table context path row).sourceRow = table.idxOf (.node row.position) ∧
    (record table context path row).concrete = row.concrete.map (fun effect => table.idxOf (.effect effect)) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem concrete_length (path : List Step) (row : Row Node Effect Symbol) :
    (record table context path row).concrete.length = row.concrete.length := by
  simp [record]

theorem concrete_position (path : List Step) (row : Row Node Effect Symbol) (index : Nat) :
    (record table context path row).concrete[index]? =
      row.concrete[index]?.map (fun effect => table.idxOf (.effect effect)) := by
  simp [record]

theorem concrete_duplicates (path : List Step) (position : Node) (effect : Effect)
    (rest : List Effect) :
    (record table context path (⟨position, effect :: effect :: rest, []⟩ : Row Node Effect Symbol)).concrete =
      table.idxOf (.effect effect) :: table.idxOf (.effect effect) ::
        rest.map (fun item => table.idxOf (.effect item)) := by
  rfl

theorem positive_filtered (path : List Step) (row : Row Node Effect Symbol) :
    emit table context ⟨true, path, some row⟩ = [] := by
  simp [emit]

theorem omitted_filtered (positive : Bool) (path : List Step) :
    emit table context (⟨positive, path, none⟩ : Port Node Effect Symbol) = [] := by
  rfl

theorem symbolic_filtered (positive : Bool) (path : List Step) (position : Node)
    (concrete : List Effect) (name : Symbol) (rest : List Symbol) :
    emit table context ⟨positive, path, some ⟨position, concrete, name :: rest⟩⟩ = [] := by
  simp [emit]

theorem empty_filtered (positive : Bool) (path : List Step) (position : Node) (variables : List Symbol) :
    emit table context ⟨positive, path, some ⟨position, [], variables⟩⟩ = [] := by
  simp [emit]

theorem concrete_emitted (path : List Step) (row : Row Node Effect Symbol)
    (nonempty : row.concrete ≠ []) (closed : row.variables = []) :
    emit table context ⟨false, path, some row⟩ = [record table context path row] := by
  simp [emit, nonempty, closed]

theorem mixed_negative_rejected (position : Node) (effect : Effect) (tail : List Effect) (name : Symbol) :
    rowAllowed false (some (⟨position, effect :: tail, [name]⟩ : Row Node Effect Symbol)) = false := by
  simp [rowAllowed]

theorem tuple_annotated_child_rejected (value : Value Node Effect Symbol) (row : Row Node Effect Symbol)
    (rest : Elements Node Effect Symbol) (positive : Bool) :
    supported (.tuple (.cons value (some row) rest)) positive = false := by
  simp [supported, supportedElements]

theorem empty_tuple_rejected (positive : Bool) :
    supported (Value.tuple (Elements.nil : Elements Node Effect Symbol)) positive = false := by
  rfl

end Theorems

structure Annotation (Node Effect Symbol : Type) where
  value : Value Node Effect Symbol
  rootRow : Option (Row Node Effect Symbol)

def nestedProjection (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (annotation : Annotation Node Effect Symbol) : List PermissionImage :=
  inventory table context annotation.value false []

def constructProjection (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (annotation : Annotation Node Effect Symbol) :
    Option (List PermissionImage) :=
  if supported annotation.value false then some (nestedProjection table context annotation) else none

theorem projection_success (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (annotation : Annotation Node Effect Symbol)
    (output : List PermissionImage) :
    constructProjection table context annotation = some output ↔
      supported annotation.value false = true ∧
        output = (ports annotation.value false []).flatMap (emit table context) := by
  cases accepted : supported annotation.value false <;>
    simp [constructProjection, nestedProjection, accepted, inventory_order_filter, eq_comm]

theorem root_row_separate (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (value : Value Node Effect Symbol)
    (before after : Option (Row Node Effect Symbol)) :
    nestedProjection table context ⟨value, before⟩ = nestedProjection table context ⟨value, after⟩ := by
  rfl

def aar : List Step := [.argument, .argument, .result]
def rrr : List Step := [.result, .result, .result]

def fixtureRows (first second : Row Node Effect Symbol) : Value Node Effect Symbol :=
  .function
    (.function (.function (.leaf .int) none (.leaf .unit) (some first)) none (.leaf .unit) none) none
    (.function (.leaf .unit) none (.function (.leaf .int) none (.leaf .unit) (some second)) none) none

theorem fixture_order (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (first second : Row Node Effect Symbol)
    (firstNonempty : first.concrete ≠ []) (firstClosed : first.variables = [])
    (secondNonempty : second.concrete ≠ []) (secondClosed : second.variables = []) :
    inventory table context (fixtureRows first second) false [] =
      [record table context aar first, record table context rrr second] := by
  simp [fixtureRows, inventory, emit, firstNonempty, firstClosed, secondNonempty, secondClosed, aar, rrr]

def ioRow (position : Node) (io : Effect) : Row Node Effect Symbol := ⟨position, [io], []⟩

theorem exact_aar_rrr_fixture (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (first second : Node) (io : Effect) :
    inventory table context (fixtureRows (ioRow first io) (ioRow second io)) false [] =
      [record table context aar (ioRow first io), record table context rrr (ioRow second io)] := by
  apply fixture_order <;> simp [ioRow]

theorem exact_fixture_admitted (first second : Node) (io : Effect) :
    supported (fixtureRows (ioRow first io : Row Node Effect Symbol) (ioRow second io)) false = true := by
  simp [fixtureRows, supported, rowAllowed, ioRow]

theorem exact_fixture_paths (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (first second : Node) (io : Effect) :
    (inventory table context (fixtureRows (ioRow first io) (ioRow second io)) false []).map PermissionImage.path =
      [aar, rrr] := by
  rw [exact_aar_rrr_fixture]
  rfl

theorem exact_fixture_rows (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (first second : Node) (io : Effect) :
    (inventory table context (fixtureRows (ioRow first io) (ioRow second io)) false []).map PermissionImage.sourceRow =
      [table.idxOf (.node first), table.idxOf (.node second)] := by
  rw [exact_aar_rrr_fixture]
  rfl

theorem exact_fixture_shared_effect (table : Table (Owner := Owner) (Occurrence := Occurrence) (Formal := Formal)
    (Scope := Scope) (Node := Node) (Effect := Effect) (Symbol := Symbol))
    (context : Context Owner Occurrence Scope) (first second : Node) (io : Effect) :
    (inventory table context (fixtureRows (ioRow first io) (ioRow second io)) false []).map PermissionImage.concrete =
      [[table.idxOf (.effect io)], [table.idxOf (.effect io)]] := by
  rw [exact_aar_rrr_fixture]
  rfl

/-- Pure append algebra only: connecting prefix/suffix to an actual same call
and State is an external source obligation, never a premise hidden here. -/
theorem appended_suffix (prefix suffix : List PermissionImage) :
    (prefix ++ suffix).drop prefix.length = suffix := by
  simp

structure Snapshot (Key : Type) where
  table : List Key
  rootEntriesBefore : List EntryImage
  nestedSuffix : List PermissionImage

inductive Failure where
  | callFailure | encoding | mismatch
  deriving DecidableEq

/-- Only compare supplied images. No claim that `actual` comes from Rust. -/
def compareAndFinish {Key : Type} (table : List Key) (expected actual : List PermissionImage)
    (entryBefore entryAfter : List EntryImage) : Except Failure (Snapshot Key) :=
  if actual = expected ∧ entryAfter = entryBefore then
    .ok ⟨table, entryBefore, actual⟩
  else .error .mismatch

theorem comparison_success {Key : Type} (table : List Key) (expected actual : List PermissionImage)
    (entryBefore entryAfter : List EntryImage) (snapshot : Snapshot Key)
    (success : compareAndFinish table expected actual entryBefore entryAfter = .ok snapshot) :
    actual = expected ∧ entryAfter = entryBefore := by
  unfold compareAndFinish at success
  split at success
  · assumption
  · cases success

def authenticated {Key : Type} : Except Failure (Snapshot Key) → Option (Snapshot Key)
  | .ok snapshot => some snapshot
  | .error _ => none

theorem error_excludes_snapshot {Key : Type} (error : Failure) (snapshot : Snapshot Key) :
    authenticated (.error error) ≠ some snapshot := by
  simp [authenticated]

end YulangClosure.FormalPermissionOrderedSnapshotR140


-- Future complete audit surface; NOT EXECUTED under R140.
set_option pp.fullNames true
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.inventory_order_filter
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.inventory_order_filter
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.element_order_filter
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.element_order_filter
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.record_fields
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.record_fields
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_length
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_length
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_position
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_position
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_duplicates
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_duplicates
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.positive_filtered
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.positive_filtered
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.omitted_filtered
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.omitted_filtered
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.symbolic_filtered
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.symbolic_filtered
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.empty_filtered
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.empty_filtered
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_emitted
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.concrete_emitted
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.mixed_negative_rejected
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.mixed_negative_rejected
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.tuple_annotated_child_rejected
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.tuple_annotated_child_rejected
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.empty_tuple_rejected
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.empty_tuple_rejected
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.projection_success
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.projection_success
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.root_row_separate
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.root_row_separate
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.fixture_order
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.fixture_order
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.exact_aar_rrr_fixture
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.exact_aar_rrr_fixture
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_admitted
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_admitted
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_paths
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_paths
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_rows
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_rows
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_shared_effect
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.exact_fixture_shared_effect
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.appended_suffix
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.appended_suffix
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.comparison_success
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.comparison_success
#check @YulangClosure.FormalPermissionOrderedSnapshotR140.error_excludes_snapshot
#print axioms YulangClosure.FormalPermissionOrderedSnapshotR140.error_excludes_snapshot
